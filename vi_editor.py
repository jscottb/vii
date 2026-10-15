#!/usr/bin/env python3

#####
#
# vii or 7  -  A single file python vi/vim-like editor -- Scott Beasley - 2022
#
# Open and free to the public for any use.
#
# AI maintained now. 
#
#####

import curses
import codecs
import errno
import sys
import os
import re
import contextlib
import fcntl
import fnmatch
import json
import base64
import hashlib
import mmap
import secrets
import selectors
import shutil
import signal
import stat
import string
import subprocess
import tempfile
import time
import unicodedata
import uuid
from bisect import bisect_left, bisect_right
from collections import deque, OrderedDict
from collections.abc import MutableSequence
from typing import Callable, Iterator, List, Tuple, Optional, Union
from dataclasses import dataclass, field
from datetime import datetime, timezone
from enum import Enum


# ---------------------------------------------------------------------------
# Data types
# ---------------------------------------------------------------------------

def _open_regular_file(filename: str, mode: str = "rb", **kwargs):
    """Open a regular file without blocking on a FIFO, including open races."""
    fd = os.open(filename, os.O_RDONLY | os.O_NONBLOCK)
    try:
        if not stat.S_ISREG(os.fstat(fd).st_mode):
            raise OSError(errno.EINVAL, "Not a regular file", filename)
        return os.fdopen(fd, mode, **kwargs)
    except BaseException:
        os.close(fd)
        raise


class PasteSegment(str):
    """Literal paste replay payload, including single control characters."""


class Mode(Enum):
    NORMAL       = "NORMAL"
    INSERT       = "INSERT"
    REPLACE      = "REPLACE"
    VISUAL       = "VISUAL"
    VISUAL_LINE  = "VLINE"
    VISUAL_BLOCK = "VBLOCK"
    HELP         = "HELP"
    HEX          = "HEX"
    LINE_ENDINGS = "LE"
    SHELL        = "SHELL"
    BUFFER_LIST   = "BUFFERS"
    FILE_BROWSER  = "FB"
    GREP_RESULTS  = "GREP"
    RECENT_FILES  = "RECENT"
    FUNCTIONS     = "FUNCS"


VISUAL_MODES = (Mode.VISUAL, Mode.VISUAL_LINE, Mode.VISUAL_BLOCK)


@dataclass
class UndoState:
    lines: List[str]
    cursor_row: int
    cursor_col: int
    marks: dict[str, Tuple[int, int]]
    auto_marks: dict[int, int] = field(default_factory=dict)
    line_endings: List[str] = field(default_factory=list)
    line_endings_trusted: bool = False
    last_jump: Optional[Tuple[int, int]] = None
    byte_cost: int = field(init=False, repr=False, compare=False)

    def __post_init__(self):
        # Conservative accounting: shared strings may be counted repeatedly.
        self.byte_cost = (
            sys.getsizeof(self.lines) + sum(map(sys.getsizeof, self.lines))
            + sys.getsizeof(self.line_endings)
            + sum(map(sys.getsizeof, self.line_endings))
            + sys.getsizeof(self.marks) + sys.getsizeof(self.auto_marks)
        )


@dataclass(frozen=True)
class CLikeParseState:
    """Lexical/structural state immediately before or after a C-like line."""

    in_block_comment: bool = False
    depth: int = 0
    stack: Tuple[Tuple[int, int, str], ...] = ()
    pending: Optional[Tuple[str, int]] = None


@dataclass(frozen=True)
class CLikeLineAnalysis:
    spans: Tuple[Tuple[int, int, str], ...]
    structure: str
    out_block_comment: bool
    brackets: Tuple[Tuple[int, str], ...]


class TrackedLines(list):
    """List that reports the earliest row affected by an in-place mutation."""

    def __init__(self, values=(), mutation_callback: Optional[Callable[[int], None]] = None):
        super().__init__(values)
        self._mutation_callback = mutation_callback

    def set_mutation_callback(self, callback: Optional[Callable[[int], None]]) -> None:
        self._mutation_callback = callback

    def _changed(self, index: int = 0) -> None:
        if self._mutation_callback is not None:
            self._mutation_callback(max(0, index))

    def _index_start(self, index) -> int:
        if isinstance(index, slice):
            start, stop, step = index.indices(len(self))
            if step < 0 and start > stop:
                return start + ((start - stop - 1) // (-step)) * step
            return start
        return index + len(self) if index < 0 else index

    def __setitem__(self, index, value):
        start = self._index_start(index)
        super().__setitem__(index, value)
        self._changed(start)

    def __delitem__(self, index):
        start = self._index_start(index)
        super().__delitem__(index)
        self._changed(start)

    def insert(self, index: int, value: str) -> None:
        start = max(0, min(index if index >= 0 else len(self) + index, len(self)))
        super().insert(index, value)
        self._changed(start)

    def append(self, value: str) -> None:
        start = len(self)
        super().append(value)
        self._changed(start)

    def extend(self, values) -> None:
        values = list(values)
        if not values:
            return
        start = len(self)
        super().extend(values)
        self._changed(start)

    def pop(self, index: int = -1):
        start = self._index_start(index)
        value = super().pop(index)
        self._changed(start)
        return value

    def remove(self, value) -> None:
        index = self.index(value)
        super().remove(value)
        self._changed(index)

    def clear(self) -> None:
        if self:
            super().clear()
            self._changed(0)

    def reverse(self) -> None:
        if len(self) > 1:
            super().reverse()
            self._changed(0)

    def sort(self, *args, **kwargs) -> None:
        if len(self) > 1:
            super().sort(*args, **kwargs)
            self._changed(0)

    def __iadd__(self, values):
        self.extend(values)
        return self

    def __imul__(self, count: int):
        if count != 1 and self:
            super().__imul__(count)
            self._changed(0)
        return self


class MMapLineStore(MutableSequence):
    """List-like, read-on-demand line storage for large files."""

    def __init__(self, filename: str, encoding: str = "utf-8"):
        self.filename = filename
        self.encoding = encoding
        self._fh = _open_regular_file(filename)
        self._mmap = None
        self._ranges: List[Tuple[int, int]] = [(0, 0)]
        self._lines: Optional[List[str]] = None
        self._size = os.fstat(self._fh.fileno()).st_size
        self._mutation_callback: Optional[Callable[[int], None]] = None
        if self._size == 0:
            self._lines = [""]
            self._line_endings = [""]
            self.close()
            return
        try:
            self._mmap = mmap.mmap(self._fh.fileno(), 0, access=mmap.ACCESS_READ)
        except ValueError:
            # The file was truncated to zero between the fstat above and the
            # mmap call; treat it as empty rather than crashing the load.
            self._lines = [""]
            self._line_endings = [""]
            self.close()
            return
        except OSError:
            # mmap can fail for reasons unrelated to file size (e.g. ENOMEM
            # mapping a very large file, or a filesystem that rejects mmap).
            # Close the file handle before propagating so the failed load
            # doesn't leak an fd -- the caller (_load_file) reports the
            # OSError and never gets a reference to this object to close it.
            self.close()
            raise
        self._ranges, self._line_endings = self._build_ranges()

    def _build_ranges(self) -> Tuple[List[Tuple[int, int]], List[str]]:
        size = len(self._mmap)
        if size == 0:
            return [(0, 0)], [""]

        ranges: List[Tuple[int, int]] = []
        endings: List[str] = []
        mm = self._mmap
        start = 0
        # mmap.find runs at C speed; a per-byte Python loop takes seconds for
        # the multi-megabyte files this store exists for.
        nl = mm.find(b"\n", 0)
        cr = mm.find(b"\r", 0)
        while start < size:
            if 0 <= nl < start:
                nl = mm.find(b"\n", start)
            if 0 <= cr < start:
                cr = mm.find(b"\r", start)
            if nl == -1 and cr == -1:
                ranges.append((start, size))
                endings.append("")
                break
            if cr != -1 and (nl == -1 or cr < nl):
                ranges.append((start, cr))
                if cr + 1 < size and mm[cr + 1] == 10:
                    endings.append("\r\n")
                    start = cr + 2
                else:
                    endings.append("\r")
                    start = cr + 1
            else:
                ranges.append((start, nl))
                endings.append("\n")
                start = nl + 1
        if not ranges:
            ranges.append((0, 0))
            endings.append("")
        return ranges, endings

    def _materialize(self) -> List[str]:
        if self._lines is None:
            self._lines = [self._line_at(i) for i in range(len(self._ranges))]
            self.close()
        return self._lines

    def _line_at(self, index: int) -> str:
        if self._mmap is None:
            raise RuntimeError("mmap is closed")
        start, end = self._ranges[index]
        # If the file shrank externally, pages past the new EOF are unmapped
        # and reading them raises SIGBUS, which kills the process uncatchably.
        # Clamp to the current size; this is best-effort (the file can still
        # shrink between the fstat and the read) but closes almost all of the
        # window. Truncated-away lines read back as empty.
        try:
            current_size = os.fstat(self._fh.fileno()).st_size
        except (OSError, ValueError, AttributeError):
            current_size = 0
        if current_size < self._size:
            end = min(end, current_size)
            start = min(start, end)
        return self._mmap[start:end].decode(self.encoding, errors="replace")

    def has_lossy_decode(self) -> bool:
        """Validate in bounded chunks without materializing mapped lines."""
        if not self.is_mapped:
            return False
        decoder = codecs.getincrementaldecoder(self.encoding)("strict")
        self._fh.seek(0)
        try:
            for chunk in iter(lambda: self._fh.read(1024 * 1024), b""):
                decoder.decode(chunk, final=False)
            decoder.decode(b"", final=True)
            return False
        except UnicodeDecodeError:
            return True
        finally:
            self._fh.seek(0)

    def line_endings(self) -> List[str]:
        return list(self._line_endings)

    def line_ending_at(self, row: int) -> Optional[str]:
        if 0 <= row < len(self._line_endings):
            return self._line_endings[row]
        return None

    def raw_bytes(self) -> Optional[bytes]:
        """Copy of the on-disk byte image, or None once materialized.

        Clamped like _line_at: if the file shrank externally, pages past the
        new EOF are unmapped and reading them raises SIGBUS.
        """
        if self._mmap is None:
            return None
        end = len(self._mmap)
        try:
            end = min(end, os.fstat(self._fh.fileno()).st_size)
        except (OSError, ValueError, AttributeError):
            end = 0
        return self._mmap[:end]

    def byte_size(self) -> int:
        """On-disk size probe that never copies file content."""
        if self._mmap is not None:
            return len(self._mmap)
        return self._size

    @property
    def is_mapped(self) -> bool:
        return self._lines is None

    def close(self):
        if self._mmap is not None:
            self._mmap.close()
            self._mmap = None
        if self._fh is not None:
            self._fh.close()
            self._fh = None

    def __del__(self):
        try:
            self.close()
        except Exception:
            pass

    def __len__(self) -> int:
        return len(self._lines) if self._lines is not None else len(self._ranges)

    def __getitem__(self, index):
        if self._lines is not None:
            return self._lines[index]
        if isinstance(index, slice):
            start, stop, step = index.indices(len(self))
            return [self[i] for i in range(start, stop, step)]
        if index < 0:
            index += len(self)
        if index < 0 or index >= len(self):
            raise IndexError(index)
        return self._line_at(index)

    def __setitem__(self, index, value):
        if isinstance(index, slice):
            slice_start, stop, step = index.indices(len(self))
            start = (
                slice_start + ((slice_start - stop - 1) // (-step)) * step
                if step < 0 and slice_start > stop else slice_start
            )
        else:
            start = index
        if start < 0:
            start += len(self)
        self._materialize()[index] = value
        self._notify_mutation(start)

    def __delitem__(self, index):
        if isinstance(index, slice):
            slice_start, stop, step = index.indices(len(self))
            start = (
                slice_start + ((slice_start - stop - 1) // (-step)) * step
                if step < 0 and slice_start > stop else slice_start
            )
        else:
            start = index
        if start < 0:
            start += len(self)
        del self._materialize()[index]
        self._notify_mutation(start)

    def insert(self, index: int, value: str):
        self._materialize().insert(index, value)
        self._notify_mutation(index)

    def append(self, value: str):
        index = len(self)
        self._materialize().append(value)
        self._notify_mutation(index)

    def set_mutation_callback(self, callback: Optional[Callable[[int], None]]) -> None:
        self._mutation_callback = callback

    def _notify_mutation(self, index: int) -> None:
        if self._mutation_callback is not None:
            self._mutation_callback(max(0, index))

    def __iter__(self) -> Iterator[str]:
        for i in range(len(self)):
            yield self[i]

    def __eq__(self, other):
        try:
            return list(self) == list(other)
        except TypeError:
            return NotImplemented


@dataclass
class BufferState:
    filename: Optional[str]
    lines: Union[List[str], MMapLineStore]
    saved_signature: object
    cursor_row: int
    cursor_col: int
    modified: bool
    top_line: int
    left_col: int
    undo_stack: List[UndoState]
    redo_stack: List[UndoState]
    marks: dict[str, Tuple[int, int]]
    auto_marks: dict[int, int] = field(default_factory=dict)
    line_endings: List[str] = field(default_factory=list)
    line_endings_trusted: bool = False
    log_type: Optional[str] = None
    saved_file_signature: Optional[Tuple[str, str, int, int]] = None
    last_jump: Optional[Tuple[int, int]] = None
    buffer_id: object = field(default_factory=object, compare=False, repr=False)
    top_wrap: int = 0


@dataclass
class FileBrowserEntry:
    name: str
    path: str
    is_dir: bool
    size: int
    mtime: float


@dataclass
class FileBrowserPanel:
    cwd: str
    cursor: int = 0
    top_line: int = 0
    show_hidden: bool = False
    sort_mode: str = "name"
    reverse_sort: bool = False
    selected: set[str] = field(default_factory=set)
    entries_cache_key: Optional[Tuple[object, ...]] = None
    entries_cache: List[FileBrowserEntry] = field(default_factory=list)


@dataclass
class FileBrowserState:
    left: FileBrowserPanel
    right: FileBrowserPanel
    active_panel: int = 0
    grep_prompt: bool = False
    grep_field: str = "pattern"
    grep_pattern: str = ""
    grep_text: str = ""
    grep_cursor: int = 0
    op_prompt: bool = False
    op_kind: str = ""
    op_text: str = ""
    op_cursor: int = 0
    op_label: str = ""
    op_payload: dict = field(default_factory=dict)
    op_completion_matches: List[str] = field(default_factory=list)
    op_completion_index: int = 0


@dataclass
class GrepResult:
    filename: str
    line_no: int
    text: str


@dataclass(frozen=True)
class TextObjectMotion:
    """iw/aw/i(/a{/etc as an operator target (di(, ya{, ...)."""
    around: bool
    ch: str


@dataclass(frozen=True)
class FindMotion:
    """f/F/t/T as an operator target (dfx, dtx, ...)."""
    cmd: str
    ch: str


@dataclass(frozen=True)
class SearchMotion:
    """/ or ? or \\ as an operator target (d/pattern, ...)."""
    cmd: str
    pattern: str


@dataclass(frozen=True)
class GotoMotion:
    """gg or G as an operator target (dgg, dG, d5G, ...)."""
    to_top: bool
    had_count: bool


# The key/motion _resolve_operator receives: either a raw curses key code
# (int) for a simple motion, or one of the tagged dataclasses above for a
# motion that carries extra data.
OperatorMotion = Union[int, TextObjectMotion, FindMotion, SearchMotion, GotoMotion]


# ---------------------------------------------------------------------------
# Editor
# ---------------------------------------------------------------------------

class ViiEditor:
    TAB_STOP    = 8
    INDENT      = "    "   # 4 spaces; change to "\t" for real tabs
    MAX_UNDO    = 200
    # Each undo state snapshots the whole buffer (a full lines list plus a
    # full line_endings list), so on huge files a deep stack can pin GBs of
    # list overhead. Cap the aggregate snapshot-lines retained across the
    # stack; the effective depth shrinks proportionally for large buffers.
    UNDO_LINE_BUDGET = 2_000_000
    UNDO_BYTE_BUDGET = 32 * 1024 * 1024  # per stack; retain one oversized snapshot
    MAX_COUNT   = 1_000_000   # cap on command counts so 99999999j can't freeze the UI
    # A count string longer than this is already guaranteed to exceed
    # MAX_COUNT once parsed (no leading zeros are ever accumulated), so
    # further digits can be dropped before int() ever sees them. Without
    # this, an unbounded digit prefix (e.g. a fast paste of a long numeral,
    # or a held-down key with terminal auto-repeat) can grow _count_str
    # past Python's int-from-string digit limit (default 4300) and raise
    # ValueError out of int(self._count_str), crashing the editor.
    MAX_COUNT_STR_LEN = len(str(MAX_COUNT))
    LARGE_FILE_MMAP_THRESHOLD = 8 * 1024 * 1024
    CLIKE_LANGUAGES = frozenset(("c", "csharp", "vala", "go"))
    CLIKE_CHECKPOINT_STRIDE = 128
    CLIKE_ROW_CACHE_LIMIT = 2048
    SYNTAX_CACHE_MAX_ENTRIES = 512
    SYNTAX_CACHE_EVICT_COUNT = 256
    SYNTAX_CACHE_BYTE_BUDGET = 16 * 1024 * 1024
    MAX_SYNTAX_LINE_CHARS = 200_000
    MAX_BRACKET_SCAN_CHARS = 1_000_000
    HEX_VIEW_MAX_BYTES = 64 * 1024 * 1024
    SESSION_PATH = os.path.expanduser("~/.vii_session")
    SESSION_MAX_FILES = 10
    IGNORED_CONTROL_KEYS = {3, 28}  # Ctrl-C, Ctrl-\ / Ctrl-4
    CHROME_ROWS = 3  # top chrome line + status line + bottom message line
    SYNTAX_PAIR_COMMENT = 1
    SYNTAX_PAIR_STRING  = 2
    SYNTAX_PAIR_KEYWORD = 3
    SYNTAX_PAIR_NUMBER  = 4
    LINENUM_PAIR        = 5
    SYNTAX_PAIR_TYPE    = 6
    SYNTAX_PAIR_BUILTIN = 7
    SYNTAX_PAIR_FUNC    = 8
    SYNTAX_PAIR_OPERATOR = 9
    SYNTAX_PAIR_PREPROC = 10
    STATUS_PAIR = 11
    BOTTOM_STATUS_PAIR = 12
    ERROR_PAIR = 13
    MAX_INTELLISENSE_MATCHES = 50
    MAX_INTELLISENSE_SCAN_LINES = 20000
    MAX_INTELLISENSE_LINE_CHARS = 20000
    SHELL_COMMAND_TIMEOUT_SECONDS = 10.0
    SHELL_COMMAND_MAX_OUTPUT_BYTES = 1024 * 1024
    FB_GREP_TIMEOUT_SECONDS = 10.0
    FB_GREP_MAX_RESULTS = 5000
    FB_GREP_MAX_LINE_BYTES = 1 << 20
    # Copy/move/delete run shutil calls synchronously in the key handler
    # (like the grep walk, there's no way to cancel mid-operation), so
    # above these sizes warn and require confirmation before blocking the
    # whole UI for however long the operation takes.
    FB_LARGE_OP_WARN_BYTES = 200 * 1024 * 1024
    FB_LARGE_OP_WARN_COUNT = 2000
    BRACKET_PAIRS = {"(": ")", ")": "(", "[": "]", "]": "[", "{": "}", "}": "{"}
    OPEN_BRACKETS = frozenset("([{")

    _COLOR_NAMES = {
        "black":   0,   # curses.COLOR_BLACK
        "red":     1,   # curses.COLOR_RED
        "green":   2,   # curses.COLOR_GREEN
        "yellow":  3,   # curses.COLOR_YELLOW
        "blue":    4,   # curses.COLOR_BLUE
        "magenta": 5,   # curses.COLOR_MAGENTA
        "cyan":    6,   # curses.COLOR_CYAN
        "white":   7,   # curses.COLOR_WHITE
    }

    def __setattr__(self, name, value):
        if name == "lines":
            callback = getattr(self, "_on_lines_mutated", None)
            if isinstance(value, TrackedLines):
                value.set_mutation_callback(callback)
            elif isinstance(value, list):
                value = TrackedLines(value, callback)
            elif isinstance(value, MMapLineStore):
                value.set_mutation_callback(callback)
            object.__setattr__(self, name, value)
            if hasattr(self, "_clike_checkpoints"):
                self._reset_incremental_syntax_state()
            return
        object.__setattr__(self, name, value)

    SYNTAX_EXTENSIONS = {
        ".c": "c", ".h": "c", ".cc": "c", ".cpp": "c", ".cxx": "c", ".hpp": "c",
        ".py": "python", ".pyw": "python",
        ".tcl": "tcl",
        ".go": "go",
        ".cs": "csharp",
        ".vala": "vala", ".vapi": "vala",
        ".sql": "sql",
        ".md": "markdown", ".markdown": "markdown",
        ".lisp": "lisp", ".lsp": "lisp", ".cl": "lisp", ".el": "lisp", ".scm": "lisp",
        ".fs": "forth", ".fth": "forth", ".4th": "forth", ".forth": "forth",
    }
    SYNTAX_KEYWORDS = {
        "c": {
            "auto", "break", "case", "char", "const", "continue", "default", "do",
            "double", "else", "enum", "extern", "float", "for", "goto", "if",
            "inline", "int", "long", "register", "restrict", "return", "short",
            "signed", "sizeof", "static", "struct", "switch", "typedef", "union",
            "unsigned", "void", "volatile", "while", "_Bool", "_Complex", "_Imaginary",
        },
        "python": {
            "and", "as", "assert", "async", "await", "break", "class", "continue",
            "def", "del", "elif", "else", "except", "False", "finally", "for",
            "from", "global", "if", "import", "in", "is", "lambda", "None",
            "nonlocal", "not", "or", "pass", "raise", "return", "True", "try",
            "while", "with", "yield",
        },
        "tcl": {
            "after", "append", "array", "break", "catch", "continue", "else",
            "elseif", "error", "eval", "expr", "for", "foreach", "global", "if",
            "incr", "proc", "return", "set", "switch", "then", "unset", "while",
        },
        "go": {
            "break", "case", "chan", "const", "continue", "default", "defer",
            "else", "fallthrough", "for", "func", "go", "goto", "if", "import",
            "interface", "map", "package", "range", "return", "select", "struct",
            "switch", "type", "var",
        },
        "csharp": {
            "abstract", "as", "base", "bool", "break", "case", "catch", "class",
            "const", "continue", "default", "delegate", "do", "double", "else",
            "enum", "event", "explicit", "extern", "false", "finally", "fixed",
            "float", "for", "foreach", "goto", "if", "implicit", "in", "int",
            "interface", "internal", "is", "lock", "namespace", "new", "null",
            "object", "operator", "out", "override", "params", "private",
            "protected", "public", "readonly", "ref", "return", "sealed",
            "sizeof", "stackalloc", "static", "string", "struct", "switch",
            "this", "throw", "true", "try", "typeof", "uint", "ulong", "unsafe",
            "using", "var", "virtual", "void", "volatile", "while",
        },
        "vala": {
            "abstract", "as", "async", "base", "bool", "break", "case", "catch",
            "class", "const", "construct", "continue", "default", "delegate",
            "do", "double", "else", "enum", "errordomain", "false", "finally",
            "float", "for", "foreach", "get", "if", "in", "int", "interface",
            "is", "lock", "namespace", "new", "null", "out", "override",
            "private", "protected", "public", "return", "set", "signal",
            "static", "string", "struct", "switch", "this", "throw", "throws",
            "true", "try", "typeof", "using", "var", "virtual", "void", "while",
            "yield",
        },
        "sql": {
            "add", "alter", "and", "as", "asc", "between", "by", "case", "create",
            "delete", "desc", "distinct", "drop", "else", "end", "exists",
            "from", "group", "having", "in", "insert", "into", "is", "join",
            "left", "like", "limit", "not", "null", "on", "or", "order", "outer",
            "primary", "references", "right", "select", "set", "table", "then",
            "union", "unique", "update", "values", "when", "where",
        },
        "lisp": {
            "and", "block", "case", "catch", "cond", "declare", "defclass",
            "defconstant", "defgeneric", "defmacro", "defmethod", "defpackage",
            "defparameter", "defstruct", "defun", "defvar", "do", "dolist",
            "dotimes", "eval-when", "flet", "if", "in-package", "labels",
            "lambda", "let", "let*", "loop", "multiple-value-bind", "not",
            "or", "progn", "prog1", "prog2", "provide", "quote", "require",
            "return", "return-from", "setf", "setq", "throw",
            "unless", "unwind-protect", "when",
        },
        "forth": {
            "if", "then", "else", "begin", "until", "while", "repeat", "again",
            "do", "loop", "leave", "unloop", "exit", "recurse", "case", "of",
            "endof", "endcase", "variable", "constant", "create", "does",
            "immediate", "postpone", "abort", "value", "to", "defer",
            "marker", "vocabulary",
        },
    }
    SYNTAX_TYPES = {
        "c": {
            "bool", "char", "double", "enum", "float", "int", "long", "short",
            "signed", "struct", "union", "unsigned", "void", "_Bool",
            "_Complex", "_Imaginary", "size_t", "ssize_t", "uint8_t", "uint16_t",
            "uint32_t", "uint64_t", "int8_t", "int16_t", "int32_t", "int64_t",
        },
        "python": {
            "bool", "bytes", "complex", "dict", "float", "frozenset", "int",
            "list", "object", "set", "str", "tuple", "type",
        },
        "go": {
            "bool", "byte", "complex64", "complex128", "error", "float32",
            "float64", "int", "int8", "int16", "int32", "int64", "rune",
            "string", "uint", "uint8", "uint16", "uint32", "uint64", "uintptr",
        },
        "csharp": {
            "bool", "byte", "char", "decimal", "double", "dynamic", "float",
            "int", "long", "object", "sbyte", "short", "string", "uint",
            "ulong", "ushort", "var", "void",
        },
        "vala": {
            "bool", "char", "double", "float", "int", "int8", "int16", "int32",
            "int64", "long", "size_t", "ssize_t", "string", "uchar", "uint",
            "uint8", "uint16", "uint32", "uint64", "ulong", "void",
        },
        "sql": {
            "bigint", "boolean", "char", "date", "datetime", "decimal", "float",
            "int", "integer", "numeric", "real", "text", "time", "timestamp",
            "varchar",
        },
        "forth": {
            "cell", "cells", "char", "chars", "double", "float",
        },
    }
    SYNTAX_BUILTINS = {
        "c": {
            "NULL", "calloc", "free", "malloc", "memcpy", "memset", "printf",
            "snprintf", "stderr", "stdin", "stdout", "strcmp", "strlen",
        },
        "python": {
            "Exception", "False", "None", "True", "abs", "all", "any", "dict",
            "enumerate", "filter", "getattr", "hasattr", "isinstance", "len",
            "list", "map", "max", "min", "open", "print", "range", "set",
            "str", "sum", "super", "tuple", "zip",
        },
        "tcl": {
            "dict", "file", "format", "join", "lappend", "lindex", "linsert",
            "list", "llength", "lrange", "lset", "puts", "regexp", "regsub",
            "split", "string",
        },
        "go": {
            "append", "cap", "close", "copy", "delete", "len", "make", "new",
            "panic", "print", "println", "recover",
        },
        "csharp": {
            "Console", "DateTime", "Enumerable", "Guid", "Math", "String",
            "Task",
        },
        "vala": {
            "GLib", "Object", "stdout", "stderr", "print", "printf",
        },
        "sql": {
            "avg", "coalesce", "count", "lower", "max", "min", "sum", "upper",
        },
        "lisp": {
            "append", "apply", "aref", "assoc", "atom", "car", "cdr", "cons",
            "consp", "eq", "eql", "equal", "eval", "find", "first", "format",
            "funcall", "length", "list", "listp", "mapc", "mapcar", "member",
            "nil", "nth", "null", "numberp", "pop", "princ", "print", "push",
            "read", "reduce", "remove", "rest", "reverse", "sort", "stringp",
            "symbolp", "t", "write",
        },
        "forth": {
            "dup", "drop", "swap", "over", "rot", "nip", "tuck", "pick", "roll",
            "depth", "and", "or", "xor", "invert", "lshift", "rshift", "mod",
            "abs", "min", "max", "negate", "dabs", "dnegate", "here", "allot",
            "cr", "emit", "key", "type", "count", "fill", "move", "compare",
            "words", "see", "dump", "true", "false",
        },
    }
    _RE_SYNTAX_WORD   = re.compile(r"\b[A-Za-z_][A-Za-z0-9_]*\b")
    _RE_INTELLISENSE_WORD = _RE_SYNTAX_WORD
    _RE_SYNTAX_NUMBER = re.compile(r"\b(?:0x[0-9A-Fa-f]+|\d+(?:\.\d+)?)\b")
    _RE_SYNTAX_OPERATOR = re.compile(r"(?:==|!=|<=|>=|&&|\|\||<<|>>|->|=>|::|:=|[-+*/%=&|^~!<>?:.;,()[\]{}'`])")
    _RE_SYNTAX_DECORATOR = re.compile(r"^\s*@[A-Za-z_][A-Za-z0-9_.]*")
    _RE_SYNTAX_PREPROC = re.compile(r"^\s*#\s*[A-Za-z_][A-Za-z0-9_]*")
    _RE_FORTH_PAREN_COMMENT = re.compile(r"\(\s.*?\s\)|\(\s\)")
    _RE_MD_HEADING = re.compile(r"^\s{0,3}(#{1,6})(?:\s+|$).*$")
    _RE_MD_SETEXT = re.compile(r"^\s{0,3}(=+|-+)\s*$")
    _RE_MD_HRULE = re.compile(r"^\s{0,3}((?:[-*_]\s*){3,})$")
    _RE_MD_BLOCKQUOTE = re.compile(r"^\s{0,3}>\s?.*$")
    _RE_MD_LIST = re.compile(r"^(\s{0,3})([-+*]|\d+[.)])(\s+)")
    _RE_MD_TASK = re.compile(r"\[[ xX]\]")
    _RE_MD_FENCE = re.compile(r"^\s{0,3}(```+|~~~+).*$")
    _RE_MD_INLINE_CODE = re.compile(r"`[^`]+`")
    _RE_MD_LINK = re.compile(r"(!?\[[^\]]+\])(\([^)]+\)|\[[^\]]+\])")
    _RE_MD_AUTO_LINK = re.compile(r"<(?:https?://[^>\s]+|[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,})>")
    _RE_MD_STRONG = re.compile(r"(\*\*|__)(?=\S)(.+?)(?<=\S)\1")
    _RE_MD_EMPH = re.compile(r"(?<!\*)\*(?!\*)(?=\S)(.+?)(?<=\S)\*(?!\*)|(?<!_)_(?!_)(?=\S)(.+?)(?<=\S)_(?!_)")
    _RE_PY_SCOPE      = re.compile(r"^\s*(?:async\s+)?(def|class)\s+([A-Za-z_][A-Za-z0-9_]*)")
    _RE_TCL_PROC      = re.compile(r"^\s*proc\s+([^\s{]+)")
    _RE_TCL_NAMESPACE = re.compile(r"^\s*namespace\s+eval\s+([^\s{]+)")
    _RE_TCL_CLASS     = re.compile(r"^\s*oo::class\s+create\s+([^\s{]+)")
    _RE_TCL_METHOD    = re.compile(r"^\s*(?:method|constructor|destructor)\s+([^\s{]+)")
    _RE_SQL_HEAD      = re.compile(
        r"^\s*(select|insert\s+into|update|delete\s+from|create\s+(?:table|view|procedure|function)|alter\s+table|drop\s+table)\b\s*([A-Za-z_][A-Za-z0-9_.]*)?",
        re.IGNORECASE,
    )
    _RE_LISP_DEFUN    = re.compile(
        r"^\s*\(\s*(defun|defmacro|defmethod|defgeneric|defclass|defstruct)\s+([^\s()]+)"
    )
    _RE_FORTH_DEFINITION = re.compile(r"^\s*:\s+(\S+)")
    _RE_CLIKE_TYPE    = re.compile(
        r"\b(namespace|class|struct|interface|enum|union|record)\s+([A-Za-z_][A-Za-z0-9_:]*)"
    )
    _RE_GO_TYPE       = re.compile(r"\btype\s+([A-Za-z_][A-Za-z0-9_]*)\s+(?:struct|interface)\b")
    _RE_GO_FUNC       = re.compile(
        r"\bfunc\s+(?:\([^)]*\)\s*)?([A-Za-z_][A-Za-z0-9_]*)\s*\("
    )
    _RE_CLIKE_FUNC    = re.compile(
        r"^\s*(?!(?:if|for|while|switch|catch|foreach|using|return|sizeof)\b)"
        r"(?:[A-Za-z_][A-Za-z0-9_:<>\[\],~*&.\s]+\s+)+"
        r"([A-Za-z_~][A-Za-z0-9_:~]*)\s*\([^;]*\)\s*(?:const\s*)?(?:throws\s+[A-Za-z0-9_.,\s]+)?(?:\{|$)"
    )
    LOG_TYPES = {"python", "lnx_auth", "http", "flask", "generic"}
    _RE_LOG_LEVEL = re.compile(r"\b(DEBUG|INFO|WARNING|WARN|ERROR|CRITICAL)\b")
    _RE_LOG_IP = re.compile(r"\b(?:\d{1,3}\.){3}\d{1,3}\b")
    _RE_LOG_DIGITS = re.compile(r"\b\d+\b")
    _RE_LOG_AUTH_WORDS = re.compile(
        r"\b(Accepted|Failed|Invalid|Disconnected|session opened|session closed)\b",
        re.IGNORECASE,
    )
    _RE_LOG_PYTHON = re.compile(
        r"^(?P<ts>\d{4}-\d{2}-\d{2}[T ][0-9:,.\-]+(?:Z|[+-]\d{2}:?\d{2})?)\s+"
        r"(?P<level>DEBUG|INFO|WARNING|WARN|ERROR|CRITICAL)\s+"
        r"(?P<logger>[A-Za-z0-9_.:-]+)\s*[-:]\s*(?P<msg>.*)$"
    )
    _RE_LOG_FLASK = re.compile(
        r"^\[(?P<ts>[^\]]+)\]\s+"
        r"(?P<level>DEBUG|INFO|WARNING|WARN|ERROR|CRITICAL)\s+in\s+"
        r"(?P<logger>[^:]+):\s*(?P<msg>.*)$"
    )
    _RE_LOG_FLASK_ACCESS = re.compile(
        r"^(?P<count>\d+)\s+\[(?P<ts>[^\]]+)\]\s+\[(?P<pid>\d+)\]\s+\[(?P<level>[A-Z]+)\]\s+"
        r"(?P<remote>\S+)\s+(?P<method>[A-Z]+)\s+(?P<path>\S+)\s+"
        r"(?:(?:HTTP/)?(?P<version>[0-9.]+)\s+)?(?P<status>\d{3})\s+(?P<size>\d+)(?:\s+(?P<extra>\S+))?$"
    )
    _RE_LOG_SYSLOG = re.compile(
        r"^(?P<ts>[A-Z][a-z]{2}\s+\d{1,2}\s+\d\d:\d\d:\d\d)\s+"
        r"(?P<host>\S+)\s+(?P<proc>[^:]+):\s*(?P<msg>.*)$"
    )
    _RE_LOG_HTTP = re.compile(
        r"^(?P<ip>\S+)\s+\S+\s+\S+\s+\[(?P<ts>[^\]]+)\]\s+"
        r'"(?P<method>[A-Z]+)\s+(?P<path>[^"]*?)(?:\s+HTTP/(?P<version>[0-9.]+))?"\s+'
        r"(?P<status>\d{3})\s+(?P<size>\S+)"
    )
    _RE_LOG_GENERIC_TS = re.compile(
        r"^(?:\d{4}-\d{2}-\d{2}[T ][0-9:,.]+(?:Z|[+-]\d{2}:?\d{2})?"
        r"|[A-Z][a-z]{2}\s+\d{1,2}\s+\d{2}:\d{2}:\d{2}"
        r"|\d{2}:\d{2}:\d{2}(?:[.,]\d+)?)"
    )
    _RE_LOG_QUOTED = re.compile(r'"[^"]*"')

    # _parse_function_line() — called per line during symbol extraction
    _RE_PY_DEF        = re.compile(r'def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(')
    _RE_PY_CLASS      = re.compile(r'class\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    _RE_PY_ASYNC_DEF  = re.compile(r'async\s+def\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(')
    _RE_C_CLASS       = re.compile(r'class\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    _RE_C_STRUCT      = re.compile(r'struct\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    _RE_C_ENUM        = re.compile(r'enum\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    _RE_C_FUNC        = re.compile(r'\b([a-zA-Z_][a-zA-Z0-9_]*)\s*\([^)]*\)\s*\{')
    _RE_JS_FUNC       = re.compile(r'function\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*\(')
    _RE_JS_ASYNC_FUNC = re.compile(r'async\s+function\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*\(')
    _RE_JS_CLASS      = re.compile(r'class\s+([a-zA-Z_$][a-zA-Z0-9_$]*)')
    _RE_JS_VARFUNC    = re.compile(r'(const|let|var)\s+([a-zA-Z_$][a-zA-Z0-9_$]*)\s*=\s*(async\s+)?(function|\([^)]*\)\s*=>)')
    _RE_JS_VARFUNC_PFX= re.compile(r'(const|let|var)\s+[a-zA-Z_$]')
    _RE_JS_METHOD     = re.compile(r'([a-zA-Z_$][a-zA-Z0-9_$]*)\s*[:=]\s*(async\s+)?(function|\()')
    _RE_SH_FUNC       = re.compile(r'([a-zA-Z_][a-zA-Z0-9_]*)\s*\(\s*\)')
    _RE_SH_FUNC_KW    = re.compile(r'function\s+([a-zA-Z_][a-zA-Z0-9_]*)')
    _RE_GO_FUNC_DEF   = re.compile(r'func\s+(?:\([^)]*\)\s+)?([a-zA-Z_][a-zA-Z0-9_]*)\s*\(')
    _RE_GO_TYPE_DEF   = re.compile(r'type\s+([a-zA-Z_][a-zA-Z0-9_]*)')

    # ord("\n") == 10; some terminals report Enter as curses.KEY_ENTER instead.
    _ENTER_KEYS = (curses.KEY_ENTER, 10)

    # Block visual mode is reached only from inside v / V: Ctrl-V, or Ctrl-X
    # for terminals that grab Ctrl-V for paste, switches to (or out of) it.
    # Neither key does anything in NORMAL mode, so a Ctrl-V paste keystroke
    # that leaks through can't start a block there. Ctrl-X is unbound in
    # every other mode, and unlike Ctrl-M (delivered as 10, the same key as
    # Enter) it can't arrive as part of an unbracketed paste.
    _BLOCK_VISUAL_KEYS = (22, 24)

    # Sentinel recorded in _insert_replay_keys for a line break that came
    # from a bracketed paste, so a later `.` or count-repeat replays it via
    # _newline(auto_indent=False) instead of the normal indent-copying
    # Enter path -- otherwise repeating an insert session that included a
    # paste would reintroduce the growing-indent problem bracketed paste
    # exists to avoid.
    _PASTE_NEWLINE = object()

    # Terminal bracketed-paste escape sequences (xterm/most terminals):
    # wrapping ON/OFF is sent once per edit() session; START/END (without
    # the leading ESC, which is read separately) bracket each paste.
    _BRACKETED_PASTE_ON   = "\x1b[?2004h"
    _BRACKETED_PASTE_OFF  = "\x1b[?2004l"
    _PASTE_START_TAIL     = "[200~"
    _PASTE_END_TAIL       = "[201~"

    HELP_LINES  = [
        "vii help",
        "",
        "Movement",
        "  h j k l  arrows      left / down / up / right",
        "  w W b B e E          word motions (small / BIG word)",
        "  0 ^ $                line start, first nonblank, end of line",
        "  gg G                 first / last line  (Ngg / NG jumps to line N)",
        "  gj gk                move down / up by display line",
        "  Markdown (.md)       with mdwrap, arrows and gj/gk move soft-wrapped rows",
        "  H M L                screen top / middle / bottom",
        "  { }                  paragraph backward / forward",
        "  f F t T ; ,          find char on line; ; repeats, , reverses",
        "  N;                   insert # before first nonblank on N lines (e.g. 10;)",
        "  N!                   delete leading # on N lines (e.g. 10!)",
        "  %                    jump to matching () [] {}",
        "  Ctrl-F/B             page down / up",
        "  Ctrl-D/U             half-page down / up",
        "  Ctrl-E/Y             scroll viewport one line down / up",
        "  zt zz zb             scroll cursor to top / middle / bottom of screen",
        "  Home End             line start / end",
        "  Ctrl-G               show file info and cursor position",
        "",
        "Editing",
        "  i a I A              insert before/after cursor, line start/end",
        "  o O                  open new line below / above",
        "  r R                  replace single char / enter replace mode",
        "  <space><space>       insert a space at the cursor",
        "  x X                  delete char under / before cursor",
        "  D C                  delete / change to end of line",
        "  s S                  substitute chars / whole lines (enter insert)",
        "  J                    join next line (count joins more)",
        "  ~                    toggle case (count toggles more chars)",
        "  u Ctrl-R             undo / redo",
        "  .                    repeat last change",
        "  ZZ ZQ                write and quit (:x) / quit without saving (:q!)",
        "",
        "Insert and Replace",
        "  ESC                  return to normal mode",
        "  Ctrl-A / Ctrl-E      move to line start / end",
        "  Backspace            delete before cursor; at col 0 joins with previous line",
        "  Delete / Ctrl-D      delete under cursor",
        "  Enter                split line, copying leading indent",
        "  paste (bracketed)    inserted literally; embedded newlines don't re-indent",
        "  Tab                  insert shiftwidth spaces (or literal tab if noexpandtab)",
        "  Shift-Tab            dedent by one indent step before cursor",
        "  Ctrl-N               insert mode: cycle intellisense matches from buffer",
        "  Ctrl-Y / Ctrl-Space / Ctrl-/ / Tab  insert mode: accept highlighted intellisense match",
        "  arrows / Home / End  move cursor while inserting",
        "  PgUp / PgDn          page up / down while inserting",
        "",
        "Operators  d y c > <",
        "  dd yy cc >> <<       operate on whole line(s)",
        "  dw d$ d0 d^          combine with any motion",
        "  dj dk dG dgg         linewise ranges",
        "  dfX dtX d/pat d?pat  find / search as motion",
        "  diw daw              inner / around word text objects",
        "  2d3w                 operator count × motion count = 6 words",
        "",
        "Yank, Registers, Marks",
        "  yy Y                 yank current line(s)",
        "  p P                  put after / before cursor",
        "  \"a{cmd}              use named register a-z with any yank, delete, or put",
        "  ma  'a  `a           set mark a; jump to line start / exact column",
        "  m.                   toggle auto-mark on current line",
        "  '[ ']                jump to nearest previous / next auto-mark",
        "  '< '>  `< `>         jump to start / end of last visual selection",
        "  '' ``                jump back to position before last jump",
        "  +                    copy word under cursor to unnamed register",
        "",
        "Search",
        "  /pat  ?pat           search forward / backward (Python regex)",
        "  \\pat                 search forward, literal text, case-insensitive",
        "  / ? \\                repeat with previous pattern",
        "  n N                  next / previous match",
        "  * #                  search word under cursor forward / backward",
        "",
        "Visual  (v charwise  V linewise; then Ctrl-V block)",
        "  o                    swap cursor to other end of selection",
        "  Ctrl-V Ctrl-X        in v / V: switch to block; in block: leave it",
        "  O                    block: other end of the current row",
        "  all movement keys    extend selection",
        "  d x  y  c s         delete / yank / change selection",
        "  S                    change selected whole lines",
        "  > <                  indent / dedent",
        "  ~                    toggle case",
        "  J                    join selected lines",
        "  p                    replace selection; deleted text becomes new register",
        "  P                    replace selection; register preserved",
        "  :                    open command line with the selection as range (:N,M)",
        "  Ctrl-V $             block: extend every row to its line end",
        "  Ctrl-V I / A         block: insert before / append after on every row",
        "  Ctrl-V c s           block: change; typed text repeats on every row",
        "  Ctrl-V r{char}       block: replace every character with {char}",
        "  p P (normal)         a yanked block is put as a column at the cursor",
        "",
        "Shell",
        "  :!cmd                run shell command, insert output below cursor",
        "  :!!                  rerun previous shell command below cursor",
        "  :sh cmd  :shell cmd  run shell command, show output in a scrollable view",
        "  :sh  :shell          reopen the view, rerunning the previous shell command",
        "  Shell view           q/ESC close  j/k scroll  Ctrl-F/B page  gg/G top/bottom",
        "",
        "Buffers",
        "  :buffers  :ls        open buffer list",
        "  :b N                 switch to buffer N",
        "  :bn  :bp             next / previous buffer",
        "  :badd file           add file without switching",
        "  :bd  :bd!            delete buffer (! discards changes)",
        "  Buffer list          q/ESC close  j/k navigate  PgUp/PgDn page  gg/G top/bottom",
        "                       digits then Enter select by buffer number",
        "                       u/d move highlighted buffer up/down in the list",
        "                       x deletes highlighted buffer (:bd), w saves it (:w)",
        "  :project name        :prj name  save named buffers as a project, or",
        "                       (if it already exists) load its files as buffers",
        "  :prj-del name        delete a saved project (no shortened form)",
        "  vii -p name          start up loading a saved project's files",
        "  :sessclr             clear the recent-files list in ~/.vii_session",
        "                       (leaves saved :project sections untouched)",
        "",
        "Recent files  :rct  :recent",
        "  Enter                open highlighted file in a new buffer",
        "  digit(s) Enter       select by number",
        "  j k  PgUp/PgDn       navigate / page",
        "  gg G  Home End       top / bottom",
        "  q  ESC               close",
        "",
        "File browser  :fb",
        "  Enter / l / Right    open file or enter directory",
        "  h / Left / Backspace go to parent",
        "  j k  arrows          move cursor",
        "  Tab / Shift-Tab      switch panel",
        "  q / ESC / F10        close browser",
        "  .                    toggle hidden files",
        "  H                    jump to home directory",
        "  c                    chdir process to active panel's directory",
        "  :                    go to directory; prompts path (Tab completes subdirs)",
        "  Insert / Space       mark entry for multi-open",
        "  s  r                 cycle sort order / reverse",
        "  g                    grep current panel (or selected dir); prompts pattern, file mask",
        "  F1 Help              open help screen",
        "  F2 Grep              grep current panel directory",
        "  F3 View              open file (binary -> hex view)",
        "  F4 Edit              open file (or marked files)",
        "  F5 Copy              copy entry / marked into other panel; prompts dest",
        "  F6 Move              rename / move entry / marked; prompts dest",
        "  F7 Mkdir             create new directory in active panel",
        "  F8 Delete            delete entry / marked (confirms; non-empty dirs need extra y)",
        "  F9 Sort              cycle sort order (same as s)",
        "",
        "Grep Results",
        "  Enter                open file at matching line",
        "  digit(s) Enter       select by number",
        "  j k  Ctrl-F/B        navigate results",
        "  q  ESC               close",
        "",
        "Hex view  :hex",
        "  j k  arrows          move cursor one line",
        "  Ctrl-F/B  PgDn/PgUp  page down / up",
        "  gg G  Home End       top / bottom",
        "  q  ESC               close",
        "",
        "Line-endings view  :le",
        "  Lines shown with [NL] [CR] [CRLF] [NONE] markers",
        "  j k  Ctrl-F/B  gg/G  same scroll keys as hex view",
        "  q  ESC               close",
        "",
        "Function list  :fnc  :functions",
        "  Lists def/class/proc/heading lines for the current syntax",
        "  j k  PgUp/PgDn       navigate",
        "  gg G  Home End       top / bottom",
        "  /pat                 incremental filter (Backspace edits, ESC keeps filter)",
        "  ESC (no filter)      close (or clear filter, then close on second press)",
        "  Enter                jump to highlighted entry",
        "  q                    close",
        "",
        "Help screen  :help  :h  (this view)",
        "  /pat  ?pat           search forward / backward within help",
        "  n N                  next / previous help match",
        "  Tab / Shift-Tab      jump to next / previous section",
        "  j k  Ctrl-F/B  gg/G  scroll keys",
        "  q  ESC  F1           close",
        "",
        "Generated inserts  (inserted at cursor)",
        "  :guid                random UUID",
        "  :pass                20-char password (upper lower digit symbol)",
        "  :secret              URL-safe random secret (base64url, 32 bytes)",
        "  :md5                 MD5 hex token",
        "  :dt-stamp            date  YYYYmmdd",
        "  :dt-dtstamp          local datetime  YYYYmmddHHMMSS",
        "  :dt-utcstamp         UTC datetime  YYYYmmddHHMMSS",
        "  :dt-datetime         local datetime  YYYY-mm-dd HH:MM:SS",
        "  :lgt/:logtype TYPE   display-format current buffer as python|lnx_auth|http|flask|generic",
        "  :lgt off             clear log display formatting (also disables .log auto-highlight)",
        "",
        "Ex commands",
        "  :w[!] [file]         write buffer (optionally to a new file; ! replaces,",
        "                       overrides external changes and backup failures)",
        "  :wa  :wall           write every modified buffer",
        "  :wo                  write override: save even if buffer is unchanged",
        "  :wnb                 write buffer, skipping the generation backup step",
        "  :N,Mw[!] file        write line range to file (ranges accept . $ N +N -N)",
        "  :q  :q!              quit (! discards changes)",
        "  :wq  :wq!  :x        write then quit (! discards changes in other buffers)",
        "  :e [file]  :e!       open / reload file (! discards changes)",
        "  :enew  :enew!        new unnamed buffer (! discards current changes)",
        "  :rf                  reload current file, preserving cursor position",
        "  :r file              insert file contents after cursor line",
        "  :0r file             insert file contents at top of buffer",
        "  :N,Mr file  :Nr file insert file contents after addressed line(s)",
        "  :f [name]            show / rename current buffer",
        "  :cd [dir]  :chdir    change / show process working directory (Tab-completes dirs)",
        "  :pwd                 print process working directory",
        "  :N  :+N  :-N  :$     jump to line",
        "  :'a  :'a,'b          jump to / range between marks (ranges also accept . $ N +N -N)",
        "  :mdel                delete all named marks and auto-marks in the current buffer",
        "  :p  :Np  :N,Mp       print current / addressed line(s) to status bar",
        "  :d  :delete  :N,Md   delete current / addressed line(s) into the register",
        "  :N,Mc  :*c           copy line range to yank register (% = current, $ = last; * = all)",
        "  :g/pat/cmd  :v/pat/cmd  run cmd on every line matching / not matching pat (! also inverts)",
        "  :hex                 read-only hex view (q/ESC closes)",
        "  :le  :le-unix  :le-win  line-ending view / set default endings",
        "  :b64d file           base64-decode file into current buffer",
        "  :b64e file           base64-encode current buffer to file",
        "  :fb                  file browser",
        "  :rct  :recent        recent-files list",
        "  :fnc  :functions     list functions/classes; / filter, Enter jump, j/k navigate",
        "  :help  :h            this help",
        "",
        "Substitute",
        "  :s/pat/repl/[gic]    current line  (g = all, i = ignore case, c = confirm)",
        "  :%s/pat/repl/gc      whole file with confirm each match",
        "  :N,Ms/pat/repl/g     line range (ranges accept . $ N +N -N)",
        "  :s//repl/            reuse last pattern",
        "  :&  :&&  :~          repeat last sub / with flags / swap pattern",
        "  delimiter            any non-alphanumeric char  (/ # | ...)",
        "  confirm keys         y=change  n=skip  a=all remaining  q/Esc=abort",
        "",
        "Command line",
        "  Left Right Home End  move cursor",
        "  Up Down              history",
        "  Tab                  filename completion (matches shown on status bar)",
        "  >                    accept highlighted completion match",
        "  ESC                  cancel",
        "",
        "Settings  :set  /  :set option=value  /  ~/.viirc",
        "  :set                 show all current settings",
        "  number  nu           show / hide line numbers",
        "  mdwrap               soft-wrap Markdown (nomdwrap to disable; default on)",
        "  expandtab            Tab inserts spaces (noexpandtab for literal tab)",
        "  backup               write generation backups on save (nobackup to disable)",
        "  visualmarks          set '< and '> marks when leaving visual mode (default off)",
        "  tabstop=N  ts=N      visual width of a hard tab",
        "  shiftwidth=N  sw=N   columns per indent step",
        "  lnendings=unix|win   default line endings for new text",
        "  undolevels=N  ul=N   undo history depth",
        "  intellisense         buffer-word insert completion (nointellisense to disable)",
        "  scrolljump=N  sj=N   vertical scroll step",
        "  sidescrolljump=N ssj=N  horizontal scroll step",
        "  sessionfiles=N       number of recent files kept in ~/.vii_session",
        "  *color=color         syntax/UI colours: linenumcolor commentcolor",
        "                         stringcolor keywordcolor numbercolor typecolor",
        "                         builtincolor functioncolor operatorcolor preproccolor",
        "                         statusfgcolor statusbgcolor",
        "                         bottomstatusfgcolor bottomstatusbgcolor",
        "                         errorcolor",
        "  colors               black red green yellow blue magenta cyan white",
        "",
        "Session and backups",
        "  ~/.vii_session       cursor position and marks saved on exit; auto-restored",
        "  .vii_backups/        generation backups written beside each saved file",
        "  -ns  --no-session-save  don't write ~/.vii_session on exit, this run",
        "  -nb  --no-backup     don't write .vii_backups/ on save, this run",
        "  -ro  --read-only     no file saves, no session save (implies -ns)",
    ]

    def __init__(self, filename: Optional[Union[str, List[str]]] = None):
        filenames = [filename] if isinstance(filename, str) else list(filename or [])
        first_filename = filenames[0] if filenames else None
        self._buffer_id = object()
        self.filename   = None
        self.lines: Union[List[str], MMapLineStore] = [""]
        self.line_endings: List[str] = [""]
        self.line_endings_trusted = False
        self.log_type: Optional[str] = None
        self.cursor_row = 0
        self.cursor_col = 0
        self._wanted_col: Optional[int] = None
        self.mode       = Mode.NORMAL
        self._modified  = False
        self._saved_signature = self._line_signature(
            self.lines, self.line_endings
        ) + (self.line_endings_trusted, None)
        self._saved_file_signature = self._file_signature_or_none(self.filename)
        self.modified   = False

        # Status / command
        self.message          = ""
        self.message_is_error = False
        self._cmd_buf         = ""      # : or / or ? or \ buffer
        self._cmd_cursor      = 0
        self._cmd_history: dict[str, List[str]] = {":": [], "/": [], "?": [], "\\": []}
        self._cmd_history_index: Optional[int] = None
        self._cmd_history_draft = ""
        self._cmd_history_max = 100
        self._filename_completion_matches: List[str] = []
        self._filename_completion_index = 0
        self._filename_completion_prefix = ""
        self._filename_completion_needs_space = False
        self._set_completion_matches: List[str] = []
        self._set_completion_index = 0
        self._set_completion_prefix = ""
        self._intellisense_completion_matches: List[str] = []
        self._intellisense_completion_index = 0
        self._intellisense_completion_prefix = ""
        self._intellisense_completion_complete = False
        # line text -> tuple of words; line strings are immutable and reused
        # across keystrokes, so unchanged rows skip the regex scan entirely.
        self._intellisense_line_words: dict = {}

        # Scrolling
        self.top_line = 0
        self.left_col = 0
        self._top_wrap = 0
        self._wrap_top_line = 0
        self._wrap_motion_cursor = None
        self._wanted_wrap_col = 0
        self._wrap_layout_cache: OrderedDict = OrderedDict()
        self._wrap_layout_cache_bytes = 0
        self.vertical_scroll_jump = 1
        self.horizontal_scroll_jump = 1

        # Screen-buffer for dirty tracking
        self._last_h: int        = 0
        self._last_w: int        = 0
        self._screen_buf: List[str] = []
        self._force_redraw       = True
        self._hide_cursor_next_draw = False
        self._last_marked_rows: set[int] = set()
        self._last_bracket_match_rows: set[int] = set()
        self._last_visual_rows: set[int] = set()
        self._syntax_cache: OrderedDict = OrderedDict()  # (lang, text) -> spans, weighted LRU
        self._syntax_cache_weights: dict = {}
        self._syntax_cache_bytes = 0
        self._clike_analysis_cache: OrderedDict = OrderedDict()
        self._clike_analysis_cache_weights: dict = {}
        self._clike_analysis_cache_bytes = 0
        self._clike_checkpoints: dict = {}
        self._clike_row_cache: OrderedDict = OrderedDict()
        # tuple(lines in a markdown table block) -> (rows, widths, alignments), weighted LRU.
        # Content-addressed so it self-invalidates on any edit without needing explicit
        # cache-clearing hooks wired into every self.lines mutation site.
        self._md_table_layout_cache: OrderedDict = OrderedDict()
        self._md_table_layout_cache_weights: dict = {}
        self._md_table_layout_cache_bytes = 0
        self._md_hot_block = None
        # Cache for _find_matching_bracket keyed on (lang, row, col, content_revision) --
        # lang is part of the key because the match itself depends on it (clike vs.
        # generic bracket scan), and lang can change (:file/:f) without a self.lines
        # reassignment to invalidate the cache another way.
        self._bracket_match_cache: dict = {}
        self._content_revision = 0
        self._breadcrumb_cache_key: Optional[Tuple[object, ...]] = None
        self._breadcrumb_cache_value: List[str] = []

        # Command parsing
        self._count_str  = ""   # accumulated digit prefix
        self._pending_op = ""   # pending operator key
        self._pending_count = 1  # count captured before a pending operator

        # Search
        self.search_pattern  = ""
        self._search_forward = True
        self._search_literal = False  # True for a \-prefixed literal, case-insensitive search
        self._search_regex_cache: OrderedDict = OrderedDict()  # (pattern, flags) -> compiled re, bounded LRU
        self.last_sub_pattern = ""
        self.last_sub_repl = ""
        self.last_sub_flags = ""
        self._sub_confirm_span: Optional[Tuple[int, int, int]] = None  # (row, byte_start, byte_end)

        # Yank
        self.yank_buffer: List[str] = []
        self.yank_is_lines          = True
        self.yank_line_endings: List[str] = []
        self.registers = {'"': ([], True)}
        self.register_line_endings = {'"': []}
        self.active_register: Optional[str] = None
        # Blockwise (Ctrl-V) yanks/deletes keep the (text, is_lines) register
        # shape -- one string per row, is_lines False -- and are flagged here
        # so p/P know to paste them as a column instead of as charwise text.
        self.yank_is_block = False
        self.block_registers: set[str] = set()

        # Visual mode
        self.visual_start: Tuple[int, int] = (0, 0)
        # Ctrl-V block extends to the end of every row after `$`.
        self._block_to_eol = False
        # Pending blockwise I/A/c: replicated onto the other rows on ESC.
        self._block_insert: Optional[dict] = None
        self.marks: dict[str, Tuple[int, int]] = {}
        self.auto_marks: dict[int, int] = {}   # {id: current_line}; id is an opaque unique key (see _set_auto_mark)
        self.last_jump: Optional[Tuple[int, int]] = None

        # Keys speculatively read (and not consumed) while probing whether an
        # ESC begins a bracketed-paste marker; drained by _read_key() before
        # it goes back to the terminal, so they're dispatched in order.
        self._pending_keys: deque = deque()

        # Undo / redo
        self.undo_stack: deque = deque()
        self.redo_stack: deque = deque()
        self._insert_pre_state: Optional[UndoState] = None
        self._insert_pre_revision: int = 0
        self._insert_replay_keys: List[Union[int, str]] = []
        self._insert_replay_mode = Mode.INSERT
        self._insert_replay_setup: Optional[Callable[[], None]] = None
        self._insert_empty_replay: Optional[Callable[[int], None]] = None
        self._insert_repeat_count = 1
        self._replace_overwritten: List[Tuple[int, int, Optional[str]]] = []
        self._last_change = None
        self._repeat_active = False
        self._pending_confirmation: Optional[Tuple[str, Callable[[], bool]]] = None
        self._cmd_context: Optional[Tuple[str, object]] = None
        self.help_top_line = 0
        self.help_search_pattern = ""
        self.help_search_forward = True
        self.hex_top_line = 0
        self.hex_cursor_line = 0           # current row, follows navigation like the editor cursor
        self._hex_line_count = 1           # cached by _open_hex_view
        self._hex_cached_data: bytes = b""  # byte image cached by _open_hex_view
        self._hex_cached_data_len = 0
        self.line_endings_top_line = 0
        self._line_endings_line_count = 1  # cached by _open_line_endings_view
        self._overlay_pending_g = False    # first "g" of gg seen in a scroll overlay
        self.shell_top_line = 0
        self.shell_lines: List[str] = []
        self.shell_command_label = ""
        self.last_shell_cmd = ""
        self.buffer_list_top_line = 0
        self.buffer_list_cursor = 0
        self.buffer_list_number = ""
        self.recent_files_list: List[str] = []
        self.recent_files_cursor = 0
        self.recent_files_top_line = 0
        self.recent_files_number = ""
        start_dir = os.getcwd()
        self.file_browser = FileBrowserState(
            FileBrowserPanel(start_dir),
            FileBrowserPanel(start_dir),
        )
        self.grep_results: List[GrepResult] = []
        self.grep_result_cursor = 0
        self.grep_result_top_line = 0
        self.grep_result_number = ""
        self.grep_result_label = ""
        self.function_list: List[Tuple[int, str]] = []
        self.function_list_cursor = 0
        self.function_list_top_line = 0
        self.function_list_search: str = ""
        self.function_list_searching: bool = False
        self.buffers: List[BufferState] = []
        self.current_buffer = 0
        self._session_cache: Optional[dict] = None  # loaded lazily, reset on save

        # Last f/F/t/T
        self._last_find_char = ""
        self._last_find_cmd  = ""

        # Display options
        self.show_line_numbers = True
        self.syntax_attrs = {}
        self.linenum_attr  = 0   # filled by _reinit_colors() once curses is up

        # Editable settings (exposed via :set and ~/.viirc)
        self.tab_stop    = 8
        self.shift_width = 4
        self.expand_tab  = True
        self.max_undo    = 200
        self.default_line_ending = "\n"
        self.intellisense = False
        self.markdown_wrap = True
        self.backup_enabled = True
        self.visual_marks = False   # set '< / '> when leaving visual mode
        self.session_max_files = self.SESSION_MAX_FILES

        # Startup-only switches (set by main() from -ns/-nb/-ro command-line
        # flags, after __init__/~/.viirc have run, so they always win).
        self.session_save_enabled = True
        self.read_only = False

        # Color names (strings) for each UI element; applied in _reinit_colors()
        self.color_linenum  = "cyan"
        self.color_comment  = "cyan"
        self.color_string   = "green"
        self.color_keyword  = "yellow"
        self.color_number   = "magenta"
        self.color_type     = "cyan"
        self.color_builtin  = "blue"
        self.color_function = "white"
        self.color_operator = "red"
        self.color_preproc  = "magenta"
        self.color_status_fg = "black"
        self.color_status_bg = "yellow"
        self.color_bottom_status_fg = "black"
        self.color_bottom_status_bg = "green"
        self.color_error = "black"
        self.status_attr = curses.A_REVERSE
        self.bottom_status_attr = curses.A_REVERSE
        self.error_attr = 0   # filled by _reinit_colors() once curses is up

        # curses window; set by run() so that color-change :set opts can reinit pairs
        self._stdscr = None

        self._load_viirc()

        if first_filename:
            normalized_first = self._normalize_path(first_filename)
            if os.path.exists(normalized_first):
                if not self._load_file(normalized_first):
                    self.filename = None
                    self.lines = [""]
                    self._mark_clean()
                    self._clear_edit_history()
            else:
                self.filename = normalized_first
                self._mark_clean()
                self.message = f'"{normalized_first}" [New]'
        self.buffers = [self._capture_buffer_state()]
        for extra in filenames[1:]:
            self._append_buffer(extra, switch=False)
        if filenames:
            self._load_buffer_state(0)

    # -----------------------------------------------------------------------
    # Config / colour helpers
    # -----------------------------------------------------------------------

    def _indent_str(self) -> str:
        """Return the string inserted by one indent step (Tab key, > operator)."""
        return " " * self.shift_width if self.expand_tab else "\t"

    def _default_line_ending_name(self) -> str:
        return "windows" if self.default_line_ending == "\r\n" else "unix"

    def _set_default_line_endings(self, style: str) -> str:
        value = style.strip().lower()
        if value in ("unix", "lf", "nl"):
            self.default_line_ending = "\n"
            return ""
        if value in ("win", "windows", "dos", "crlf"):
            self.default_line_ending = "\r\n"
            return ""
        return f"lnendings must be unix or win: {style!r}"

    def _parse_color(self, name: str):
        """Return the curses colour integer for *name*, or None if unknown."""
        return self._COLOR_NAMES.get(name.lower())

    def _reinit_colors(self) -> None:
        """(Re-)initialise all curses colour pairs from the current color_* attrs.

        Safe to call before curses is up (self._stdscr is None) — it just returns
        without doing anything; pairs are initialised for real on the first call
        from run().
        """
        if self._stdscr is None:
            return
        try:
            def _pair(name: str, pair_id: int, bg: int = -1) -> int:
                c = self._parse_color(name)
                if c is None:
                    c = self._COLOR_NAMES["white"]
                curses.init_pair(pair_id, c, bg)
                return curses.color_pair(pair_id)

            _pair(self.color_comment, self.SYNTAX_PAIR_COMMENT)
            _pair(self.color_string,  self.SYNTAX_PAIR_STRING)
            _pair(self.color_keyword, self.SYNTAX_PAIR_KEYWORD)
            _pair(self.color_number,  self.SYNTAX_PAIR_NUMBER)
            _pair(self.color_type,    self.SYNTAX_PAIR_TYPE)
            _pair(self.color_builtin, self.SYNTAX_PAIR_BUILTIN)
            _pair(self.color_function, self.SYNTAX_PAIR_FUNC)
            _pair(self.color_operator, self.SYNTAX_PAIR_OPERATOR)
            _pair(self.color_preproc, self.SYNTAX_PAIR_PREPROC)
            self.linenum_attr = _pair(self.color_linenum, self.LINENUM_PAIR) | curses.A_DIM
            status_fg = self._parse_color(self.color_status_fg)
            status_bg = self._parse_color(self.color_status_bg)
            if status_fg is None:
                status_fg = self._COLOR_NAMES["black"]
            if status_bg is None:
                status_bg = self._COLOR_NAMES["yellow"]
            curses.init_pair(self.STATUS_PAIR, status_fg, status_bg)
            self.status_attr = curses.color_pair(self.STATUS_PAIR)
            bottom_fg = self._parse_color(self.color_bottom_status_fg)
            bottom_bg = self._parse_color(self.color_bottom_status_bg)
            if bottom_fg is None:
                bottom_fg = self._COLOR_NAMES["black"]
            if bottom_bg is None:
                bottom_bg = self._COLOR_NAMES["green"]
            curses.init_pair(self.BOTTOM_STATUS_PAIR, bottom_fg, bottom_bg)
            self.bottom_status_attr = curses.color_pair(self.BOTTOM_STATUS_PAIR)
            error_fg = self._parse_color(self.color_error)
            if error_fg is None:
                error_fg = self._COLOR_NAMES["black"]
            curses.init_pair(self.ERROR_PAIR, error_fg, bottom_bg)
            self.error_attr = curses.color_pair(self.ERROR_PAIR)

            self.syntax_attrs = {
                "comment": curses.color_pair(self.SYNTAX_PAIR_COMMENT) | curses.A_DIM,
                "string":  curses.color_pair(self.SYNTAX_PAIR_STRING),
                "keyword": curses.color_pair(self.SYNTAX_PAIR_KEYWORD) | curses.A_BOLD,
                "number":  curses.color_pair(self.SYNTAX_PAIR_NUMBER),
                "type":    curses.color_pair(self.SYNTAX_PAIR_TYPE) | curses.A_BOLD,
                "builtin": curses.color_pair(self.SYNTAX_PAIR_BUILTIN),
                "function": curses.color_pair(self.SYNTAX_PAIR_FUNC) | curses.A_BOLD,
                "operator": curses.color_pair(self.SYNTAX_PAIR_OPERATOR),
                "preproc": curses.color_pair(self.SYNTAX_PAIR_PREPROC) | curses.A_BOLD,
            }
            self._force_redraw = True
        except curses.error:
            pass

    def _apply_set_opt(self, opt: str) -> str:
        """Apply a single :set option token.  Returns an error string or ""."""
        # boolean / toggle flags
        if opt in ("nu", "number"):
            self.show_line_numbers = True
            self._force_redraw = True
            return ""
        if opt in ("nonu", "nonumber"):
            self.show_line_numbers = False
            self._force_redraw = True
            return ""
        if opt in ("nu!", "number!", "invnu", "invnumber"):
            self.show_line_numbers = not self.show_line_numbers
            self._force_redraw = True
            return ""
        if opt in ("mdwrap", "nomdwrap", "mdwrap!", "invmdwrap"):
            if opt == "mdwrap":
                self.markdown_wrap = True
            elif opt == "nomdwrap":
                self.markdown_wrap = False
            else:
                self.markdown_wrap = not self.markdown_wrap
            self._top_wrap = 0
            self._wrap_top_line = self.top_line
            self._wrap_motion_cursor = None
            self._force_redraw = True
            return ""
        if opt in ("intellisense", "intelisense", "intellisence", "intelisence",
                   "autocomplete"):
            self.intellisense = True
            return ""
        if opt in ("nointellisense", "nointelisense", "nointellisence",
                   "nointelisence", "noautocomplete"):
            self.intellisense = False
            self._clear_intellisense_completion()
            return ""
        if opt in ("intellisense!", "intelisense!", "intellisence!",
                   "intelisence!", "autocomplete!", "invintellisense",
                   "invintelisense", "invintellisence", "invintelisence",
                   "invautocomplete"):
            self.intellisense = not self.intellisense
            if not self.intellisense:
                self._clear_intellisense_completion()
            return ""
        if opt == "expandtab":
            self.expand_tab = True
            return ""
        if opt == "noexpandtab":
            self.expand_tab = False
            return ""
        if opt == "backup":
            self.backup_enabled = True
            return ""
        if opt == "nobackup":
            self.backup_enabled = False
            return ""
        if opt in ("backup!", "invbackup"):
            self.backup_enabled = not self.backup_enabled
            return ""
        if opt in ("visualmarks", "novisualmarks", "visualmarks!", "invvisualmarks"):
            if opt == "visualmarks":
                self.visual_marks = True
            elif opt == "novisualmarks":
                self.visual_marks = False
            else:
                self.visual_marks = not self.visual_marks
            if not self.visual_marks:
                self._drop_visual_marks()
            return ""

        # key=value options
        if "=" in opt:
            key, _, raw = opt.partition("=")
            key = key.strip()
            raw = raw.strip()

            if key in ("tabstop", "ts"):
                try:
                    v = int(raw)
                    if v < 1:
                        raise ValueError
                    self.tab_stop = v
                    self._force_redraw = True
                    return ""
                except ValueError:
                    return f"tabstop must be a positive integer: {raw!r}"

            if key in ("shiftwidth", "sw"):
                try:
                    v = int(raw)
                    if v < 1:
                        raise ValueError
                    self.shift_width = v
                    return ""
                except ValueError:
                    return f"shiftwidth must be a positive integer: {raw!r}"

            if key in ("undolevels", "ul"):
                try:
                    v = int(raw)
                    if v < 1:
                        raise ValueError
                    self.max_undo = v
                    while len(self.undo_stack) > v:
                        self.undo_stack.popleft()
                    return ""
                except ValueError:
                    return f"undolevels must be a positive integer: {raw!r}"

            if key in ("lnendings", "lineendings"):
                return self._set_default_line_endings(raw)

            if key in ("sessionfiles", "sessfiles"):
                try:
                    v = int(raw)
                    if v < 1:
                        raise ValueError
                    self.session_max_files = v
                    return ""
                except ValueError:
                    return f"sessionfiles must be a positive integer: {raw!r}"

            if key in ("scrolljump", "sj", "vscrolljump", "verticalscrolljump"):
                try:
                    v = int(raw)
                    if v < 0:
                        raise ValueError
                    self.vertical_scroll_jump = v
                    return ""
                except ValueError:
                    return f"scrolljump must be a non-negative integer: {raw!r}"

            if key in ("sidescrolljump", "ssj", "hscrolljump", "horizontalscrolljump"):
                try:
                    v = int(raw)
                    if v < 0:
                        raise ValueError
                    self.horizontal_scroll_jump = v
                    return ""
                except ValueError:
                    return f"sidescrolljump must be a non-negative integer: {raw!r}"

            _color_opts = {
                "linenumcolor":  "color_linenum",
                "commentcolor":  "color_comment",
                "stringcolor":   "color_string",
                "keywordcolor":  "color_keyword",
                "numbercolor":   "color_number",
                "typecolor":     "color_type",
                "builtincolor":  "color_builtin",
                "functioncolor": "color_function",
                "operatorcolor": "color_operator",
                "preproccolor":  "color_preproc",
                "statusfgcolor": "color_status_fg",
                "statusfg":      "color_status_fg",
                "statusbgcolor": "color_status_bg",
                "statusbg":      "color_status_bg",
                "bottomstatusfgcolor": "color_bottom_status_fg",
                "bottomstatusfg":      "color_bottom_status_fg",
                "bottomstatusbgcolor": "color_bottom_status_bg",
                "bottomstatusbg":      "color_bottom_status_bg",
                "errorcolor":          "color_error",
                "errorfg":             "color_error",
            }
            if key in _color_opts:
                if self._parse_color(raw) is None:
                    known = ", ".join(self._COLOR_NAMES)
                    return f"Unknown colour {raw!r}. Known: {known}"
                setattr(self, _color_opts[key], raw.lower())
                self._reinit_colors()
                return ""

            return f"Unknown option: {opt}"

        # query-only forms (no =)
        _queries = {
            "tabstop": lambda: f"tabstop={self.tab_stop}",
            "ts":      lambda: f"tabstop={self.tab_stop}",
            "shiftwidth": lambda: f"shiftwidth={self.shift_width}",
            "sw":      lambda: f"shiftwidth={self.shift_width}",
            "undolevels": lambda: f"undolevels={self.max_undo}",
            "ul":      lambda: f"undolevels={self.max_undo}",
            "lnendings": lambda: f"lnendings={self._default_line_ending_name()}",
            "lineendings": lambda: f"lnendings={self._default_line_ending_name()}",
            "sessionfiles": lambda: f"sessionfiles={self.session_max_files}",
            "sessfiles": lambda: f"sessionfiles={self.session_max_files}",
            "scrolljump": lambda: f"scrolljump={self.vertical_scroll_jump}",
            "sj": lambda: f"scrolljump={self.vertical_scroll_jump}",
            "vscrolljump": lambda: f"scrolljump={self.vertical_scroll_jump}",
            "verticalscrolljump": lambda: f"scrolljump={self.vertical_scroll_jump}",
            "sidescrolljump": lambda: f"sidescrolljump={self.horizontal_scroll_jump}",
            "ssj": lambda: f"sidescrolljump={self.horizontal_scroll_jump}",
            "hscrolljump": lambda: f"sidescrolljump={self.horizontal_scroll_jump}",
            "horizontalscrolljump": lambda: f"sidescrolljump={self.horizontal_scroll_jump}",
            "statusfgcolor": lambda: f"statusfgcolor={self.color_status_fg}",
            "statusfg": lambda: f"statusfgcolor={self.color_status_fg}",
            "statusbgcolor": lambda: f"statusbgcolor={self.color_status_bg}",
            "statusbg": lambda: f"statusbgcolor={self.color_status_bg}",
            "bottomstatusfgcolor": lambda: f"bottomstatusfgcolor={self.color_bottom_status_fg}",
            "bottomstatusfg": lambda: f"bottomstatusfgcolor={self.color_bottom_status_fg}",
            "bottomstatusbgcolor": lambda: f"bottomstatusbgcolor={self.color_bottom_status_bg}",
            "bottomstatusbg": lambda: f"bottomstatusbgcolor={self.color_bottom_status_bg}",
            "errorcolor": lambda: f"errorcolor={self.color_error}",
            "errorfg": lambda: f"errorcolor={self.color_error}",
            "intellisense": lambda: "intellisense" if self.intellisense else "nointellisense",
            "intelisense": lambda: "intellisense" if self.intellisense else "nointellisense",
            "intellisence": lambda: "intellisense" if self.intellisense else "nointellisense",
            "intelisence": lambda: "intellisense" if self.intellisense else "nointellisense",
            "autocomplete": lambda: "intellisense" if self.intellisense else "nointellisense",
            "backup": lambda: "backup" if self.backup_enabled else "nobackup",
            "mdwrap?": lambda: "mdwrap" if self.markdown_wrap else "nomdwrap",
        }
        if opt in _queries:
            self.message = _queries[opt]()
            return ""

        return f"Unknown option: {opt}"

    @classmethod
    def _is_ignored_control_key(cls, key: int) -> bool:
        return key in cls.IGNORED_CONTROL_KEYS

    def _extract_functions(self) -> List[Tuple[int, str]]:
        """Scan all lines and return (line_no, label) for each function/class/heading."""
        lang = self._syntax_language()
        results: List[Tuple[int, str]] = []
        for lnum, line in enumerate(self.lines):
            label = self._parse_function_line(line, lang)
            if label:
                results.append((lnum, label))
        return results

    def _parse_function_line(self, line: str, syntax: Optional[str]) -> Optional[str]:
        """Return a label string if this line declares a function/class/heading, else None."""
        stripped = line.strip()
        if not stripped:
            return None
        # Markdown headings start with '#' — do NOT skip them as comments.
        # For all other syntaxes '#' is a comment character.
        if syntax != "markdown" and (stripped.startswith('#') or stripped.startswith('//')
                                      or stripped.startswith(';')):
            return None

        if syntax == "python":
            if stripped.startswith('async def '):
                m = self._RE_PY_ASYNC_DEF.match(stripped)
                if m:
                    return f"async def {m.group(1)}"
            elif stripped.startswith('def '):
                m = self._RE_PY_DEF.match(stripped)
                if m:
                    return f"def {m.group(1)}"
            elif stripped.startswith('class '):
                m = self._RE_PY_CLASS.match(stripped)
                if m:
                    return f"class {m.group(1)}"

        elif syntax in ("c", "cpp"):
            if stripped.startswith('class '):
                m = self._RE_C_CLASS.match(stripped)
                if m:
                    return f"class {m.group(1)}"
            elif stripped.startswith('struct '):
                m = self._RE_C_STRUCT.match(stripped)
                if m:
                    return f"struct {m.group(1)}"
            elif stripped.startswith('enum '):
                m = self._RE_C_ENUM.match(stripped)
                if m:
                    return f"enum {m.group(1)}"
            elif '(' in stripped and '{' in line:
                if not any(stripped.startswith(kw) for kw in ('if', 'while', 'for', 'switch', 'catch', '#')):
                    m = self._RE_C_FUNC.search(line)
                    if m and m.group(1) not in ('if', 'while', 'for', 'switch', 'catch'):
                        return m.group(1)

        elif syntax in ("js", "ts"):
            if stripped.startswith('async function '):
                m = self._RE_JS_ASYNC_FUNC.match(stripped)
                if m:
                    return f"async {m.group(1)}"
            elif stripped.startswith('function '):
                m = self._RE_JS_FUNC.match(stripped)
                if m:
                    return f"function {m.group(1)}"
            elif stripped.startswith('class '):
                m = self._RE_JS_CLASS.match(stripped)
                if m:
                    return f"class {m.group(1)}"
            elif self._RE_JS_VARFUNC_PFX.match(stripped):
                m = self._RE_JS_VARFUNC.match(stripped)
                if m:
                    return m.group(2)
            else:
                # _RE_JS_METHOD group(1) already captures the method name
                m = self._RE_JS_METHOD.match(stripped)
                if m:
                    return m.group(1)

        elif syntax in ("sh", "bash"):
            if '()' in stripped:
                m = self._RE_SH_FUNC.match(stripped)
                if m:
                    return f"fn {m.group(1)}"
            elif stripped.startswith('function '):
                m = self._RE_SH_FUNC_KW.match(stripped)
                if m:
                    return f"fn {m.group(1)}"

        elif syntax == "go":
            if stripped.startswith('func '):
                m = self._RE_GO_FUNC_DEF.match(stripped)
                if m:
                    return f"func {m.group(1)}"
            elif stripped.startswith('type ') and ('struct' in stripped or 'interface' in stripped):
                m = self._RE_GO_TYPE_DEF.match(stripped)
                if m:
                    return f"type {m.group(1)}"

        elif syntax == "lisp":
            m = self._RE_LISP_DEFUN.match(stripped)
            if m:
                return f"{m.group(1)} {m.group(2)}"

        elif syntax == "forth":
            m = self._RE_FORTH_DEFINITION.match(stripped)
            if m:
                return f": {m.group(1)}"

        elif syntax == "markdown":
            if stripped.startswith('#'):
                depth = len(stripped) - len(stripped.lstrip('#'))
                if 0 < depth <= 6:
                    text = stripped[depth:].strip()
                    if text:
                        return f"{'#' * depth} {text[:60]}"

        return None

    def _filtered_function_list(self) -> List[Tuple[int, str]]:
        if not self.function_list_search:
            return self.function_list
        q = self.function_list_search.lower()
        return [(lnum, label) for lnum, label in self.function_list if q in label.lower()]

    def _open_function_list(self):
        funcs = self._extract_functions()
        if not funcs:
            lang = self._syntax_language() or "this file type"
            self._set_error(f"No functions/classes found ({lang})")
            return
        self.function_list = funcs
        self.function_list_search = ""
        self.function_list_searching = False
        # Pre-select the entry closest to the current cursor
        best = 0
        for i, (lnum, _) in enumerate(funcs):
            if lnum <= self.cursor_row:
                best = i
        self.function_list_cursor = best
        # Center the pre-selected entry rather than starting at top
        text_rows = max(1, (self._last_h or 24) - 2)
        self.function_list_top_line = max(0, best - text_rows // 2)
        self.mode = Mode.FUNCTIONS
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True



    # Default viirc content — each line is written verbatim.
    # Active lines start with "set"; commented lines start with '"'.
    _DEFAULT_VIIRC = """\
" ~/.viirc — vii editor configuration
" Lines that begin with " are comments.  Edit values and remove the leading
" " to activate a setting.  All defaults are shown.

" ── Display ──────────────────────────────────────────────────────────────────
set number                  " show line numbers  (nonu to disable)
set mdwrap                  " soft-wrap Markdown files  (nomdwrap to disable)
set expandtab               " expand Tab key to spaces  (noexpandtab to disable)
set backup                  " write generation backups on save  (nobackup to disable)
" set visualmarks           " set '< and '> marks when leaving visual mode

" ── Indentation ──────────────────────────────────────────────────────────────
" set tabstop=8              " visual width of a hard tab character
" set shiftwidth=4           " columns added / removed by >> and <<

" ── Editing ──────────────────────────────────────────────────────────────────
" set intellisense        " suggest words from the current buffer in insert mode
" set lnendings=unix        " default line endings: unix or win
" set undolevels=200         " maximum number of undo steps kept in memory

" ── Scrolling ────────────────────────────────────────────────────────────────
" 0 and 1 scroll normally by one line/column; higher values jump by that amount.
" set scrolljump=1           " vertical scroll jump for Ctrl-E/Y and edge scroll
" set sidescrolljump=1       " horizontal jump when cursor scrolls off screen

" ── Session ──────────────────────────────────────────────────────────────────
" set sessionfiles=10        " number of recent files kept in ~/.vii_session

" ── Syntax-highlight colours ─────────────────────────────────────────────────
" Available colours: black red green yellow blue magenta cyan white
" set linenumcolor=cyan
" set commentcolor=cyan
" set stringcolor=green
" set keywordcolor=yellow
" set numbercolor=magenta
" set typecolor=cyan
" set builtincolor=blue
" set functioncolor=white
" set operatorcolor=red
" set preproccolor=magenta
set statusfgcolor=black       " status line text colour
set statusbgcolor=yellow      " status line background colour
set bottomstatusfgcolor=black " bottom status line text colour
set bottomstatusbgcolor=green " bottom status line background colour
set errorcolor=black          " error message text colour on the bottom line
"""

    def _write_default_viirc(self, rc_path: str) -> None:
        """Write a well-commented default ~/.viirc.  Silently ignores errors."""
        try:
            with open(rc_path, "w", encoding="utf-8") as fh:
                fh.write(self._DEFAULT_VIIRC)
        except OSError:
            pass

    def _load_viirc(self) -> None:
        """Load ~/.viirc at startup, creating a default one if absent.

        Syntax mirrors vim's .vimrc subset:
          • Lines beginning with " are comments.
          • Blank lines are ignored.
          • ``set option`` / ``set option=value`` lines are applied in order.
          • Unrecognised :set options are silently skipped (no curses yet).
        """
        rc_path = os.path.expanduser("~/.viirc")
        if not os.path.isfile(rc_path):
            self._write_default_viirc(rc_path)
        try:
            fh = open(rc_path, encoding="utf-8", errors="replace")
        except OSError:
            return
        with fh:
            for raw in fh:
                line = raw.split('"', 1)[0].strip()
                if not line or line.startswith('"'):
                    continue
                if line.startswith("set "):
                    for opt in line[4:].split():
                        self._apply_set_opt(opt)
                elif line == "set":
                    pass  # bare "set" with no args — nothing to do at load time
                elif line.startswith("lnendings="):
                    self._apply_set_opt(line)

    # -----------------------------------------------------------------------
    # Session save / restore
    # -----------------------------------------------------------------------

    @staticmethod
    def _read_session_map(session_path: str) -> dict:
        """Return {abspath: (row, col, marks, auto_marks)} parsed from
        *session_path*.

        Only a missing file is treated as "empty" -- any other OSError
        (permission denied, I/O error, ...) propagates. Mirrors
        _read_project_sections/_read_raw_session_mru_lines: a caller doing a
        read-modify-write (_save_session) needs to be able to tell "nothing
        on disk yet" from "couldn't read what's there" so a transient read
        failure doesn't get treated as an empty history and silently
        overwrite entries for every other file.
        """
        result: dict = {}
        try:
            with open(session_path, "r", encoding="utf-8", errors="replace") as fh:
                for raw in fh:
                    line = raw.rstrip("\n")
                    if not line or line.startswith("#"):
                        continue
                    parsed = _parse_session_line(line)
                    if parsed is not None:
                        path, row, col, marks, auto_marks = parsed
                        normalized = ViiEditor._normalize_path(path)
                        if normalized:
                            result[normalized] = (row, col, marks, auto_marks)
        except FileNotFoundError:
            pass
        return result

    def _session_map(self) -> dict:
        """Return {abspath: (row, col, marks, auto_marks)} from the session file.

        Best-effort for ordinary cursor-restore use: a read failure (missing
        file or otherwise) just means "no saved position." Callers that need
        to distinguish those cases (_save_session's read-modify-write) should
        use _read_session_map directly instead.
        """
        if self._session_cache is not None:
            return self._session_cache
        try:
            result = self._read_session_map(self.SESSION_PATH)
        except OSError:
            result = {}
        self._session_cache = result
        return result

    @contextlib.contextmanager
    def _session_lock(self):
        """Exclusive lock (via flock on a sidecar file) guarding the
        read-modify-write cycle against SESSION_PATH, so two vii processes
        exiting (or saving/deleting a project) around the same time can't
        each read a stale snapshot and clobber the other's entries when they
        write back. Best-effort: if the lock file can't even be opened, fall
        through and proceed unlocked rather than fail the whole save.
        """
        lock_path = self.SESSION_PATH + ".lock"
        lock_fh = None
        try:
            lock_fh = open(lock_path, "a")
            fcntl.flock(lock_fh, fcntl.LOCK_EX)
        except OSError:
            lock_fh = None
        try:
            yield
        finally:
            if lock_fh is not None:
                try:
                    fcntl.flock(lock_fh, fcntl.LOCK_UN)
                except OSError:
                    pass
                lock_fh.close()

    def _apply_session_cursor(self, filename: str) -> bool:
        """Move cursor/marks to the saved state for *filename* if one exists."""
        entry = self._session_map().get(self._normalize_path(filename))
        if entry is None:
            return False
        row, col, marks, auto_marks = entry
        row = max(0, min(row, len(self.lines) - 1))
        col = max(0, min(col, len(self.lines[row]) - 1) if self.lines[row] else 0)
        self.cursor_row = row
        self.cursor_col = col
        self.marks = self._clamp_session_marks(marks)
        self.auto_marks = auto_marks
        self.top_line = max(0, row - 10)
        self._clamp_marks()
        if not self.visual_marks:
            self.marks.pop("<", None)
            self.marks.pop(">", None)
        return True

    def _drop_visual_marks(self):
        """Remove '< / '> from every buffer (used when :set novisualmarks)."""
        self.marks.pop("<", None)
        self.marks.pop(">", None)
        for buf in self.buffers:
            buf.marks.pop("<", None)
            buf.marks.pop(">", None)
        self._force_redraw = True

    def _clamp_session_marks(self, marks: dict[str, Tuple[int, int]]) -> dict[str, Tuple[int, int]]:
        clamped = {}
        for name, (row, col) in marks.items():
            if not (len(name) == 1 and (name.isalpha() or name in "<>")):
                continue
            row = max(0, min(row, len(self.lines) - 1))
            line = self.lines[row]
            col = max(0, min(col, len(line) - 1) if line else 0)
            clamped[name] = (row, col)
        return clamped

    def _clamp_marks(self):
        self.marks = self._clamp_session_marks(self.marks)
        self._clamp_auto_marks()

    def _clamp_auto_marks(self):
        max_row = len(self.lines) - 1
        # This runs after every edit (including once per matched line inside
        # :g, which can stash hundreds/thousands of temporary tag entries in
        # auto_marks -- see _run_global_command). The _adjust_marks_for_*
        # helpers already keep entries in range whenever lines are actually
        # inserted/deleted, so the common case here is a no-op; checking
        # first avoids rebuilding the whole dict (and the min/max/tuple
        # churn that goes with it) on every single call. (Session/file
        # reloads can still hand this out-of-range values wholesale, so the
        # check itself always has to run -- only the rebuild is skippable.)
        if all(0 <= cur <= max_row for cur in self.auto_marks.values()):
            return
        self.auto_marks = {
            id_: max(0, min(cur, max_row))
            for id_, cur in self.auto_marks.items()
        }

    def _edit_positions(self) -> dict[Optional[str], Tuple[int, int]]:
        """Named marks and the jump position share every edit transform.

        None is an internal key only; it is never stored in self.marks or
        serialized as a named mark.
        """
        positions = dict(self.marks)
        if self.last_jump is not None:
            positions[None] = self.last_jump
        return positions

    def _set_edit_positions(self, positions: dict[Optional[str], Tuple[int, int]]):
        self.last_jump = positions.pop(None, None)
        self.marks = positions

    def _adjust_marks_for_line_insert(self, row: int, count: int):
        if count <= 0:
            return
        self._set_edit_positions({
            name: (mark_row + count, mark_col) if mark_row >= row else (mark_row, mark_col)
            for name, (mark_row, mark_col) in self._edit_positions().items()
        })
        self.auto_marks = {
            id_: cur + count if cur >= row else cur
            for id_, cur in self.auto_marks.items()
        }

    def _adjust_marks_for_line_delete(self, r1: int, r2: int):
        removed = max(0, r2 - r1 + 1)
        if removed <= 0:
            return
        adjusted = {}
        for name, (row, col) in self._edit_positions().items():
            if r1 <= row <= r2:
                continue
            if row > r2:
                row -= removed
            adjusted[name] = (row, col)
        self._set_edit_positions(adjusted)
        new_auto = {}
        for id_, cur in self.auto_marks.items():
            if r1 <= cur <= r2:
                continue   # mark's line was deleted
            if cur > r2:
                cur -= removed
            new_auto[id_] = cur
        self.auto_marks = new_auto

    def _adjust_marks_for_same_line_insert(self, row: int, col: int, length: int):
        if length <= 0:
            return
        positions = self._edit_positions()
        for name, (mark_row, mark_col) in list(positions.items()):
            if mark_row == row and mark_col >= col:
                positions[name] = (mark_row, mark_col + length)
        self._set_edit_positions(positions)

    def _adjust_marks_for_same_line_delete(self, row: int, c1: int, c2: int):
        removed = max(0, c2 - c1 + 1)
        if removed <= 0:
            return
        adjusted = {}
        for name, (mark_row, mark_col) in self._edit_positions().items():
            if mark_row == row:
                if mark_col > c2:
                    mark_col -= removed
                elif mark_col >= c1:
                    mark_col = c1
            adjusted[name] = (mark_row, mark_col)
        self._set_edit_positions(adjusted)

    def _adjust_marks_for_multiline_char_delete(self, r1: int, c1: int, r2: int, c2: int):
        removed_rows = r2 - r1
        adjusted = {}
        for name, (row, col) in self._edit_positions().items():
            if row < r1:
                adjusted[name] = (row, col)
            elif row == r1:
                adjusted[name] = (row, min(col, c1))
            elif row == r2:
                if col > c2:
                    adjusted[name] = (r1, c1 + (col - c2 - 1))
                else:
                    adjusted[name] = (r1, c1)
            elif row > r2:
                adjusted[name] = (row - removed_rows, col)
        self._set_edit_positions(adjusted)
        new_auto = {}
        for id_, cur in self.auto_marks.items():
            if cur <= r1:
                new_auto[id_] = cur          # rows before (and including) r1 unchanged
            elif cur == r2:
                new_auto[id_] = r1           # r2 content after c2 merges into r1
            elif cur > r2:
                new_auto[id_] = cur - removed_rows   # rows after r2 shift up
            # rows r1+1..r2-1 are deleted — drop those marks
        self.auto_marks = new_auto

    def _adjust_marks_for_line_replace(self, row: int, old: str, new: str):
        prefix = 0
        max_prefix = min(len(old), len(new))
        while prefix < max_prefix and old[prefix] == new[prefix]:
            prefix += 1

        suffix = 0
        max_suffix = min(len(old) - prefix, len(new) - prefix)
        while (suffix < max_suffix and
               old[len(old) - 1 - suffix] == new[len(new) - 1 - suffix]):
            suffix += 1

        old_suffix_start = len(old) - suffix
        new_changed_len = len(new) - prefix - suffix
        delta = len(new) - len(old)

        adjusted = {}
        for name, (mark_row, mark_col) in self._edit_positions().items():
            if mark_row == row:
                if mark_col < prefix:
                    pass
                elif mark_col >= old_suffix_start:
                    mark_col += delta
                else:
                    mark_col = prefix + max(0, new_changed_len - 1)
            adjusted[name] = (mark_row, mark_col)
        self._set_edit_positions(adjusted)

    def _adjust_marks_for_line_matches(
            self, row: int, spans: List[Tuple[int, int, str]]):
        """Precise sibling of _adjust_marks_for_line_replace for a line with
        several separate substitutions applied in one pass (:s///g). `spans`
        are the (old_start, old_end, replacement_text) of each match, in
        ascending old-line order. Unlike a whole-line prefix/suffix diff,
        this tracks each edit's own boundaries, so a mark sitting on an
        untouched character *between* two matches keeps following that
        character instead of being collapsed onto one match's replacement.
        """
        if not spans:
            return
        adjusted = {}
        for name, (mark_row, mark_col) in self._edit_positions().items():
            if mark_row != row:
                adjusted[name] = (mark_row, mark_col)
                continue
            col = mark_col
            shift = 0
            for old_start, old_end, rep_text in spans:
                if col < old_start:
                    col += shift
                    break
                if col < old_end:
                    col = old_start + shift + max(0, len(rep_text) - 1)
                    break
                shift += len(rep_text) - (old_end - old_start)
            else:
                col += shift
            adjusted[name] = (mark_row, col)
        self._set_edit_positions(adjusted)

    def _remap_marks_for_row_split(self, row: int, new_lines: List[str]):
        """Follow-up to _adjust_marks_for_line_replace/_adjust_marks_for_line_matches
        for a :s replacement that embedded a literal newline and split `row`
        into multiple lines. Those two helpers compute each mark's column as
        a *flat* offset into the fully joined replacement text (correct, but
        still tagged with the original single row); this walks that flat
        offset across new_lines' boundaries so a mark that landed past the
        end of new_lines[0] moves onto the later row it actually sits on,
        instead of being left pinned to `row` at a meaningless column. Marks
        on other rows are untouched -- callers already shift those via
        _adjust_marks_for_line_insert.
        """
        if len(new_lines) <= 1:
            return
        adjusted = {}
        for name, (mark_row, mark_col) in self._edit_positions().items():
            if mark_row == row:
                offset = 0
                for i, seg in enumerate(new_lines):
                    if i == len(new_lines) - 1 or mark_col <= offset + len(seg):
                        mark_row, mark_col = row + i, mark_col - offset
                        break
                    offset += len(seg) + 1
            adjusted[name] = (mark_row, mark_col)
        self._set_edit_positions(adjusted)

    def _encode_session_entry(self, path: str, row: int, col: int,
                               marks: dict, auto_marks: dict) -> str:
        encoded_path = json.dumps(path, ensure_ascii=True)
        marks_out = {
            name: [int(row_), int(col_)]
            for name, (row_, col_) in sorted(marks.items())
            if len(name) == 1 and name.isalpha()
        }
        encoded_marks = json.dumps(marks_out, separators=(",", ":"), sort_keys=True)
        auto_out = {str(id_): int(cur) for id_, cur in sorted(auto_marks.items())}
        encoded_auto_marks = json.dumps(auto_out, separators=(",", ":"), sort_keys=True)
        return f"{encoded_path}\t{row}\t{col}\t{encoded_marks}\t{encoded_auto_marks}"

    PROJECT_SECTION_PREFIX = "# project: "

    @staticmethod
    def _read_raw_session_mru_lines(session_path: str) -> List[str]:
        """Raw lines of *session_path* up to (not including) the first project
        section header, preserved byte-for-byte so project save/delete only
        ever touches the project-section part of the file.

        Takes the path explicitly (rather than reading self/cls.SESSION_PATH)
        so it honors per-instance SESSION_PATH overrides -- a classmethod
        bound to cls.SESSION_PATH would silently fall back to the real
        ~/.vii_session even when a test (or caller) redirected an instance's
        SESSION_PATH elsewhere.

        Only a missing file is treated as "start empty" -- any other OSError
        (permission denied, I/O error, ...) propagates, since a caller about
        to rewrite the file must not mistake "couldn't read it" for "there
        was nothing to preserve" and silently overwrite real content.
        """
        lines: List[str] = []
        try:
            with open(session_path, "r", encoding="utf-8", errors="replace") as fh:
                for raw in fh:
                    line = raw.rstrip("\n")
                    if line.startswith(ViiEditor.PROJECT_SECTION_PREFIX):
                        break
                    lines.append(line)
        except FileNotFoundError:
            pass
        return lines or ["# vii session"]

    @staticmethod
    def _read_project_sections(session_path: str) -> dict[str, List[str]]:
        """Return {project_name: [abspath, ...]} parsed from *session_path*.

        Project entries are bare JSON-encoded path strings (no trailing
        tab-separated fields), which lets the ordinary MRU-line parser
        (_parse_session_line) safely ignore them -- a project section line
        parses as valid JSON but leaves trailing content unconsumed, or (for
        genuine bare-path lines) has no "\t" to split on, so it never gets
        mistaken for an MRU entry. See _read_raw_session_mru_lines for why
        the path is taken as a parameter instead of read off cls/self, and
        why only FileNotFoundError (not every OSError) is treated as empty.
        """
        sections: dict[str, List[str]] = {}
        current: Optional[str] = None
        try:
            with open(session_path, "r", encoding="utf-8", errors="replace") as fh:
                for raw in fh:
                    line = raw.rstrip("\n")
                    if line.startswith(ViiEditor.PROJECT_SECTION_PREFIX):
                        current = line[len(ViiEditor.PROJECT_SECTION_PREFIX):]
                        sections.setdefault(current, [])
                        continue
                    if not line:
                        continue
                    if line.startswith("#"):
                        current = None
                        continue
                    if current is None:
                        continue
                    try:
                        path, end = json.JSONDecoder().raw_decode(line)
                    except (TypeError, ValueError, json.JSONDecodeError):
                        continue
                    if isinstance(path, str) and end == len(line):
                        sections[current].append(path)
        except FileNotFoundError:
            pass
        return sections

    def _atomic_write_session_lines(self, out: List[str]) -> bool:
        """Returns True on success. Callers must check this -- a failed write
        must not be reported to the user as a completed save/delete."""
        # A unique temp name keeps concurrently exiting editor instances from
        # clobbering (or unlinking) each other's in-flight session write;
        # _session_lock() (held by callers) keeps the read-modify-write of
        # *out* itself from racing across processes.
        session_dir = os.path.dirname(self.SESSION_PATH) or "."
        tmp = None
        success = True
        try:
            fd, tmp = tempfile.mkstemp(
                prefix=".vii_session.", suffix=".tmp", dir=session_dir,
            )
            # surrogateescape (not strict) so a path containing invalid-UTF-8
            # bytes -- decoded via surrogateescape when it entered self.lines
            # -- round-trips back to its original bytes instead of raising
            # UnicodeEncodeError here, which would otherwise skip the
            # os.unlink(tmp) cleanup below (UnicodeEncodeError isn't an
            # OSError) and abort the whole session save. See _atomic_write_text.
            with os.fdopen(fd, "w", encoding="utf-8", errors="surrogateescape") as fh:
                fh.write("\n".join(out) + "\n")
                fh.flush()
                os.fsync(fh.fileno())
            os.replace(tmp, self.SESSION_PATH)
            self._fsync_dir(session_dir)
        except OSError:
            success = False
            if tmp is not None:
                try:
                    os.unlink(tmp)
                except OSError:
                    pass
        self._session_cache = None  # invalidate so next load re-reads
        return success

    def _write_project_sections(self, sections: dict[str, List[str]]) -> bool:
        """Rewrite SESSION_PATH, keeping the MRU portion untouched and
        replacing the project-sections portion with *sections*. Returns False
        (without writing anything) if the existing MRU portion couldn't be
        read, or if the write itself failed.

        Callers are responsible for holding _session_lock() across their own
        read of the current sections (to decide *sections*) and this write --
        this method does not lock itself, since flock() is per open file
        description and a second flock() from the same process (a different
        fd on the same lock file) would self-deadlock rather than nest."""
        try:
            out = list(self._read_raw_session_mru_lines(self.SESSION_PATH))
        except OSError:
            return False
        for name, paths in sections.items():
            out.append(f"{self.PROJECT_SECTION_PREFIX}{name}")
            out.extend(json.dumps(p, ensure_ascii=True) for p in paths)
        return self._atomic_write_session_lines(out)

    def _named_buffer_paths(self) -> List[str]:
        """Absolute paths of every named buffer, current buffer first, deduped."""
        self._sync_current_buffer()
        seen: set = set()
        paths: List[str] = []
        if not self.buffers:
            return paths
        current = max(0, min(self.current_buffer, len(self.buffers) - 1))
        ordered = (
            [self.buffers[current]]
            + [b for i, b in enumerate(self.buffers) if i != current]
        )
        for b in ordered:
            if not b.filename:
                continue
            abspath = os.path.abspath(b.filename)
            if abspath in seen:
                continue
            seen.add(abspath)
            paths.append(abspath)
        return paths

    def _save_current_project(self, name: str) -> None:
        paths = self._named_buffer_paths()
        if not paths:
            self._set_error("No named buffers to save as a project")
            return
        with self._session_lock():
            try:
                sections = self._read_project_sections(self.SESSION_PATH)
            except OSError as exc:
                self._set_error(f"Could not read {self.SESSION_PATH}: {exc}")
                return
            sections[name] = paths
            wrote = self._write_project_sections(sections)
        if not wrote:
            self._set_error(f"Failed to save project '{name}' (could not write {self.SESSION_PATH})")
            return
        self.message = f"Project '{name}' saved ({len(paths)} file{'s' if len(paths) != 1 else ''})"
        self.message_is_error = False

    def _load_project_files(self, name: str, paths: List[str]) -> None:
        existing = [p for p in paths if os.path.isfile(p)]
        missing = len(paths) - len(existing)
        if not existing:
            self._set_error(f"Project '{name}': no files found")
            return
        loaded = 0
        failed = 0
        switched = False
        for p in existing:
            # Keep retrying "become the active buffer" against the next
            # candidate until one actually succeeds, rather than only ever
            # trying it on existing[0] regardless of whether that one loads.
            if self._append_buffer(p, switch=not switched):
                loaded += 1
                switched = True
            else:
                failed += 1
        if loaded == 0:
            self._set_error(f"Project '{name}': failed to open any of its {len(existing)} file(s)")
            return
        parts = [f"loaded {loaded} file{'s' if loaded != 1 else ''}"]
        if missing:
            parts.append(f"{missing} missing")
        if failed:
            parts.append(f"{failed} failed to open")
        self.message = f"Project '{name}': " + ", ".join(parts)
        # A file that vanished before we got to it is unsurprising and
        # already reflected in the message; an actual open failure on a file
        # that just passed the isfile() check is not, and should stand out.
        self.message_is_error = bool(failed)

    def _cmd_project(self, name: str) -> None:
        name = name.strip()
        if not name:
            self._set_error("Project name required")
            return
        try:
            sections = self._read_project_sections(self.SESSION_PATH)
        except OSError as exc:
            self._set_error(f"Could not read {self.SESSION_PATH}: {exc}")
            return
        if name in sections:
            self._load_project_files(name, sections[name])
        else:
            self._save_current_project(name)

    def _cmd_project_del(self, name: str) -> None:
        name = name.strip()
        if not name:
            self._set_error("Project name required")
            return
        with self._session_lock():
            try:
                sections = self._read_project_sections(self.SESSION_PATH)
            except OSError as exc:
                self._set_error(f"Could not read {self.SESSION_PATH}: {exc}")
                return
            if name not in sections:
                self._set_error(f"No such project: {name}")
                return
            del sections[name]
            wrote = self._write_project_sections(sections)
        if not wrote:
            self._set_error(f"Failed to delete project '{name}' (could not write {self.SESSION_PATH})")
            return
        self.message = f"Project '{name}' deleted"
        self.message_is_error = False

    def _cmd_sessclr(self) -> None:
        """Clear the MRU file list from SESSION_PATH, leaving named project
        sections untouched. Mirrors _write_project_sections but replaces the
        MRU portion with just the header line instead of preserving it."""
        with self._session_lock():
            try:
                sections = self._read_project_sections(self.SESSION_PATH)
            except OSError as exc:
                self._set_error(f"Could not read {self.SESSION_PATH}: {exc}")
                return
            out = ["# vii session"]
            for name, paths in sections.items():
                out.append(f"{self.PROJECT_SECTION_PREFIX}{name}")
                out.extend(json.dumps(p, ensure_ascii=True) for p in paths)
            wrote = self._atomic_write_session_lines(out)
        if not wrote:
            self._set_error(f"Failed to clear session (could not write {self.SESSION_PATH})")
            return
        self.message = "Session file cleared"
        self.message_is_error = False

    def _save_session(self) -> None:
        """Persist named buffers to SESSION_PATH as a most-recently-used list.

        Currently open buffers are written first (current buffer, then the
        rest in buffer order); older entries already on disk fill in behind
        them. The combined list is capped at self.session_max_files (:set
        sessionfiles=N), so files that drop off the end (the least recently
        used) are removed on each save.
        """
        if not self.session_save_enabled:
            return
        self._sync_current_buffer()
        seen: set = set()
        entries: List[Tuple[str, int, int, dict, dict]] = []
        if self.buffers:
            current = max(0, min(self.current_buffer, len(self.buffers) - 1))
            ordered = (
                [self.buffers[current]]
                + [b for i, b in enumerate(self.buffers) if i != current]
            )
        else:
            ordered = []
        for b in ordered:
            if not b.filename:
                continue
            abspath = os.path.abspath(b.filename)
            if abspath in seen:
                continue
            seen.add(abspath)
            entries.append((abspath, b.cursor_row, b.cursor_col, dict(b.marks), dict(b.auto_marks)))

        # Everything from here on reads-then-rewrites the shared session
        # file, so it all has to happen under one lock acquisition: a second
        # vii process doing the same read-modify-write between our read and
        # our write would otherwise have its own entries silently clobbered
        # (or would clobber ours) once both writes land. See _session_lock.
        with self._session_lock():
            self._session_cache = None  # force a fresh read of what's currently on disk
            # _read_session_map (like _read_project_sections below) only
            # treats a missing file as empty and raises on a genuine read
            # failure (permissions, I/O error, ...) -- this method must
            # never raise (it runs from a `finally` block that already
            # assumes that, same as _dump_crash_recovery), so on a real read
            # failure skip the session save entirely rather than treating
            # "couldn't read the existing MRU list" as "there is none" and
            # silently dropping every other file's saved position.
            try:
                disk_entries = self._read_session_map(self.SESSION_PATH)
            except OSError:
                return
            for path, (row, col, marks, auto_marks) in disk_entries.items():
                if path in seen:
                    continue
                seen.add(path)
                entries.append((path, row, col, marks, auto_marks))

            entries = entries[: self.session_max_files]

            out = ["# vii session"]
            for path, row, col, marks, auto_marks in entries:
                out.append(self._encode_session_entry(path, row, col, marks, auto_marks))

            # The MRU list above is a full rewrite of that portion of the
            # file; named project sections live past it and must be re-read
            # and re-appended here or a plain quit-triggered session save
            # would silently drop them. Same never-raise/skip-on-failure
            # reasoning as the MRU read above.
            try:
                sections = self._read_project_sections(self.SESSION_PATH)
            except OSError:
                return
            for name, paths in sections.items():
                out.append(f"{self.PROJECT_SECTION_PREFIX}{name}")
                out.extend(json.dumps(p, ensure_ascii=True) for p in paths)

            self._atomic_write_session_lines(out)

    def _dump_crash_recovery(self) -> List[str]:
        """Best-effort dump of every modified buffer before an unexpected crash.

        Named buffers dump to <file>.vii_crash next to the original; unnamed
        buffers dump to ~/.vii_crash_noname_<n>. Returns the paths written.
        Never raises: this runs while an exception is already propagating and
        must not mask it.
        """
        written: List[str] = []
        try:
            self._sync_current_buffer()
        except Exception:
            pass
        unnamed = 0
        for b in getattr(self, "buffers", []):
            try:
                if self._buffer_signature(b) == b.saved_signature:
                    continue
                lines = list(b.lines)
                endings = list(b.line_endings)
                if len(endings) != len(lines):
                    endings = [self.default_line_ending] * len(lines)
                text = "".join(
                    line + (endings[idx] or self.default_line_ending)
                    for idx, line in enumerate(lines)
                )
                if b.filename:
                    dump_path = b.filename + ".vii_crash"
                else:
                    unnamed += 1
                    dump_path = os.path.expanduser(f"~/.vii_crash_noname_{unnamed}")
                with open(dump_path, "w", encoding="utf-8", newline="") as fh:
                    fh.write(text)
                written.append(dump_path)
            except Exception:
                continue
        return written

    # -----------------------------------------------------------------------
    # File I/O
    # -----------------------------------------------------------------------

    @property
    def modified(self) -> bool:
        return self._modified

    @modified.setter
    def modified(self, value: bool):
        self._modified = bool(value)

    def _reset_incremental_syntax_state(self) -> None:
        """Discard row-indexed state after wholesale buffer replacement."""
        self._md_hot_block = None
        self._clike_checkpoints.clear()
        self._clike_row_cache.clear()
        self._breadcrumb_cache_key = None
        self._breadcrumb_cache_value = []
        self._bracket_match_cache.clear()
        self._content_revision += 1

    def _on_lines_mutated(self, first_row: int) -> None:
        """Invalidate incremental state at and after an in-place line edit."""
        self._md_hot_block = None
        first_row = max(0, first_row)
        for checkpoints in self._clike_checkpoints.values():
            for row in [row for row in checkpoints if row > first_row]:
                del checkpoints[row]
        for key in [key for key in self._clike_row_cache if key[1] >= first_row]:
            del self._clike_row_cache[key]
        self._breadcrumb_cache_key = None
        self._breadcrumb_cache_value = []
        self._bracket_match_cache.clear()
        self._content_revision += 1
        if self._display_syntax_language() in self.CLIKE_LANGUAGES:
            first_slot = max(0, first_row - self.top_line)
            for slot in range(first_slot, len(self._screen_buf)):
                self._screen_buf[slot] = ""

    @staticmethod
    def _line_signature(lines, line_endings: Optional[List[str]] = None) -> Tuple[str, str]:
        digest = hashlib.blake2b(digest_size=16)
        try:
            line_count = len(lines)
        except TypeError:
            lines = list(lines)
            line_count = len(lines)
        include_endings = line_endings is not None and len(line_endings) == line_count
        digest.update(b"E1" if include_endings else b"L1")
        for idx, line in enumerate(lines):
            data = line.encode("utf-8", errors="surrogatepass")
            digest.update(len(data).to_bytes(8, "big"))
            digest.update(data)
            if include_endings:
                ending = line_endings[idx].encode("utf-8", errors="surrogatepass")
                digest.update(len(ending).to_bytes(2, "big"))
                digest.update(ending)
        return ("lines", digest.hexdigest())

    @staticmethod
    def _line_endings_signature(line_endings: List[str]) -> str:
        digest = hashlib.blake2b(digest_size=16)
        digest.update(b"E1")
        empty_len = (0).to_bytes(8, "big")
        for ending_text in line_endings:
            digest.update(empty_len)
            ending = ending_text.encode("utf-8", errors="surrogatepass")
            digest.update(len(ending).to_bytes(2, "big"))
            digest.update(ending)
        return digest.hexdigest()

    @staticmethod
    def _split_bytes_with_line_endings(data: bytes, encoding: str = "utf-8") -> Tuple[List[str], List[str]]:
        if not data:
            return [""], [""]
        lines: List[str] = []
        endings: List[str] = []
        for part in data.splitlines(keepends=True):
            if part.endswith(b"\r\n"):
                body = part[:-2]
                ending = "\r\n"
            elif part.endswith(b"\n"):
                body = part[:-1]
                ending = "\n"
            elif part.endswith(b"\r"):
                body = part[:-1]
                ending = "\r"
            else:
                body = part
                ending = ""
            lines.append(body.decode(encoding, errors="replace"))
            endings.append(ending)
        if not lines:
            lines.append("")
            endings.append("")
        return lines, endings

    @staticmethod
    def _file_signature(filename: str) -> Tuple[str, str, int, int]:
        st = os.stat(filename)
        return ("file", os.path.abspath(filename), st.st_size, st.st_mtime_ns)

    @staticmethod
    def _signature_filename(filename: Optional[str]) -> Optional[str]:
        return ViiEditor._normalize_path(filename)

    @staticmethod
    def _normalize_path(filename: Optional[str]) -> Optional[str]:
        if not filename:
            return None
        return os.path.abspath(os.path.expanduser(filename))

    @staticmethod
    def _safe_getcwd(fallback: str) -> str:
        """os.getcwd() called right after a chdir() that's already known to
        have succeeded -- if the directory vanishes/unmounts in that same
        instant, fall back to the (already-absolute) path just changed
        into rather than raising or reporting the change itself as failed.
        Shared by every "chdir, then report where we ended up" call site so
        the fallback can't drift out of sync between them."""
        try:
            return os.getcwd()
        except OSError:
            return fallback

    def _validate_is_directory(self, target: str, original_text: str) -> bool:
        """Shared by :cd/:chdir and the file-browser goto-directory prompt:
        both resolve user-typed text to an absolute `target` differently,
        then need the identical "does this exist as a directory" check and
        "Not a directory: <what they actually typed>" error."""
        if os.path.isdir(target):
            return True
        self._set_error(f"Not a directory: {original_text}")
        return False

    @classmethod
    def _paths_refer_to_same_file(cls, first: Optional[str],
                                  second: Optional[str]) -> bool:
        first_path = cls._normalize_path(first)
        second_path = cls._normalize_path(second)
        if not first_path or not second_path:
            return False
        if first_path == second_path:
            return True
        try:
            return os.path.samefile(first_path, second_path)
        except OSError:
            return False

    @classmethod
    def _file_signature_or_none(cls, filename: Optional[str]) -> Optional[Tuple[str, str, int, int]]:
        if not filename:
            return None
        try:
            return cls._file_signature(filename)
        except OSError:
            return None

    def _current_signature(self, line_endings: Optional[List[str]] = None):
        line_endings = self.line_endings if line_endings is None else line_endings
        filename_sig = self._signature_filename(self.filename)
        if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
            try:
                return self._file_signature(self.lines.filename) + (
                    self._line_endings_signature(line_endings),
                    self.line_endings_trusted,
                    filename_sig,
                )
            except OSError:
                pass
        return self._line_signature(self.lines, line_endings) + (
            self.line_endings_trusted,
            filename_sig,
        )

    def _buffer_signature(self, b: BufferState):
        filename_sig = self._signature_filename(b.filename)
        if isinstance(b.lines, MMapLineStore) and b.lines.is_mapped:
            try:
                return self._file_signature(b.lines.filename) + (
                    self._line_endings_signature(b.line_endings),
                    b.line_endings_trusted,
                    filename_sig,
                )
            except OSError:
                pass
        return self._line_signature(b.lines, b.line_endings) + (
            b.line_endings_trusted,
            filename_sig,
        )

    def _mark_clean(self):
        self._saved_signature = self._current_signature()
        self._saved_file_signature = self._file_signature_or_none(self.filename)
        self.modified = False

    def _prepare_line_endings_for_edit(self):
        # Computing the pre-edit signature means hashing every line in the
        # buffer (see _line_signature), so it's only worth paying for when
        # normalization is actually going to change something -- which, in
        # steady-state editing, it almost never does (lines/line_endings
        # stay in sync after the first normalization). Checking that first
        # keeps the overwhelmingly common no-op case O(len(line_endings))
        # instead of O(total buffer content) on every single edit.
        before = list(self.line_endings)
        self._normalize_line_endings()
        if self.line_endings == before:
            return
        if self._current_signature(before) == self._saved_signature:
            self._mark_clean()

    def _clear_edit_history(self):
        self.undo_stack = deque()
        self.redo_stack = deque()
        self._insert_pre_state = None
        self._insert_replay_keys = []
        self._replace_overwritten = []
        self._insert_replay_setup = None
        self._insert_empty_replay = None

    def _ensure_content_baseline(self, snapshot: Optional[List[str]] = None,
                                 line_endings: Optional[List[str]] = None):
        if isinstance(self._saved_signature, tuple) and self._saved_signature[:1] == ("file",):
            self._saved_signature = self._line_signature(
                snapshot if snapshot is not None else self.lines,
                line_endings if line_endings is not None else self.line_endings,
            ) + (
                self.line_endings_trusted,
                self._signature_filename(self.filename),
            )

    def _refresh_modified(self):
        self.modified = self._current_signature() != self._saved_signature

    def _normalize_line_endings(self):
        if len(self.line_endings) < len(self.lines):
            start = len(self.line_endings)
            self.line_endings.extend(
                self.default_line_ending if idx < len(self.lines) - 1 else ""
                for idx in range(start, len(self.lines))
            )
        elif len(self.line_endings) > len(self.lines):
            del self.line_endings[len(self.lines):]
        if not self.line_endings and self.lines:
            self.line_endings = [""] * len(self.lines)

    def _insert_line_endings(self, index: int, count: int,
                             ending: Optional[str] = None):
        if count <= 0:
            return
        self._insert_line_ending_values(
            index, [(self.default_line_ending if ending is None else ending)] * count
        )

    def _insert_line_ending_values(self, index: int, endings: List[str]):
        if not endings:
            return
        self._normalize_line_endings()
        index = max(0, min(index, len(self.line_endings)))
        if index == len(self.lines) and self.line_endings and self.line_endings[-1] == "":
            self.line_endings[-1] = self.default_line_ending
        self.line_endings[index:index] = list(endings)

    def _delete_line_endings(self, start: int, stop: int):
        self._normalize_line_endings()
        del self.line_endings[start:stop]
        if not self.line_endings and self.lines:
            self.line_endings = [""] * len(self.lines)

    def _line_endings_for_range(self, start: int, stop: int) -> List[str]:
        if stop < start:
            return []
        return [
            self._line_ending_for_row(row)
            for row in range(start, min(stop + 1, len(self.lines)))
        ]

    def _line_separator_for_insert(self, index: int) -> str:
        for row in range(min(index - 1, len(self.lines) - 1), -1, -1):
            ending = self._line_ending_for_row(row)
            if ending:
                return ending
        for row in range(max(0, index), len(self.lines)):
            ending = self._line_ending_for_row(row)
            if ending:
                return ending
        return self.default_line_ending

    def _linewise_put_endings(self, index: int, repeat: int = 1) -> List[str]:
        return self._linewise_put_endings_for(
            self.yank_buffer, self.yank_line_endings, index, repeat
        )

    def _linewise_put_endings_for(
        self, buffer: List[str], line_endings: List[str],
        index: int, repeat: int = 1
    ) -> List[str]:
        if len(line_endings) != len(buffer):
            return []
        endings = list(line_endings) * max(1, repeat)
        final_after_insert = len(self.lines) + len(endings) - 1
        separator = self._line_separator_for_insert(index)
        for offset, ending in enumerate(endings):
            if ending == "" and index + offset < final_after_insert:
                endings[offset] = separator
        return endings

    def _capture_buffer_state(self) -> BufferState:
        # MMapLineStore is a handle — store as-is. Plain lists are mutable and
        # must be copied so that in-place edits don't corrupt the stored snapshot.
        lines_to_store = self.lines if isinstance(self.lines, MMapLineStore) else list(self.lines)
        return BufferState(
            self.filename,
            lines_to_store,
            self._saved_signature,
            self.cursor_row,
            self.cursor_col,
            self.modified,
            self.top_line,
            self.left_col,
            list(self.undo_stack),
            list(self.redo_stack),
            dict(self.marks),
            dict(self.auto_marks),
            line_endings=list(self.line_endings),
            line_endings_trusted=self.line_endings_trusted,
            log_type=self.log_type,
            saved_file_signature=self._saved_file_signature,
            last_jump=self.last_jump,
            buffer_id=self._buffer_id,
            top_wrap=self._top_wrap,
        )

    def _sync_current_buffer(self):
        if self.buffers and 0 <= self.current_buffer < len(self.buffers):
            self.buffers[self.current_buffer] = self._capture_buffer_state()

    def _refresh_all_buffer_modified_flags(self):
        self._refresh_modified()
        self._sync_current_buffer()
        for b in self.buffers:
            b.modified = self._buffer_signature(b) != b.saved_signature

    def _load_buffer_state(self, index: int):
        b = self.buffers[index]
        self._buffer_id = b.buffer_id
        self.filename = b.filename
        self.lines = b.lines or [""]
        self.line_endings = list(b.line_endings)
        self.line_endings_trusted = b.line_endings_trusted
        self.log_type = b.log_type
        self._saved_signature = b.saved_signature
        self._saved_file_signature = b.saved_file_signature
        self.cursor_row = b.cursor_row
        self.cursor_col = b.cursor_col
        self.modified = b.modified
        self.top_line = b.top_line
        self.left_col = b.left_col
        self._top_wrap = b.top_wrap
        self._wrap_top_line = b.top_line
        self._wrap_motion_cursor = None
        self.undo_stack = deque(b.undo_stack)
        self.redo_stack = deque(b.redo_stack)
        self.marks = dict(b.marks)
        self.auto_marks = dict(b.auto_marks)
        self.last_jump = b.last_jump
        self.current_buffer = index
        self.mode = Mode.NORMAL
        self._wanted_col = None
        self._count_str = ""
        self._pending_op = ""
        self._pending_count = 1
        self._clear_cmd_buf()
        self._insert_pre_state = None
        self._insert_replay_keys = []
        self._replace_overwritten = []
        self._insert_replay_setup = None
        self._insert_empty_replay = None
        self._insert_repeat_count = 1
        self.active_register = None
        self._last_change = None
        self._pending_confirmation = None
        self._sub_confirm_span = None
        self._content_revision += 1
        self._breadcrumb_cache_key = None
        self._breadcrumb_cache_value = []
        self._clamp_cursor()
        self._force_redraw = True

    def _switch_buffer(self, index: int):
        if not 0 <= index < len(self.buffers):
            self._set_error("No such buffer")
            return
        self._sync_current_buffer()
        self._load_buffer_state(index)
        self.message = f"Buffer {index + 1}/{len(self.buffers)}: {self._current_file_label()}"

    def _find_buffer_by_filename(self, filename: Optional[str],
                                 exclude_index: Optional[int] = None) -> Optional[int]:
        full_filename = self._normalize_path(filename)
        if not full_filename:
            return None
        for i, b in enumerate(self.buffers):
            if exclude_index is not None and i == exclude_index:
                continue
            if self._paths_refer_to_same_file(b.filename, full_filename):
                return i
        return None

    def _replace_current_buffer_with_file(self, filename: str,
                                          force_reload_existing: bool = False) -> bool:
        old_index = self.current_buffer
        if not self._append_buffer(
            filename,
            switch=True,
            refresh_existing=True,
            force_reload_existing=force_reload_existing,
        ):
            return False
        if self.current_buffer == old_index or not (0 <= old_index < len(self.buffers)):
            return True
        new_index = self.current_buffer
        del self.buffers[old_index]
        if new_index > old_index:
            new_index -= 1
        self._load_buffer_state(new_index)
        self._sync_current_buffer()
        return True

    def _append_buffer(self, filename: Optional[str] = None, switch: bool = True,
                       refresh_existing: bool = False,
                       force_reload_existing: bool = False) -> bool:
        self._sync_current_buffer()
        old_index = self.current_buffer
        full_filename = self._normalize_path(filename)
        # If the file is already open in another buffer, switch to it instead of
        # creating a duplicate with its own diverging undo history.
        if full_filename:
            existing_index = self._find_buffer_by_filename(full_filename)
            if existing_index is not None:
                target_modified = (
                    self._buffer_signature(self.buffers[existing_index])
                    != self.buffers[existing_index].saved_signature
                )
                should_reload = switch and (
                    force_reload_existing
                    or (refresh_existing and not target_modified)
                )
                if switch and existing_index != old_index:
                    self._load_buffer_state(existing_index)
                    if not should_reload:
                        self.message = f"Buffer {existing_index + 1}/{len(self.buffers)}: {full_filename}"
                if should_reload and not self._load_file(full_filename):
                    if existing_index != old_index:
                        self._load_buffer_state(old_index)
                    return False
                return True
        state = BufferState(
            full_filename,
            [""],
            self._line_signature([""], [""]) + (False, full_filename),
            0,
            0,
            False,
            0,
            0,
            [],
            [],
            {},
            {},
            line_endings=[""],
            line_endings_trusted=False,
            log_type=None,
            saved_file_signature=self._file_signature_or_none(full_filename),
        )
        self.buffers.append(state)
        new_index = len(self.buffers) - 1
        self._load_buffer_state(new_index)
        if filename:
            if not self._load_file(full_filename):
                if not os.path.exists(full_filename):
                    self.filename = full_filename
                    self.lines = [""]
                    self.line_endings = [""]
                    self.line_endings_trusted = False
                    self._mark_clean()
                    self._clear_edit_history()
                    self.marks = {}
                    self.auto_marks = {}
                    self.message = f'"{full_filename}" [New]'
                    self.message_is_error = False
                    self._sync_current_buffer()
                    if not switch:
                        self._load_buffer_state(old_index)
                        self.message = f"Buffer added: {full_filename or '[No Name]'}"
                    return True
                del self.buffers[new_index]
                if self.buffers:
                    self._load_buffer_state(min(old_index, len(self.buffers) - 1))
                return False
            self._sync_current_buffer()
        else:
            self.message = '"[No Name]" [New]'
            self._sync_current_buffer()
        if not switch:
            self._load_buffer_state(old_index)
            self.message = f"Buffer added: {full_filename or '[No Name]'}"
        return True

    def _delete_current_buffer(self, force: bool = False):
        self._refresh_modified()
        if self.modified and not force:
            self._sync_current_buffer()
            self._set_error("No write since last change (use :bd! to override)")
            return
        if len(self.buffers) == 1:
            self._new_buffer(reuse_current=True)
            self._sync_current_buffer()
            return
        del self.buffers[self.current_buffer]
        index = min(self.current_buffer, len(self.buffers) - 1)
        self._load_buffer_state(index)
        self.message = f"Buffer deleted; now {index + 1}/{len(self.buffers)}"

    def _show_buffers(self):
        # Verify every buffer's modified flag once, up front, rather than on
        # every redraw of the list (see _draw_buffer_list): no buffer's
        # content can change while Mode.BUFFER_LIST is active, since the
        # only actions available are navigating the list and selecting a
        # buffer to switch to.
        self._refresh_all_buffer_modified_flags()
        self.mode = Mode.BUFFER_LIST
        self.buffer_list_cursor = self.current_buffer
        text_rows = max(1, (self._last_h or 24) - 2)
        self.buffer_list_top_line = max(0, self.current_buffer - text_rows + 1)
        self.buffer_list_number = ""
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _buffer_list_lines(self) -> List[str]:
        lines = []
        for i, b in enumerate(self.buffers):
            current = "%" if i == self.current_buffer else " "
            modified = "+" if b.modified else " "
            mapped = "m" if isinstance(b.lines, MMapLineStore) and b.lines.is_mapped else " "
            name = b.filename or "[No Name]"
            lines.append(f"{current}{i + 1:3d}{modified}{mapped} {name} {len(b.lines)}L")
        return lines

    def _show_recent_files(self):
        self._sync_current_buffer()
        seen: set = set()
        paths: List[str] = []
        for b in self.buffers:
            if b.filename:
                abspath = os.path.abspath(b.filename)
                if abspath not in seen:
                    seen.add(abspath)
                    paths.append(abspath)
        for p in _read_session_filenames():
            if p not in seen:
                seen.add(p)
                paths.append(p)
            if len(paths) >= 10:
                break
        self.recent_files_list = paths[:10]
        self.recent_files_cursor = 0
        self.recent_files_top_line = 0
        self.recent_files_number = ""
        self.mode = Mode.RECENT_FILES
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _load_file(self, filename: str) -> bool:
        old_filename = self.filename
        full_filename = self._normalize_path(filename)
        lossy_decode = False
        # Read into locals first so a failed load leaves the current buffer
        # untouched. ValueError covers mmap races on files that shrink or
        # empty out between the size check and the map.
        try:
            size = os.path.getsize(full_filename)
            if size > 0 and size >= self.LARGE_FILE_MMAP_THRESHOLD:
                new_lines: Union[List[str], MMapLineStore] = MMapLineStore(full_filename)
                new_line_endings = new_lines.line_endings()
                lossy_decode = new_lines.has_lossy_decode()
            else:
                with _open_regular_file(full_filename) as fh:
                    raw = fh.read()
                new_lines, new_line_endings = self._split_bytes_with_line_endings(raw)
                try:
                    raw.decode("utf-8")
                except UnicodeDecodeError:
                    # Undecodable bytes were replaced with U+FFFD; a later :w
                    # would write the replacements, not the original bytes.
                    lossy_decode = True
        except (OSError, ValueError) as exc:
            self._set_error(str(exc))
            return False
        self._buffer_id = object()
        self.last_jump = None
        self.lines = new_lines
        self.line_endings = new_line_endings
        if not self.lines:
            self.lines = [""]
            self.line_endings = [""]
        self._normalize_line_endings()
        self.line_endings_trusted = True
        self.filename = full_filename
        self._mark_clean()
        self._clear_edit_history()
        self._force_redraw = True
        loaded_session = self._apply_session_cursor(full_filename)
        old_abspath = os.path.abspath(old_filename) if old_filename else None
        if not loaded_session and old_abspath != full_filename:
            self.cursor_row = 0
            self.cursor_col = 0
            self.top_line = 0
            self.left_col = 0
            self._top_wrap = 0
            self._wrap_top_line = 0
            self.marks = {}
            self.auto_marks = {}
        self._clamp_cursor()
        self._clamp_marks()
        suffix = " [mmap]" if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped else ""
        if lossy_decode:
            suffix += " [non-UTF-8: bad bytes shown as �, :w rewrites them]"
        self.message = f'"{full_filename}" {len(self.lines)}L{suffix}'
        self._sync_current_buffer()
        return True

    def _load_base64_file(self, filename: str):
        if self._current_buffer_is_modified():
            self._set_error("No write since last change (use :enew! before :b64d to override)")
            return
        full_filename = self._normalize_path(filename)
        if not full_filename:
            self._set_error("No file name")
            return
        try:
            with _open_regular_file(full_filename) as fh:
                encoded = fh.read()
            decoded = base64.b64decode(b"".join(encoded.split()), validate=True)
            self._buffer_id = object()
            self.last_jump = None
            self.lines, self.line_endings = self._split_bytes_with_line_endings(decoded)
            if not self.lines:
                self.lines = [""]
                self.line_endings = [""]
            self.line_endings_trusted = True
            self.filename = None
            self._mark_clean()
            self._clear_edit_history()
            self.marks = {}
            self.auto_marks = {}
            self._reset_view()
            self.message = f'"{full_filename}" decoded to {len(self.lines)}L'
            self._sync_current_buffer()
        except (OSError, ValueError, base64.binascii.Error) as exc:
            self._set_error(str(exc))

    def _save_base64_file(self, filename: str) -> bool:
        if self.read_only:
            self._set_error("Read-only mode (started with -ro/--read-only): file not saved")
            return False
        full_filename = self._normalize_path(filename)
        if not full_filename:
            self._set_error("No file name")
            return False
        try:
            with self._target_write_lock(full_filename):
                write_target = os.path.realpath(full_filename) if os.path.islink(full_filename) else full_filename
                raw = self._buffer_bytes(preserve_complete_endings=True)
                encoded = base64.b64encode(raw)
                self._atomic_write_text(write_target, encoded.decode("ascii"))
                self.message = f'"{full_filename}" base64 written'
                return True
        except OSError as exc:
            self._set_error(str(exc))
            return False

    def _buffer_bytes(self, preserve_complete_endings: bool = False) -> bytes:
        if (preserve_complete_endings and self.line_endings_trusted
                and len(self.line_endings) == len(self.lines)):
            return b"".join(
                (str(line) + self.line_endings[idx]).encode("utf-8", errors="replace")
                for idx, line in enumerate(self.lines)
            )
        return (
            self.default_line_ending.join(self.lines) + self.default_line_ending
        ).encode("utf-8", errors="replace")

    def _request_overwrite_confirmation(self, target: str, action: Callable[[], bool]) -> bool:
        self._pending_confirmation = (target, action)
        self.message = f'Replace "{target}"? (y/n)'
        self.message_is_error = False
        return True

    def _confirm_overwrite_or_run(self, target: str, action: Callable[[], bool]) -> bool:
        normalized_target = self._normalize_path(target)
        if normalized_target is None:
            return action()
        if os.path.exists(normalized_target) and not os.path.isdir(normalized_target):
            return self._request_overwrite_confirmation(normalized_target, action)
        return action()

    def _handle_pending_confirmation(self, key: int) -> bool:
        pending = self._pending_confirmation
        if pending is None:
            return False
        target, action = pending
        if key in (ord("y"), ord("Y")):
            self._pending_confirmation = None
            self.message = ""
            self.message_is_error = False
            action()
            return True
        if key in (ord("n"), ord("N"), 27):
            self._pending_confirmation = None
            self.message = f'Replace "{target}" cancelled'
            self.message_is_error = False
            return True
        self.message = f'Replace "{target}"? (y/n)'
        self.message_is_error = False
        return True

    def _write_copy_without_renaming(self, target: str, original_filename: Optional[str]) -> bool:
        if not self._save_file(target, rename_buffer=False):
            return False
        self.filename = original_filename
        self._sync_current_buffer()
        return True

    def _buffer_text_for_line_range(self, start: int, stop: int) -> str:
        lines = list(self.lines[start:stop + 1])
        return self.default_line_ending.join(lines) + self.default_line_ending

    def _write_line_range_to_file(self, start: int, stop: int, filename: str) -> bool:
        if self.read_only:
            self._set_error("Read-only mode (started with -ro/--read-only): file not saved")
            return False
        full_filename = self._normalize_path(filename)
        try:
            with self._target_write_lock(full_filename):
                write_target = os.path.realpath(full_filename) if os.path.islink(full_filename) else full_filename
                target_dir = os.path.dirname(os.path.abspath(write_target)) or "."
                if not os.path.isdir(target_dir):
                    raise FileNotFoundError(target_dir)
                text = self._buffer_text_for_line_range(start, stop)
                backup_state = (
                    self._stage_generation_backup(write_target, text)
                    if self.backup_enabled else None
                )
                try:
                    self._atomic_write_text(write_target, text)
                except Exception:
                    if backup_state is not None:
                        self._rollback_generation_backup(backup_state)
                    raise
                if backup_state is not None:
                    self._finalize_generation_backup(backup_state)
                self.message = f'"{full_filename}" {stop - start + 1}L written'
                self.message_is_error = False
                self._sync_current_buffer()
                return True
        except OSError as exc:
            self._set_error(str(exc))
            return False

    def _set_log_type(self, log_type: Optional[str]) -> bool:
        if log_type not in (None, "") and log_type not in self.LOG_TYPES:
            self._set_error(f"Unknown log type: {log_type}")
            return False
        self.log_type = log_type
        self._syntax_cache.clear()
        self._syntax_cache_weights.clear()
        self._syntax_cache_bytes = 0
        self._breadcrumb_cache_key = None
        self._breadcrumb_cache_value = []
        self._sync_current_buffer()
        self._force_redraw = True
        if not log_type:
            self.message = "Log display formatting off"
        else:
            self.message = f"Log display formatting: {log_type}"
        self.message_is_error = False
        return True

    def _buffer_text_for_save(self) -> Tuple[str, List[str]]:
        return (
            self.default_line_ending.join(self.lines) + self.default_line_ending,
            [self.default_line_ending] * len(self.lines),
        )

    def _backup_paths(self, target: str) -> Tuple[str, str, str, str, str]:
        target_dir = os.path.dirname(os.path.abspath(target)) or "."
        base = os.path.basename(target)
        stem, ext = os.path.splitext(base)
        ext_name = ext[1:]
        backup_dir = os.path.join(target_dir, ".vii_backups")
        generation_dir = os.path.join(backup_dir, "generation_counts")
        generation_file = os.path.join(generation_dir, f"{stem}_{ext_name}.gen")
        return backup_dir, generation_dir, generation_file, stem, ext_name

    def _read_generation_file(self, generation_file: str) -> Tuple[int, int]:
        last_generation = 0
        keep = 0
        try:
            with open(generation_file, "r", encoding="utf-8", errors="replace") as fh:
                for raw in fh:
                    key, sep, value = raw.strip().partition("=")
                    if not sep:
                        continue
                    try:
                        parsed = int(value)
                    except ValueError:
                        continue
                    if key == "last_generation":
                        last_generation = max(0, parsed)
                    elif key == "keep":
                        keep = max(0, parsed)
        except FileNotFoundError:
            pass
        return last_generation, keep

    def _write_generation_file(self, generation_file: str,
                               last_generation: int, keep: int):
        self._atomic_write_text(
            generation_file,
            f"last_generation={last_generation}\nkeep={keep}\n",
        )

    def _fsync_dir(self, path: str):
        try:
            fd = os.open(path, os.O_RDONLY)
        except OSError:
            return
        try:
            os.fsync(fd)
        except OSError:
            pass
        finally:
            os.close(fd)

    def _atomic_write_text(self, target: str, text: str, *, private: bool = False):
        # os.replace swaps in a new inode: hard links to the target keep the
        # old content, and only mode/uid/gid are carried over (no ACLs or
        # xattrs). That is the standard atomic-write tradeoff; callers resolve
        # symlinks with realpath so links themselves are preserved.
        target_dir = os.path.dirname(os.path.abspath(target)) or "."
        target_base = os.path.basename(target)
        try:
            target_stat = os.stat(target)
        except OSError:
            target_stat = None
        fd, tmp_path = tempfile.mkstemp(
            prefix=f".{target_base}.",
            suffix=".tmp",
            dir=target_dir,
            text=True,
        )
        try:
            try:
                # surrogateescape (not strict) so any lone surrogate that
                # made it into buffer text round-trips back to its original
                # byte instead of raising UnicodeEncodeError -- a save
                # failure here must stay an OSError-reportable :w error, not
                # an unrelated exception type that skips that handling.
                fh = os.fdopen(fd, "w", encoding="utf-8", errors="surrogateescape", newline="")
            except Exception:
                os.close(fd)
                raise
            with fh:
                fh.write(text)
                fh.flush()
                os.fsync(fh.fileno())
            if private:
                # Backup contents must never be published with broader access
                # than the private mkstemp file, including when replacing an
                # older backup. A failure to enforce this must abort the save.
                os.chmod(tmp_path, 0o600)
            try:
                if private:
                    pass
                elif target_stat is not None:
                    try:
                        os.chown(tmp_path, target_stat.st_uid, target_stat.st_gid)
                    except OSError:
                        pass
                    os.chmod(tmp_path, target_stat.st_mode & 0o7777)
                else:
                    current_umask = os.umask(0)
                    os.umask(current_umask)
                    os.chmod(tmp_path, 0o666 & ~current_umask)
            except OSError:
                pass
            os.replace(tmp_path, target)
            self._fsync_dir(target_dir)
        except Exception:
            try:
                os.unlink(tmp_path)
            except OSError:
                pass
            raise

    def _backup_filename(self, stem: str, ext_name: str, generation: int) -> str:
        if ext_name:
            return f"{stem}_{generation}.{ext_name}"
        return f"{stem}_{generation}"

    def _prune_backups(self, backup_dir: str, stem: str,
                       ext_name: str, keep: int):
        if keep <= 0:
            return
        if ext_name:
            pattern = re.compile(rf"^{re.escape(stem)}_(\d+)\.{re.escape(ext_name)}$")
        else:
            pattern = re.compile(rf"^{re.escape(stem)}_(\d+)$")

        generations = []
        for name in os.listdir(backup_dir):
            match = pattern.fullmatch(name)
            if match:
                generations.append((int(match.group(1)), name))
        generations.sort()
        for _, name in generations[:-keep]:
            try:
                os.remove(os.path.join(backup_dir, name))
            except FileNotFoundError:
                pass

    def _stage_generation_backup(self, target: str, text: str):
        backup_dir, generation_dir, generation_file, stem, ext_name = self._backup_paths(target)
        backup_dir_existed = os.path.isdir(backup_dir)
        generation_dir_existed = os.path.isdir(generation_dir)
        old_generation_exists = os.path.exists(generation_file)
        old_generation_text = ""
        if old_generation_exists:
            with open(generation_file, "r", encoding="utf-8", errors="replace") as fh:
                old_generation_text = fh.read()
        os.makedirs(backup_dir, exist_ok=True)
        os.makedirs(generation_dir, exist_ok=True)
        last_generation, keep = self._read_generation_file(generation_file)
        generation = last_generation + 1
        backup_name = self._backup_filename(stem, ext_name, generation)
        backup_path = os.path.join(backup_dir, backup_name)

        def _cleanup_dirs():
            if not generation_dir_existed:
                try:
                    os.rmdir(generation_dir)
                except OSError:
                    pass
            if not backup_dir_existed:
                try:
                    os.rmdir(backup_dir)
                except OSError:
                    pass

        # Bump the generation counter *before* writing the backup body: if
        # the process dies between the two writes, the counter has already
        # moved past this generation, so a later save can't recompute and
        # reuse (silently clobbering) the same slot. The only cost of a
        # crash in that window is a numbering gap, never an overwritten
        # backup.
        try:
            self._write_generation_file(generation_file, generation, keep)
        except Exception:
            _cleanup_dirs()
            raise
        try:
            self._atomic_write_text(backup_path, text, private=True)
        except Exception:
            if old_generation_exists:
                try:
                    self._atomic_write_text(generation_file, old_generation_text)
                except OSError:
                    pass
            else:
                try:
                    os.unlink(generation_file)
                except FileNotFoundError:
                    pass
            _cleanup_dirs()
            raise
        return {
            "backup_dir": backup_dir,
            "generation_dir": generation_dir,
            "generation_file": generation_file,
            "backup_path": backup_path,
            "stem": stem,
            "ext_name": ext_name,
            "keep": keep,
            "backup_dir_existed": backup_dir_existed,
            "generation_dir_existed": generation_dir_existed,
            "old_generation_exists": old_generation_exists,
            "old_generation_text": old_generation_text,
        }

    def _rollback_generation_backup(self, state: dict):
        try:
            os.remove(state["backup_path"])
        except FileNotFoundError:
            pass
        if state["old_generation_exists"]:
            try:
                self._atomic_write_text(state["generation_file"], state["old_generation_text"])
            except OSError:
                pass
        else:
            try:
                os.remove(state["generation_file"])
            except FileNotFoundError:
                pass
        if not state["generation_dir_existed"]:
            try:
                os.rmdir(state["generation_dir"])
            except OSError:
                pass
        if not state["backup_dir_existed"]:
            try:
                os.rmdir(state["backup_dir"])
            except OSError:
                pass

    def _finalize_generation_backup(self, state: dict):
        backup_dir = state["backup_dir"]
        stem = state["stem"]
        ext_name = state["ext_name"]
        keep = state["keep"]
        try:
            self._prune_backups(backup_dir, stem, ext_name, keep)
        except OSError:
            # The primary save and generation metadata are already durable here.
            # Retention cleanup is best-effort so a prune failure does not turn
            # a completed write into a reported save failure.
            pass

    @contextlib.contextmanager
    def _target_write_lock(self, target: str):
        """Serialize checks, backups, replacement and rollback across editors.

        The sidecar is unlinked while the lock is still held, so it does not
        linger after the write. A waiter that opened the old inode wins the
        flock only after that unlink, sees the path no longer names its inode,
        and retries on a fresh sidecar, so two writers never hold locks on
        different inodes at once. Use the backup metadata identity so
        colliding generation namespaces are serialized as well as symlink
        aliases of the same destination.
        """
        target = os.path.realpath(target)
        generation_file = self._backup_paths(target)[2]
        digest = hashlib.sha256(os.fsencode(generation_file)).hexdigest()
        lock_path = os.path.join(os.path.dirname(target), f".vii-write-{digest}.lock")
        while True:
            fd = os.open(lock_path, os.O_CREAT | os.O_RDWR, 0o600)
            try:
                fcntl.flock(fd, fcntl.LOCK_EX)
                held = os.fstat(fd)
                try:
                    current = os.stat(lock_path)
                except FileNotFoundError:
                    current = None
            except BaseException:
                os.close(fd)
                raise
            if current is not None and (current.st_dev, current.st_ino) == (held.st_dev, held.st_ino):
                break
            os.close(fd)
        try:
            yield
        finally:
            try:
                os.unlink(lock_path)
            except OSError:
                pass
            os.close(fd)

    def _save_file(self, filename: Optional[str] = None, rename_buffer: bool = True,
                   force: bool = False, skip_unchanged_check: bool = False,
                   skip_backup: bool = False) -> bool:
        if self.read_only:
            self._set_error("Read-only mode (started with -ro/--read-only): file not saved")
            return False
        target = filename or self.filename
        if not target:
            self._set_error("No file name")
            return False
        display_target = self._normalize_path(target)
        try:
            with self._target_write_lock(display_target):
                self._refresh_modified()
                same_target = (
                    self.filename is not None
                    and self._paths_refer_to_same_file(display_target, self.filename)
                )
                current_file_signature = self._file_signature_or_none(display_target)
                if (
                    same_target
                    and not force
                    and current_file_signature is not None
                    and current_file_signature != self._saved_file_signature
                ):
                    # A missing file is silently recreated, but overwriting content
                    # someone else wrote since our last read/write needs an explicit
                    # override: the generation backup only keeps our new text, so
                    # the external edits would be unrecoverable.
                    self._set_error("File changed on disk since last read (use :w! to override)")
                    return False
                if (
                    same_target
                    and not self.modified
                    and os.path.exists(display_target)
                    and current_file_signature == self._saved_file_signature
                    and not skip_unchanged_check
                ):
                    if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
                        # A clean :w should still detach the live buffer from the
                        # file-backed mmap so later file replacement or external
                        # edits do not leave the editor pinned to stale storage.
                        materialized = list(self.lines)
                        self.lines = materialized
                        self._ensure_content_baseline(materialized, list(self.line_endings))
                    self.message = f'"{display_target}" {len(self.lines)}L unchanged'
                    self.message_is_error = False
                    self._sync_current_buffer()
                    return True
                write_target = os.path.realpath(display_target) if os.path.islink(display_target) else display_target
                target_dir = os.path.dirname(os.path.abspath(write_target)) or "."
                if not os.path.isdir(target_dir):
                    raise FileNotFoundError(target_dir)
                if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
                    # Detach only when this save changes or rewrites the current
                    # file. Copy-writes should preserve the original mmap-backed
                    # buffer and its external-change tracking.
                    if same_target or rename_buffer:
                        materialized = list(self.lines)
                        self.lines = materialized
                        self._ensure_content_baseline(materialized, list(self.line_endings))
                text, saved_endings = self._buffer_text_for_save()
                # Saving joins with the default line ending; warn when that
                # actually converts endings the file was loaded with.
                endings_converted = (
                    self.line_endings_trusted
                    and len(self.line_endings) == len(self.lines)
                    and any(
                        ending and ending != self.default_line_ending
                        for ending in self.line_endings
                    )
                )
                if skip_backup or not self.backup_enabled:
                    backup_state = None
                else:
                    try:
                        backup_state = self._stage_generation_backup(write_target, text)
                    except OSError as exc:
                        if not force:
                            self._set_error(f"Backup failed: {exc} (use :w! to write without backup)")
                            return False
                        # Forced writes still save the user's data when the backup
                        # machinery is broken (e.g. a stray file named .vii_backups).
                        backup_state = None
                try:
                    self._atomic_write_text(write_target, text)
                except Exception:
                    if backup_state is not None:
                        self._rollback_generation_backup(backup_state)
                    raise
                if backup_state is not None:
                    self._finalize_generation_backup(backup_state)
                if rename_buffer:
                    self.filename = display_target
                    self.line_endings = saved_endings
                    self.line_endings_trusted = True
                    self._mark_clean()
                else:
                    self._refresh_modified()
                converted_note = (
                    f" [endings → {self._default_line_ending_name()}]"
                    if endings_converted else ""
                )
                if backup_state is None:
                    converted_note += " [no backup]"
                self.message  = f'"{display_target}" {len(self.lines)}L written{converted_note}'
                self._sync_current_buffer()
                return True
        except OSError as exc:
            self._set_error(str(exc))
            return False

    def _write_all_buffers(self) -> bool:
        """:wa / :wall — save every modified buffer, leaving the current one active."""
        self._refresh_all_buffer_modified_flags()
        original_index = self.current_buffer
        written = 0
        failed: List[str] = []
        try:
            for i, b in enumerate(list(self.buffers)):
                if not b.modified:
                    continue
                self._load_buffer_state(i)
                if self._save_file():
                    written += 1
                else:
                    failed.append(self._current_file_label())
        finally:
            # However the loop above exits -- including an exception from
            # deep inside _save_file that isn't an OSError and so wasn't
            # caught there -- the buffer the user was actually looking at
            # before :wa must end up active again, not whichever buffer
            # happened to be mid-save.
            self._load_buffer_state(min(original_index, len(self.buffers) - 1))
        if failed:
            written_note = f" ({written} written)" if written else ""
            self._set_error(f"Failed to write: {', '.join(failed)}{written_note}")
            return False
        if written:
            self.message = f"{written} buffer{'s' if written != 1 else ''} written"
        else:
            self.message = "No buffers changed"
        self.message_is_error = False
        return True

    # -----------------------------------------------------------------------
    # Undo / redo
    # -----------------------------------------------------------------------

    def _snapshot_undo_baseline(self) -> UndoState:
        """Capture a pre-edit undo snapshot of the live buffer. Shared by
        every path that needs one *before* an edit happens -- _push_undo(),
        _capture_undo_state_for_edit(), and _begin_insert_session() -- so
        the line-ending normalization / content-baseline dance only has to
        be right in one place."""
        self._prepare_line_endings_for_edit()
        snapshot = list(self.lines)
        line_endings_snapshot = list(self.line_endings)
        self._ensure_content_baseline(snapshot, line_endings_snapshot)
        return UndoState(
            snapshot, self.cursor_row, self.cursor_col,
            dict(self.marks), self._snapshot_auto_marks(), line_endings_snapshot,
            self.line_endings_trusted, self.last_jump,
        )

    def _snapshot_live_state(self) -> UndoState:
        """Capture the current live buffer as-is (already normalized), for
        pushing onto the *other* stack when undoing/redoing."""
        return UndoState(
            list(self.lines), self.cursor_row, self.cursor_col,
            dict(self.marks), self._snapshot_auto_marks(), list(self.line_endings),
            self.line_endings_trusted, self.last_jump,
        )

    def _snapshot_auto_marks(self) -> dict[int, int]:
        # Negative IDs belong to an executing :global, not to the document.
        return {key: row for key, row in self.auto_marks.items() if key >= 0}

    def _restore_undo_state(self, s: UndoState):
        (self.lines, self.cursor_row, self.cursor_col, self.marks,
         self.auto_marks, self.line_endings, self.line_endings_trusted,
         self.last_jump) = (
            list(s.lines), s.cursor_row, s.cursor_col, dict(s.marks),
            dict(s.auto_marks), list(s.line_endings), s.line_endings_trusted,
            s.last_jump
        )
        self._normalize_line_endings()
        self._clamp_cursor()
        # Assigning self.lines above goes through the tracked buffer setter,
        # which advances the revision and clears row-indexed caches even when
        # this undo/redo happens to restore the saved (modified=False) text.
        self._refresh_modified()
        self._force_redraw = True

    def _push_undo(self):
        self._append_undo_state(self._snapshot_undo_baseline())

    def _effective_undo_cap(self, state: UndoState) -> int:
        # The floor of 4 exists so a huge buffer (where UNDO_LINE_BUDGET //
        # len(lines) can round down to 0 or 1) still keeps a few undo steps
        # -- it's a floor under the *budget-derived* shrinkage, not under
        # self.max_undo itself. Flooring the min() of both (as this used to
        # do) meant ":set undolevels=1/2/3" got silently overridden back up
        # to 4 on the very next edit: the :set handler trims undo_stack to
        # the requested size immediately, but that one-time trim is the
        # only place the setting ever took effect, since every subsequent
        # _append_undo_state() call recomputed the cap as max(4, min(1,
        # budget)) == 4 regardless of the explicit smaller max_undo.
        budget_cap = max(4, self.UNDO_LINE_BUDGET // max(1, len(state.lines)))
        return min(self.max_undo, budget_cap)

    def _push_capped(self, stack: "deque[UndoState]", state: UndoState):
        # Shared by every path that appends to either undo_stack or
        # redo_stack, so max_undo / UNDO_LINE_BUDGET are honored no matter
        # which side is growing -- _undo()/_redo() push onto the *other*
        # stack from the one _push_undo() fills, and used to append there
        # directly with no cap check at all, so shrinking undolevels (or a
        # buffer-size-driven budget shrink) had no effect on a stack built
        # up via repeated u / Ctrl-R instead of fresh edits.
        cap = self._effective_undo_cap(state)
        stack.append(state)
        cost = sum(item.byte_cost for item in stack)
        while len(stack) > cap or (len(stack) > 1 and cost > self.UNDO_BYTE_BUDGET):
            cost -= stack.popleft().byte_cost

    def _append_undo_state(self, state: UndoState):
        self._push_capped(self.undo_stack, state)
        self.redo_stack.clear()

    def _capture_undo_state_for_edit(self) -> UndoState:
        return self._snapshot_undo_baseline()

    def _undo(self):
        if not self.undo_stack:
            self.message = "Already at oldest change"
            return
        self._push_capped(self.redo_stack, self._snapshot_live_state())
        self._restore_undo_state(self.undo_stack.pop())

    def _redo(self):
        if not self.redo_stack:
            self.message = "Already at newest change"
            return
        self._push_capped(self.undo_stack, self._snapshot_live_state())
        self._restore_undo_state(self.redo_stack.pop())

    # -----------------------------------------------------------------------
    # Cursor helpers
    # -----------------------------------------------------------------------

    def _clamp_cursor(self):
        if not self.lines:
            self.lines = [""]
        self.cursor_row = max(0, min(self.cursor_row, len(self.lines) - 1))
        line = self.lines[self.cursor_row]
        if self.mode in (Mode.INSERT, Mode.REPLACE, Mode.NORMAL):
            self.cursor_col = max(0, min(self.cursor_col, len(line)))
        else:
            self.cursor_col = max(0, min(self.cursor_col, len(line) - 1 if line else 0))

    def _move(self, row: int, col: int):
        self._wanted_col = None
        self._wrap_motion_cursor = None
        self.cursor_row = row
        self.cursor_col = col
        self._clamp_cursor()

    def _hide_cursor_for_scroll(self):
        """Ask the next draw to run with the terminal cursor hidden.
        edit() re-shows the cursor as soon as the scrolled frame has been
        painted, so it never jumps visibly across the screen while a
        paging/scrolling command repaints the view."""
        self._hide_cursor_next_draw = True

    def _page_move_keep_col(self, direction: int):
        """Scroll one screenful and carry the cursor with it, keeping the
        column (insert/replace-mode PgUp/PgDn)."""
        self._hide_cursor_for_scroll()
        text_rows = self._editor_text_rows(self._last_h)
        if self._markdown_wrap_enabled():
            self._scroll_wrapped_view(direction * text_rows, move_cursor=True)
            return
        if direction > 0:
            self.top_line = min(len(self.lines) - 1, self.top_line + text_rows)
            self._move(min(self.cursor_row + text_rows, len(self.lines) - 1),
                       self.cursor_col)
        else:
            self.top_line = max(0, self.top_line - text_rows)
            self._move(max(self.cursor_row - text_rows, 0), self.cursor_col)

    def _move_vertical(self, row: int):
        self._wrap_motion_cursor = None
        if self._wanted_col is None:
            self._wanted_col = self.cursor_col
        if not self.lines:
            self.lines = [""]
        self.cursor_row = max(0, min(row, len(self.lines) - 1))
        line = self.lines[self.cursor_row]
        if self.mode in (Mode.INSERT, Mode.REPLACE, Mode.NORMAL):
            self.cursor_col = max(0, min(self._wanted_col, len(line)))
        else:
            self.cursor_col = max(0, min(self._wanted_col, len(line) - 1 if line else 0))

    def _move_insert_cursor(self, row: int, col: int):
        self._wanted_col = None
        self._wrap_motion_cursor = None
        if not self.lines:
            self.lines = [""]
        self.cursor_row = max(0, min(row, len(self.lines) - 1))
        line = self.lines[self.cursor_row]
        self.cursor_col = max(0, min(col, len(line)))

    def _first_nonblank(self, row: Optional[int] = None) -> int:
        row = self.cursor_row if row is None else row
        for i, ch in enumerate(self.lines[row]):
            if not ch.isspace():
                return i
        return 0

    def _caret_line_start_col(self, row: Optional[int] = None, col: Optional[int] = None) -> int:
        row = self.cursor_row if row is None else row
        col = self.cursor_col if col is None else col
        first = self._first_nonblank(row)
        if col == 0 and first != 0:
            return first
        if col == first:
            return 0
        return first

    def _is_word_char(self, ch: str) -> bool:
        return ch.isalnum() or ch == "_"

    # --- Word movement ---

    def _word_forward(self, count: int, big: bool = False):
        for _ in range(count):
            start = (self.cursor_row, self.cursor_col)
            row, col = self.cursor_row, self.cursor_col
            line = self.lines[row]
            n = len(line)
            if big:
                while col < n and not line[col].isspace():
                    col += 1
                while col < n and line[col].isspace():
                    col += 1
            else:
                if col < n:
                    if self._is_word_char(line[col]):
                        while col < n and self._is_word_char(line[col]):
                            col += 1
                    elif not line[col].isspace():
                        while col < n and not self._is_word_char(line[col]) and not line[col].isspace():
                            col += 1
                while col < n and line[col].isspace():
                    col += 1
            if col >= n and row + 1 < len(self.lines):
                row += 1
                col  = 0
                ln   = self.lines[row]
                while col < len(ln) and ln[col].isspace():
                    col += 1
            self._move(row, col)
            if (self.cursor_row, self.cursor_col) == start:
                break   # stuck at buffer edge; a huge count must not spin

    def _word_forward_target(self, row: int, col: int, count: int,
                             big: bool = False) -> Tuple[int, int]:
        """Return a word-forward target without normal-mode EOL clamping."""
        for _ in range(count):
            start = (row, col)
            line = self.lines[row]
            n = len(line)
            if big:
                while col < n and not line[col].isspace():
                    col += 1
                while col < n and line[col].isspace():
                    col += 1
            else:
                if col < n:
                    if self._is_word_char(line[col]):
                        while col < n and self._is_word_char(line[col]):
                            col += 1
                    elif not line[col].isspace():
                        while col < n and not self._is_word_char(line[col]) and not line[col].isspace():
                            col += 1
                while col < n and line[col].isspace():
                    col += 1
            if col >= n and row + 1 < len(self.lines):
                row += 1
                col = 0
                line = self.lines[row]
                while col < len(line) and line[col].isspace():
                    col += 1
            if (row, col) == start:
                break
        return row, col

    def _word_backward(self, count: int, big: bool = False):
        for _ in range(count):
            row, col = self.cursor_row, self.cursor_col
            if col == 0:
                if row == 0:
                    break   # at buffer start; a huge count must not spin
                row -= 1
                col  = len(self.lines[row])
            col -= 1
            line = self.lines[row]
            if big:
                while col > 0 and line[col].isspace():
                    col -= 1
                while col > 0 and not line[col - 1].isspace():
                    col -= 1
            else:
                while col > 0 and line[col].isspace():
                    col -= 1
                if col > 0:
                    if self._is_word_char(line[col]):
                        while col > 0 and self._is_word_char(line[col - 1]):
                            col -= 1
                    else:
                        while col > 0 and not self._is_word_char(line[col - 1]) and not line[col - 1].isspace():
                            col -= 1
            self._move(row, col)

    def _word_end(self, count: int, big: bool = False):
        for _ in range(count):
            start = (self.cursor_row, self.cursor_col)
            row, col = self.cursor_row, self.cursor_col
            line = self.lines[row]
            col += 1
            if col >= len(line):
                if row + 1 < len(self.lines):
                    row += 1
                    col  = 0
                    line = self.lines[row]
                else:
                    self._move(row, max(0, len(line) - 1))
                    if (self.cursor_row, self.cursor_col) == start:
                        break   # at buffer end; a huge count must not spin
                    continue
            if big:
                while col < len(line) and line[col].isspace():
                    col += 1
                while col + 1 < len(line) and not line[col + 1].isspace():
                    col += 1
            else:
                while col < len(line) and line[col].isspace():
                    col += 1
                if col < len(line):
                    if self._is_word_char(line[col]):
                        while col + 1 < len(line) and self._is_word_char(line[col + 1]):
                            col += 1
                    else:
                        while col + 1 < len(line) and not self._is_word_char(line[col + 1]) and not line[col + 1].isspace():
                            col += 1
            self._move(row, col)
            if (self.cursor_row, self.cursor_col) == start:
                break

    def _para_forward(self, count: int = 1):
        for _ in range(count):
            before = self.cursor_row
            r = self.cursor_row + 1
            while r < len(self.lines) and self.lines[r].strip():
                r += 1
            while r < len(self.lines) and not self.lines[r].strip():
                r += 1
            self._move(min(r, len(self.lines) - 1), 0)
            if self.cursor_row == before:
                break   # at buffer edge; a huge count must not spin

    def _para_backward(self, count: int = 1):
        for _ in range(count):
            before = self.cursor_row
            r = self.cursor_row - 1
            while r > 0 and not self.lines[r].strip():
                r -= 1
            while r > 0 and self.lines[r - 1].strip():
                r -= 1
            self._move(max(r, 0), 0)
            if self.cursor_row == before:
                break

    # -----------------------------------------------------------------------
    # Search
    # -----------------------------------------------------------------------

    def _compile_pattern(self, pattern: str, flags: int = 0):
        """Return a cached compiled regex, or None on error."""
        key = (pattern, flags)
        cached = self._search_regex_cache.get(key)
        if cached is not None:
            self._search_regex_cache.move_to_end(key)
            return cached
        try:
            compiled = re.compile(pattern, flags)
        except re.error:
            return None
        if len(self._search_regex_cache) >= 512:
            for _ in range(256):
                self._search_regex_cache.popitem(last=False)
        self._search_regex_cache[key] = compiled
        return compiled

    def _search(self, pattern: str, forward: bool, wrap_msg: bool = True, literal: bool = False):
        if not pattern:
            return
        self.search_pattern  = pattern
        self._search_forward = forward
        self._search_literal = literal
        if literal:
            regex = self._compile_pattern(re.escape(pattern), re.IGNORECASE)
        else:
            regex = self._compile_pattern(pattern)
        if regex is None:
            self._set_error(f"Invalid pattern: {pattern}")
            return

        row, col = self.cursor_row, self.cursor_col

        if forward:
            m = regex.search(self.lines[row], col + 1)
            if m:
                self._move(row, m.start())
                return
            for r in range(row + 1, len(self.lines)):
                m = regex.search(self.lines[r])
                if m:
                    self._move(r, m.start())
                    return
            for r in range(0, row + 1):
                m = regex.search(self.lines[r])
                if m and (r != row or m.start() <= col):
                    self._move(r, m.start())
                    if wrap_msg:
                        self.message = "search wrapped"
                    return
        else:
            # Backward search: the match must *start* before the cursor (vim
            # semantics) but may extend past it, so scan the whole line and
            # stop at the first match starting at or after the cursor.
            last = None
            for m in regex.finditer(self.lines[row]):
                if m.start() >= col:
                    break
                last = m
            if last:
                self._move(row, last.start())
                return
            for r in range(row - 1, -1, -1):
                last = None
                for m in regex.finditer(self.lines[r]):
                    last = m
                if last:
                    self._move(r, last.start())
                    return
            for r in range(len(self.lines) - 1, row - 1, -1):
                start = col if r == row else 0
                last = None
                for m in regex.finditer(self.lines[r], start):
                    last = m
                if last:
                    self._move(r, last.start())
                    if wrap_msg:
                        self.message = "search wrapped"
                    return

        self._set_error(f"Pattern not found: {pattern}")

    def _search_repeated(self, pattern: str, forward: bool, count: int, literal: bool = False):
        original_direction = self._search_forward
        try:
            self._search_repeated_impl(pattern, forward, count, literal)
        finally:
            self._search_forward = original_direction

    def _search_repeated_impl(self, pattern: str, forward: bool, count: int, literal: bool = False):
        """Repeat a search *count* times for n/N.

        Search wraps, so the visited positions cycle; once a position repeats
        the remaining repetitions are resolved modulo the cycle length instead
        of running a regex pass per repetition for huge counts.
        """
        visited: dict[Tuple[int, int], int] = {}
        order: List[Tuple[int, int]] = []
        for i in range(count):
            self._search(pattern, forward, literal=literal)
            if self.message_is_error:
                break   # pattern not found; repeating cannot succeed
            pos = (self.cursor_row, self.cursor_col)
            first_seen = visited.get(pos)
            if first_seen is not None:
                period = i - first_seen
                remaining = (count - 1 - i) % period
                self._move(*order[first_seen + remaining])
                break
            visited[pos] = i
            order.append(pos)

    def _search_word_under_cursor(self, forward: bool):
        word = self._word_under_cursor()
        if word is None:
            return
        self._search(r"\b" + re.escape(word) + r"\b", forward)

    def _word_under_cursor(self) -> Optional[str]:
        line = self.lines[self.cursor_row]
        col = self.cursor_col
        if col >= len(line) or not self._is_word_char(line[col]):
            return None
        start = col
        while start > 0 and self._is_word_char(line[start - 1]):
            start -= 1
        end = col
        while end < len(line) and self._is_word_char(line[end]):
            end += 1
        return line[start:end]

    def _copy_word_under_cursor_to_register(self):
        word = self._word_under_cursor()
        if word is None:
            self._set_error("No word under cursor")
            return
        self._store_register([word], False)
        self.message = f"copied '{word}'"

    # -----------------------------------------------------------------------
    # Editing primitives
    # -----------------------------------------------------------------------

    def _insert_char(self, ch: str):
        line = self.lines[self.cursor_row]
        self._adjust_marks_for_same_line_insert(self.cursor_row, self.cursor_col, len(ch))
        if self.mode == Mode.REPLACE:
            self._replace_overwritten = [
                (r, c + len(ch) if r == self.cursor_row and c >= self.cursor_col else c, original)
                for r, c, original in self._replace_overwritten
            ]
        self.lines[self.cursor_row] = line[:self.cursor_col] + ch + line[self.cursor_col:]
        self.cursor_col += len(ch)
        self._clamp_marks()
        self.modified = True

    def _insert_text_at_cursor(self, text: str):
        if not text:
            return
        self._push_undo()
        line = self.lines[self.cursor_row]
        self._adjust_marks_for_same_line_insert(self.cursor_row, self.cursor_col, len(text))
        self.lines[self.cursor_row] = line[:self.cursor_col] + text + line[self.cursor_col:]
        self.cursor_col += len(text)
        self._clamp_marks()
        self._clamp_cursor()
        self.modified = True
        self._force_redraw = True

    def _join_line(self, row: int):
        if row + 1 < len(self.lines):
            head_len = len(self.lines[row])
            next_line = self.lines[row + 1]
            tail = self.lines[row + 1].lstrip()
            stripped = len(next_line) - len(tail)
            sep  = " " if tail else ""
            adjusted = {}
            for name, (mark_row, mark_col) in self._edit_positions().items():
                if mark_row == row + 1:
                    if mark_col < stripped:
                        mark_col = head_len
                    else:
                        mark_col = head_len + len(sep) + mark_col - stripped
                    adjusted[name] = (row, mark_col)
                elif mark_row > row + 1:
                    adjusted[name] = (mark_row - 1, mark_col)
                else:
                    adjusted[name] = (mark_row, mark_col)
            self._set_edit_positions(adjusted)
            self.auto_marks = {
                id_: row if cur == row + 1 else cur - 1 if cur > row + 1 else cur
                for id_, cur in self.auto_marks.items()
            }
            joined_ending = self._line_ending_for_row(row + 1)
            self.lines[row] = self.lines[row] + sep + tail
            self._normalize_line_endings()
            self.line_endings[row] = joined_ending
            self._delete_line_endings(row + 1, row + 2)
            del self.lines[row + 1]
            self._clamp_marks()

    def _delete_range(self, r1: int, c1: int, r2: int, c2: int,
                      linewise: bool) -> List[str]:
        """Delete region and return the deleted text as a list of strings."""
        if (r1, c1) > (r2, c2):
            r1, c1, r2, c2 = r2, c2, r1, c1

        if linewise:
            yanked = list(self.lines[r1:r2 + 1])
            if len(self.lines) == 1 and r1 == 0 and r2 == 0 and self.lines[0] == "":
                return yanked
            self._adjust_marks_for_line_delete(r1, r2)
            self._delete_line_endings(r1, r2 + 1)
            del self.lines[r1:r2 + 1]
            if not self.lines:
                self.lines = [""]
                self.line_endings = [""]
            self._clamp_marks()
            row = min(r1, len(self.lines) - 1)
            self._move(row, self._first_nonblank(row))
            return yanked

        # Character-wise
        if r1 == r2:
            yanked = [self.lines[r1][c1:c2 + 1]]
            self._adjust_marks_for_same_line_delete(r1, c1, c2)
            self.lines[r1] = self.lines[r1][:c1] + self.lines[r1][c2 + 1:]
            self._clamp_marks()
            self._move(r1, c1)
        else:
            yanked = ([self.lines[r1][c1:]] +
                      list(self.lines[r1 + 1:r2]) +
                      [self.lines[r2][:c2 + 1]])
            self._adjust_marks_for_multiline_char_delete(r1, c1, r2, c2)
            merged_ending = self._line_ending_for_row(r2)
            self.lines[r1] = self.lines[r1][:c1] + self.lines[r2][c2 + 1:]
            self._normalize_line_endings()
            self.line_endings[r1] = merged_ending
            self._delete_line_endings(r1 + 1, r2 + 1)
            del self.lines[r1 + 1:r2 + 1]
            self._clamp_marks()
            self._move(r1, c1)
        if not self.lines:
            self.lines = [""]
            self.line_endings = [""]
        return yanked

    def _get_char_range(self, r1: int, c1: int, r2: int, c2: int) -> List[str]:
        if r1 == r2:
            return [self.lines[r1][c1:max(0, c2 + 1)]]
        result = [self.lines[r1][c1:]]
        result.extend(self.lines[r1 + 1:r2])
        result.append(self.lines[r2][:max(0, c2 + 1)])
        return result

    def _indent_lines(self, r1: int, r2: int, dedent: bool) -> bool:
        ind = self._indent_str()
        changed = False
        for r in range(r1, r2 + 1):
            if dedent:
                if self.lines[r].startswith(ind):
                    self.lines[r] = self.lines[r][len(ind):]
                    self._adjust_marks_for_same_line_delete(r, 0, len(ind) - 1)
                    changed = True
                elif self.lines[r].startswith("\t"):
                    self.lines[r] = self.lines[r][1:]
                    self._adjust_marks_for_same_line_delete(r, 0, 0)
                    changed = True
            else:
                self.lines[r] = ind + self.lines[r]
                self._adjust_marks_for_same_line_insert(r, 0, len(ind))
                changed = True
        if changed:
            self._clamp_marks()
        return changed

    def _insert_hash_lines(self, r1: int, cnt: int) -> bool:
        """Insert '#' before the first non-blank char on `cnt` lines starting
        at r1 (used by the count-only N; command, e.g. `10;`). Blank lines
        (no non-blank character) are left untouched."""
        r2 = min(r1 + cnt - 1, len(self.lines) - 1)
        changed = False
        for r in range(r1, r2 + 1):
            old_line = self.lines[r]
            if not old_line.strip():
                continue
            col = self._first_nonblank(r)
            new_line = old_line[:col] + "#" + old_line[col:]
            self._adjust_marks_for_line_replace(r, old_line, new_line)
            self.lines[r] = new_line
            changed = True
        self._clamp_marks()
        return changed

    def _indent_lines_would_change(self, r1: int, r2: int, dedent: bool) -> bool:
        if not dedent:
            return r1 <= r2
        ind = self._indent_str()
        return any(
            self.lines[r].startswith(ind) or self.lines[r].startswith("\t")
            for r in range(r1, r2 + 1)
        )

    def _clamped_indent_repeat_count(self, r1: int, r2: int, cnt: int) -> int:
        # Visual '>' repeats a full O(selection size) _indent_lines() pass
        # cnt times (real vim's [count]> shifts by [count] shiftwidths), so
        # an uncapped cnt combined with a large selection scales cost as
        # cnt * selection_size with no bound -- e.g. selecting a few
        # thousand lines and typing a six-digit count froze the editor for
        # minutes. Clamp so that product can't exceed MAX_COUNT, the same
        # budget every other counted command is held to.
        selection_size = max(1, r2 - r1 + 1)
        indent_cnt = max(1, cnt)
        if selection_size * indent_cnt > self.MAX_COUNT:
            indent_cnt = max(1, self.MAX_COUNT // selection_size)
            self._set_error("Count too large for selection; clamped")
        return indent_cnt

    def _repeat_visual_indent(self, nlines: int, cnt: int, dedent: bool):
        """Dot-repeat target for visual '>' / '<': re-run the same
        line-count/shift-count as the original command, starting at the
        current cursor row."""
        r1 = self.cursor_row
        r2 = min(len(self.lines) - 1, r1 + nlines - 1)
        if dedent:
            # Capture first, commit only if something actually changed --
            # mirrors the original '<' handler in _handle_visual_key and
            # _repeat_visual_char_delete. Pushing the checkpoint eagerly (via
            # _push_capped) before knowing whether the dedent is a no-op
            # would evict the oldest undo_stack entry once the stack is at
            # its cap, and popping the tentative entry back off on a no-op
            # does not restore that evicted entry -- it just leaks it,
            # silently shrinking undo history for a repeat that changed
            # nothing.
            undo_state = self._capture_undo_state_for_edit()
            changed = False
            for _ in range(max(1, cnt)):
                if self._indent_lines(r1, r2, True):
                    changed = True
                else:
                    break
            if not changed:
                return
            self._append_undo_state(undo_state)
        else:
            cnt = self._clamped_indent_repeat_count(r1, r2, cnt)
            self._push_undo()
            for _ in range(cnt):
                self._indent_lines(r1, r2, False)
        self._move(r1, self._first_nonblank(r1))
        self.modified      = True
        self._force_redraw = True
        self._set_last_change(
            lambda n=nlines, c=cnt, d=dedent: self._repeat_visual_indent(n, c, d)
        )

    # -----------------------------------------------------------------------
    # Visual selection helpers
    # -----------------------------------------------------------------------

    def _visual_bounds(self) -> Tuple[int, int, int, int]:
        sr, sc = self.visual_start
        er, ec = self.cursor_row, self.cursor_col
        if (sr, sc) <= (er, ec):
            return sr, sc, er, ec
        return er, ec, sr, sc

    def _visual_selection_will_change(self, r1: int, c1: int, r2: int, c2: int,
                                      linewise: bool) -> bool:
        """Cheap predicate: would deleting [r1,c1]..[r2,c2] mutate the buffer?

        Avoids the O(N) `before = list(self.lines); self.lines != before`
        pattern, which materialises the whole buffer (including all rows of an
        MMapLineStore) just to detect a no-op.
        """
        if linewise:
            return not (len(self.lines) == 1 and r1 == 0 and r2 == 0
                        and self.lines[0] == "")
        if r1 != r2:
            return True
        line = self.lines[r1]
        if c1 >= len(line):
            return False
        return c2 >= c1

    def _swap_visual_anchor(self):
        self.visual_start, current = (self.cursor_row, self.cursor_col), self.visual_start
        self._move(*current)

    def _replace_visual_selection(self, after: bool, exchange: bool = False):
        put_buffer, put_is_lines, put_line_endings = self._resolve_put_source()
        if not put_buffer:
            self.message = "Nothing in register"
            self.message_is_error = True
            self._force_redraw = True
            return

        r1, c1, r2, c2 = self._visual_bounds()
        linewise = (self.mode == Mode.VISUAL_LINE)
        saved_yank = list(put_buffer)
        saved_is_lines = put_is_lines
        saved_line_endings = list(put_line_endings)
        original_yank = list(self.yank_buffer)
        original_is_lines = self.yank_is_lines
        original_line_endings = list(self.yank_line_endings)
        empty_charwise_put = (
            not saved_is_lines and len(saved_yank) == 1 and saved_yank[0] == ""
        )
        empty_selection = not self._visual_selection_will_change(r1, c1, r2, c2, linewise)
        if empty_charwise_put and empty_selection:
            self.mode = Mode.NORMAL
            self._force_redraw = True
            return

        deleted_endings = self._line_endings_for_range(r1, r2) if linewise else None
        self._push_undo()
        deleted = self._delete_range(r1, c1, r2, c2, linewise)
        if linewise and put_is_lines and deleted == [""] and self.lines == [""]:
            self.lines = []
            self.line_endings = []
            self.cursor_row = 0
            self.cursor_col = 0
        elif linewise and not put_is_lines and not (deleted == [""] and self.lines == [""]):
            # A charwise register pasted over a linewise-deleted selection
            # needs a blank placeholder line to splice into (mirrors the
            # blank line _begin_substitute_lines leaves for "cc"/"S") --
            # otherwise the charwise text merges directly into whatever
            # line followed the deleted selection instead of becoming its
            # own line, the way vim's v_p behaves for this combination.
            insert_at = min(r1, len(self.lines))
            placeholder_ending = (
                deleted_endings[-1] if deleted_endings else self.default_line_ending
            )
            self._adjust_marks_for_line_insert(insert_at, 1)
            self._insert_line_endings(insert_at, 1, placeholder_ending)
            self.lines.insert(insert_at, "")
            self._clamp_marks()
            self._move(insert_at, 0)
        self.yank_buffer = saved_yank
        self.yank_is_lines = saved_is_lines
        self.yank_line_endings = saved_line_endings
        put_after = after and not linewise
        if not linewise and put_is_lines:
            # A linewise register pasted over a charwise-deleted selection
            # needs to split the (now merged) line at the deletion point
            # and insert the yanked lines between the two halves, instead
            # of inserting them as whole lines before/after the merged
            # line. Reuse _put's existing charwise multi-segment splice --
            # which already does this splitting with correct mark handling
            # -- by bracketing the linewise buffer with empty strings:
            # [""] + lines + [""] makes _put treat `lines` as the segments
            # between the split line's prefix and suffix.
            self.yank_buffer = [""] + saved_yank + [""]
            self.yank_is_lines = False
            self.yank_line_endings = []
        self._put(after=put_after, push_undo=False)
        repeat_after = put_after
        if exchange:
            # p: deleted selection becomes the new unnamed register content
            self._store_register(deleted, linewise, deleted_endings)
        else:
            # P: preserve the original register unchanged
            self.yank_buffer = original_yank
            self.yank_is_lines = original_is_lines
            self.yank_line_endings = original_line_endings
        self._set_last_change(
            lambda after=repeat_after, text=saved_yank, is_lines=saved_is_lines,
                   endings=saved_line_endings:
            self._repeat_put_text(after, text, is_lines, endings)
        )
        self.mode = Mode.NORMAL
        self.modified = True
        self._force_redraw = True

    # --- Visual block (Ctrl-V) ---------------------------------------------
    #
    # A block is rows r1..r2 by inclusive display columns vl..vr, so tabs and
    # wide characters line up the way they look on screen. vr is _BLOCK_EOL
    # after `$`, which stretches every row of the block to its own line end.

    _BLOCK_EOL = 1 << 60

    # Cap on the spaces one block put / A may add to bring short rows out to
    # the block's column. A block anchored deep in a long line over many short
    # rows otherwise grows by (line width x rows) from a single keystroke.
    BLOCK_PAD_LIMIT = 8_000_000

    def _block_pad_cells(self, row: int, nrows: int, vcol: int) -> int:
        """Spaces needed to bring rows row..row+nrows-1 out to display
        column vcol (rows past the buffer end count as empty)."""
        total = 0
        for r in range(row, row + nrows):
            w = self._display_width(self.lines[r]) if r < len(self.lines) else 0
            total += max(0, vcol - w)
        return total

    def _block_pad_refused(self, row: int, nrows: int, vcol: int) -> bool:
        """Set an error and return True when padding rows row.. out to vcol
        would exceed BLOCK_PAD_LIMIT. Callers check before changing anything."""
        if self._block_pad_cells(row, nrows, vcol) <= self.BLOCK_PAD_LIMIT:
            return False
        self._set_error("Block too wide to pad short lines; aborted")
        self._force_redraw = True
        return True

    def _block_vcol(self, row: int, col: int) -> int:
        """Display column where character `col` of `row` starts."""
        return self._display_width(self.lines[row][:col])

    def _block_char_extent(self, row: int, col: int) -> Tuple[int, int]:
        """(first, last) display columns covered by character `col` of `row`.
        A position at or past the line end (e.g. on an empty line) covers
        one column."""
        line = self.lines[row]
        start = self._block_vcol(row, col)
        if col >= len(line):
            return start, start
        return start, start + max(1, self._display_width_at_col(line[col], start)) - 1

    def _col_at_vcol(self, line: str, vcol: int) -> int:
        """Index of the first character of `line` starting at or after display
        column `vcol` (len(line) if the line is too short)."""
        if line.isascii() and "\t" not in line and "\x00" not in line:
            return min(max(0, vcol), len(line))
        v = 0
        for i, (_, width) in enumerate(self._display_chunks(line, 0)):
            if v >= vcol and width > 0:
                return i
            v += width
        return len(line)

    def _visual_block_bounds(self) -> Tuple[int, int, int, int]:
        """(r1, r2, vl, vr) of the current Ctrl-V selection."""
        ar, ac = self.visual_start
        ar = max(0, min(ar, len(self.lines) - 1))
        a_first, a_last = self._block_char_extent(ar, ac)
        c_first, c_last = self._block_char_extent(self.cursor_row, self.cursor_col)
        vl = min(a_first, c_first)
        vr = self._BLOCK_EOL if self._block_to_eol else max(a_last, c_last)
        return min(ar, self.cursor_row), max(ar, self.cursor_row), vl, vr

    def _block_from_cursor(self, height: int, width: int,
                           to_eol: bool) -> Tuple[int, int, int, int]:
        """A block of the given size anchored at the cursor (for `.`)."""
        r1 = self.cursor_row
        r2 = min(len(self.lines) - 1, r1 + max(1, height) - 1)
        vl = self._block_vcol(r1, self.cursor_col)
        vr = self._BLOCK_EOL if to_eol else vl + max(1, width) - 1
        return r1, r2, vl, vr

    def _block_row_span(self, row: int, vl: int, vr: int) -> Tuple[int, int]:
        """Half-open character range [c1, c2) of `row` whose display cells
        overlap columns vl..vr. Rows that don't reach vl give an empty range
        at the line end."""
        line = self.lines[row]
        if line.isascii() and "\t" not in line and "\x00" not in line:
            return min(vl, len(line)), min(vr + 1, len(line))
        c1 = c2 = -1
        v = 0
        for i, (_, width) in enumerate(self._display_chunks(line, 0)):
            # Zero-width (combining) characters belong to the cell before.
            first = v if width > 0 else max(0, v - 1)
            last = v + width - 1 if width > 0 else first
            if first > vr:
                break
            if last >= vl:
                if c1 < 0:
                    c1 = i
                c2 = i + 1
            v += width
        if c1 < 0:
            return len(line), len(line)
        return c1, c2

    def _block_will_change(self, r1: int, r2: int, vl: int, vr: int) -> bool:
        for row in range(r1, r2 + 1):
            c1, c2 = self._block_row_span(row, vl, vr)
            if c2 > c1:
                return True
        return False

    def _block_text(self, r1: int, r2: int, vl: int, vr: int) -> List[str]:
        pieces = []
        for row in range(r1, r2 + 1):
            c1, c2 = self._block_row_span(row, vl, vr)
            pieces.append(self.lines[row][c1:c2])
        return pieces

    def _block_delete_rows(self, r1: int, r2: int, vl: int, vr: int) -> List[str]:
        """Cut the block out of every row; returns the removed pieces."""
        deleted = []
        for row in range(r1, r2 + 1):
            c1, c2 = self._block_row_span(row, vl, vr)
            line = self.lines[row]
            deleted.append(line[c1:c2])
            if c2 > c1:
                self._adjust_marks_for_same_line_delete(row, c1, c2 - 1)
                self.lines[row] = line[:c1] + line[c2:]
        self._clamp_marks()
        return deleted

    def _block_rest_cursor(self, row: int, vcol: int):
        """Put the NORMAL-mode cursor on the block's top-left cell."""
        line = self.lines[row]
        self._move(row, min(self._col_at_vcol(line, vcol), max(0, len(line) - 1)))

    def _block_delete(self, r1: int, r2: int, vl: int, vr: int):
        if self._block_will_change(r1, r2, vl, vr):
            self._push_undo()
            deleted = self._block_delete_rows(r1, r2, vl, vr)
            self._store_register(deleted, False, blockwise=True)
            self.modified = True
            self._force_redraw = True
            self._set_last_change(
                lambda h=r2 - r1 + 1, w=vr - vl + 1, eol=vr == self._BLOCK_EOL:
                self._block_delete(*self._block_from_cursor(h, w, eol))
            )
        self._block_rest_cursor(r1, vl)

    def _block_transform(self, r1: int, r2: int, vl: int, vr: int,
                         kind: str, ch: str = ""):
        """Rewrite the block's text in place: ~ toggles case, r replaces
        every character with `ch`."""
        changed = False
        for row in range(r1, r2 + 1):
            c1, c2 = self._block_row_span(row, vl, vr)
            if c2 <= c1:
                continue
            line = self.lines[row]
            piece = line[c1:c2]
            piece = piece.swapcase() if kind == "~" else ch * len(piece)
            new = line[:c1] + piece + line[c2:]
            if new == line:
                continue
            if not changed:
                self._push_undo()
                changed = True
            self._adjust_marks_for_line_replace(row, line, new)
            self.lines[row] = new
        if changed:
            self._clamp_marks()
            self.modified = True
            self._force_redraw = True
            self._set_last_change(
                lambda h=r2 - r1 + 1, w=vr - vl + 1, eol=vr == self._BLOCK_EOL,
                       kind=kind, ch=ch:
                self._block_transform(*self._block_from_cursor(h, w, eol), kind, ch)
            )
        self._block_rest_cursor(r1, vl)

    def _block_yank(self, r1: int, r2: int, vl: int, vr: int):
        self._store_register(self._block_text(r1, r2, vl, vr), False, blockwise=True)
        n = r2 - r1 + 1
        self.message = f"block of {n} line{'s' if n > 1 else ''} yanked"
        self._block_rest_cursor(r1, vl)

    def _pending_put_is_block(self) -> bool:
        """Whether the register the next put will read holds a block."""
        if self.active_register:
            return self.active_register in self.block_registers
        return self.yank_is_block

    def _put_block_text(self, pieces: List[str], row: int, vcol: int,
                        count: int = 1) -> int:
        """Insert `pieces` as a column at display column `vcol` of `row` and
        the rows below it, padding short rows with spaces and appending rows
        past the end of the buffer. Each piece is padded to the block width
        when text follows it, so later columns stay aligned. Returns the
        character column of the insertion on `row`."""
        width = max((self._display_width(p) for p in pieces), default=0)
        first_col = 0
        for i, piece in enumerate(pieces):
            r = row + i
            if r >= len(self.lines):
                at = len(self.lines)
                self._adjust_marks_for_line_insert(at, 1)
                # Carry a missing final newline over to the new last row, as `o` does.
                self._insert_line_endings(at, 1, self._line_ending_for_row(at - 1))
                self.lines.insert(at, "")
            line = self.lines[r]
            line_w = self._display_width(line)
            if line_w < vcol:
                line += " " * (vcol - line_w)
                col = len(line)
            else:
                col = self._col_at_vcol(line, vcol)
            padded = piece + " " * max(0, width - self._display_width(piece))
            text = padded * (count - 1) + (padded if col < len(line) else piece)
            if i == 0:
                first_col = col
            if text:
                self._adjust_marks_for_same_line_insert(r, col, len(text))
                self.lines[r] = line[:col] + text + line[col:]
        self._clamp_marks()
        return first_col

    def _put_block(self, after: bool, count: int = 1):
        """p/P of a blockwise register in NORMAL mode."""
        put_buffer, _, _ = self._resolve_put_source()
        self._put_block_payload(put_buffer, after, count)

    def _put_block_payload(self, pieces: List[str], after: bool, count: int = 1):
        if not pieces or not any(pieces):
            self.message = "Nothing in register"
            self.message_is_error = True
            return
        count = max(1, count)
        # Every row is padded to the block width (each extra copy too), so
        # size the clamp by padded cells, not by the register's raw text.
        width = max((self._display_width(p) for p in pieces), default=0)
        unit_size = max(1, width * len(pieces))
        row = self.cursor_row
        if after and self.lines[row]:
            vcol = self._block_char_extent(row, self.cursor_col)[1] + 1
        else:
            vcol = self._block_vcol(row, self.cursor_col)
        if self._block_pad_refused(row, len(pieces), vcol):
            return
        if unit_size * count > self.MAX_COUNT:
            count = max(1, self.MAX_COUNT // unit_size)
            self._set_error("Count too large for register contents; clamped")
        self._push_undo()
        col = self._put_block_text(list(pieces), row, vcol, count)
        self._move(row, col)
        self.modified = True
        self._force_redraw = True
        self._set_last_change(
            lambda text=list(pieces), after=after, count=count:
            self._put_block_payload(text, after, count)
        )

    def _replace_visual_block(self, exchange: bool):
        """v_b_p / v_b_P: replace the block with the register. A block or a
        single line of text fills the block column-wise; multi-line text has
        no column shape, so it's put as ordinary text at the block."""
        src_is_block = self._pending_put_is_block()
        put_buffer, put_is_lines, put_line_endings = self._resolve_put_source()
        if self._put_source_is_empty(put_buffer, put_is_lines):
            self.message = "Nothing in register"
            self.message_is_error = True
            self._force_redraw = True
            return
        r1, r2, vl, vr = self._visual_block_bounds()
        as_column = src_is_block or (not put_is_lines and len(put_buffer) == 1)
        if as_column:
            pieces = list(put_buffer) if src_is_block else put_buffer * (r2 - r1 + 1)
            if self._block_pad_refused(r1, len(pieces), vl):
                return
        self.mode = Mode.NORMAL
        self._push_undo()
        deleted = self._block_delete_rows(r1, r2, vl, vr)
        if as_column:
            col =self._put_block_text(pieces, r1, vl)
            self._move(r1, col)
            self._set_last_change(
                lambda h=r2 - r1 + 1, w=vr - vl + 1, eol=vr == self._BLOCK_EOL,
                       text=list(put_buffer), is_block=src_is_block:
                self._repeat_block_replace(
                    text, is_block, *self._block_from_cursor(h, w, eol))
            )
        else:
            if put_is_lines:
                self._move(r2, 0)
            else:
                self._move(r1, self._col_at_vcol(self.lines[r1], vl))
            saved = (self.yank_buffer, self.yank_is_lines, self.yank_line_endings)
            try:
                self.yank_buffer = list(put_buffer)
                self.yank_is_lines = put_is_lines
                self.yank_line_endings = list(put_line_endings)
                self._put(after=put_is_lines, push_undo=False)
            finally:
                self.yank_buffer, self.yank_is_lines, self.yank_line_endings = saved
        if exchange:
            self._store_register(deleted, False, blockwise=True)
        self.modified = True
        self._force_redraw = True

    def _repeat_block_replace(self, text: List[str], is_block: bool,
                              r1: int, r2: int, vl: int, vr: int):
        """`.` after a block p/P: replace a same-sized block at the cursor.
        Single-line text fills however many rows the new block has (fewer
        near the end of the buffer); a block register is put whole."""
        pieces = list(text) if is_block else list(text) * (r2 - r1 + 1)
        if self._block_pad_refused(r1, len(pieces), vl):
            return
        self._push_undo()
        self._block_delete_rows(r1, r2, vl, vr)
        self._move(r1, self._put_block_text(pieces, r1, vl))
        self.modified = True
        self._force_redraw = True

    def _visual_block_swap_horizontal(self):
        """v_b_O: jump to the other end of the block's current row."""
        ar, ac = self.visual_start
        ar = max(0, min(ar, len(self.lines) - 1))
        anchor_v = self._block_vcol(ar, ac)
        cursor_v = self._block_vcol(self.cursor_row, self.cursor_col)
        anchor_line = self.lines[ar]
        self.visual_start = (
            ar, min(self._col_at_vcol(anchor_line, cursor_v), max(0, len(anchor_line) - 1))
        )
        self._move(self.cursor_row, self._col_at_vcol(self.lines[self.cursor_row], anchor_v))

    def _block_begin_insert(self, kind: str, r1: int, r2: int, vl: int, vr: int):
        """Start I (before block), A (after block) or c (change block). The
        text typed on the first row is copied onto the rest of the block
        when insert mode ends -- see _finish_block_insert."""
        to_eol = vr == self._BLOCK_EOL
        # A pads the first row now and the rest on ESC (_finish_block_insert);
        # refuse before entering INSERT so nothing is half-done.
        if kind == "A" and not to_eol and self._block_pad_refused(r1, r2 - r1 + 1, vr + 1):
            self._block_rest_cursor(r1, vl)
            return
        self._enter_insert()
        if kind == "c":
            if self._block_will_change(r1, r2, vl, vr):
                deleted = self._block_delete_rows(r1, r2, vl, vr)
                self._store_register(deleted, False, blockwise=True)
                self.modified = True
                self._force_redraw = True
        line = self.lines[r1]
        unpadded = None
        if kind == "A" and to_eol:
            col = len(line)
        elif kind == "A":
            line_w = self._display_width(line)
            if line_w <= vr:
                unpadded = line
                line += " " * (vr + 1 - line_w)
                self.lines[r1] = line
            col = self._col_at_vcol(line, vr + 1)
        else:
            col = self._col_at_vcol(line, vl)
        self._move_insert_cursor(r1, col)
        self._block_insert = {
            "kind": kind, "row": r1, "r2": r2, "vl": vl, "vr": vr,
            "col": col, "orig": line, "unpadded": unpadded,
            "nlines": len(self.lines),
        }
        self._insert_replay_setup = (
            lambda kind=kind, h=r2 - r1 + 1, w=vr - vl + 1, eol=to_eol:
            self._block_begin_insert(kind, *self._block_from_cursor(h, w, eol))
        )

    def _finish_block_insert(self) -> Optional[Tuple[int, int]]:
        """Copy the text inserted on the block's first row onto its other
        rows. Returns where the cursor should rest, or None when the insert
        wasn't a plain single-line insertion (nothing is replicated then)."""
        info, self._block_insert = self._block_insert, None
        if info is None:
            return None
        r1, col, orig = info["row"], info["col"], info["orig"]
        if len(self.lines) != info["nlines"] or self.cursor_row != r1:
            return None
        new = self.lines[r1]
        if new == orig:
            if info["unpadded"] is not None:
                # Nothing typed after A: drop the padding A added.
                self.lines[r1] = info["unpadded"]
                self._clamp_marks()
            return (r1, col)
        delta = len(new) - len(orig)
        if delta <= 0 or new[:col] != orig[:col] or new[col + delta:] != orig[col:]:
            return None
        text = new[col:col + delta]
        vl, vr = info["vl"], info["vr"]
        for row in range(r1 + 1, info["r2"] + 1):
            line = self.lines[row]
            if info["kind"] == "A":
                if vr == self._BLOCK_EOL:
                    c = len(line)
                else:
                    line_w = self._display_width(line)
                    if line_w <= vr:
                        line += " " * (vr + 1 - line_w)
                    c = self._col_at_vcol(line, vr + 1)
            else:
                if self._display_width(line) < vl:
                    continue   # short rows are left alone by I and c
                c = self._col_at_vcol(line, vl)
            self._adjust_marks_for_same_line_insert(row, c, len(text))
            self.lines[row] = line[:c] + text + line[c:]
        self._clamp_marks()
        self._force_redraw = True
        return (r1, col)

    def _insert_linewise_change_target(self, row: int, deleted_count: int,
                                       ending: Optional[str] = None):
        """Create the single replacement line used by linewise change."""
        if deleted_count <= 0:
            return
        if ending is None:
            ending = self.default_line_ending
        if len(self.lines) == 1 and self.lines[0] == "":
            self.line_endings = [ending]
            self._move(0, 0)
            return
        insert_at = min(row, len(self.lines))
        self._adjust_marks_for_line_insert(insert_at, 1)
        self._insert_line_endings(insert_at, 1, ending)
        self.lines.insert(insert_at, "")
        self._clamp_marks()
        self._move(insert_at, 0)

    # -----------------------------------------------------------------------
    # Screen rendering (optimised)
    # -----------------------------------------------------------------------

    @staticmethod
    def _markdown_split_table_row(line: str) -> Optional[List[str]]:
        if "|" not in line:
            return None
        cells: List[str] = []
        current: List[str] = []
        saw_pipe = False
        in_code = False
        idx = 0
        while idx < len(line):
            ch = line[idx]
            if ch == "`":
                in_code = not in_code
                current.append(ch)
                idx += 1
                continue
            if not in_code and ch == "\\" and idx + 1 < len(line) and line[idx + 1] == "|":
                current.extend(("\\", "|"))
                idx += 2
                continue
            if not in_code and ch == "|":
                saw_pipe = True
                cells.append("".join(current))
                current = []
            else:
                current.append(ch)
            idx += 1
        cells.append("".join(current))
        if not saw_pipe:
            return None
        if line.lstrip().startswith("|") and cells:
            cells = cells[1:]
        if line.rstrip().endswith("|") and cells:
            cells = cells[:-1]
        if len(cells) < 2:
            return None
        return [cell.strip() for cell in cells]

    @staticmethod
    def _markdown_split_table_row_spans(line: str) -> Optional[List[Tuple[str, int, int, int, int]]]:
        if "|" not in line:
            return None
        segments: List[Tuple[int, int]] = []
        saw_pipe = False
        in_code = False
        start = 0
        idx = 0
        while idx < len(line):
            ch = line[idx]
            if ch == "`":
                in_code = not in_code
                idx += 1
                continue
            if not in_code and ch == "\\" and idx + 1 < len(line) and line[idx + 1] == "|":
                idx += 2
                continue
            if not in_code and ch == "|":
                saw_pipe = True
                segments.append((start, idx))
                start = idx + 1
            idx += 1
        segments.append((start, len(line)))
        if not saw_pipe:
            return None
        if line.lstrip().startswith("|") and segments:
            segments = segments[1:]
        if line.rstrip().endswith("|") and segments:
            segments = segments[:-1]
        if len(segments) < 2:
            return None

        cells: List[Tuple[str, int, int, int, int]] = []
        for seg_start, seg_end in segments:
            content_start, content_end = seg_start, seg_end
            while content_start < content_end and line[content_start].isspace():
                content_start += 1
            while content_end > content_start and line[content_end - 1].isspace():
                content_end -= 1
            cells.append((line[content_start:content_end], seg_start, seg_end, content_start, content_end))
        return cells

    @staticmethod
    def _markdown_table_alignments(cells: List[str]) -> Optional[List[str]]:
        alignments: List[str] = []
        for cell in cells:
            marker = cell.replace(" ", "")
            if not re.fullmatch(r":?-+:?", marker):
                return None
            left = marker.startswith(":")
            right = marker.endswith(":")
            if left and right:
                alignments.append("center")
            elif right:
                alignments.append("right")
            elif left:
                alignments.append("left")
            else:
                alignments.append("none")
        return alignments

    def _display_text_at_col(self, text: str, start_col: int) -> str:
        return self._display_slice(text, start_col)

    @staticmethod
    def _char_display_width(ch: str) -> int:
        if unicodedata.combining(ch):
            return 0
        return 2 if unicodedata.east_asian_width(ch) in ("W", "F") else 1

    def _display_chunks(self, text: str, start_col: int) -> Iterator[Tuple[str, int]]:
        col = start_col
        for ch in text:
            if ch == "\t":
                width = self.tab_stop - (col % self.tab_stop)
                rendered = " " * width
            elif ch == "\x00":
                rendered = "^@"
                width = 2
            else:
                rendered = ch
                width = self._char_display_width(ch)
            yield rendered, width
            col += width

    def _display_slice(
        self,
        text: str,
        start_col: int,
        skip_cols: int = 0,
        max_width: Optional[int] = None,
    ) -> str:
        if text.isascii() and "\t" not in text and "\x00" not in text:
            start = max(0, skip_cols)
            if max_width is None:
                return text[start:]
            return text[start:start + max(0, max_width)]
        out: List[str] = []
        remaining_skip = max(0, skip_cols)
        used = 0
        for rendered, width in self._display_chunks(text, start_col):
            chunk = rendered
            chunk_width = width
            if remaining_skip:
                if remaining_skip >= chunk_width:
                    remaining_skip -= chunk_width
                    continue
                if len(rendered) == chunk_width:
                    chunk = rendered[remaining_skip:]
                    chunk_width -= remaining_skip
                    remaining_skip = 0
                else:
                    remaining = chunk_width - remaining_skip
                    if max_width is not None:
                        remaining = min(remaining, max_width - used)
                    if remaining > 0:
                        out.append(" " * remaining)
                        used += remaining
                    remaining_skip = 0
                    continue
            if max_width is not None:
                remaining = max_width - used
                if remaining <= 0:
                    if chunk_width == 0 and out:
                        out.append(chunk)
                        continue
                    break
                if chunk_width > remaining:
                    if len(chunk) == chunk_width:
                        chunk = chunk[:remaining]
                        chunk_width = remaining
                    else:
                        out.append(" " * remaining)
                        used += remaining
                        break
            out.append(chunk)
            used += chunk_width
        return "".join(out)

    def _display_width_at_col(self, text: str, start_col: int) -> int:
        # '\t' display width depends on start_col; '\x00' renders as 2-char "^@";
        # wide/combining Unicode requires unicodedata. Everything else is 1 per char.
        if text.isascii() and '\t' not in text and '\x00' not in text:
            return len(text)
        return sum(width for _, width in self._display_chunks(text, start_col))

    def _display_partition_by_cols(self, text: str, start_col: int,
                                   start: int, end: int) -> Tuple[str, str, str]:
        start = max(0, start)
        end = max(start, end)
        before = self._display_slice(text, start_col, max_width=start)
        selected = self._display_slice(
            text, start_col, skip_cols=start, max_width=end - start
        )
        after = self._display_slice(text, start_col, skip_cols=end)
        return before, selected, after

    def _display_ljust(self, text: str, width: int, start_col: int = 0) -> str:
        width = max(0, width)
        visible = self._display_slice(text, start_col, max_width=width)
        return visible + (" " * max(0, width - self._display_width(visible)))

    def _markdown_table_widths(self, rows: List[List[str]], separator_idx: int) -> List[int]:
        column_count = max(len(row_cells) for row_cells in rows)
        widths = [3] * column_count
        pipe_col = 0
        for idx in range(column_count):
            content_col = pipe_col + 2
            width = 3
            for row_idx, row_cells in enumerate(rows):
                if row_idx == separator_idx:
                    continue
                cell = row_cells[idx] if idx < len(row_cells) else ""
                width = max(width, self._display_width_at_col(cell, content_col))
            widths[idx] = width
            pipe_col += width + 3
        return widths

    def _markdown_align_cell_text(
        self, cell: str, width: int, alignment: str, content_col: int
    ) -> Tuple[str, int, int]:
        if alignment == "right":
            best_left = 0
            best_rendered = self._display_text_at_col(cell, content_col)
            for left_pad in range(width + 1):
                rendered = self._display_text_at_col(cell, content_col + left_pad)
                rendered_width = self._display_width(rendered)
                if left_pad + rendered_width <= width:
                    best_left = left_pad
                    best_rendered = rendered
            rendered_width = self._display_width(best_rendered)
            right_pad = max(0, width - best_left - rendered_width)
            return (" " * best_left) + best_rendered + (" " * right_pad), best_left, rendered_width

        if alignment == "center":
            best_left = 0
            best_rendered = self._display_text_at_col(cell, content_col)
            best_score: Optional[Tuple[int, int]] = None
            for left_pad in range(width + 1):
                rendered = self._display_text_at_col(cell, content_col + left_pad)
                rendered_width = self._display_width(rendered)
                total = left_pad + rendered_width
                if total > width:
                    continue
                right_pad = width - total
                score = (abs(left_pad - right_pad), left_pad)
                if best_score is None or score < best_score:
                    best_score = score
                    best_left = left_pad
                    best_rendered = rendered
            rendered_width = self._display_width(best_rendered)
            right_pad = max(0, width - best_left - rendered_width)
            return (" " * best_left) + best_rendered + (" " * right_pad), best_left, rendered_width

        rendered = self._display_text_at_col(cell, content_col)
        rendered_width = self._display_width(rendered)
        right_pad = max(0, width - rendered_width)
        return rendered + (" " * right_pad), 0, rendered_width

    def _markdown_format_table_row(
        self, cells: List[str], widths: List[int], alignments: List[str], separator: bool
    ) -> str:
        pieces = []
        pipe_col = 0
        for idx, width in enumerate(widths):
            cell = cells[idx] if idx < len(cells) else ""
            alignment = alignments[idx] if idx < len(alignments) else "none"
            if separator:
                dash_count = max(3, width)
                if alignment == "center":
                    cell = ":" + ("-" * max(1, dash_count - 2)) + ":"
                elif alignment == "right":
                    cell = ("-" * max(1, dash_count - 1)) + ":"
                elif alignment == "left":
                    cell = ":" + ("-" * max(1, dash_count - 1))
                else:
                    cell = "-" * dash_count
                cell = cell.ljust(width)
            else:
                content_col = pipe_col + 2
                cell, _, _ = self._markdown_align_cell_text(cell, width, alignment, content_col)
            pieces.append(f" {cell} ")
            pipe_col += width + 3
        return "|" + "|".join(pieces) + "|"

    def _markdown_table_block(self, row: int) -> Optional[Tuple[int, int, int]]:
        if self._syntax_language() != "markdown" or not (0 <= row < len(self.lines)):
            return None
        if self._markdown_split_table_row(self.lines[row]) is None:
            return None

        start = row
        while start > 0 and self._markdown_split_table_row(self.lines[start - 1]) is not None:
            start -= 1
        end = row
        while end + 1 < len(self.lines) and self._markdown_split_table_row(self.lines[end + 1]) is not None:
            end += 1

        separator_row = -1
        for candidate in range(start, end + 1):
            cells = self._markdown_split_table_row(self.lines[candidate])
            if cells and self._markdown_table_alignments(cells) is not None:
                separator_row = candidate
                break
        if separator_row <= start:
            return None
        table_start = separator_row - 1
        if not (table_start <= row <= end):
            return None
        return table_start, separator_row, end

    def _markdown_table_layout(self, row: int) -> Optional[Tuple[List[str], List[int], List[str], bool]]:
        token = (id(self.lines), self._content_revision,
                 self._syntax_language(), self.tab_stop)
        hot = self._md_hot_block
        if hot is not None:
            saved_token, start, separator, end, key = hot
            if saved_token == token and start <= row <= end:
                cached = self._md_table_layout_cache.get(key)
                if cached is not None:
                    self._md_table_layout_cache.move_to_end(key)
                    rows, widths, alignments = cached
                    return rows[row - start], widths, alignments, row == separator
        block = self._markdown_table_block(row)
        if block is None:
            return None
        table_start, separator_row, table_end = block
        separator_idx = separator_row - table_start

        # Content-addressed: keyed on the table's actual line text, so a hit is
        # guaranteed fresh and multiple call sites rendering the same visible
        # row (bypass check, glyph draw, cursor/selection column mapping) don't
        # each re-parse every row and re-scan every column from scratch.
        cache_key = (self.tab_stop, tuple(self.lines[table_start:table_end + 1]))
        cached = self._md_table_layout_cache.get(cache_key)
        if cached is not None:
            self._md_table_layout_cache.move_to_end(cache_key)
            rows, widths, alignments = cached
        else:
            rows = []
            for idx in range(table_start, table_end + 1):
                cells = self._markdown_split_table_row(self.lines[idx])
                if cells is None:
                    return None
                rows.append(cells)
            alignments = self._markdown_table_alignments(rows[separator_idx])
            if alignments is None:
                return None

            widths = self._markdown_table_widths(rows, separator_idx)
            if len(alignments) < len(widths):
                alignments = alignments + ["none"] * (len(widths) - len(alignments))

            # Weighted, not just count-bounded: a table's cached rows
            # duplicate every cell's text out of the raw lines, so entry
            # count alone doesn't cap memory -- a handful of very large
            # tables could otherwise retain unbounded cache content.
            weight = (
                sum(len(cell) for line_cells in rows for cell in line_cells)
                + len(widths) * 8 + sum(len(a) for a in alignments)
            )
            if weight <= self.SYNTAX_CACHE_BYTE_BUDGET:
                while (
                    self._md_table_layout_cache
                    and (
                        len(self._md_table_layout_cache) >= 64
                        or self._md_table_layout_cache_bytes + weight > self.SYNTAX_CACHE_BYTE_BUDGET
                    )
                ):
                    old_key, _ = self._md_table_layout_cache.popitem(last=False)
                    self._md_table_layout_cache_bytes -= (
                        self._md_table_layout_cache_weights.pop(old_key, 0)
                    )
                self._md_table_layout_cache[cache_key] = (rows, widths, alignments)
                self._md_table_layout_cache_weights[cache_key] = weight
                self._md_table_layout_cache_bytes += weight

        # Only retain a reference to entries admitted by the weighted cache.
        if cache_key in self._md_table_layout_cache:
            self._md_hot_block = (
                token, table_start, separator_row, table_end, cache_key
            )
        current_cells = rows[row - table_start]
        is_separator = row == separator_row
        return current_cells, widths, alignments, is_separator

    def _markdown_table_display_line(self, row: int) -> Optional[str]:
        layout = self._markdown_table_layout(row)
        if layout is None:
            return None
        current_cells, widths, alignments, is_separator = layout
        return self._markdown_format_table_row(current_cells, widths, alignments, is_separator)

    def _display_line_text(self, row: int) -> str:
        if self.log_type:
            return self._format_log_line(self.lines[row], self.log_type)
        table_line = self._markdown_table_display_line(row)
        if table_line is not None:
            return table_line
        return self.lines[row]

    def _tab_expand(self, line: str, max_cols: int) -> str:
        return self._display_slice(line, 0, max_width=max_cols)

    def _display_width(self, text: str) -> int:
        return self._display_width_at_col(text, 0)

    def _markdown_table_display_col(self, row: int, col: int) -> Optional[int]:
        layout = self._markdown_table_layout(row)
        spans = self._markdown_split_table_row_spans(self.lines[row])
        if layout is None or spans is None:
            return None
        cells, widths, alignments, is_separator = layout
        pipe_col = 0
        for idx, (cell, seg_start, seg_end, start, end) in enumerate(spans):
            width = widths[idx] if idx < len(widths) else 3
            alignment = alignments[idx] if idx < len(alignments) else "none"
            formatted_cell = cells[idx] if idx < len(cells) else cell
            if is_separator:
                cell_start = pipe_col + 2
                rendered_width = len(formatted_cell)
            elif alignment == "right":
                _, left_pad, rendered_width = self._markdown_align_cell_text(
                    formatted_cell, width, alignment, pipe_col + 2
                )
                cell_start = pipe_col + 2 + left_pad
            elif alignment == "center":
                _, left_pad, rendered_width = self._markdown_align_cell_text(
                    formatted_cell, width, alignment, pipe_col + 2
                )
                cell_start = pipe_col + 2 + left_pad
            else:
                _, _, rendered_width = self._markdown_align_cell_text(
                    formatted_cell, width, alignment, pipe_col + 2
                )
                cell_start = pipe_col + 2
            next_pipe_col = pipe_col + width + 3
            cell_end = cell_start + rendered_width
            if col < seg_start:
                return pipe_col
            if col <= seg_end or idx == len(spans) - 1:
                if col >= seg_end:
                    return next_pipe_col
                elif col < start:
                    return min(cell_start, pipe_col + 1 + max(0, col - seg_start))
                elif col < end:
                    raw_offset = min(len(formatted_cell), col - start)
                    return min(
                        cell_end,
                        cell_start + self._display_width_at_col(
                            formatted_cell[:raw_offset], cell_start
                        ),
                    )
                else:
                    return min(next_pipe_col, cell_end + (col - end))
            pipe_col = next_pipe_col
        return None

    def _display_col(self, row: int, col: int) -> int:
        table_col = self._markdown_table_display_col(row, col)
        if table_col is not None:
            return table_col
        log_col = self._log_display_col(row, col)
        if log_col is not None:
            return log_col
        return self._display_width(self.lines[row][:col])

    def _display_syntax_language(self) -> Optional[str]:
        if self.log_type:
            return f"log:{self.log_type}"
        if self.log_type is None and self.filename:
            _, ext = os.path.splitext(self.filename.lower())
            if ext == ".log":
                return "log:generic"
        return self._syntax_language()

    def _syntax_language(self) -> Optional[str]:
        if not self.filename:
            return None
        _, ext = os.path.splitext(self.filename.lower())
        return self.SYNTAX_EXTENSIONS.get(ext)

    def _build_log_layout(self, line: str, log_type: str) -> dict:
        fields = []

        def add_field(match: re.Match[str], name: str, rendered: str,
                      display_start: int) -> Tuple[int, int]:
            raw_start, raw_end = match.span(name)
            display_end = display_start + self._display_width_at_col(rendered, display_start)
            fields.append((raw_start, raw_end, display_start, display_end, rendered))
            return display_start, display_end

        def advance(display_start: int, rendered: str) -> int:
            return display_start + self._display_width_at_col(rendered, display_start)

        if log_type == "python":
            match = self._RE_LOG_PYTHON.match(line)
            if match:
                parts = []
                display_col = 0
                for idx, (name, rendered) in enumerate((
                    ("ts", match.group("ts")),
                    ("level", f"{match.group('level'):8}"),
                    ("logger", match.group("logger")),
                    ("msg", match.group("msg")),
                )):
                    if idx:
                        parts.append(" | ")
                        display_col += 3
                    parts.append(rendered)
                    add_field(match, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                return {"text": "".join(parts), "type": "python", "fields": fields}
            return {"text": line, "type": "python", "fields": []}
        if log_type == "lnx_auth":
            match = self._RE_LOG_SYSLOG.match(line)
            if match:
                parts = []
                display_col = 0
                for idx, name in enumerate(("ts", "host", "proc", "msg")):
                    if idx:
                        parts.append(" | ")
                        display_col += 3
                    rendered = match.group(name)
                    parts.append(rendered)
                    add_field(match, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                return {"text": "".join(parts), "type": "lnx_auth", "fields": fields}
            return {"text": line, "type": "lnx_auth", "fields": []}
        if log_type == "http":
            match = self._RE_LOG_HTTP.match(line)
            if match:
                path = match.group("path")
                size = match.group("size")
                if size.isdigit():
                    size = self._fb_format_size(int(size))
                parts = []
                display_col = 0
                for idx, (name, rendered) in enumerate((
                    ("ip", match.group("ip")),
                    ("ts", match.group("ts")),
                )):
                    if idx:
                        parts.append(" | ")
                        display_col += 3
                    parts.append(rendered)
                    add_field(match, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                parts.append(" | ")
                display_col += 3
                method = match.group("method")
                parts.append(method)
                add_field(match, "method", method, display_col)
                display_col = advance(display_col, method)
                parts.append(" ")
                display_col += 1
                parts.append(path)
                add_field(match, "path", path, display_col)
                display_col = advance(display_col, path)
                for name, rendered in (("status", match.group("status")), ("size", size)):
                    parts.append(" | ")
                    display_col += 3
                    parts.append(rendered)
                    add_field(match, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                return {"text": "".join(parts), "type": "http", "fields": fields}
            return {"text": line, "type": "http", "fields": []}
        if log_type == "flask":
            match = self._RE_LOG_FLASK.match(line)
            if match:
                parts = []
                display_col = 0
                for idx, (name, rendered) in enumerate((
                    ("ts", match.group("ts")),
                    ("level", f"{match.group('level'):8}"),
                    ("logger", match.group("logger")),
                    ("msg", match.group("msg")),
                )):
                    if idx:
                        parts.append(" | ")
                        display_col += 3
                    parts.append(rendered)
                    add_field(match, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                return {"text": "".join(parts), "type": "flask", "fields": fields}
            access = self._RE_LOG_FLASK_ACCESS.match(line)
            if access:
                parts = []
                display_col = 0
                field_specs = [
                    ("ts", access.group("ts")),
                    ("level", f"{access.group('level'):8}"),
                    ("pid", access.group("pid")),
                    ("remote", self._normalize_remote_addr(access.group("remote"))),
                    ("request", f"{access.group('method')} {access.group('path')}"),
                    ("status", access.group("status")),
                    ("size", self._fb_format_size(int(access.group("size")))),
                ]
                extra = access.group("extra")
                if extra:
                    field_specs.append(("extra", extra))
                for idx, (name, rendered) in enumerate(field_specs):
                    if idx:
                        parts.append(" | ")
                        display_col += 3
                    parts.append(rendered)
                    if name == "request":
                        method = access.group("method")
                        add_field(access, "method", method, display_col)
                        add_field(
                            access,
                            "path",
                            access.group("path"),
                            advance(display_col, method) + 1,
                        )
                    elif name == "size":
                        add_field(access, "size", rendered, display_col)
                    else:
                        add_field(access, name, rendered, display_col)
                    display_col = advance(display_col, rendered)
                return {"text": "".join(parts), "type": "flask_access", "fields": fields}
            return self._build_log_layout(line, "http")
        return {"text": line, "type": log_type, "fields": []}

    def _format_log_line(self, line: str, log_type: str) -> str:
        return self._build_log_layout(line, log_type)["text"]

    def _normalize_remote_addr(self, remote: str) -> str:
        if not remote:
            return remote
        if remote.count(":") > 1 and "." not in remote:
            return remote
        host = remote
        port = ""
        if ":" in remote:
            host, _, port = remote.rpartition(":")
            if not port.isdigit():
                host = remote
                port = ""

        if re.fullmatch(r"(?:\d{1,3}\.){3}\d{1,3}", host):
            octets = [int(part) for part in host.split(".")]
            if all(0 <= part <= 255 for part in octets):
                return remote

        candidates = []
        for start in range(len(host)):
            for end in range(start + 7, min(len(host), start + 16) + 1):
                piece = host[start:end]
                if not re.fullmatch(r"(?:\d{1,3}\.){3}\d{1,3}", piece):
                    continue
                octets = [int(part) for part in piece.split(".")]
                if not all(0 <= part <= 255 for part in octets):
                    continue
                last_width = len(piece.rsplit(".", 1)[-1])
                candidates.append((start, last_width, end, piece))
        if not candidates:
            return remote
        _, _, _, best = min(candidates, key=lambda item: (item[0], item[1], item[2]))
        if port:
            return f"{best}:{port}"
        return best

    def _log_display_col(self, row: int, col: int) -> Optional[int]:
        if not self.log_type or not (0 <= row < len(self.lines)):
            return None
        layout = self._build_log_layout(self.lines[row], self.log_type)
        fields = layout["fields"]
        if not fields:
            return None
        display_text = layout["text"]
        prev_raw_end = 0
        prev_display_end = 0
        for raw_start, raw_end, display_start, display_end, rendered in fields:
            if col < raw_start:
                return min(display_start, prev_display_end + max(0, col - prev_raw_end))
            if col < raw_end:
                raw_offset = min(len(rendered), max(0, col - raw_start))
                return min(
                    display_end,
                    display_start + self._display_width_at_col(rendered[:raw_offset], display_start),
                )
            prev_raw_end = raw_end
            prev_display_end = display_end
        return min(
            self._display_width(display_text),
            prev_display_end + max(0, col - prev_raw_end),
        )

    def _log_field_spans(self, text: str) -> List[Tuple[int, int]]:
        spans = []
        start = 0
        while True:
            sep = text.find(" | ", start)
            if sep < 0:
                spans.append((start, len(text)))
                break
            spans.append((start, sep))
            start = sep + 3
        return spans

    def _level_span_kind(self, level: str) -> str:
        level = level.upper()
        if level in ("ERROR", "CRITICAL"):
            return "preproc"
        if level in ("WARNING", "WARN"):
            return "type"
        if level == "DEBUG":
            return "comment"
        return "keyword"

    def _message_extra_spans(self, text: str, start: int) -> List[Tuple[int, int, str]]:
        spans: List[Tuple[int, int, str]] = []
        for match in self._RE_LOG_IP.finditer(text):
            spans.append((start + match.start(), start + match.end(), "string"))
        for match in self._RE_LOG_DIGITS.finditer(text):
            spans.append((start + match.start(), start + match.end(), "number"))
        for match in self._RE_LOG_LEVEL.finditer(text):
            spans.append((
                start + match.start(),
                start + match.end(),
                self._level_span_kind(match.group(1)),
            ))
        return spans

    def _generic_log_syntax_spans(self, text: str) -> List[Tuple[int, int, str]]:
        if not text:
            return []
        if text.startswith("Traceback"):
            return [(0, len(text), "preproc")]
        spans: List[Tuple[int, int, str]] = []
        ts_match = self._RE_LOG_GENERIC_TS.match(text)
        scan_start = 0
        if ts_match:
            spans.append((ts_match.start(), ts_match.end(), "comment"))
            scan_start = ts_match.end()
        for match in self._RE_LOG_QUOTED.finditer(text):
            spans.append((match.start(), match.end(), "string"))
        spans.extend(self._message_extra_spans(text[scan_start:], scan_start))
        spans.sort(key=lambda s: (s[0], s[1]))
        return spans

    def _log_syntax_spans(self, text: str, log_type: str) -> List[Tuple[int, int, str]]:
        if not text:
            return []
        if log_type == "generic":
            return self._generic_log_syntax_spans(text)
        fields = self._log_field_spans(text)
        spans: List[Tuple[int, int, str]] = []
        effective_type = log_type
        if log_type == "flask" and len(fields) >= 7:
            maybe_level = text[fields[1][0]:fields[1][1]].strip()
            maybe_status = text[fields[5][0]:fields[5][1]].strip()
            if maybe_level in ("DEBUG", "INFO", "WARNING", "WARN", "ERROR", "CRITICAL") and maybe_status.isdigit():
                effective_type = "flask_access"
        if log_type == "flask" and len(fields) >= 5:
            request = text[fields[2][0]:fields[2][1]]
            status_text = text[fields[3][0]:fields[3][1]].strip()
            if " " in request and status_text.isdigit():
                effective_type = "http"
        elif log_type == "flask":
            effective_type = "python"

        if effective_type in ("python", "flask") and len(fields) >= 4:
            spans.append((fields[0][0], fields[0][1], "comment"))
            spans.append((fields[1][0], fields[1][1], self._level_span_kind(text[fields[1][0]:fields[1][1]].strip())))
            spans.append((fields[2][0], fields[2][1], "function"))
            spans.extend(self._message_extra_spans(text[fields[3][0]:fields[3][1]], fields[3][0]))
        elif effective_type == "flask_access" and len(fields) >= 7:
            spans.append((fields[0][0], fields[0][1], "comment"))
            spans.append((fields[1][0], fields[1][1], self._level_span_kind(text[fields[1][0]:fields[1][1]].strip())))
            spans.append((fields[2][0], fields[2][1], "function"))
            spans.append((fields[3][0], fields[3][1], "builtin"))
            request = text[fields[4][0]:fields[4][1]]
            method, _, path = request.partition(" ")
            if method:
                spans.append((fields[4][0], fields[4][0] + len(method), "keyword"))
            if path:
                spans.append((fields[4][0] + len(method) + 1, fields[4][1], "string"))
            status_text = text[fields[5][0]:fields[5][1]].strip()
            status_kind = "number"
            if status_text.startswith(("4", "5")):
                status_kind = "preproc"
            elif status_text.startswith("3"):
                status_kind = "type"
            elif status_text.startswith("2"):
                status_kind = "keyword"
            spans.append((fields[5][0], fields[5][1], status_kind))
            spans.append((fields[6][0], fields[6][1], "number"))
            if len(fields) > 7:
                spans.append((fields[7][0], fields[7][1], "number"))
        elif effective_type == "lnx_auth" and len(fields) >= 4:
            spans.append((fields[0][0], fields[0][1], "comment"))
            spans.append((fields[1][0], fields[1][1], "builtin"))
            spans.append((fields[2][0], fields[2][1], "function"))
            spans.extend(self._message_extra_spans(text[fields[3][0]:fields[3][1]], fields[3][0]))
            for match in self._RE_LOG_AUTH_WORDS.finditer(text[fields[3][0]:fields[3][1]]):
                spans.append((fields[3][0] + match.start(), fields[3][0] + match.end(), "keyword"))
        elif effective_type == "http" and len(fields) >= 5:
            spans.append((fields[0][0], fields[0][1], "comment"))
            spans.append((fields[1][0], fields[1][1], "builtin"))
            request = text[fields[2][0]:fields[2][1]]
            method, _, path = request.partition(" ")
            if method:
                spans.append((fields[2][0], fields[2][0] + len(method), "keyword"))
            if path:
                spans.append((fields[2][0] + len(method) + 1, fields[2][1], "string"))
            status_text = text[fields[3][0]:fields[3][1]]
            status_kind = "number"
            if status_text.startswith(("4", "5")):
                status_kind = "preproc"
            elif status_text.startswith("3"):
                status_kind = "type"
            elif status_text.startswith("2"):
                status_kind = "keyword"
            spans.append((fields[3][0], fields[3][1], status_kind))
            spans.append((fields[4][0], fields[4][1], "number"))
        elif text.startswith("Traceback"):
            spans.append((0, len(text), "preproc"))
        else:
            spans.extend(self._message_extra_spans(text, 0))
        spans.sort(key=lambda s: (s[0], s[1]))
        return spans

    def _syntax_comment_markers(self, lang: str) -> Tuple[str, ...]:
        if lang in ("python", "tcl"):
            return ("#",)
        if lang == "sql":
            return ("--",)
        if lang == "lisp":
            return (";",)
        if lang == "forth":
            return ("\\",)
        if lang == "markdown":
            return ()
        return ("//",)

    def _markdown_syntax_spans(self, text: str) -> List[Tuple[int, int, str]]:
        spans: List[Tuple[int, int, str]] = []
        occupied = bytearray(len(text))

        def add_span(start: int, end: int, kind: str) -> bool:
            start = max(0, min(start, len(text)))
            end = max(start, min(end, len(text)))
            if start == end or any(occupied[start:end]):
                return False
            spans.append((start, end, kind))
            occupied[start:end] = b'\x01' * (end - start)
            return True

        if not text:
            return []

        if self._RE_MD_FENCE.match(text):
            add_span(0, len(text), "string")
            return spans
        if len(text) >= 4 and (text.startswith("    ") or text.startswith("\t")):
            add_span(0, len(text), "string")
            return spans
        if self._RE_MD_BLOCKQUOTE.match(text):
            add_span(0, len(text), "comment")

        heading = self._RE_MD_HEADING.match(text)
        if heading:
            add_span(heading.start(1), heading.end(1), "preproc")
            if heading.end(1) < len(text):
                add_span(heading.end(1), len(text), "keyword")
        elif self._RE_MD_SETEXT.match(text) or self._RE_MD_HRULE.match(text):
            add_span(0, len(text), "preproc")

        list_match = self._RE_MD_LIST.match(text)
        if list_match:
            add_span(list_match.start(2), list_match.end(2), "operator")

        for m in self._RE_MD_TASK.finditer(text):
            add_span(m.start(), m.end(), "builtin")

        for m in self._RE_MD_INLINE_CODE.finditer(text):
            add_span(m.start(), m.end(), "string")

        for m in self._RE_MD_LINK.finditer(text):
            add_span(m.start(1), m.end(1), "builtin")
            add_span(m.start(2), m.end(2), "string")

        for m in self._RE_MD_AUTO_LINK.finditer(text):
            add_span(m.start(), m.end(), "string")

        for m in self._RE_MD_STRONG.finditer(text):
            add_span(m.start(1), m.start(1) + len(m.group(1)), "preproc")
            add_span(m.end(0) - len(m.group(1)), m.end(0), "preproc")

        for m in self._RE_MD_EMPH.finditer(text):
            add_span(m.start(), m.start() + 1, "preproc")
            add_span(m.end() - 1, m.end(), "preproc")

        return sorted(spans, key=lambda span: (span[0], span[1]))

    def _pop_syntax_cache_lru(self) -> None:
        key, _ = self._syntax_cache.popitem(last=False)
        self._syntax_cache_bytes -= self._syntax_cache_weights.pop(key, 0)

    def _syntax_spans(self, text: str, lang: Optional[str] = None) -> List[Tuple[int, int, str]]:
        lang = lang or self._display_syntax_language()
        if not lang:
            return []
        cache_key = (lang, text)
        cached = self._syntax_cache.get(cache_key)
        if cached is not None:
            self._syntax_cache.move_to_end(cache_key)
            return list(cached)

        if len(text) > self.MAX_SYNTAX_LINE_CHARS and lang not in self.CLIKE_LANGUAGES:
            return []
        if lang.startswith("log:"):
            spans = self._log_syntax_spans(text, lang.split(":", 1)[1])
        elif lang == "markdown":
            spans = self._markdown_syntax_spans(text)
        else:
            spans = self._syntax_spans_core(text, lang)

        weight = len(text) + len(spans) * 64
        # An entry heavier than the whole budget can never fit -- evicting
        # every other cached line in a futile attempt to make room would
        # just thrash the cache for nothing. Skip straight to "don't cache".
        if weight <= self.SYNTAX_CACHE_BYTE_BUDGET:
            if len(self._syntax_cache) >= self.SYNTAX_CACHE_MAX_ENTRIES:
                for _ in range(self.SYNTAX_CACHE_EVICT_COUNT):
                    self._pop_syntax_cache_lru()
            while self._syntax_cache and self._syntax_cache_bytes + weight > self.SYNTAX_CACHE_BYTE_BUDGET:
                self._pop_syntax_cache_lru()
            self._syntax_cache[cache_key] = spans
            self._syntax_cache_weights[cache_key] = weight
            self._syntax_cache_bytes += weight
        return list(spans)

    def _syntax_protected_regions(
        self, text: str, lang: str, in_block_comment: bool = False
    ) -> Tuple[List[Tuple[int, int, str]], List[Tuple[int, int]], bool, str]:
        """Split a line into protected spans and code ranges, preserving offsets."""
        markers = self._syntax_comment_markers(lang)
        is_sql = lang == "sql"
        block_comments = lang in self.CLIKE_LANGUAGES
        squote_is_string = lang not in ("lisp", "forth")
        needs_scan = (
            in_block_comment
            or (block_comments and "/*" in text)
            or any(marker in text for marker in markers)
            or '"' in text
            or (squote_is_string and "'" in text)
        )
        if not needs_scan:
            return [], ([(0, len(text))] if text else []), False, text

        protected: List[Tuple[int, int, str]] = []
        code_ranges: List[Tuple[int, int]] = []
        structure = list(text)
        n = len(text)
        i = 0
        code_start = 0

        def protect(start: int, end: int, kind: str) -> None:
            if start > code_start:
                code_ranges.append((code_start, start))
            protected.append((start, end, kind))
            structure[start:end] = " " * (end - start)

        while i < n:
            if in_block_comment:
                end = text.find("*/", i)
                if end < 0:
                    protect(i, n, "comment")
                    return protected, code_ranges, True, "".join(structure)
                end += 2
                protect(i, end, "comment")
                in_block_comment = False
                i = code_start = end
                continue

            if block_comments and text.startswith("/*", i):
                end = text.find("*/", i + 2)
                if end < 0:
                    protect(i, n, "comment")
                    return protected, code_ranges, True, "".join(structure)
                end += 2
                protect(i, end, "comment")
                i = code_start = end
                continue

            marker = next((marker for marker in markers if text.startswith(marker, i)), None)
            if marker is not None:
                protect(i, n, "comment")
                return protected, code_ranges, False, "".join(structure)

            if text[i] == '"' or (squote_is_string and text[i] == "'"):
                quote = text[i]
                start = i
                i += 1
                while i < n:
                    if text[i] == "\\" and not is_sql:
                        i = min(n, i + 2)
                        continue
                    if is_sql and text[i] == quote and i + 1 < n and text[i + 1] == quote:
                        i += 2
                        continue
                    if text[i] == quote:
                        i += 1
                        break
                    i += 1
                protect(start, i, "string")
                code_start = i
                continue
            i += 1

        if code_start < n:
            code_ranges.append((code_start, n))
        return protected, code_ranges, False, "".join(structure)

    def _analyze_syntax_line(
        self, text: str, lang: str, in_block_comment: bool = False
    ) -> CLikeLineAnalysis:
        protected, code_ranges, out_block_comment, structure = self._syntax_protected_regions(
            text, lang, in_block_comment
        )
        spans: List[Tuple[int, int, str]] = list(protected)
        occupied = bytearray(len(text))
        for start, end, _ in protected:
            occupied[start:end] = b'\x01' * (end - start)

        def add_span(start: int, end: int, kind: str) -> bool:
            if start >= end or occupied.find(1, start, end) != -1:
                return False
            spans.append((start, end, kind))
            occupied[start:end] = b'\x01' * (end - start)
            return True

        if len(text) <= self.MAX_SYNTAX_LINE_CHARS:
            if lang in ("python", "csharp"):
                match = self._RE_SYNTAX_DECORATOR.match(text)
                if match:
                    add_span(match.start(), match.end(), "preproc")
            if lang in ("c", "csharp", "vala"):
                match = self._RE_SYNTAX_PREPROC.match(text)
                if match:
                    add_span(match.start(), match.end(), "preproc")
            if lang == "forth" and "(" in text:
                for match in self._RE_FORTH_PAREN_COMMENT.finditer(text):
                    add_span(match.start(), match.end(), "comment")

            is_sql = lang == "sql"
            keywords = self.SYNTAX_KEYWORDS.get(lang, set())
            types = self.SYNTAX_TYPES.get(lang, set())
            builtins = self.SYNTAX_BUILTINS.get(lang, set())
            for range_start, range_end in code_ranges:
                for match in self._RE_SYNTAX_WORD.finditer(text, range_start, range_end):
                    word = match.group(0)
                    key = word.lower() if is_sql else word
                    if key in types:
                        add_span(match.start(), match.end(), "type")
                    elif key in keywords:
                        add_span(match.start(), match.end(), "keyword")
                    elif key in builtins:
                        add_span(match.start(), match.end(), "builtin")
                    else:
                        pos = match.end()
                        while pos < range_end and text[pos] in ' \t':
                            pos += 1
                        if pos < range_end and text[pos] == '(':
                            add_span(match.start(), match.end(), "function")
                for match in self._RE_SYNTAX_NUMBER.finditer(text, range_start, range_end):
                    add_span(match.start(), match.end(), "number")
                for match in self._RE_SYNTAX_OPERATOR.finditer(text, range_start, range_end):
                    add_span(match.start(), match.end(), "operator")

        brackets: Tuple[Tuple[int, str], ...]
        if lang in self.CLIKE_LANGUAGES and len(text) <= self.MAX_SYNTAX_LINE_CHARS:
            brackets = tuple(
                (index, text[index])
                for start, end in code_ranges
                for index in range(start, end)
                if text[index] in self.BRACKET_PAIRS
            )
        else:
            brackets = ()
        return CLikeLineAnalysis(
            tuple(sorted(spans, key=lambda span: (span[0], span[1]))),
            structure,
            out_block_comment,
            brackets,
        )

    def _syntax_spans_core(self, text: str, lang: str) -> List[Tuple[int, int, str]]:
        return list(self._analyze_syntax_line(text, lang).spans)

    def _syntax_attr(self, kind: str) -> int:
        attr = self.syntax_attrs.get(kind)
        if attr is not None:
            return attr
        if kind == "comment":
            return curses.A_DIM
        if kind in ("keyword", "type", "function", "preproc"):
            return curses.A_BOLD
        return curses.A_NORMAL

    def _strip_line_for_structure(self, line: str, lang: str, _ctx=None) -> str:
        if _ctx is None:
            markers = self._syntax_comment_markers(lang)
            marker_firsts = frozenset(m[0] for m in markers)
            is_sql = lang == "sql"
        else:
            markers, marker_firsts, is_sql = _ctx
        out: List[str] = []
        i = 0
        n = len(line)
        quote = ""
        while i < n:
            if quote:
                ch = line[i]
                if ch == "\\" and not is_sql:
                    out.append(" ")
                    if i + 1 < n:
                        out.append(" ")
                    i += 2
                    continue
                if is_sql and ch == quote and i + 1 < n and line[i + 1] == quote:
                    out.extend((" ", " "))
                    i += 2
                    continue
                out.append(" ")
                if ch == quote:
                    quote = ""
                i += 1
                continue

            if line[i] in marker_firsts:
                marker = next((m for m in markers if line.startswith(m, i)), None)
                if marker:
                    break
            if line[i] in ("'", '"'):
                quote = line[i]
                out.append(" ")
            else:
                out.append(line[i])
            i += 1
        return "".join(out)

    def _brace_delta(self, line: str, lang: str) -> int:
        stripped = self._strip_line_for_structure(line, lang)
        return stripped.count("{") - stripped.count("}")

    def _python_breadcrumbs(self, row: int) -> List[str]:
        stack: List[Tuple[int, int, str]] = []
        end = min(row, len(self.lines) - 1)
        for lineno in range(end + 1):
            line = self.lines[lineno]
            lstripped = line.lstrip(" \t")
            if not lstripped or lstripped[0] == '#':
                continue

            indent = len(line) - len(lstripped)
            while stack and indent <= stack[-1][0] and lineno > stack[-1][1]:
                stack.pop()

            # Skip regex unless line could be a def/class/async def.
            if "def " not in line and "class " not in line:
                continue
            m = self._RE_PY_SCOPE.match(line)
            if m:
                kind, name = m.groups()
                label = f"{kind} {name}"
                stack.append((indent, lineno, label))
        return [label for _, _, label in stack]

    def _tcl_breadcrumbs(self, row: int) -> List[str]:
        stack: List[Tuple[int, int, str]] = []
        depth = 0
        end = min(row, len(self.lines) - 1)
        _scope_kw = ("proc ", "namespace ", "oo::class ", "method ", "constructor", "destructor")
        _tcl_markers = self._syntax_comment_markers("tcl")
        _tcl_ctx = (_tcl_markers, frozenset(m[0] for m in _tcl_markers), False)
        for lineno in range(end + 1):
            line = self.lines[lineno]
            start_depth = max(0, depth)
            while stack and start_depth <= stack[-1][0] and lineno > stack[-1][1]:
                stack.pop()

            # Only attempt the 4 regexes when a scope keyword is present.
            lstripped = line.lstrip()
            if lstripped.startswith(_scope_kw):
                label = ""
                for regex, prefix in (
                    (self._RE_TCL_CLASS, "class"),
                    (self._RE_TCL_NAMESPACE, "namespace"),
                    (self._RE_TCL_PROC, "proc"),
                    (self._RE_TCL_METHOD, "method"),
                ):
                    m = regex.match(line)
                    if m:
                        label = f"{prefix} {m.group(1)}"
                        break
                if label:
                    stack.append((start_depth, lineno, label))

            stripped = self._strip_line_for_structure(line, "tcl", _tcl_ctx)
            depth += stripped.count("{") - stripped.count("}")
        return [label for _, _, label in stack]

    def _lisp_breadcrumbs(self, row: int) -> List[str]:
        stack: List[Tuple[int, int, str]] = []
        depth = 0
        end = min(row, len(self.lines) - 1)
        _lisp_markers = self._syntax_comment_markers("lisp")
        _lisp_ctx = (_lisp_markers, frozenset(m[0] for m in _lisp_markers), False)
        for lineno in range(end + 1):
            line = self.lines[lineno]
            stripped = self._strip_line_for_structure(line, "lisp", _lisp_ctx)
            start_depth = max(0, depth)
            while stack and start_depth <= stack[-1][0] and lineno > stack[-1][1]:
                stack.pop()

            m = self._RE_LISP_DEFUN.match(stripped)
            if m:
                stack.append((start_depth, lineno, f"{m.group(1)} {m.group(2)}"))

            depth += stripped.count("(") - stripped.count(")")
        return [label for _, _, label in stack]

    def _forth_breadcrumbs(self, row: int) -> List[str]:
        end = min(row, len(self.lines) - 1)
        _forth_markers = self._syntax_comment_markers("forth")
        _forth_ctx = (_forth_markers, frozenset(m[0] for m in _forth_markers), False)
        label = ""
        closed_at = -1
        for lineno in range(end + 1):
            if closed_at != -1 and lineno > closed_at:
                label = ""
                closed_at = -1
            stripped = self._strip_line_for_structure(self.lines[lineno], "forth", _forth_ctx)
            m = self._RE_FORTH_DEFINITION.match(stripped)
            if m:
                label = f": {m.group(1)}"
                closed_at = -1
            elif label and ";" in stripped.split():
                closed_at = lineno
        return [label] if label else []

    def _sql_breadcrumbs(self, row: int) -> List[str]:
        end = min(row, len(self.lines) - 1)
        statement = ""
        _sql_markers = self._syntax_comment_markers("sql")
        _sql_ctx = (_sql_markers, frozenset(m[0] for m in _sql_markers), True)
        for lineno in range(end, -1, -1):
            part = self._strip_line_for_structure(self.lines[lineno], "sql", _sql_ctx).strip()
            if not part:
                continue
            statement = f"{part} {statement}".strip()
            if ";" in part:
                statement = part.rsplit(";", 1)[-1].strip()
                break
        if not statement:
            return []

        m = self._RE_SQL_HEAD.match(statement)
        if not m:
            return []
        head = " ".join(m.group(1).upper().split())
        target = "" if head == "SELECT" else (m.group(2) or "")
        return [f"{head} {target}".strip()]

    def _pop_clike_analysis_lru(self) -> None:
        key, _ = self._clike_analysis_cache.popitem(last=False)
        self._clike_analysis_cache_bytes -= self._clike_analysis_cache_weights.pop(key, 0)

    def _cached_clike_analysis(
        self, text: str, lang: str, in_block_comment: bool
    ) -> CLikeLineAnalysis:
        key = (lang, text, in_block_comment)
        cached = self._clike_analysis_cache.get(key)
        if cached is not None:
            self._clike_analysis_cache.move_to_end(key)
            return cached
        analysis = self._analyze_syntax_line(text, lang, in_block_comment)
        weight = (
            len(text) + len(analysis.structure)
            + len(analysis.spans) * 64 + len(analysis.brackets) * 24
        )
        # An entry heavier than the whole budget can never fit -- evicting
        # every other cached line's analysis in a futile attempt to make
        # room would just thrash the cache for nothing (this is reachable:
        # _syntax_protected_regions builds a full-length `structure` copy
        # of `text` with no MAX_SYNTAX_LINE_CHARS gate, so one very long
        # C-like line is enough to blow the budget on its own). Skip
        # straight to "don't cache" instead.
        if weight <= self.SYNTAX_CACHE_BYTE_BUDGET:
            while (
                self._clike_analysis_cache
                and (
                    len(self._clike_analysis_cache) >= self.SYNTAX_CACHE_MAX_ENTRIES
                    or self._clike_analysis_cache_bytes + weight > self.SYNTAX_CACHE_BYTE_BUDGET
                )
            ):
                self._pop_clike_analysis_lru()
            self._clike_analysis_cache[key] = analysis
            self._clike_analysis_cache_weights[key] = weight
            self._clike_analysis_cache_bytes += weight
        return analysis

    def _clike_scope_label(self, structure: str, lang: str) -> str:
        if lang == "go":
            match = self._RE_GO_FUNC.search(structure)
            if match:
                return f"func {match.group(1)}"
            match = self._RE_GO_TYPE.search(structure)
            return f"type {match.group(1)}" if match else ""
        match = self._RE_CLIKE_TYPE.search(structure)
        if match:
            return f"{match.group(1)} {match.group(2)}"
        match = self._RE_CLIKE_FUNC.match(structure)
        return match.group(1).split("::")[-1] if match else ""

    def _advance_clike_state(
        self, state: CLikeParseState, analysis: CLikeLineAnalysis,
        lineno: int, lang: str
    ) -> CLikeParseState:
        structure = analysis.structure
        stack = list(state.stack)
        pending = state.pending
        start_depth = max(0, state.depth)
        while stack and start_depth <= stack[-1][0] and lineno > stack[-1][1]:
            stack.pop()

        label = self._clike_scope_label(structure, lang)
        opens_scope = "{" in structure
        if label and opens_scope:
            stack.append((start_depth, lineno, label))
            pending = None
        elif label:
            pending = (label, start_depth)
        elif pending and opens_scope:
            stack.append((pending[1], lineno, pending[0]))
            pending = None
        elif structure.rstrip().endswith(";"):
            pending = None

        return CLikeParseState(
            analysis.out_block_comment,
            state.depth + structure.count("{") - structure.count("}"),
            tuple(stack),
            pending,
        )

    def _ensure_clike_state(self, row: int, lang: str) -> CLikeParseState:
        """Return structural state after *row* without tokenizing its prefix."""
        row = max(0, min(row, len(self.lines) - 1))
        row_key = (lang, row)
        cached = self._clike_row_cache.get(row_key)
        if cached is not None:
            self._clike_row_cache.move_to_end(row_key)
            return cached

        checkpoints = self._clike_checkpoints.setdefault(lang, {0: CLikeParseState()})
        checkpoint_row = row - (row % self.CLIKE_CHECKPOINT_STRIDE)
        while checkpoint_row not in checkpoints:
            checkpoint_row = max(0, checkpoint_row - self.CLIKE_CHECKPOINT_STRIDE)
        state = checkpoints[checkpoint_row]
        for lineno in range(checkpoint_row, row + 1):
            key = (lang, lineno)
            cached_row = self._clike_row_cache.get(key)
            if cached_row is not None:
                state = cached_row
                self._clike_row_cache.move_to_end(key)
            else:
                _, _, out_block_comment, structure = self._syntax_protected_regions(
                    self.lines[lineno], lang, state.in_block_comment
                )
                structural_analysis = CLikeLineAnalysis(
                    (), structure, out_block_comment, ()
                )
                state = self._advance_clike_state(
                    state, structural_analysis, lineno, lang
                )
                self._clike_row_cache[key] = state
                if len(self._clike_row_cache) > self.CLIKE_ROW_CACHE_LIMIT:
                    self._clike_row_cache.popitem(last=False)
            if (lineno + 1) % self.CLIKE_CHECKPOINT_STRIDE == 0:
                checkpoints[lineno + 1] = state
        return state

    def _ensure_clike_row(
        self, row: int, lang: str, text: Optional[str] = None
    ) -> Tuple[CLikeLineAnalysis, CLikeParseState]:
        row = max(0, min(row, len(self.lines) - 1))
        before = CLikeParseState() if row == 0 else self._ensure_clike_state(row - 1, lang)
        analysis = self._cached_clike_analysis(
            self.lines[row] if text is None else text, lang, before.in_block_comment
        )
        row_key = (lang, row)
        state = self._clike_row_cache.get(row_key)
        if state is None:
            state = self._advance_clike_state(before, analysis, row, lang)
            self._clike_row_cache[row_key] = state
            if len(self._clike_row_cache) > self.CLIKE_ROW_CACHE_LIMIT:
                self._clike_row_cache.popitem(last=False)
            if (row + 1) % self.CLIKE_CHECKPOINT_STRIDE == 0:
                self._clike_checkpoints.setdefault(lang, {0: CLikeParseState()})[row + 1] = state
        else:
            self._clike_row_cache.move_to_end(row_key)
        return analysis, state

    def _clike_breadcrumbs(self, row: int, lang: str) -> List[str]:
        state = self._ensure_clike_state(row, lang)
        return [label for _, _, label in state.stack]

    def _current_breadcrumbs(self) -> List[str]:
        if self.log_type:
            return []
        lang = self._syntax_language()
        if not lang or not self.lines:
            return []

        row = max(0, min(self.cursor_row, len(self.lines) - 1))
        if lang in self.CLIKE_LANGUAGES:
            return self._clike_breadcrumbs(row, lang)
        cache_key = (lang, row, self._content_revision, id(self.lines), len(self.lines))
        if self._breadcrumb_cache_key == cache_key:
            return list(self._breadcrumb_cache_value)

        if lang == "python":
            crumbs = self._python_breadcrumbs(row)
        elif lang == "tcl":
            crumbs = self._tcl_breadcrumbs(row)
        elif lang == "sql":
            crumbs = self._sql_breadcrumbs(row)
        elif lang == "lisp":
            crumbs = self._lisp_breadcrumbs(row)
        elif lang == "forth":
            crumbs = self._forth_breadcrumbs(row)
        else:
            crumbs = []
        self._breadcrumb_cache_key = cache_key
        self._breadcrumb_cache_value = list(crumbs)
        return crumbs

    def _format_status(self, left_s: str, right_s: str, width: int) -> str:
        usable = max(0, width - 1)
        if usable <= 0:
            return ""
        left_s = self._display_text_at_col(left_s, 0)
        right_s = self._display_text_at_col(right_s, 0)
        left_width = self._display_width(left_s)
        right_width = self._display_width(right_s)
        if left_width + right_width > usable:
            keep = max(0, usable - right_width)
            if keep >= 2 and left_width > keep:
                left_tail = self._display_slice(left_s, 0, skip_cols=max(0, left_width - (keep - 1)))
                left_s = "<" + left_tail
            else:
                left_s = self._display_slice(left_s, 0, max_width=keep)
            left_width = self._display_width(left_s)
        gap = max(0, usable - left_width - right_width)
        status = left_s + (" " * gap) + right_s
        return status + (" " * max(0, usable - self._display_width(status)))

    def _draw_status_line(self, stdscr, row: int, status: str):
        attr = self.status_attr if self.status_attr else curses.A_REVERSE
        stdscr.attron(attr)
        self._add_curses_text(stdscr, row, 0, status)
        stdscr.attroff(attr)

    class _DerivedWindowProxy:
        def __init__(self, parent, begin_y: int, begin_x: int, height: int, width: int):
            self._parent = parent
            self._begin_y = begin_y
            self._begin_x = begin_x
            self._height = height
            self._width = width

        def getmaxyx(self):
            return self._height, self._width

        def move(self, row: int, col: int):
            return self._parent.move(self._begin_y + row, self._begin_x + col)

        def clrtoeol(self):
            return self._parent.clrtoeol()

        def addstr(self, row: int, col: int, text: str, *args):
            return self._parent.addstr(self._begin_y + row, self._begin_x + col, text, *args)

        def attron(self, attr):
            return self._parent.attron(attr)

        def attroff(self, attr):
            return self._parent.attroff(attr)

        def noutrefresh(self):
            return None

    def _make_derived_window(self, stdscr, height: int, width: int, begin_y: int, begin_x: int):
        if hasattr(stdscr, "derwin"):
            try:
                return stdscr.derwin(height, width, begin_y, begin_x)
            except curses.error:
                pass
        return self._DerivedWindowProxy(stdscr, begin_y, begin_x, height, width)

    def _bar_windows(self, stdscr, height: int, width: int):
        usable_width = max(1, width)
        status_win = self._make_derived_window(stdscr, 1, usable_width, max(0, height - 2), 0)
        bottom_win = self._make_derived_window(stdscr, 1, usable_width, max(0, height - 1), 0)
        return status_win, bottom_win

    def _chrome_window(self, stdscr, width: int):
        return self._make_derived_window(stdscr, 1, max(1, width), 0, 0)

    def _editor_text_rows(self, height: int) -> int:
        return max(1, height - self.CHROME_ROWS)

    def _draw_chrome_line(self, win, width: int, crumb_s: str):
        attr = self.status_attr if self.status_attr else curses.A_REVERSE
        self._add_curses_text(win, 0, 0, " " * max(0, width - 1), attr)
        if crumb_s:
            self._add_curses_text(
                win, 0, 0,
                self._display_slice(crumb_s, 0, max_width=max(0, width - 1)),
                attr,
            )

    @staticmethod
    def _noutrefresh_all(stdscr, *windows):
        stdscr.noutrefresh()
        for window in windows:
            try:
                window.noutrefresh()
            except (AttributeError, curses.error):
                pass

    def _bottom_status_text_attr(self, error: bool = False) -> int:
        if error:
            attr = self.error_attr or self.bottom_status_attr or curses.A_REVERSE
            return attr | curses.A_BOLD
        return self.bottom_status_attr if self.bottom_status_attr else curses.A_REVERSE

    def _draw_bottom_status_line(self, stdscr, row: int, width: int):
        self._add_curses_text(
            stdscr,
            row,
            0,
            " " * max(0, width - 1),
            self._bottom_status_text_attr(),
        )

    def _draw_bottom_status_text(self, stdscr, row: int, col: int, text: str,
                                 error: bool = False):
        self._add_curses_text(stdscr, row,
              col, text, self._bottom_status_text_attr(error),
        )

    def _draw_completion_matches(
            self, stdscr, row: int, width: int, matches: List[str],
            selected_index: int):
        usable = max(0, width - 1)
        if usable <= 0:
            return
        attr = self._bottom_status_text_attr()
        selected_attr = attr | curses.A_REVERSE | curses.A_BOLD
        selected_index = max(0, min(selected_index, len(matches) - 1)) if matches else 0

        def _start_index(prefix_width: int) -> int:
            start = selected_index
            used = prefix_width
            for idx in range(selected_index, -1, -1):
                piece_width = self._display_width_at_col(matches[idx], used)
                needed = piece_width
                if idx < selected_index:
                    needed += self._display_width_at_col("  ", used + piece_width)
                if used + needed > usable:
                    break
                start = idx
                used += needed
            return start

        prefix_width = 4 if selected_index > 0 else 0
        force_left_indicator = False
        if (
            prefix_width
            and self._display_width_at_col(matches[selected_index], prefix_width) > usable - prefix_width
        ):
            prefix_width = 0
            force_left_indicator = True
        start_idx = _start_index(prefix_width)
        if prefix_width and start_idx > 0:
            plain_start_idx = _start_index(0)
            if plain_start_idx < start_idx:
                prefix_width = 0
                start_idx = plain_start_idx

        def _draw_hidden_indicator(col: int, left: bool = False) -> int:
            remaining = max(0, usable - col)
            if remaining <= 0:
                return 0
            if left:
                text = "... " if remaining >= 4 else "." * min(3, remaining)
            else:
                text = " ..." if remaining >= 4 else "." * min(3, remaining)
            return self._add_curses_text(stdscr, row, col, text, attr)

        def _overlay_selected_hidden_markers(col: int, visible_width: int, right_hidden: bool):
            if visible_width <= 0:
                return
            if right_hidden:
                if col + visible_width < usable:
                    _draw_hidden_indicator(col + visible_width)

        col = 0
        left_hidden = start_idx > 0 or force_left_indicator
        if prefix_width and left_hidden:
            col += _draw_hidden_indicator(col, left=True)
        for idx in range(start_idx, len(matches)):
            match = matches[idx]
            piece = match
            separator = "  " if idx < len(matches) - 1 else ""
            draw_col = col
            piece_width = self._display_width_at_col(piece, col)
            if col + piece_width > usable:
                if idx == selected_index and col < usable:
                    drawn = self._add_curses_text(
                        stdscr, row, col, piece,
                        selected_attr if idx == selected_index else attr,
                    )
                    visible_drawn = min(drawn, max(0, usable - col))
                    right_hidden = idx < len(matches) - 1
                    _overlay_selected_hidden_markers(col, visible_drawn, right_hidden)
                    break
                if idx < len(matches) - 1 or idx > selected_index:
                    _draw_hidden_indicator(col)
                break
            col += self._add_curses_text(
                stdscr, row, col, piece,
                selected_attr if idx == selected_index else attr,
            )
            if separator:
                separator_width = self._display_width_at_col(separator, col)
                if col + separator_width > usable:
                    if idx == selected_index:
                        _overlay_selected_hidden_markers(draw_col, piece_width, right_hidden=True)
                    else:
                        _draw_hidden_indicator(col)
                    break
                col += self._add_curses_text(stdscr, row, col, separator, attr)

    def _draw_filename_completion_matches(self, stdscr, row: int, width: int):
        self._draw_completion_matches(
            stdscr, row, width,
            self._filename_completion_matches,
            self._filename_completion_index,
        )

    def _draw_intellisense_completion_matches(self, stdscr, row: int, width: int):
        self._draw_completion_matches(
            stdscr, row, width,
            self._intellisense_completion_matches,
            self._intellisense_completion_index,
        )

    def _prompt_view(self, text: str, cursor: int, width: int) -> Tuple[str, int]:
        usable = max(0, width - 1)
        if usable <= 0:
            return "", 0
        cursor = max(0, min(cursor, len(text)))
        cursor_col = self._display_width(text[:cursor])
        rendered_width = self._display_width(text)
        rendered = self._display_text_at_col(text, 0)
        if rendered_width <= usable:
            return rendered, min(cursor_col, width - 1)
        start = max(0, cursor_col - usable + 1)
        visible = self._display_slice(text, 0, skip_cols=start, max_width=usable)
        cursor_col = max(0, min(cursor_col - start, width - 1))
        return visible, cursor_col

    def _draw_prompt_line(self, win, text: str, cursor: int, width: int) -> int:
        """Draw an editable prompt on *win* row 0 with a software cursor.

        Renders the (possibly scrolled) prompt text in normal video, overlays
        the character under the cursor with A_REVERSE, and moves the window
        cursor there.  Returns the on-screen cursor column.
        """
        visible, cursor_col = self._prompt_view(text, cursor, width)
        win.clrtoeol()
        self._add_curses_text(win, 0, 0, visible)
        cursor_char = text[cursor] if 0 <= cursor < len(text) else " "
        if len(cursor_char) != 1 or not cursor_char.isprintable():
            cursor_char = " "
        try:
            win.addstr(0, cursor_col, cursor_char, curses.A_REVERSE)
        except curses.error:
            pass
        win.move(0, cursor_col)
        return cursor_col

    @staticmethod
    def _curses_safe_text(text: str) -> str:
        return text.replace("\x00", "^@")

    def _add_curses_text(self, stdscr, row: int, col: int, text: str, attr: Optional[int] = None) -> int:
        display_width = self._display_width_at_col(text, col)
        text = self._display_text_at_col(text, col)
        height, width = self._last_h, self._last_w
        if height <= 0 or width <= 0:
            try:
                height, width = stdscr.getmaxyx()
            except (AttributeError, curses.error):
                height = max(row + 1, 1)
                width = max(col + display_width, 1)
        if row < 0 or col < 0 or height <= 0 or width <= 0 or row >= height or col >= width:
            return display_width
        visible = self._display_slice(text, 0, max_width=max(0, width - col))
        if not visible:
            return display_width
        visible_width = self._display_width(visible)
        try:
            if attr is None:
                stdscr.addstr(row, col, visible)
            else:
                stdscr.addstr(row, col, visible, attr)
        except curses.error:
            # Some curses implementations raise when text lands exactly in the
            # lower-right cell, even if the write is otherwise in bounds.
            if row == height - 1 and col + visible_width == width and visible:
                visible = self._display_slice(visible, 0, max_width=max(0, visible_width - 1))
                if not visible.strip():
                    return display_width
                try:
                    if attr is None:
                        stdscr.addstr(row, col, visible)
                    else:
                        stdscr.addstr(row, col, visible, attr)
                except curses.error:
                    pass
            else:
                raise
        return display_width

    def _add_syntax_text(self, stdscr, row: int, col: int, text: str, lnum: int,
                         span_text: Optional[str] = None, span_offset: int = 0):
        source = text if span_text is None else span_text
        line_index = lnum
        if (
            self._syntax_language() == "markdown"
            and 0 <= line_index < len(self.lines)
            and self._display_line_text(line_index) != self.lines[line_index]
        ):
            self._add_curses_text(stdscr, row, col, text)
            return
        lang = self._display_syntax_language()
        if (
            lang in self.CLIKE_LANGUAGES
            and 0 <= line_index < len(self.lines)
            and span_text is not None
        ):
            analysis, _ = self._ensure_clike_row(line_index, lang, source)
            spans = analysis.spans
        else:
            spans = self._syntax_spans(source, lang)
        if not spans:
            self._add_curses_text(stdscr, row, col, text)
            return

        visible_width = self._display_width(text)
        view_start = max(0, span_offset)
        view_end = view_start + visible_width

        # Build cumulative display-column array for source once (O(N)),
        # so each span lookup is O(1) instead of reprocessing a growing prefix.
        n = len(source)
        if source.isascii() and '\t' not in source and '\x00' not in source:
            src_cols = None  # display column == char index for pure ASCII
            raw_view_start = min(n, view_start)
            raw_view_end = min(n, view_end)
        else:
            src_cols = [0] * (n + 1)
            c = 0
            for i, ch in enumerate(source):
                src_cols[i] = c
                if ch == "\t":
                    c += self.tab_stop - (c % self.tab_stop)
                elif ch == "\x00":
                    c += 2
                else:
                    c += self._char_display_width(ch)
            src_cols[n] = c
            raw_view_start = max(0, bisect_right(src_cols, view_start) - 2)
            raw_view_end = min(n, bisect_right(src_cols, view_end))

        pos = 0
        x = col
        first_span = bisect_right(spans, raw_view_start, key=lambda span: span[1])
        for raw_start, raw_end, kind in spans[first_span:]:
            if raw_start >= raw_view_end:
                break
            if src_cols is None:
                span_start = min(raw_start, n)
                span_end = min(raw_end, n)
            else:
                span_start = src_cols[min(raw_start, n)]
                span_end = src_cols[min(raw_end, n)]
            start = max(span_start, view_start) - view_start
            end = min(span_end, view_end) - view_start
            if end <= start or end <= pos:
                continue
            start = max(start, pos)
            if start > pos:
                chunk = self._display_slice(text, 0, skip_cols=pos, max_width=start - pos)
                x += self._add_curses_text(stdscr, row, x, chunk)
            if end > start:
                chunk = self._display_slice(text, 0, skip_cols=start, max_width=end - start)
                x += self._add_curses_text(stdscr, row, x, chunk, self._syntax_attr(kind))
            pos = max(pos, end)
        if pos < visible_width:
            self._add_curses_text(stdscr, row, x, self._display_slice(text, 0, skip_cols=pos))

    def _visible_line_parts(self, lnum: int, text_w: int) -> Tuple[str, str]:
        line = self._display_line_text(lnum)
        visible = self._display_slice(line, 0, skip_cols=self.left_col, max_width=text_w)
        content_visible = visible + (" " * max(0, text_w - self._display_width(visible)))
        return visible, content_visible

    def _markdown_wrap_enabled(self) -> bool:
        return self.markdown_wrap and self.log_type is None and self._syntax_language() == "markdown"

    def _wrap_text_width(self) -> int:
        return max(1, self._last_w - self._line_number_width())

    def _wrapped_line_layout(self, row: int, text_w: int) -> List[Tuple[int, str]]:
        """Display-column offsets and text for soft-wrapped rows; never edit the buffer."""
        text_w = max(1, text_w)
        source = self._display_line_text(row)
        needs_eol_cell = (
            row == self.cursor_row
            and self.cursor_col == len(self.lines[row])
            and self.mode in (Mode.NORMAL, Mode.INSERT, Mode.REPLACE)
        )
        key = (source, text_w, self.tab_stop, needs_eol_cell)
        cached = self._wrap_layout_cache.get(key)
        if cached is not None:
            self._wrap_layout_cache.move_to_end(key)
            return cached[0]

        text = self._display_text_at_col(source, 0)
        ascii_text = text.isascii()
        widths = None if ascii_text else [self._char_display_width(ch) for ch in text]
        layout: List[Tuple[int, str]] = []
        start = offset = 0
        last_width = 0
        while start < len(text):
            end = start
            used = 0
            word_end = start
            word_width = 0
            while end < len(text):
                char_width = 1 if widths is None else widths[end]
                if used + char_width > text_w and end > start:
                    break
                used += char_width
                end += 1
                if text[end - 1].isspace():
                    word_end, word_width = end, used
            if end < len(text) and word_end > start:
                end, used = word_end, word_width
            layout.append((offset, text[start:end]))
            offset += used
            start = end
            last_width = used
        # An insertion cursor after a completely full row needs its own cell.
        if not layout or (needs_eol_cell and last_width >= text_w):
            layout.append((offset, ""))

        weight = len(source) * 4 + len(text) * 4 + len(layout) * 128
        if weight <= 4 * 1024 * 1024:
            while self._wrap_layout_cache and (
                len(self._wrap_layout_cache) >= 256
                or self._wrap_layout_cache_bytes + weight > 4 * 1024 * 1024
            ):
                _, (_, old_weight) = self._wrap_layout_cache.popitem(last=False)
                self._wrap_layout_cache_bytes -= old_weight
            self._wrap_layout_cache[key] = (layout, weight)
            self._wrap_layout_cache_bytes += weight
        return layout

    def _wrapped_cursor_position(self, text_w: int) -> Tuple[int, int]:
        layout = self._wrapped_line_layout(self.cursor_row, text_w)
        dcol = self._display_col(self.cursor_row, self.cursor_col)
        segment = max(0, bisect_right(layout, dcol, key=lambda part: part[0]) - 1)
        return self.cursor_row, segment

    def _advance_wrapped_position(
        self, position: Tuple[int, int], amount: int, text_w: int
    ) -> Tuple[int, int]:
        row, segment = position
        row = max(0, min(row, len(self.lines) - 1))
        segment = max(0, min(segment, len(self._wrapped_line_layout(row, text_w)) - 1))
        while amount > 0:
            remaining = len(self._wrapped_line_layout(row, text_w)) - segment - 1
            if amount <= remaining:
                return row, segment + amount
            if row == len(self.lines) - 1:
                return row, segment + remaining
            amount -= remaining + 1
            row, segment = row + 1, 0
        while amount < 0:
            if -amount <= segment:
                return row, segment + amount
            if row == 0:
                return 0, 0
            amount += segment + 1
            row -= 1
            segment = len(self._wrapped_line_layout(row, text_w)) - 1
        return row, segment

    def _wrapped_view_top(self, text_w: int) -> Tuple[int, int]:
        if self._wrap_top_line != self.top_line:
            self._top_wrap = 0
        self.top_line, self._top_wrap = self._advance_wrapped_position(
            (self.top_line, self._top_wrap), 0, text_w
        )
        self._wrap_top_line = self.top_line
        return self.top_line, self._top_wrap

    def _set_wrapped_view_top(self, position: Tuple[int, int]):
        self.top_line, self._top_wrap = position
        self._wrap_top_line = self.top_line

    def _move_to_wrapped_position(
        self, position: Tuple[int, int], screen_col: int = 0, direction: int = 1
    ):
        row, segment = position
        text_w = self._wrap_text_width()
        layout = self._wrapped_line_layout(row, text_w)
        offset, text = layout[segment]
        display_width = self._display_width(text)
        allow_eol = (
            segment == len(layout) - 1
            and self.mode in (Mode.NORMAL, Mode.INSERT, Mode.REPLACE)
        )
        last_col = display_width if allow_eol else max(0, display_width - 1)
        target_col = offset + min(max(0, screen_col), last_col)
        line = self.lines[row]
        max_col = len(line) if self.mode in (Mode.NORMAL, Mode.INSERT, Mode.REPLACE) else max(0, len(line) - 1)
        # Table padding has no source character. Find the closest editable column.
        if self._markdown_table_layout(row) is not None:
            after = bisect_left(range(max_col + 1), target_col, key=lambda c: self._display_col(row, c))
            candidates = {max(0, min(after - 1, max_col)), min(after, max_col)}
        else:
            col = display_col = 0
            for _, char_width in self._display_chunks(line, 0):
                if display_col + char_width > target_col:
                    break
                display_col += char_width
                col += 1
            candidates = {min(col, max_col), min(col + 1, max_col)}
        end_col = offset + display_width
        within_segment = {
            col for col in candidates
            if offset <= self._display_col(row, col) < end_col
            or (allow_eol and self._display_col(row, col) == end_col)
        }
        if within_segment:
            col = min(within_segment, key=lambda c: (abs(self._display_col(row, c) - target_col), c))
        else:
            # A tab or table padding can occupy an entire display row. Skip
            # to the next source position in the direction of the motion.
            col = max(candidates) if direction >= 0 else min(candidates)
        self._move(row, col)

    def _move_screen_vertical(self, amount: int):
        if not self._markdown_wrap_enabled():
            self._move_vertical(self.cursor_row + amount)
            return
        text_w = self._wrap_text_width()
        position = self._wrapped_cursor_position(text_w)
        if self._wrap_motion_cursor != (self.cursor_row, self.cursor_col):
            offset = self._wrapped_line_layout(position[0], text_w)[position[1]][0]
            self._wanted_wrap_col = self._display_col(self.cursor_row, self.cursor_col) - offset
        wanted = self._wanted_wrap_col
        self._move_to_wrapped_position(
            self._advance_wrapped_position(position, amount, text_w), wanted, amount
        )
        self._wanted_wrap_col = wanted
        self._wrap_motion_cursor = (self.cursor_row, self.cursor_col)

    def _scroll_wrapped_view(self, amount: int, *, move_cursor: bool = False):
        text_w = self._wrap_text_width()
        top = self._wrapped_view_top(text_w)
        self._set_wrapped_view_top(self._advance_wrapped_position(top, amount, text_w))
        if move_cursor:
            self._move_screen_vertical(amount)
        else:
            cursor = self._wrapped_cursor_position(text_w)
            top = (self.top_line, self._top_wrap)
            bottom = self._advance_wrapped_position(
                top, self._editor_text_rows(self._last_h) - 1, text_w
            )
            if cursor < top:
                self._move_to_wrapped_position(top)
            elif cursor > bottom:
                self._move_to_wrapped_position(bottom, direction=-1)

    def _move_to_screen_row(self, screen_row: int):
        if self._markdown_wrap_enabled():
            text_w = self._wrap_text_width()
            position = self._advance_wrapped_position(
                self._wrapped_view_top(text_w), max(0, screen_row), text_w
            )
            self._move_to_wrapped_position(position)
        else:
            row = min(self.top_line + max(0, screen_row), len(self.lines) - 1)
            self._move(row, self._first_nonblank(row))

    def _handle_wrapped_screen_key(self, key: int, count: int) -> bool:
        if not self._markdown_wrap_enabled():
            return False
        text_rows = self._editor_text_rows(self._last_h)
        if key in (curses.KEY_DOWN, curses.KEY_UP):
            self._move_screen_vertical(count if key == curses.KEY_DOWN else -count)
        elif key in (ord("H"), ord("M"), ord("L")):
            screen_row = {
                ord("H"): count - 1, ord("M"): text_rows // 2, ord("L"): text_rows - 1
            }[key]
            self._move_to_screen_row(min(screen_row, text_rows - 1))
        elif key in (6, 2, curses.KEY_NPAGE, curses.KEY_PPAGE, 4, 21, 5, 25):
            self._hide_cursor_for_scroll()
            if key in (5, 25):
                amount = max(1, self.vertical_scroll_jump) * count
            elif key in (4, 21):
                amount = max(1, text_rows // 2) * count
            else:
                amount = text_rows * count
            if key in (2, curses.KEY_PPAGE, 21, 25):
                amount = -amount
            self._scroll_wrapped_view(amount, move_cursor=key not in (5, 25))
        else:
            return False
        return True

    def _expanded_line_prefix(self, lnum: int, text_w: int) -> str:
        return self._tab_expand(self._display_line_text(lnum), self.left_col + text_w)

    def _line_number_width(self) -> int:
        if not self.show_line_numbers:
            return 0
        return max(5, len(str(max(1, len(self.lines)))) + 1)

    def _format_line_number(self, lnum: int) -> str:
        lnum_w = self._line_number_width()
        return f"{lnum + 1:{lnum_w - 1}d} "

    def _find_matching_bracket(self, row: int, col: int) -> Optional[Tuple[int, int]]:
        if not (0 <= row < len(self.lines)):
            return None
        line = self.lines[row]
        if not (0 <= col < len(line)):
            return None
        ch = line[col]
        target = self.BRACKET_PAIRS.get(ch)
        if target is None:
            return None

        lang = self._syntax_language()
        if lang in self.CLIKE_LANGUAGES:
            return self._find_matching_clike_bracket(row, col, ch, target, lang)

        forward = ch in self.OPEN_BRACKETS
        depth = 0
        r, c = row, col
        while 0 <= r < len(self.lines):
            ln = self.lines[r]
            cols = range(c, len(ln)) if forward else range(c, -1, -1)
            for ci in cols:
                if ln[ci] == ch:
                    depth += 1
                elif ln[ci] == target:
                    depth -= 1
                    if depth == 0:
                        return r, ci
            r += 1 if forward else -1
            if 0 <= r < len(self.lines):
                c = 0 if forward else len(self.lines[r]) - 1
        return None

    def _find_matching_clike_bracket(
        self, row: int, col: int, ch: str, target: str, lang: str
    ) -> Optional[Tuple[int, int]]:
        """Match only code brackets, with a hard work budget for malformed files."""
        forward = ch in self.OPEN_BRACKETS
        depth = 0
        scanned = 0
        line_range = range(row, len(self.lines)) if forward else range(row, -1, -1)
        for lineno in line_range:
            line = self.lines[lineno]
            scanned += len(line)
            if scanned > self.MAX_BRACKET_SCAN_CHARS:
                return None
            analysis, _ = self._ensure_clike_row(lineno, lang)
            positions = analysis.brackets if forward else reversed(analysis.brackets)
            for bracket_col, bracket in positions:
                if lineno == row and (
                    (forward and bracket_col < col) or (not forward and bracket_col > col)
                ):
                    continue
                if bracket == ch:
                    depth += 1
                elif bracket == target:
                    depth -= 1
                    if depth == 0:
                        return lineno, bracket_col
        return None

    def _matching_bracket_pair(self) -> Optional[Tuple[Tuple[int, int], Tuple[int, int]]]:
        # lang is part of the key -- :file/:f can change the effective
        # syntax language (and thus which bracket-matching algorithm
        # applies) without reassigning self.lines, so content_revision
        # alone doesn't invalidate a stale match computed under the old
        # language.
        lang = self._syntax_language()
        cache_key = (lang, self.cursor_row, self.cursor_col, self._content_revision)
        if cache_key in self._bracket_match_cache:
            match = self._bracket_match_cache[cache_key]
        else:
            match = self._find_matching_bracket(self.cursor_row, self.cursor_col)
            if len(self._bracket_match_cache) >= 200:
                cur_rev = self._content_revision
                stale = [k for k in self._bracket_match_cache if k[3] != cur_rev]
                for k in stale:
                    del self._bracket_match_cache[k]
                if len(self._bracket_match_cache) >= 200:
                    for k in list(self._bracket_match_cache)[:100]:
                        del self._bracket_match_cache[k]
            self._bracket_match_cache[cache_key] = match
        if match is None:
            return None
        return (self.cursor_row, self.cursor_col), match

    def _draw_bracket_match(
        self,
        stdscr,
        srow: int,
        lnum: int,
        lnum_w: int,
        text_w: int,
        bracket_positions: set[Tuple[int, int]],
        cursor_pos: Optional[Tuple[int, int]] = None,
        span_offset: Optional[int] = None,
    ):
        if not bracket_positions:
            return
        line = self.lines[lnum]
        base_attr = curses.A_REVERSE | curses.A_BOLD
        for row, col in bracket_positions:
            if row != lnum or not (0 <= col < len(line)):
                continue
            dcol = self._display_col(lnum, col) - (
                self.left_col if span_offset is None else span_offset
            )
            if 0 <= dcol < text_w:
                attr = base_attr
                if cursor_pos is not None and (row, col) == cursor_pos:
                    attr |= curses.A_BLINK
                self._add_curses_text(stdscr, srow, lnum_w + dcol, line[col], attr)

    def _scroll_to_cursor(self, height: int, width: int):
        text_rows = self._editor_text_rows(height)
        lnum_w    = self._line_number_width()
        text_w    = max(1, width - lnum_w)
        vjump      = min(text_rows, max(1, self.vertical_scroll_jump))
        hjump      = min(text_w, max(1, self.horizontal_scroll_jump))

        if self._markdown_wrap_enabled():
            self.left_col = 0
            top = self._wrapped_view_top(text_w)
            cursor = self._wrapped_cursor_position(text_w)
            bottom = self._advance_wrapped_position(top, text_rows - 1, text_w)
            if cursor < top:
                self._set_wrapped_view_top(
                    self._advance_wrapped_position(cursor, 1 - vjump, text_w)
                )
            elif cursor > bottom:
                self._set_wrapped_view_top(
                    self._advance_wrapped_position(cursor, vjump - text_rows, text_w)
                )
            return
        self._top_wrap = 0
        self._wrap_top_line = self.top_line

        # Vertical
        if self.cursor_row < self.top_line:
            self.top_line = max(0, self.cursor_row - vjump + 1)
        elif self.cursor_row >= self.top_line + text_rows:
            self.top_line = max(0, self.cursor_row - text_rows + vjump)

        # Horizontal
        dcol = self._display_col(self.cursor_row, self.cursor_col)
        if dcol < self.left_col:
            self.left_col = max(0, dcol - hjump + 1)
        elif dcol >= self.left_col + text_w:
            self.left_col = max(0, dcol - text_w + hjump)

    def draw(self, stdscr):
        height, width = stdscr.getmaxyx()
        if height != self._last_h or width != self._last_w:
            self._last_h, self._last_w = height, width
            self._wrap_motion_cursor = None
            self._screen_buf = [""] * height
            self._force_redraw = True
        status_win, bottom_win = self._bar_windows(stdscr, height, width)

        if self.mode == Mode.HELP:
            self._draw_help(stdscr, height, width)
            return
        if self.mode == Mode.HEX:
            self._draw_hex(stdscr, height, width)
            return
        if self.mode == Mode.LINE_ENDINGS:
            self._draw_line_endings(stdscr, height, width)
            return
        if self.mode == Mode.SHELL:
            self._draw_shell(stdscr, height, width)
            return
        if self.mode == Mode.BUFFER_LIST:
            self._draw_buffer_list(stdscr, height, width)
            return
        if self.mode == Mode.RECENT_FILES:
            self._draw_recent_files(stdscr, height, width)
            return
        if self.mode == Mode.FILE_BROWSER:
            self._draw_file_browser(stdscr, height, width)
            return
        if self.mode == Mode.GREP_RESULTS:
            self._draw_grep_results(stdscr, height, width)
            return
        if self.mode == Mode.FUNCTIONS:
            self._draw_functions(stdscr, height, width)
            return

        self._scroll_to_cursor(height, width)

        chrome_win = self._chrome_window(stdscr, width)
        text_rows = self._editor_text_rows(height)
        lnum_w    = self._line_number_width()
        text_w    = max(1, width - lnum_w)
        lang      = self._display_syntax_language()
        wrapped = self._markdown_wrap_enabled()
        wrapped_rows = []
        if wrapped:
            row, segment = self._wrapped_view_top(text_w)
            while row < len(self.lines) and len(wrapped_rows) < text_rows:
                layout = self._wrapped_line_layout(row, text_w)
                for index in range(segment, min(len(layout), segment + text_rows - len(wrapped_rows))):
                    offset, text = layout[index]
                    wrapped_rows.append((row, index, offset, text))
                row, segment = row + 1, 0
        bracket_pair = self._matching_bracket_pair()
        bracket_positions = set(bracket_pair) if bracket_pair is not None else set()
        bracket_rows = {row for row, _ in bracket_positions}

        # Visual selection range
        v_r1 = v_c1 = v_r2 = v_c2 = -1
        b_vl = b_vr = -1
        if self.mode == Mode.VISUAL_BLOCK:
            v_r1, v_r2, b_vl, b_vr = self._visual_block_bounds()
        elif self.mode in VISUAL_MODES:
            v_r1, v_c1, v_r2, v_c2 = self._visual_bounds()
        has_visual = self.mode in VISUAL_MODES
        marked_rows = {
            row for row, _ in self.marks.values()
            if 0 <= row < len(self.lines)
        } | {
            cur for cur in self.auto_marks.values()
            if 0 <= cur < len(self.lines)
        }

        # --- Draw text area (physical rows start below the chrome line) ---
        for srow in range(text_rows):
            prow = srow + 1
            span_offset = self.left_col
            continuation = False
            if wrapped and srow < len(wrapped_rows):
                lnum, segment, span_offset, visible = wrapped_rows[srow]
                continuation = segment > 0
            else:
                lnum = len(self.lines) if wrapped else self.top_line + srow

            if lnum >= len(self.lines):
                content = "~" + " " * (width - 1)
                visible = ""
            else:
                if wrapped:
                    visible = self._display_slice(visible, 0, max_width=text_w)
                    content_visible = self._display_ljust(visible, text_w)
                else:
                    visible, content_visible = self._visible_line_parts(lnum, text_w)
                lnum_str = (
                    " " * lnum_w if continuation else self._format_line_number(lnum)
                ) if self.show_line_numbers else ""
                content = (lnum_str + content_visible, lang, span_offset, lnum)
                if wrapped:
                    content += (self.lines[lnum],)

            visual_row = has_visual and v_r1 <= lnum <= v_r2
            marked_row = lnum in marked_rows
            mark_state_changed = marked_row or lnum in self._last_marked_rows
            confirm_highlight = (
                self._sub_confirm_span is not None and self._sub_confirm_span[0] == lnum
            )

            if (not self._force_redraw and
                    srow < len(self._screen_buf) and
                    self._screen_buf[srow] == content and
                    not visual_row and
                    lnum not in self._last_visual_rows and
                    not mark_state_changed and
                    not confirm_highlight and
                    lnum not in bracket_rows and
                    lnum not in self._last_bracket_match_rows):
                continue

            row_ok = True
            try:
                stdscr.move(prow, 0)
                stdscr.clrtoeol()

                if lnum >= len(self.lines):
                    self._add_curses_text(stdscr, prow, 0, "~", curses.A_DIM)
                else:
                    # Line-number prefix
                    if self.show_line_numbers:
                        attr = self.linenum_attr if self.linenum_attr else curses.A_DIM
                        if marked_row:
                            attr |= curses.A_REVERSE | curses.A_BOLD
                        self._add_curses_text(stdscr, prow, 0, lnum_str, attr)

                    if visual_row:
                        draw_visible = content_visible if self.mode == Mode.VISUAL_LINE else visible
                        if self.mode == Mode.VISUAL_LINE:
                            hl_s, hl_e = 0, self._display_width(draw_visible)
                        elif self.mode == Mode.VISUAL_BLOCK:
                            b_c1, b_c2 = self._block_row_span(lnum, b_vl, b_vr)
                            hl_s = max(0, self._display_col(lnum, b_c1) - span_offset)
                            hl_e = min(self._display_width(draw_visible),
                                       self._display_col(lnum, b_c2) - span_offset)
                        else:
                            def _dc(r, c):
                                return self._display_col(r, c) - span_offset
                            hl_s = _dc(lnum, v_c1) if lnum == v_r1 else 0
                            hl_e = _dc(lnum, v_c2 + 1) if lnum == v_r2 else self._display_width(visible)
                            hl_s = max(0, hl_s)
                            hl_e = min(self._display_width(draw_visible), hl_e)

                        x = lnum_w
                        before, hilite, after = self._display_partition_by_cols(
                            draw_visible, 0, hl_s, hl_e
                        )
                        if before:
                            x += self._add_curses_text(stdscr, prow, x, before)
                        if hilite:
                            x += self._add_curses_text(stdscr, prow, x, hilite, curses.A_REVERSE)
                        if after:
                            try:
                                self._add_curses_text(stdscr, prow, x, after)
                            except curses.error:
                                row_ok = False
                    elif confirm_highlight:
                        _, sc, ec = self._sub_confirm_span
                        hl_s = max(0, self._display_col(lnum, sc) - span_offset)
                        hl_e = min(
                            self._display_width(visible),
                            self._display_col(lnum, ec) - span_offset,
                        )
                        x = lnum_w
                        before, hilite, after = self._display_partition_by_cols(
                            visible, 0, hl_s, hl_e
                        )
                        if before:
                            x += self._add_curses_text(stdscr, prow, x, before)
                        if hilite:
                            x += self._add_curses_text(stdscr, prow, x, hilite, curses.A_BOLD | curses.A_REVERSE)
                        if after:
                            try:
                                self._add_curses_text(stdscr, prow, x, after)
                            except curses.error:
                                row_ok = False
                    else:
                        try:
                            span_source = (
                                self._expanded_line_prefix(lnum, text_w)
                                if lang and lang.startswith("log:")
                                else self.lines[lnum]
                            )
                            self._add_syntax_text(
                                stdscr, prow, lnum_w, visible, lnum, span_source, span_offset
                            )
                        except curses.error:
                            row_ok = False
                    self._draw_bracket_match(
                        stdscr, prow, lnum, lnum_w,
                        min(text_w, self._display_width(visible)) if wrapped else text_w,
                        bracket_positions,
                        cursor_pos=(self.cursor_row, self.cursor_col),
                        span_offset=span_offset,
                    )

                # Only record the row as rendered once the write actually
                # happened -- committing the cache before the attempt would
                # leave a row falsely marked "clean" (and thus skipped on
                # every future frame) if this draw raised curses.error, e.g.
                # during a terminal-resize race where getmaxyx() lags the
                # real size. The nested try/excepts above swallow their own
                # curses.error locally (some marginal overflow at the right
                # edge is tolerated), so row_ok tracks whether any of them
                # actually failed to write.
                if row_ok:
                    if srow < len(self._screen_buf):
                        self._screen_buf[srow] = content
                    else:
                        self._screen_buf.append(content)

            except curses.error:
                pass

        # --- Status line ---
        fname    = self.filename or "[No Name]"
        if self.log_type:
            fname = f"{fname} [log:{self.log_type}]"
        mod_str  = "[+]" if self.modified else ""
        pct      = int(100 * (self.cursor_row + 1) / len(self.lines))
        display_col = self._display_col(self.cursor_row, self.cursor_col) + 1
        pos_col = display_col if self.log_type else self.cursor_col + 1
        pos_str  = f"{self.cursor_row + 1},{pos_col}  {pct}%"
        pending  = self._pending_op + self._count_str
        left_s   = f" {self.mode.value:<7} {mod_str} {fname}"
        right_s  = f" {pending} {pos_str} "
        status   = self._format_status(left_s, right_s, width)
        try:
            self._draw_status_line(status_win, 0, status)
        except curses.error:
            pass

        # --- Chrome line (breadcrumbs) ---
        crumb_s = " > ".join(self._current_breadcrumbs())
        try:
            self._draw_chrome_line(chrome_win, width, crumb_s)
        except curses.error:
            pass

        # Pre-compute command cursor position so both drawing and cursor sections share it
        _visible_cmd: Optional[str] = None
        _cmd_cursor_col: Optional[int] = None
        if self._cmd_buf:
            try:
                _visible_cmd, _cmd_cursor_col = self._prompt_view(
                    self._cmd_buf, self._cmd_cursor, width
                )
            except curses.error:
                pass

        # --- Message / command line ---
        try:
            bottom_win.move(0, 0)
            if self._cmd_buf and not self._filename_completion_matches and _visible_cmd is not None:
                # Draw command line in NORMAL (no reverse) so the cursor is visible
                _cmd_cursor_col = self._draw_prompt_line(
                    bottom_win, self._cmd_buf, self._cmd_cursor, width
                )
            else:
                self._draw_bottom_status_line(bottom_win, 0, width)
                if self._cmd_buf and self._filename_completion_matches:
                    self._draw_filename_completion_matches(bottom_win, 0, width)
                elif self.mode == Mode.INSERT and self._intellisense_completion_matches:
                    self._draw_intellisense_completion_matches(bottom_win, 0, width)
                elif self.message:
                    self._draw_bottom_status_text(
                        bottom_win, 0, 0, self.message, self.message_is_error
                    )
        except curses.error:
            pass

        # --- Cursor position ---
        srow   = self.cursor_row - self.top_line
        dcol   = self._display_col(self.cursor_row, self.cursor_col) - self.left_col
        if wrapped:
            cursor_segment = self._wrapped_cursor_position(text_w)[1]
            srow = -1
            for index, (row, segment, offset, _) in enumerate(wrapped_rows):
                if row == self.cursor_row and segment == cursor_segment:
                    srow = index
                    dcol = self._display_col(row, self.cursor_col) - offset
                    break
        scol   = dcol + lnum_w
        phys_row: Optional[int] = None
        phys_col: Optional[int] = None
        try:
            if self._cmd_buf and _cmd_cursor_col is not None:
                phys_row, phys_col = height - 1, _cmd_cursor_col
            elif 0 <= srow < text_rows and 0 <= scol < width:
                phys_row, phys_col = srow + 1, scol
                stdscr.move(srow + 1, scol)
        except curses.error:
            pass

        self._noutrefresh_all(stdscr, chrome_win, status_win, bottom_win)
        try:
            if phys_row is not None:
                curses.setsyx(phys_row, phys_col)
        except (curses.error, AttributeError):
            pass
        curses.doupdate()
        self._force_redraw = False
        self._last_marked_rows = marked_rows
        self._last_bracket_match_rows = bracket_rows
        self._last_visual_rows = (
            set(range(v_r1, v_r2 + 1)) if has_visual else set()
        )

    def _draw_overlay_frame(self, stdscr, height: int, width: int, *,
                            status_left: str, status_right: str,
                            total: int, top_line: int,
                            draw_row: Callable, filler: bool = False,
                            bottom: Optional[Callable] = None,
                            cursor: Tuple[int, int] = (0, 0)):
        """Shared scaffold for full-screen overlay draws: text rows, status
        bar, bottom bar, refresh, and cursor placement. `draw_row(scr, srow,
        idx)` renders one visible row; `bottom(bottom_win)` draws the bottom
        bar and may return a (row, col) cursor position overriding `cursor`.
        """
        status_win, bottom_win = self._bar_windows(stdscr, height, width)
        text_rows = max(1, height - 2)
        for srow in range(text_rows):
            idx = top_line + srow
            try:
                stdscr.move(srow, 0)
                stdscr.clrtoeol()
                if idx < total:
                    draw_row(stdscr, srow, idx)
                elif filler:
                    self._add_curses_text(stdscr, srow, 0, "~", curses.A_DIM)
            except curses.error:
                pass

        status = self._format_status(status_left, status_right, width)
        try:
            self._draw_status_line(status_win, 0, status)
            bottom_win.move(0, 0)
            if bottom is not None:
                cursor = bottom(bottom_win) or cursor
        except curses.error:
            pass

        self._noutrefresh_all(stdscr, status_win, bottom_win)
        try:
            curses.setsyx(*cursor)
        except (curses.error, AttributeError):
            pass
        curses.doupdate()
        self._force_redraw = False

    def _draw_overlay_bottom(self, bottom_win, width: int, text: str,
                             error: bool = False):
        self._draw_bottom_status_line(bottom_win, 0, width)
        self._draw_bottom_status_text(bottom_win, 0, 0, text, error)

    def _clamp_list_view(self, cursor_attr: str, top_attr: str, total: int,
                         text_rows: int):
        """Clamp a list overlay's cursor and scroll the view to keep it visible."""
        cursor = max(0, min(getattr(self, cursor_attr), max(0, total - 1)))
        top = getattr(self, top_attr)
        if cursor < top:
            top = cursor
        elif cursor >= top + text_rows:
            top = cursor - text_rows + 1
        setattr(self, cursor_attr, cursor)
        setattr(self, top_attr, max(0, min(top, max(0, total - text_rows))))

    def _draw_help(self, stdscr, height: int, width: int):
        text_rows = max(1, height - 2)
        total = len(self.HELP_LINES)
        self.help_top_line = max(0, min(self.help_top_line, max(0, total - text_rows)))

        def draw_row(scr, srow, idx):
            line = self.HELP_LINES[idx]
            attr = curses.A_BOLD if idx == 0 or not line.startswith("  ") else curses.A_NORMAL
            self._add_curses_text(scr, srow, 0, line, attr)

        def bottom(bottom_win):
            if self._cmd_buf:
                col = self._draw_prompt_line(
                    bottom_win, self._cmd_buf, self._cmd_cursor, width
                )
                return height - 1, col
            if self.message:
                self._draw_overlay_bottom(bottom_win, width, self.message, self.message_is_error)
            else:
                self._draw_overlay_bottom(
                    bottom_win, width,
                    "q/ESC/F1 close, j/k scroll, Tab sections, / search, n/N repeat",
                )
            return None

        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=" HELP    vii",
            status_right=f" {self.help_top_line + 1}-{min(total, self.help_top_line + text_rows)}/{total} ",
            total=total, top_line=self.help_top_line,
            draw_row=draw_row, bottom=bottom,
        )

    def _open_help(self):
        self.mode = Mode.HELP
        self.help_top_line = 0
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _help_section_lines(self) -> List[int]:
        return [
            idx for idx, line in enumerate(self.HELP_LINES)
            if (idx != 0 and line and not line.startswith("  ") and
                idx + 1 < len(self.HELP_LINES) and self.HELP_LINES[idx + 1].startswith("  "))
        ]

    def _jump_help_section(self, forward: bool):
        sections = self._help_section_lines()
        if not sections:
            return
        if forward:
            target = next((idx for idx in sections if idx > self.help_top_line), sections[0])
        else:
            target = next((idx for idx in reversed(sections) if idx < self.help_top_line), sections[-1])
        self.help_top_line = target
        self.message = self.HELP_LINES[target]
        self.message_is_error = False
        self._force_redraw = True

    def _search_help(self, pattern: str, forward: bool, wrap_msg: bool = True):
        if not pattern:
            self._set_error("No previous help search pattern")
            return
        regex = self._compile_pattern(pattern, re.IGNORECASE)
        if regex is None:
            self._set_error(f"Invalid pattern: {pattern}")
            return

        self.help_search_pattern = pattern
        self.help_search_forward = forward
        total = len(self.HELP_LINES)
        if total == 0:
            return

        start = self.help_top_line
        offsets = range(1, total + 1) if forward else range(-1, -total - 1, -1)
        wrapped = False
        for offset in offsets:
            idx = (start + offset) % total
            if (forward and start + offset >= total) or (not forward and start + offset < 0):
                wrapped = True
            if regex.search(self.HELP_LINES[idx]):
                self.help_top_line = idx
                self.message = "help search wrapped" if wrapped and wrap_msg else ""
                self.message_is_error = False
                self._force_redraw = True
                return

        self._set_error(f"Help pattern not found: {pattern}")

    def _open_shell_output(self, command: str, lines: List[str], remember_shell: bool = True):
        self.mode = Mode.SHELL
        self.shell_command_label = command
        if remember_shell:
            self.last_shell_cmd = command
        self.shell_lines = lines or [""]
        self.shell_top_line = 0
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _draw_shell(self, stdscr, height: int, width: int):
        text_rows = max(1, height - 2)
        total = len(self.shell_lines)
        self.shell_top_line = max(0, min(self.shell_top_line, max(0, total - text_rows)))
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=f" SHELL   :!{self.shell_command_label}",
            status_right=f" {self.shell_top_line + 1}-{min(total, self.shell_top_line + text_rows)}/{total} ",
            total=total, top_line=self.shell_top_line,
            draw_row=lambda scr, srow, idx: self._add_curses_text(
                scr, srow, 0, self.shell_lines[idx]),
            bottom=lambda win: self._draw_overlay_bottom(
                win, width, "q/ESC close, j/k scroll, Ctrl-D/U and gg/G jump"),
        )

    def _handle_scroll_overlay(self, key: int, top_line_attr: str, total_lines: int, close_keys: Tuple[int, ...]) -> bool:
        text_rows = max(1, self._last_h - 2)
        max_top = max(0, total_lines - text_rows)
        top_line = getattr(self, top_line_attr)

        if key in close_keys:
            self.mode = Mode.NORMAL
            self._count_str = ""
            self._pending_op = ""
            self._overlay_pending_g = False
            self._force_redraw = True
            return True
        if self._overlay_pending_g:
            self._overlay_pending_g = False
            if key == ord("g"):
                setattr(self, top_line_attr, 0)
            self._force_redraw = True
            return True
        if key in (ord("j"), curses.KEY_DOWN):
            top_line = min(max_top, top_line + 1)
        elif key in (ord("k"), curses.KEY_UP):
            top_line = max(0, top_line - 1)
        elif key in (6, curses.KEY_NPAGE):
            top_line = min(max_top, top_line + text_rows)
        elif key in (2, curses.KEY_PPAGE):
            top_line = max(0, top_line - text_rows)
        elif key == 4:
            top_line = min(max_top, top_line + max(1, text_rows // 2))
        elif key == 21:
            top_line = max(0, top_line - max(1, text_rows // 2))
        elif key == curses.KEY_HOME:
            top_line = 0
        elif key == curses.KEY_END:
            top_line = max_top
        elif key == ord("g"):
            self._overlay_pending_g = True
        elif key == ord("G"):
            top_line = max_top

        setattr(self, top_line_attr, top_line)
        self._force_redraw = True
        return True

    def _list_overlay_nav(self, key, cursor_attr: str, total: int) -> bool:
        """Shared cursor navigation for list overlays. Returns True if the
        key was consumed. Callers that accept text input (e.g. the function
        list filter) must consume printable keys before delegating here,
        since j/k/g/G double as navigation."""
        text_rows = max(1, self._last_h - 2)
        max_cursor = max(0, total - 1)
        cursor = getattr(self, cursor_attr)
        if key in (ord("j"), curses.KEY_DOWN):
            cursor = min(max_cursor, cursor + 1)
        elif key in (ord("k"), curses.KEY_UP):
            cursor = max(0, cursor - 1)
        elif key in (6, curses.KEY_NPAGE):
            cursor = min(max_cursor, cursor + text_rows)
        elif key in (2, curses.KEY_PPAGE):
            cursor = max(0, cursor - text_rows)
        elif key == 4:
            cursor = min(max_cursor, cursor + max(1, text_rows // 2))
        elif key == 21:
            cursor = max(0, cursor - max(1, text_rows // 2))
        elif key in (curses.KEY_HOME, ord("g")):
            cursor = 0
        elif key in (curses.KEY_END, ord("G")):
            cursor = max_cursor
        else:
            return False
        setattr(self, cursor_attr, cursor)
        return True

    def _handle_list_overlay(self, key, cursor_attr: str, total: int,
                             on_select: Callable[[int], None],
                             number_attr: str) -> bool:
        """Close / navigate / digit-select / Enter handling shared by the
        cursor-based list overlay modes (buffer list, recent files, grep
        results). `on_select(index)` validates the index itself."""
        number = getattr(self, number_attr)
        if key in (27, ord("q")):
            self.mode = Mode.NORMAL
            number = ""
        elif self._list_overlay_nav(key, cursor_attr, total):
            number = ""
        elif key in (curses.KEY_BACKSPACE, 127, 8):
            number = number[:-1]
        elif isinstance(key, int) and ord("0") <= key <= ord("9"):
            number += chr(key)
            try:
                typed = int(number)
            except ValueError:
                typed = 0
            if 1 <= typed <= total:
                setattr(self, cursor_attr, typed - 1)
            self.message = ""
            self.message_is_error = False
        elif key in self._ENTER_KEYS:
            if number:
                try:
                    index = int(number) - 1
                except ValueError:
                    index = -1
            else:
                index = max(0, min(getattr(self, cursor_attr), total - 1))
            number = ""
            setattr(self, number_attr, number)
            on_select(index)
        setattr(self, number_attr, number)
        self._force_redraw = True
        return True

    def _handle_help(self, key: int) -> bool:
        if key in (ord("\t"),):
            self._overlay_pending_g = False
            self._jump_help_section(True)
            return True
        if key == curses.KEY_BTAB:
            self._overlay_pending_g = False
            self._jump_help_section(False)
            return True
        if key in (ord("/"), ord("?")):
            self._overlay_pending_g = False
            self._start_cmd_buf(chr(key), ("help_search", chr(key) == "/"))
            self._force_redraw = True
            return True
        if key in (ord("n"), ord("N")):
            self._overlay_pending_g = False
            direction = self.help_search_forward
            try:
                self._search_help(self.help_search_pattern,
                                  direction if key == ord("n") else not direction)
            finally:
                self.help_search_forward = direction
            return True
        return self._handle_scroll_overlay(
            key, "help_top_line", len(self.HELP_LINES), (27, curses.KEY_F1, ord("q"))
        )

    def _buffer_hex_bytes(self) -> bytes:
        if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
            # A still-mapped store is by definition unmodified, so the on-disk
            # image is the buffer image — skip decoding and re-encoding every
            # line of a large file.
            raw = self.lines.raw_bytes()
            if raw is not None:
                return raw
        return "".join(
            str(line) + self._line_ending_for_row(idx)
            for idx, line in enumerate(self.lines)
        ).encode("utf-8", errors="replace")

    def _hex_source_size(self) -> int:
        """Cheap upper-bound size probe that never copies file content,
        so it can gate _buffer_hex_bytes()'s full materialization."""
        if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
            return self.lines.byte_size()
        # Must count encoded bytes, not characters: multi-byte UTF-8 content
        # (CJK, emoji, ...) can be up to 4x more bytes than characters, and
        # _buffer_hex_bytes() below encodes to UTF-8. A char-based count
        # would let content past HEX_VIEW_MAX_BYTES slip through the gate.
        return sum(
            len(str(line).encode("utf-8", errors="replace"))
            + len(self._line_ending_for_row(idx).encode("utf-8", errors="replace"))
            for idx, line in enumerate(self.lines)
        )

    @staticmethod
    def _format_hex_line(offset: int, chunk: bytes) -> str:
        if not chunk:
            return "00000000                                                  |                |"
        hex_pairs = [f"{byte:02x}" for byte in chunk]
        left = " ".join(hex_pairs[:8])
        right = " ".join(hex_pairs[8:])
        hex_part = f"{left:<23}  {right:<23}"
        ascii_part = "".join(chr(byte) if 32 <= byte <= 126 else "." for byte in chunk)
        return f"{offset:08x}  {hex_part}  |{ascii_part:<16}|"

    def _hex_view_lines(self, data: Optional[bytes] = None) -> List[str]:
        if data is None:
            data = self._buffer_hex_bytes()
        if not data:
            return [self._format_hex_line(0, b"")]
        return [
            self._format_hex_line(offset, data[offset:offset + 16])
            for offset in range(0, len(data), 16)
        ]

    def _open_hex_view(self):
        # Gate on a cheap size probe before materializing anything: both
        # _buffer_hex_bytes() paths (mmap full-slice copy, or re-encoding
        # every line) copy the ENTIRE file/buffer into one bytes object,
        # which defeats the whole point of MMapLineStore for the large
        # files this view is most likely to be used on (binaries surfaced
        # via the file browser's "View" action) and can exhaust memory.
        size = self._hex_source_size()
        if size > self.HEX_VIEW_MAX_BYTES:
            self._set_error(
                f"File too large to view as hex ({size} bytes, "
                f"limit {self.HEX_VIEW_MAX_BYTES})"
            )
            return
        try:
            data = self._buffer_hex_bytes()
        except MemoryError:
            self._set_error("File too large to view as hex")
            return
        # Only switch mode and update the cached snapshot once the data is
        # in hand -- flipping mode first would leave HEX mode active with
        # a stale (or never-populated) cache if materialization above
        # failed.
        self._open_hex_view_for_bytes(data)

    def _open_hex_view_for_bytes(self, data: bytes):
        """Enter HEX mode over a precomputed byte image, bypassing any
        text-buffer decode/encode round trip. Used for exact-bytes sources
        (e.g. a file read straight off disk) where re-deriving the bytes
        from a decoded buffer -- as _open_hex_view()'s default path does --
        would be lossy for non-UTF-8 content."""
        self.mode = Mode.HEX
        self.hex_top_line = 0
        self.hex_cursor_line = 0
        # HEX mode is read-only and has no buffer-switch path, so the byte
        # image can't change while the view is open — capture it once here.
        # Rows are formatted lazily by _draw_hex so opening a large file
        # doesn't build one string per 16 bytes up front.
        self._hex_cached_data = data
        self._hex_cached_data_len = len(data)
        self._hex_line_count = max(1, (len(data) + 15) // 16)
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _draw_hex(self, stdscr, height: int, width: int):
        data = self._hex_cached_data
        total = self._hex_line_count
        text_rows = max(1, height - 2)
        # Keeps hex_cursor_line visible (scrolling hex_top_line as needed),
        # the same way the other cursor-based overlays (buffer list, grep
        # results) track their current row.
        self._clamp_list_view("hex_cursor_line", "hex_top_line", total, text_rows)

        def draw_row(scr, srow, idx):
            offset = idx * 16
            attr = curses.A_REVERSE if idx == self.hex_cursor_line else curses.A_NORMAL
            self._add_curses_text(
                scr, srow, 0, self._format_hex_line(offset, data[offset:offset + 16]), attr)

        fname = self.filename or "[No Name]"
        # Place the real terminal cursor on the current row too, like the
        # editor's own cursor does while scrolling, instead of leaving it
        # wherever the last draw call happened to land it.
        cursor_row = max(0, min(self.hex_cursor_line - self.hex_top_line, text_rows - 1))
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=f" HEX     {fname}",
            status_right=f" {self._hex_cached_data_len} bytes  {self.hex_top_line + 1}-{min(total, self.hex_top_line + text_rows)}/{total} ",
            total=total, top_line=self.hex_top_line,
            draw_row=draw_row, filler=True,
            bottom=lambda win: self._draw_overlay_bottom(
                win, width,
                "ESC/q close, j/k move, PgUp/PgDn page, Home/End top/bottom"),
            cursor=(cursor_row, 0),
        )

    def _handle_hex(self, key: int) -> bool:
        if key in (27, ord("q")):
            self.mode = Mode.NORMAL
            self._count_str = ""
            self._pending_op = ""
            self._overlay_pending_g = False
            self._hex_cached_data = b""   # release the byte image on close
            self._force_redraw = True
            return True

        total = self._hex_line_count
        max_cursor = max(0, total - 1)
        cursor = self.hex_cursor_line
        text_rows = max(1, self._last_h - 2)

        if self._overlay_pending_g:
            self._overlay_pending_g = False
            if key == ord("g"):
                cursor = 0
        elif key in (ord("j"), curses.KEY_DOWN):
            cursor = min(max_cursor, cursor + 1)
        elif key in (ord("k"), curses.KEY_UP):
            cursor = max(0, cursor - 1)
        elif key in (6, curses.KEY_NPAGE):
            cursor = min(max_cursor, cursor + text_rows)
        elif key in (2, curses.KEY_PPAGE):
            cursor = max(0, cursor - text_rows)
        elif key == 4:
            cursor = min(max_cursor, cursor + max(1, text_rows // 2))
        elif key == 21:
            cursor = max(0, cursor - max(1, text_rows // 2))
        elif key == curses.KEY_HOME:
            cursor = 0
        elif key == curses.KEY_END:
            cursor = max_cursor
        elif key == ord("g"):
            self._overlay_pending_g = True
        elif key == ord("G"):
            cursor = max_cursor

        self.hex_cursor_line = cursor
        self._force_redraw = True
        return True

    def _line_ending_for_row(self, row: int) -> str:
        if isinstance(self.lines, MMapLineStore) and self.lines.is_mapped:
            ending = self.lines.line_ending_at(row)
            if ending is not None:
                return ending
        if len(self.line_endings) == len(self.lines) and row < len(self.line_endings):
            return self.line_endings[row]
        if row < len(self.lines) - 1:
            return self.default_line_ending
        return ""

    @staticmethod
    def _line_ending_marker(ending: str) -> str:
        if ending == "\r\n":
            return "[CRLF]"
        if ending == "\r":
            return "[CR]"
        if ending == "\n":
            return "[NL]"
        return "[NONE]"

    def _line_endings_view_line(self, idx: int) -> str:
        if idx >= len(self.lines):
            return "[NONE]"
        return f"{self.lines[idx]}{self._line_ending_marker(self._line_ending_for_row(idx))}"

    def _line_endings_view_lines(self) -> List[str]:
        return [
            self._line_endings_view_line(idx) for idx in range(len(self.lines))
        ] or ["[NONE]"]

    def _open_line_endings_view(self):
        self.mode = Mode.LINE_ENDINGS
        self.line_endings_top_line = 0
        # LINE_ENDINGS mode is read-only and has no buffer-switch path, so
        # the rendered lines can't change while the view is open. Rows are
        # formatted lazily by _draw_line_endings; only the count is fixed here.
        self._line_endings_line_count = max(1, len(self.lines))
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _draw_line_endings(self, stdscr, height: int, width: int):
        total = self._line_endings_line_count
        text_rows = max(1, height - 2)
        self.line_endings_top_line = max(
            0, min(self.line_endings_top_line, max(0, total - text_rows)))

        fname = self.filename or "[No Name]"
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=f" LE      {fname}",
            status_right=f" {self.line_endings_top_line + 1}-{min(total, self.line_endings_top_line + text_rows)}/{total} ",
            total=total, top_line=self.line_endings_top_line,
            draw_row=lambda scr, srow, idx: self._add_curses_text(
                scr, srow, 0, self._line_endings_view_line(idx)),
            filler=True,
            bottom=lambda win: self._draw_overlay_bottom(
                win, width,
                r"ESC/q close; [CR]=\r [NL]=\n [CRLF]=\r\n [NONE]=no final ending"),
        )

    def _handle_line_endings(self, key: int) -> bool:
        return self._handle_scroll_overlay(
            key, "line_endings_top_line", self._line_endings_line_count, (27, ord("q"))
        )

    def _handle_shell(self, key: int) -> bool:
        return self._handle_scroll_overlay(
            key, "shell_top_line", len(self.shell_lines), (27, ord("q"))
        )

    def _start_cmd_buf(self, prefix: str, context: Optional[Tuple[str, object]] = None):
        self._cmd_buf = prefix
        self._cmd_cursor = len(prefix)
        self._cmd_context = context
        self._cmd_history_index = None
        self._cmd_history_draft = prefix
        self._clear_filename_completion()

    def _clear_cmd_buf(self):
        self._cmd_buf = ""
        self._cmd_cursor = 0
        self._cmd_context = None
        self._cmd_history_index = None
        self._cmd_history_draft = ""
        self._clear_filename_completion()

    def _cmd_history_key(self) -> Optional[str]:
        if self._cmd_buf and self._cmd_buf[0] in self._cmd_history:
            return self._cmd_buf[0]
        return None

    def _record_cmd_history(self, buf: str):
        if len(buf) <= 1:
            return
        key = buf[0] if buf[0] in self._cmd_history else None
        if key is None:
            return
        history = self._cmd_history[key]
        if not history or history[-1] != buf:
            history.append(buf)
            if len(history) > self._cmd_history_max:
                del history[:-self._cmd_history_max]
        self._cmd_history_index = None
        self._cmd_history_draft = ""

    def _recall_cmd_history(self, delta: int) -> bool:
        key = self._cmd_history_key()
        if key is None:
            return False
        history = self._cmd_history[key]
        if not history:
            return False

        if self._cmd_history_index is None:
            self._cmd_history_draft = self._cmd_buf
            index = len(history)
        else:
            index = self._cmd_history_index

        index += delta
        if index < 0:
            index = 0
        if index >= len(history):
            self._cmd_history_index = None
            self._cmd_buf = self._cmd_history_draft or key
        else:
            self._cmd_history_index = index
            self._cmd_buf = history[index]
        self._cmd_cursor = len(self._cmd_buf)
        self.message = ""
        self.message_is_error = False
        return True

    def _draw_buffer_list(self, stdscr, height: int, width: int):
        # Modified flags are verified once, when the list is opened (see
        # _show_buffers) and again after 'x'/'w' act on a buffer -- not on
        # every redraw, since navigating alone can't change any buffer's
        # content.
        lines = self._buffer_list_lines()
        text_rows = max(1, height - 2)
        self._clamp_list_view("buffer_list_cursor", "buffer_list_top_line",
                              len(lines), text_rows)

        def draw_row(scr, srow, idx):
            attr = curses.A_REVERSE if idx == self.buffer_list_cursor else curses.A_NORMAL
            self._add_curses_text(scr, srow, 0, lines[idx], attr)

        typed = f" number:{self.buffer_list_number}" if self.buffer_list_number else ""
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=" BUFFERS :ls",
            status_right=f" {self.buffer_list_cursor + 1 if lines else 0}/{len(lines)}{typed} ",
            total=len(lines), top_line=self.buffer_list_top_line,
            draw_row=draw_row,
            bottom=lambda win: self._draw_overlay_bottom(
                win, width,
                self.message or "Enter selects, u/d move up/down, x deletes (:bd), w saves (:w), digits then Enter select by number, q/ESC close, j/k and PgUp/PgDn navigate",
                self.message_is_error),
        )

    def _select_buffer_from_list(self, index: int):
        self.buffer_list_number = ""
        if not 0 <= index < len(self.buffers):
            self._set_error("No such buffer")
            return
        self.buffer_list_cursor = index
        self._switch_buffer(index)

    def _make_buffer_current(self, index: int) -> bool:
        """Switch the live editor state to buffers[index] if it isn't already
        current. Returns False (with an error message set) for a bad index."""
        if not 0 <= index < len(self.buffers):
            self._set_error("No such buffer")
            return False
        if index != self.current_buffer:
            self._sync_current_buffer()
            self._load_buffer_state(index)
        return True

    def _run_buffer_list_ex_command(self, cmd: str) -> None:
        """Run an ex command triggered from the buffer list with the same
        crash-isolation guarantee _handle_cmd_buf gives a typed command: a
        bug in the command must show up as an error message, not take down
        the whole session just because it was invoked from this overlay
        instead of the : command line."""
        try:
            self._execute_cmd(cmd)
        except Exception as exc:
            self._set_error(f"Command failed: {exc}")

    def _delete_buffer_from_list(self, index: int):
        """'x' in the buffer list -- delete the highlighted buffer via the
        normal :bd ex-command path (same unsaved-changes guard and message),
        then stay in the list instead of dropping to Mode.NORMAL."""
        self.buffer_list_number = ""
        if not self._make_buffer_current(index):
            return
        self._run_buffer_list_ex_command(":bd")
        self.mode = Mode.BUFFER_LIST
        self._refresh_all_buffer_modified_flags()
        self.buffer_list_cursor = min(self.current_buffer, len(self.buffers) - 1)
        self._force_redraw = True

    def _save_buffer_from_list(self, index: int):
        """'w' in the buffer list -- save the highlighted buffer via the
        normal :w ex-command path, then stay in the list."""
        self.buffer_list_number = ""
        if not self._make_buffer_current(index):
            return
        self._run_buffer_list_ex_command(":w")
        self.mode = Mode.BUFFER_LIST
        self._refresh_all_buffer_modified_flags()
        self.buffer_list_cursor = self.current_buffer
        self._force_redraw = True

    def _move_buffer_in_list(self, index: int, delta: int):
        """'u'/'d' in the buffer list -- swap the highlighted buffer with its
        neighbour above (delta=-1) or below (delta=+1), keeping it
        highlighted and keeping current_buffer pointing at the same buffer."""
        self.buffer_list_number = ""
        target = index + delta
        if not (0 <= index < len(self.buffers) and 0 <= target < len(self.buffers)):
            return
        self._sync_current_buffer()
        bufs = self.buffers
        bufs[index], bufs[target] = bufs[target], bufs[index]
        if self.current_buffer == index:
            self.current_buffer = target
        elif self.current_buffer == target:
            self.current_buffer = index
        self.buffer_list_cursor = target
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True

    def _handle_buffer_list(self, key: int) -> bool:
        if key in (ord("u"), ord("d")):
            self._move_buffer_in_list(
                self.buffer_list_cursor, -1 if key == ord("u") else 1
            )
            return True
        if key == ord("x"):
            self._delete_buffer_from_list(
                max(0, min(self.buffer_list_cursor, len(self.buffers) - 1))
            )
            return True
        if key == ord("w"):
            self._save_buffer_from_list(
                max(0, min(self.buffer_list_cursor, len(self.buffers) - 1))
            )
            return True
        return self._handle_list_overlay(
            key, "buffer_list_cursor", len(self.buffers),
            self._select_buffer_from_list, "buffer_list_number",
        )

    def _draw_recent_files(self, stdscr, height: int, width: int):
        paths = self.recent_files_list
        text_rows = max(1, height - 2)
        self._clamp_list_view("recent_files_cursor", "recent_files_top_line",
                              len(paths), text_rows)

        def draw_row(scr, srow, idx):
            attr = curses.A_REVERSE if idx == self.recent_files_cursor else curses.A_NORMAL
            self._add_curses_text(scr, srow, 0, f" {idx + 1:2d}  {paths[idx]}", attr)

        typed = f" number:{self.recent_files_number}" if self.recent_files_number else ""
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=" RECENT FILES :rct",
            status_right=f" {self.recent_files_cursor + 1 if paths else 0}/{len(paths)}{typed} ",
            total=len(paths), top_line=self.recent_files_top_line,
            draw_row=draw_row,
            bottom=lambda win: self._draw_overlay_bottom(
                win, width,
                self.message or "Enter opens in new buffer, digit(s)+Enter select by number, q/ESC close, j/k navigate",
                self.message_is_error),
        )

    def _open_recent_file(self, index: int):
        paths = self.recent_files_list
        self.recent_files_number = ""
        if not 0 <= index < len(paths):
            self._set_error("No such recent file")
            return
        path = paths[index]
        for i, b in enumerate(self.buffers):
            if b.filename and os.path.abspath(b.filename) == path:
                self.mode = Mode.NORMAL
                self._switch_buffer(i)
                self._force_redraw = True
                return
        self._open_file_from_path(path)

    def _handle_recent_files(self, key: int) -> bool:
        return self._handle_list_overlay(
            key, "recent_files_cursor", len(self.recent_files_list),
            self._open_recent_file, "recent_files_number",
        )

    def _open_file_browser(self):
        self._sync_current_buffer()
        self.mode = Mode.FILE_BROWSER
        self.file_browser.grep_prompt = False
        self.file_browser.grep_field = "pattern"
        self.file_browser.grep_pattern = ""
        self.file_browser.grep_text = ""
        self.file_browser.grep_cursor = 0
        self._fb_cancel_prompt()
        self._clear_cmd_buf()
        self._count_str = ""
        self._pending_op = ""
        self.active_register = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True
        for panel in (self.file_browser.left, self.file_browser.right):
            self._invalidate_fb_entries(panel)
            if not os.path.isdir(panel.cwd):
                panel.cwd = os.getcwd()
                panel.cursor = 0
                panel.top_line = 0
            self._clamp_fb_panel(panel)

    def _fb_panels(self) -> Tuple[FileBrowserPanel, FileBrowserPanel]:
        return self.file_browser.left, self.file_browser.right

    def _active_fb_panel(self) -> FileBrowserPanel:
        return self._fb_panels()[self.file_browser.active_panel]

    def _fb_entries_cache_key(self, panel: FileBrowserPanel) -> Tuple[object, ...]:
        try:
            st = os.stat(panel.cwd)
            dir_sig = (st.st_ino, st.st_size, st.st_mtime_ns)
        except OSError:
            dir_sig = None
        return (
            os.path.abspath(panel.cwd),
            panel.show_hidden,
            panel.sort_mode,
            panel.reverse_sort,
            dir_sig,
        )

    @staticmethod
    def _invalidate_fb_entries(panel: FileBrowserPanel):
        panel.entries_cache_key = None
        panel.entries_cache = []

    def _fb_entries(self, panel: FileBrowserPanel) -> List[FileBrowserEntry]:
        cache_key = self._fb_entries_cache_key(panel)
        if panel.entries_cache_key == cache_key:
            return panel.entries_cache

        parent_path = os.path.dirname(panel.cwd) or panel.cwd
        try:
            parent_mtime = os.stat(parent_path).st_mtime
        except OSError:
            parent_mtime = 0.0
        entries = [FileBrowserEntry("..", parent_path, True, 0, parent_mtime)]
        try:
            with os.scandir(panel.cwd) as it:
                for entry in it:
                    name = entry.name
                    if not panel.show_hidden and name.startswith("."):
                        continue
                    try:
                        is_dir = entry.is_dir()
                    except OSError:
                        is_dir = False
                    try:
                        stat = entry.stat(follow_symlinks=False)
                        size = stat.st_size
                        mtime = stat.st_mtime
                    except OSError:
                        size = 0
                        mtime = 0.0
                    entries.append(FileBrowserEntry(name, entry.path, is_dir, size, mtime))
        except OSError as exc:
            self._set_error(str(exc))

        def sort_key(item: FileBrowserEntry):
            if item.name == "..":
                return (0, "", 0)
            dir_rank = 1 if item.is_dir else 2
            if panel.sort_mode == "ext":
                value = os.path.splitext(item.name.lower())[1]
            elif panel.sort_mode == "size":
                value = item.size
            else:
                value = item.name.lower()
            return (dir_rank, value, item.name.lower())

        parent = entries[:1]
        non_parent = entries[1:]
        dirs  = [e for e in non_parent if e.is_dir]
        files = [e for e in non_parent if not e.is_dir]
        sorted_dirs  = sorted(dirs,  key=sort_key, reverse=panel.reverse_sort)
        sorted_files = sorted(files, key=sort_key, reverse=panel.reverse_sort)
        panel.entries_cache_key = cache_key
        panel.entries_cache = parent + sorted_dirs + sorted_files
        return panel.entries_cache

    def _clamp_fb_panel(self, panel: FileBrowserPanel):
        entries = self._fb_entries(panel)
        panel.cursor = max(0, min(panel.cursor, len(entries) - 1))
        panel.top_line = max(0, min(panel.top_line, max(0, len(entries) - 1)))

    def _fb_selected_entry(self) -> Optional[FileBrowserEntry]:
        panel = self._active_fb_panel()
        entries = self._fb_entries(panel)
        if not entries:
            return None
        panel.cursor = max(0, min(panel.cursor, len(entries) - 1))
        return entries[panel.cursor]

    @staticmethod
    def _fb_visible_entry_rows(height: int) -> int:
        return max(1, height - 3)

    @staticmethod
    def _fb_function_key_bar(width: int) -> str:
        full = ("F1Help  F2Grep  F3View  F4Edit  F5Copy  F6Move  "
                "F7Mkdir  F8Del  F9Sort  F10Quit")
        if width - 1 >= len(full):
            return full
        compact = ("1Help 2Grep 3View 4Edit 5Copy 6Move "
                   "7Mkdir 8Del 9Sort 10Quit")
        if width - 1 >= len(compact):
            return compact
        terse = "1H 2G 3V 4E 5Cp 6Mv 7Mk 8Rm 9Srt 10Q"
        return terse[:max(0, width - 1)]

    def _fb_ensure_cursor_visible(self, panel: FileBrowserPanel, height: int):
        entries = self._fb_entries(panel)
        visible_rows = self._fb_visible_entry_rows(height)
        max_top = max(0, len(entries) - visible_rows)
        panel.cursor = max(0, min(panel.cursor, len(entries) - 1))
        panel.top_line = max(0, min(panel.top_line, max_top))
        vjump = min(visible_rows, max(1, self.vertical_scroll_jump))
        if panel.cursor < panel.top_line:
            panel.top_line = max(0, panel.cursor - vjump + 1)
        elif panel.cursor >= panel.top_line + visible_rows:
            panel.top_line = max(0, panel.cursor - visible_rows + vjump)
        panel.top_line = max(0, min(panel.top_line, max_top))

    @staticmethod
    def _fb_format_size(size: int) -> str:
        if size < 1024:
            return str(size)
        units = ("K", "M", "G", "T", "P")
        value = float(size)
        unit_idx = -1
        while value >= 1024.0 and unit_idx < len(units) - 1:
            value /= 1024.0
            unit_idx += 1
        while unit_idx < len(units) - 1:
            rounded = round(value, 1 if value < 10 else 0)
            if rounded < 1024.0:
                break
            value /= 1024.0
            unit_idx += 1
        rounded = round(value, 1 if value < 10 else 0)
        if rounded >= 10 or float(rounded).is_integer():
            return f"{rounded:.0f}{units[unit_idx]}"
        return f"{rounded:.1f}{units[unit_idx]}"

    @staticmethod
    def _fb_format_mtime(timestamp: float) -> str:
        if timestamp <= 0:
            return "---- -- -- --:--"
        try:
            return datetime.fromtimestamp(timestamp).strftime("%Y-%m-%d %H:%M")
        except (OverflowError, OSError, ValueError):
            return "---- -- -- --:--"

    def _fb_entry_line(self, panel: FileBrowserPanel, entry: FileBrowserEntry, width: int) -> str:
        suffix = "/" if entry.is_dir and entry.name != ".." else ""
        mark = "*" if entry.path in panel.selected else " "
        name = f"{mark}{entry.name}{suffix}"
        size = "<DIR>" if entry.is_dir else self._fb_format_size(entry.size)
        mtime = self._fb_format_mtime(entry.mtime)
        if width > 34:
            meta = f"{mtime} {size:>6}"
            name_w = max(1, width - len(meta) - 1)
            name_text = self._display_ljust(name, name_w)
            return name_text + " " + meta
        if width > 18:
            name_w = max(1, width - 9)
            name_text = self._display_ljust(name, name_w)
            return name_text + size[-8:].rjust(8) + " "
        return self._display_slice(name, 0, max_width=max(0, width - 1))

    def _draw_file_browser(self, stdscr, height: int, width: int):
        status_win, bottom_win = self._bar_windows(stdscr, height, width)
        visible_rows = self._fb_visible_entry_rows(height)
        left, right = self._fb_panels()
        panel_w = max(10, width // 2)
        widths = [panel_w, max(10, width - panel_w)]

        try:
            stdscr.move(0, 0)
            stdscr.clrtoeol()
        except curses.error:
            pass
        for panel_idx, panel in enumerate((left, right)):
            entries = self._fb_entries(panel)
            self._fb_ensure_cursor_visible(panel, height)
            x0 = 0 if panel_idx == 0 else widths[0]
            w = widths[panel_idx]
            header = f" {panel.cwd} "
            if panel_idx == self.file_browser.active_panel:
                header = "[" + self._display_ljust(header, max(0, w - 2)) + "]"
            else:
                header = " " + self._display_ljust(header, max(0, w - 2)) + " "
            try:
                self._add_curses_text(stdscr, 0, x0, self._display_ljust(header, w), curses.A_REVERSE)
            except curses.error:
                pass

            for srow in range(1, visible_rows + 1):
                idx = panel.top_line + srow - 1
                try:
                    stdscr.move(srow, x0)
                    stdscr.clrtoeol()
                    if idx < len(entries):
                        entry = entries[idx]
                        line = self._fb_entry_line(panel, entry, w)
                        attr = curses.A_REVERSE if panel_idx == self.file_browser.active_panel and idx == panel.cursor else curses.A_BOLD if entry.is_dir else curses.A_NORMAL
                        self._add_curses_text(stdscr, srow, x0, self._display_ljust(line, w), attr)
                except curses.error:
                    pass

        active = self._active_fb_panel()
        selected = self._fb_selected_entry()
        selected_name = selected.name if selected else ""
        left_s = f" FB      {active.cwd}"
        right_s = f" {selected_name}  sort:{active.sort_mode}{' rev' if active.reverse_sort else ''} "
        status = self._format_status(left_s, right_s, width)
        _fb_prompt_cursor_col: Optional[int] = None
        try:
            self._draw_status_line(status_win, 0, status)
            bottom_win.move(0, 0)
            if self.file_browser.op_prompt:
                s = self.file_browser
                if s.op_kind.startswith("confirm:"):
                    self._draw_bottom_status_line(bottom_win, 0, width)
                    self._draw_bottom_status_text(
                        bottom_win, 0, 0, s.op_label[:max(0, width - 1)]
                    )
                else:
                    label = s.op_label
                    _fb_prompt_cursor_col = self._draw_prompt_line(
                        bottom_win, label + s.op_text, len(label) + s.op_cursor, width
                    )
            elif self.file_browser.grep_prompt:
                label = "grep pattern: " if self.file_browser.grep_field == "pattern" else "file mask [*]: "
                _fb_prompt_cursor_col = self._draw_prompt_line(
                    bottom_win,
                    label + self.file_browser.grep_text,
                    len(label) + self.file_browser.grep_cursor,
                    width,
                )
            else:
                self._draw_bottom_status_line(bottom_win, 0, width)
                if self.message:
                    self._draw_bottom_status_text(
                        bottom_win, 0, 0, self.message, self.message_is_error
                    )
                else:
                    hint = self._fb_function_key_bar(width)
                    self._draw_bottom_status_text(bottom_win, 0, 0, hint)
        except curses.error:
            pass
        self._noutrefresh_all(stdscr, status_win, bottom_win)
        try:
            if _fb_prompt_cursor_col is not None:
                curses.setsyx(height - 1, _fb_prompt_cursor_col)
        except (curses.error, AttributeError):
            pass
        curses.doupdate()
        self._force_redraw = False

    def _fb_move(self, delta: int):
        panel = self._active_fb_panel()
        entries = self._fb_entries(panel)
        panel.cursor = max(0, min(panel.cursor + delta, len(entries) - 1))
        self._fb_ensure_cursor_visible(panel, self._last_h or 24)
        self._force_redraw = True

    def _fb_enter_dir(self, path: str):
        panel = self._active_fb_panel()
        old = panel.cwd
        panel.cwd = os.path.abspath(path)
        panel.cursor = 0
        panel.top_line = 0
        self._invalidate_fb_entries(panel)
        if os.path.abspath(path) == os.path.dirname(old):
            base = os.path.basename(old)
            entries = self._fb_entries(panel)
            for i, entry in enumerate(entries):
                if entry.name == base:
                    panel.cursor = i
                    break
        self._force_redraw = True

    def _open_file_from_path(self, path: str, line_no: Optional[int] = None):
        saved_mode = self.mode
        if not self._append_buffer(path, switch=True):
            self.mode = saved_mode
            return
        if line_no is not None:
            self.cursor_row = max(0, min(line_no - 1, len(self.lines) - 1))
            self.cursor_col = self._first_nonblank(self.cursor_row)
            text_rows = max(1, (self._last_h or 24) - 2)
            self.top_line = max(0, self.cursor_row - text_rows // 2)
            self._sync_current_buffer()
        self.mode = Mode.NORMAL
        self._force_redraw = True

    def _open_marked_file_browser_entries(self, panel: FileBrowserPanel) -> bool:
        paths = sorted(
            path for path in panel.selected
            if os.path.isfile(path)
        )
        if not paths:
            return False
        saved_mode = self.mode
        first_opened = False
        opened = 0
        for path in paths:
            if self._append_buffer(path, switch=not first_opened):
                first_opened = True
                opened += 1
        panel.selected.clear()
        if opened:
            self.mode = Mode.NORMAL
            self.message = f"{opened} file{'s' if opened != 1 else ''} opened"
            self.message_is_error = False
            self._force_redraw = True
            return True
        self.mode = saved_mode
        return False

    # --- File-browser op prompts (copy / move / mkdir / delete confirms) ---

    def _fb_other_panel(self) -> FileBrowserPanel:
        return self._fb_panels()[1 - self.file_browser.active_panel]

    def _fb_op_targets(self, panel: FileBrowserPanel) -> List[str]:
        if panel.selected:
            paths = sorted(p for p in panel.selected if os.path.lexists(p))
            if paths:
                return paths
        entry = self._fb_selected_entry()
        if entry and entry.name != "..":
            return [entry.path]
        return []

    @staticmethod
    def _fb_short_name(path: str) -> str:
        return os.path.basename(path.rstrip(os.sep)) or path

    def _fb_targets_label(self, targets: List[str]) -> str:
        if len(targets) == 1:
            return f"'{self._fb_short_name(targets[0])}'"
        return f"{len(targets)} items"

    def _fb_start_text_prompt(self, kind: str, label: str, default: str = "",
                              payload: Optional[dict] = None):
        s = self.file_browser
        s.op_prompt = True
        s.op_kind = kind
        s.op_label = label
        s.op_text = default
        s.op_cursor = len(default)
        s.op_payload = payload or {}
        self._fb_clear_op_completion()
        self._force_redraw = True

    def _fb_start_confirm(self, kind: str, label: str,
                          payload: Optional[dict] = None):
        s = self.file_browser
        s.op_prompt = True
        s.op_kind = "confirm:" + kind
        s.op_label = label
        s.op_text = ""
        s.op_cursor = 0
        s.op_payload = payload or {}
        self._fb_clear_op_completion()
        self._force_redraw = True

    def _fb_cancel_prompt(self):
        s = self.file_browser
        s.op_prompt = False
        s.op_kind = ""
        s.op_label = ""
        s.op_text = ""
        s.op_cursor = 0
        s.op_payload = {}
        self._fb_clear_op_completion()
        self._force_redraw = True

    def _fb_clear_op_completion(self):
        s = self.file_browser
        s.op_completion_matches = []
        s.op_completion_index = 0

    def _fb_show_op_completion(self):
        matches = self.file_browser.op_completion_matches
        idx = self.file_browser.op_completion_index
        parts = []
        for i, m in enumerate(matches[:8]):
            parts.append(f"[{m}]" if i == idx else m)
        more = " ..." if len(matches) > 8 else ""
        self.message = "  ".join(parts) + more
        self.message_is_error = False

    def _fb_resolve_goto_target(self, text: str) -> str:
        """Anchor a bare/relative directory fragment typed into the
        goto-directory prompt to the active panel's cwd, not the process's
        -- the two commonly differ (that's exactly what 'c' / :cd exist to
        reconcile), and resolving against the wrong one would silently
        offer/enter directories the user never navigated to."""
        expanded = os.path.expanduser(text)
        if os.path.isabs(expanded):
            return expanded
        return os.path.join(self._active_fb_panel().cwd, expanded)

    def _fb_complete_goto_dir(self) -> bool:
        # Cycles through directory matches one Tab press at a time (like
        # _complete_set_opt): each press always inserts a concrete match
        # rather than a computed common prefix. Comparing against the match
        # at the cached index (not scanning the whole list with "in") keeps
        # repeated cycling O(1) per press instead of O(n) per press.
        s = self.file_browser
        end = s.op_cursor
        suffix = s.op_text[end:]

        if (s.op_completion_matches
                and s.op_text[:end] == s.op_completion_matches[s.op_completion_index]):
            s.op_completion_index = (s.op_completion_index + 1) % len(s.op_completion_matches)
            replacement = s.op_completion_matches[s.op_completion_index]
            s.op_text = replacement + suffix
            s.op_cursor = len(replacement)
            self._fb_show_op_completion()
            return True

        prefix = self._fb_resolve_goto_target(s.op_text[:end])
        try:
            matches = self._list_path_completions(prefix, dirs_only=True)
        except OSError as exc:
            self._fb_clear_op_completion()
            self._set_error(str(exc))
            return True

        if not matches:
            self._fb_clear_op_completion()
            self._set_error("No directory match")
            return True

        s.op_completion_matches = matches
        s.op_completion_index = 0
        replacement = matches[0]
        s.op_text = replacement + suffix
        s.op_cursor = len(replacement)
        self._fb_show_op_completion()
        return True

    def _fb_clear_marks_for(self, paths: List[str]):
        for panel in self._fb_panels():
            panel.selected.difference_update(paths)

    def _fb_after_op_refresh(self, focus_path: Optional[str] = None):
        for panel in self._fb_panels():
            self._invalidate_fb_entries(panel)
        if focus_path:
            panel = self._active_fb_panel()
            entries = self._fb_entries(panel)
            base = self._fb_short_name(focus_path)
            for i, entry in enumerate(entries):
                if entry.name == base:
                    panel.cursor = i
                    break
        for panel in self._fb_panels():
            self._clamp_fb_panel(panel)
        self._force_redraw = True

    # --- Action handlers (F-keys) ---

    @staticmethod
    def _fb_path_is_binary(path: str, sample: int = 1024) -> bool:
        try:
            with _open_regular_file(path) as fh:
                chunk = fh.read(sample)
        except OSError:
            return False
        return b"\x00" in chunk

    def _fb_action_help(self):
        self._open_help()

    def _fb_action_chdir(self):
        panel = self._active_fb_panel()
        try:
            os.chdir(panel.cwd)
        except OSError as exc:
            self._set_error(str(exc))
            return
        self.message = self._safe_getcwd(fallback=panel.cwd)
        self.message_is_error = False

    def _fb_action_grep(self):
        s = self.file_browser
        s.grep_prompt = True
        s.grep_field = "pattern"
        s.grep_pattern = ""
        s.grep_text = ""
        s.grep_cursor = 0
        self._force_redraw = True

    def _fb_action_view(self):
        entry = self._fb_selected_entry()
        if not entry:
            return
        if entry.is_dir:
            self._fb_enter_dir(entry.path)
            return
        if self._fb_path_is_binary(entry.path):
            # Check the on-disk size against the hex-view cap *before*
            # reading the file at all.
            try:
                size = os.path.getsize(entry.path)
            except OSError as exc:
                self._set_error(str(exc))
                return
            if size > self.HEX_VIEW_MAX_BYTES:
                self._set_error(
                    f"File too large to view as hex ({size} bytes, "
                    f"limit {self.HEX_VIEW_MAX_BYTES})"
                )
                return
            # Read the raw bytes directly rather than going through
            # _append_buffer()/_load_file(), which decode the file as UTF-8
            # text (errors="replace") before hex view re-encodes it -- for
            # binary content that isn't valid UTF-8 (the entire reason this
            # branch was taken), that round trip mangles the byte offsets
            # and values the hex view is supposed to be showing, with no
            # indication to the user that what's on screen doesn't match
            # what's on disk.
            try:
                with _open_regular_file(entry.path) as fh:
                    raw = fh.read()
            except OSError as exc:
                self._set_error(str(exc))
                return
            self._open_hex_view_for_bytes(raw)
            return
        self._open_file_from_path(entry.path)

    def _fb_action_edit(self):
        panel = self._active_fb_panel()
        if panel.selected:
            if self._open_marked_file_browser_entries(panel):
                return
            self._set_error("No files in selection (only directories marked)")
            return
        entry = self._fb_selected_entry()
        if not entry:
            return
        if entry.is_dir:
            self._fb_enter_dir(entry.path)
        else:
            self._open_file_from_path(entry.path)

    def _fb_resolve_dest(self, dest: str, base_cwd: str) -> Tuple[str, bool]:
        trailing = dest.endswith("/") or dest.endswith(os.sep)
        dest = os.path.expanduser(dest)
        if not os.path.isabs(dest):
            dest = os.path.join(base_cwd, dest)
        return os.path.normpath(dest), trailing

    @staticmethod
    def _fb_with_trailing_sep(path: str) -> str:
        return path if path.endswith(os.sep) else path + os.sep

    _FB_SORT_MODES = ["name", "ext", "size"]

    def _fb_cycle_sort_mode(self, panel: FileBrowserPanel):
        order = self._FB_SORT_MODES
        panel.sort_mode = order[(order.index(panel.sort_mode) + 1) % len(order)]
        panel.cursor = 0
        panel.top_line = 0
        self._invalidate_fb_entries(panel)

    def _fb_estimate_op_size(self, sources: List[str]) -> Tuple[int, int, bool]:
        """Cheap upper-bound probe of an operation's total byte count and
        item count, stopping as soon as either FB_LARGE_OP_WARN_* threshold
        is crossed -- this only needs to answer "is this big enough to warn
        about", not produce an exact total, so it must stay fast even when
        `sources` includes a huge directory tree."""
        total_bytes = 0
        total_count = 0
        for src in sources:
            if os.path.isdir(src) and not os.path.islink(src):
                for dirpath, _dirnames, filenames in os.walk(src):
                    for name in filenames:
                        total_count += 1
                        try:
                            total_bytes += os.lstat(os.path.join(dirpath, name)).st_size
                        except OSError:
                            pass
                        if (total_bytes >= self.FB_LARGE_OP_WARN_BYTES
                                or total_count >= self.FB_LARGE_OP_WARN_COUNT):
                            return total_bytes, total_count, True
            else:
                total_count += 1
                try:
                    total_bytes += os.lstat(src).st_size
                except OSError:
                    pass
                if (total_bytes >= self.FB_LARGE_OP_WARN_BYTES
                        or total_count >= self.FB_LARGE_OP_WARN_COUNT):
                    return total_bytes, total_count, True
        return total_bytes, total_count, False

    def _fb_large_op_suffix(self, total_bytes: int, total_count: int) -> str:
        return (f" ({total_count}+ files, {self._fb_format_size(total_bytes)}+) "
                f"-- this will block the editor until finished")

    def _fb_action_copy(self):
        panel = self._active_fb_panel()
        targets = self._fb_op_targets(panel)
        if not targets:
            self._set_error("Nothing to copy")
            return
        total_bytes, total_count, large = self._fb_estimate_op_size(targets)
        if large:
            self._fb_start_confirm(
                "large_copy",
                f"Copy {self._fb_targets_label(targets)}"
                f"{self._fb_large_op_suffix(total_bytes, total_count)}. Continue? [y/N] ",
                payload={"sources": targets, "src_cwd": panel.cwd},
            )
            return
        self._fb_start_copy_dest_prompt(targets, panel.cwd)

    def _fb_start_copy_dest_prompt(self, targets: List[str], src_cwd: str):
        other = self._fb_other_panel()
        default = self._fb_with_trailing_sep(other.cwd)
        self._fb_start_text_prompt(
            "copy_dest",
            f"Copy {self._fb_targets_label(targets)} to: ",
            default=default,
            payload={"sources": targets, "src_cwd": src_cwd},
        )

    def _fb_action_move(self):
        panel = self._active_fb_panel()
        targets = self._fb_op_targets(panel)
        if not targets:
            self._set_error("Nothing to move")
            return
        total_bytes, total_count, large = self._fb_estimate_op_size(targets)
        if large:
            self._fb_start_confirm(
                "large_move",
                f"Move/rename {self._fb_targets_label(targets)}"
                f"{self._fb_large_op_suffix(total_bytes, total_count)}. Continue? [y/N] ",
                payload={"sources": targets, "src_cwd": panel.cwd},
            )
            return
        self._fb_start_move_dest_prompt(targets, panel.cwd)

    def _fb_start_move_dest_prompt(self, targets: List[str], src_cwd: str):
        other = self._fb_other_panel()
        if len(targets) == 1:
            default = os.path.join(other.cwd, self._fb_short_name(targets[0]))
        else:
            default = self._fb_with_trailing_sep(other.cwd)
        self._fb_start_text_prompt(
            "move_dest",
            f"Move/rename {self._fb_targets_label(targets)} to: ",
            default=default,
            payload={"sources": targets, "src_cwd": src_cwd},
        )

    def _fb_action_mkdir(self):
        panel = self._active_fb_panel()
        self._fb_start_text_prompt(
            "mkdir_name",
            "Create directory: ",
            default="",
            payload={"cwd": panel.cwd},
        )

    def _fb_action_goto(self):
        panel = self._active_fb_panel()
        self._fb_start_text_prompt(
            "goto_dir",
            "Go to directory: ",
            default=self._fb_with_trailing_sep(panel.cwd),
        )

    def _fb_action_delete(self):
        panel = self._active_fb_panel()
        targets = self._fb_op_targets(panel)
        if not targets:
            self._set_error("Nothing to delete")
            return
        nonempty_dirs = 0
        for p in targets:
            if os.path.isdir(p) and not os.path.islink(p):
                try:
                    with os.scandir(p) as it:
                        if any(True for _ in it):
                            nonempty_dirs += 1
                except OSError:
                    # Can't verify emptiness (e.g. permission denied) --
                    # assume the worse case so the stronger recursive-delete
                    # confirmation is shown rather than a misleadingly
                    # reassuring plain-delete prompt.
                    nonempty_dirs += 1
        if len(targets) == 1:
            name = self._fb_short_name(targets[0])
            if nonempty_dirs:
                label = f"Recursively delete non-empty directory '{name}'?"
                kind = "delete_recursive"
            elif os.path.isdir(targets[0]) and not os.path.islink(targets[0]):
                label = f"Delete directory '{name}'?"
                kind = "delete"
            else:
                label = f"Delete '{name}'?"
                kind = "delete"
        else:
            if nonempty_dirs:
                label = (f"Delete {len(targets)} items "
                         f"({nonempty_dirs} non-empty dir{'s' if nonempty_dirs != 1 else ''})"
                         f", recurse?")
                kind = "delete_recursive"
            else:
                label = f"Delete {len(targets)} items?"
                kind = "delete"
        total_bytes, total_count, large = self._fb_estimate_op_size(targets)
        if large:
            label += self._fb_large_op_suffix(total_bytes, total_count) + "."
        self._fb_start_confirm(kind, label + " [y/N] ", payload={"sources": targets})

    # --- Operation execution after prompts ---

    def _fb_finish_dest_prompt(self, perform):
        """Shared by copy_dest/move_dest: both prompts collect the same
        (sources, src_cwd) payload and a typed destination, then hand off
        to a perform_fn(sources, dest, into_dir=...) with the same
        signature -- only that final call differs between copy and move."""
        s = self.file_browser
        dest_text = s.op_text.strip()
        sources: List[str] = list(s.op_payload.get("sources", []))
        src_cwd = s.op_payload.get("src_cwd")
        if src_cwd is None:
            src_cwd = self._safe_getcwd(fallback=".")
        self._fb_cancel_prompt()
        if not dest_text or not sources:
            return
        dest, into_dir = self._fb_resolve_dest(dest_text, src_cwd)
        perform(sources, dest, into_dir=into_dir)

    def _fb_finish_copy_prompt(self):
        self._fb_finish_dest_prompt(self._fb_perform_copy)

    def _fb_finish_move_prompt(self):
        self._fb_finish_dest_prompt(self._fb_perform_move)

    def _fb_finish_mkdir_prompt(self):
        s = self.file_browser
        name = s.op_text.strip()
        cwd = s.op_payload.get("cwd")
        if cwd is None:
            cwd = self._safe_getcwd(fallback=".")
        self._fb_cancel_prompt()
        if not name:
            return
        path, _ = self._fb_resolve_dest(name, cwd)
        try:
            os.makedirs(path, exist_ok=False)
        except FileExistsError:
            self._set_error(f"Already exists: {path}")
            return
        except OSError as exc:
            self._set_error(f"mkdir failed: {exc}")
            return
        self._fb_after_op_refresh(focus_path=path)
        self.message = f"Created {path}"
        self.message_is_error = False

    def _fb_finish_goto_prompt(self):
        s = self.file_browser
        text = s.op_text.strip()
        self._fb_cancel_prompt()
        if not text:
            return
        target = self._fb_resolve_goto_target(text)
        if not self._validate_is_directory(target, text):
            return
        self._fb_enter_dir(target)

    def _fb_check_buffer_conflicts(self, pairs: List[Tuple[str, str]],
                                   op_is_move: bool) -> Optional[str]:
        for src, tgt in pairs:
            tgt_idx = self._find_buffer_by_filename(tgt)
            if tgt_idx is None:
                tgt_idx = self._find_buffer_under_path(tgt)
                if tgt_idx is None:
                    continue
            src_idx = self._find_buffer_by_filename(src) if op_is_move else None
            if src_idx is None and op_is_move:
                src_idx = self._find_buffer_under_path(src)
            if src_idx is not None and src_idx == tgt_idx:
                continue
            label = self.buffers[tgt_idx].filename or "[No Name]"
            return (f"Cannot overwrite '{label}': open in buffer "
                    f"{tgt_idx + 1}/{len(self.buffers)} (close with :bd first)")
        return None

    @classmethod
    def _path_is_within(cls, path: Optional[str], parent: Optional[str]) -> bool:
        full_path = cls._normalize_path(path)
        full_parent = cls._normalize_path(parent)
        if not full_path or not full_parent:
            return False
        try:
            return os.path.commonpath([full_path, full_parent]) == full_parent
        except ValueError:
            return False

    @classmethod
    def _path_is_descendant(cls, path: Optional[str], parent: Optional[str]) -> bool:
        full_path = cls._normalize_path(path)
        full_parent = cls._normalize_path(parent)
        if not full_path or not full_parent or full_path == full_parent:
            return False
        try:
            return os.path.commonpath([full_path, full_parent]) == full_parent
        except ValueError:
            return False

    @classmethod
    def _physical_path_is_within(cls, path: Optional[str], parent: Optional[str]) -> bool:
        path, parent = cls._normalize_path(path), cls._normalize_path(parent)
        if not path or not parent:
            return False
        path, parent = os.path.realpath(path), os.path.realpath(parent)
        return os.path.commonpath([path, parent]) == parent

    def _find_buffer_under_path(self, path: Optional[str]) -> Optional[int]:
        full_path = self._normalize_path(path)
        if not full_path or not os.path.isdir(full_path):
            return None
        for i, b in enumerate(self.buffers):
            # Removing a symlink only removes the alias, not its referent.
            # Buffers opened via that alias still need protection.
            if (self._path_is_within(b.filename, full_path)
                    or (not os.path.islink(full_path)
                        and self._physical_path_is_within(b.filename, full_path))):
                return i
        return None

    def _fb_pair_paths(self, sources: List[str], dest: str,
                       into_dir: bool = False) -> Tuple[List[Tuple[str, str]], Optional[str]]:
        multi = len(sources) > 1
        is_existing_dir = os.path.isdir(dest) and not os.path.islink(dest)
        if multi and not is_existing_dir:
            return [], f"Destination must be an existing directory: {dest}"
        for parent in sources:
            if not (os.path.isdir(parent) and not os.path.islink(parent)):
                continue
            for child in sources:
                if child != parent and self._physical_path_is_within(child, parent):
                    return [], f"Cannot operate on nested selection: '{child}' is inside '{parent}'"
        treat_as_dir = is_existing_dir and (multi or into_dir)
        pairs: List[Tuple[str, str]] = []
        for src in sources:
            tgt = (os.path.join(dest, self._fb_short_name(src))
                   if treat_as_dir else dest)
            try:
                if os.path.lexists(tgt) and os.path.samefile(src, tgt):
                    return [], f"Cannot operate on '{src}' onto itself"
            except OSError:
                pass
            if (os.path.isdir(src) and not os.path.islink(src)
                    and self._physical_path_is_within(tgt, src)):
                return [], f"Cannot operate on '{src}' inside itself"
            pairs.append((src, tgt))
        return pairs, None

    @staticmethod
    def _fb_remove_existing_target(tgt: str):
        if not os.path.lexists(tgt):
            return
        if os.path.isdir(tgt) and not os.path.islink(tgt):
            shutil.rmtree(tgt)
        else:
            os.unlink(tgt)

    @staticmethod
    def _fb_overwrite_backup_path(tgt: str) -> str:
        parent = os.path.dirname(os.path.abspath(tgt)) or "."
        base = os.path.basename(tgt.rstrip(os.sep)) or "target"
        while True:
            candidate = os.path.join(parent, f".vii-overwrite-{base}-{uuid.uuid4().hex}")
            if not os.path.lexists(candidate):
                return candidate

    def _fb_replace_existing_target(self, tgt: str, action: Callable[[], None]):
        if not os.path.lexists(tgt):
            try:
                action()
            except Exception:
                # action() may have partially written tgt before failing
                # (disk full mid-copy, copytree erroring after copying some
                # files). There is no pre-existing original to restore, but
                # a partial file/tree must not be left behind masquerading
                # as a real result once the panel refreshes.
                try:
                    self._fb_remove_existing_target(tgt)
                except OSError:
                    pass
                raise
            return
        backup = self._fb_overwrite_backup_path(tgt)
        os.rename(tgt, backup)
        try:
            action()
        except Exception as exc:
            restore_exc = None
            try:
                # os.rename atomically replaces an existing file (or an
                # absent path) in one step, so there is never a window
                # where tgt holds neither the original nor the failed
                # partial result.
                os.rename(backup, tgt)
            except OSError:
                # tgt is a non-empty directory left by a partially
                # completed copytree/move; POSIX rename can't replace
                # those atomically, so fall back to remove-then-rename.
                # This narrow window (tgt briefly absent) is unavoidable
                # for directory targets.
                try:
                    self._fb_remove_existing_target(tgt)
                except OSError:
                    # A partial target we cannot remove would make the
                    # restore rename fail; fall through and report where
                    # the original is.
                    pass
                try:
                    os.rename(backup, tgt)
                except OSError as second_exc:
                    restore_exc = second_exc
            if restore_exc is not None:
                raise OSError(
                    f"{exc}; original preserved at {backup} "
                    f"(restore failed: {restore_exc})"
                ) from exc
            raise
        try:
            self._fb_remove_existing_target(backup)
        except OSError:
            # Deliberate: the new content is in place, so a failed cleanup of
            # the hidden backup must not turn the operation into a failure
            # (test_fb_f5_copy_success_ignores_overwrite_backup_cleanup_failure).
            pass

    def _fb_report_batch_result(self, verb: str, succeeded: int,
                                failures: List[Tuple[str, str]]):
        """Set self.message/message_is_error for a batch op that may have
        partially failed. `failures` is a list of (path, error) pairs for
        items that were skipped so the rest of the batch could continue."""
        if not failures:
            self.message = f"{verb} {succeeded} item{'s' if succeeded != 1 else ''}"
            self.message_is_error = False
            return
        first_path, first_err = failures[0]
        detail = f"{os.path.basename(first_path)}: {first_err}"
        if len(failures) > 1:
            detail += f" (+{len(failures) - 1} more failed)"
        if succeeded:
            noun = "item" if succeeded == 1 else "items"
            self.message = f"{verb} {succeeded} {noun}; {detail}"
        else:
            self.message = f"{verb} failed: {detail}"
        self.message_is_error = True

    def _fb_prepare_dest_op(
            self, sources: List[str], dest: str, overwrite: bool, into_dir: bool,
            op_is_move: bool, confirm_kind: str) -> Optional[List[Tuple[str, str]]]:
        """Shared by _fb_perform_copy/_fb_perform_move: pair sources with
        destinations, reject conflicts with already-open buffers, and
        (unless overwrite) start a confirmation prompt before clobbering
        anything that already exists. Returns the (src, tgt) pairs to
        actually apply, or None if the caller should stop -- either an
        error was already reported, or an overwrite prompt was started
        (which re-invokes the caller with overwrite=True on 'y')."""
        self.message = ""
        self.message_is_error = False
        pairs, err = self._fb_pair_paths(sources, dest, into_dir=into_dir)
        if err:
            self._set_error(err)
            return None
        clobbering = [(src, tgt) for src, tgt in pairs if os.path.lexists(tgt)]
        conflict = self._fb_check_buffer_conflicts(clobbering, op_is_move=op_is_move)
        if conflict:
            self._set_error(conflict)
            return None
        if not overwrite:
            existing = [tgt for _, tgt in pairs if os.path.lexists(tgt)]
            if existing:
                count = len(existing)
                noun = "path" if count == 1 else "paths"
                self._fb_start_confirm(
                    confirm_kind,
                    f"Overwrite {count} existing {noun}? [y/N] ",
                    payload={"sources": sources, "dest": dest, "into_dir": into_dir},
                )
                return None
        return pairs

    @staticmethod
    def _fb_copy_one(src: str, tgt: str):
        if os.path.islink(src):
            os.symlink(os.readlink(src), tgt)
        elif os.path.isdir(src):
            shutil.copytree(src, tgt, symlinks=True)
        else:
            shutil.copy2(src, tgt, follow_symlinks=False)

    def _fb_move_one(self, src: str, tgt: str):
        try:
            self._fb_replace_existing_target(tgt, lambda: os.rename(src, tgt))
            return
        except OSError as exc:
            if exc.errno != errno.EXDEV:
                raise
        self._fb_replace_existing_target(tgt, lambda: self._fb_copy_one(src, tgt))
        # The complete copy is committed. A partial source deletion must
        # never trigger destination rollback and destroy the remaining data.
        try:
            self._fb_remove_existing_target(src)
        except OSError as exc:
            self._fb_after_op_refresh(focus_path=tgt)
            raise OSError(
                f"Complete copy preserved at {tgt}; source cleanup incomplete: {exc}"
            ) from exc

    def _fb_perform_copy(self, sources: List[str], dest: str,
                         overwrite: bool = False, into_dir: bool = False):
        pairs = self._fb_prepare_dest_op(
            sources, dest, overwrite, into_dir,
            op_is_move=False, confirm_kind="copy_overwrite",
        )
        if pairs is None:
            return
        succeeded = 0
        failures: List[Tuple[str, str]] = []
        last_target: Optional[str] = None
        for src, tgt in pairs:
            try:
                self._fb_replace_existing_target(
                    tgt, lambda src=src, tgt=tgt: self._fb_copy_one(src, tgt)
                )
                succeeded += 1
                last_target = tgt
            except (OSError, shutil.Error) as exc:
                failures.append((src, str(exc)))
        if succeeded:
            self._fb_after_op_refresh(focus_path=last_target)
        self._fb_report_batch_result("Copied", succeeded, failures)

    def _fb_perform_move(self, sources: List[str], dest: str,
                         overwrite: bool = False, into_dir: bool = False):
        pairs = self._fb_prepare_dest_op(
            sources, dest, overwrite, into_dir,
            op_is_move=True, confirm_kind="move_overwrite",
        )
        if pairs is None:
            return
        succeeded = 0
        moved_pairs: List[Tuple[str, str]] = []
        failures: List[Tuple[str, str]] = []
        last_target: Optional[str] = None
        for src, tgt in pairs:
            try:
                self._fb_move_one(src, tgt)
                succeeded += 1
                moved_pairs.append((src, tgt))
                last_target = tgt
            except (OSError, shutil.Error) as exc:
                failures.append((src, str(exc)))
        if moved_pairs:
            self._fb_clear_marks_for([s for s, _ in moved_pairs])
            self._fb_rebind_open_buffers(moved_pairs)
            self._fb_after_op_refresh(focus_path=last_target)
        self._fb_report_batch_result("Moved", succeeded, failures)

    def _fb_perform_delete(self, sources: List[str], recursive: bool = False):
        self.message = ""
        self.message_is_error = False
        conflict = self._fb_delete_buffer_conflict(sources)
        if conflict:
            self._set_error(conflict)
            return
        succeeded = 0
        deleted: List[str] = []
        failures: List[Tuple[str, str]] = []
        for path in sources:
            try:
                if os.path.islink(path):
                    os.unlink(path)
                elif os.path.isdir(path):
                    if recursive:
                        shutil.rmtree(path)
                    else:
                        os.rmdir(path)
                else:
                    os.remove(path)
                succeeded += 1
                deleted.append(path)
            except OSError as exc:
                failures.append((path, str(exc)))
        if deleted:
            self._fb_clear_marks_for(deleted)
            self._fb_after_op_refresh()
        self._fb_report_batch_result("Deleted", succeeded, failures)

    def _fb_delete_buffer_conflict(self, sources: List[str]) -> Optional[str]:
        for path in sources:
            idx = self._find_buffer_by_filename(path)
            if idx is None:
                idx = self._find_buffer_under_path(path)
            if idx is not None:
                label = self.buffers[idx].filename or "[No Name]"
                return (f"Cannot delete '{label}': open in buffer "
                        f"{idx + 1}/{len(self.buffers)} (close with :bd first)")
        return None

    def _fb_rebind_open_buffers(self, moved_pairs: List[Tuple[str, str]]):
        for src, tgt in moved_pairs:
            src_norm = self._normalize_path(src)
            tgt_norm = self._normalize_path(tgt)
            if not src_norm or not tgt_norm:
                continue
            for idx, b in enumerate(self.buffers):
                old_name = self._normalize_path(b.filename)
                if not old_name:
                    continue
                if old_name == src_norm:
                    normalized = tgt_norm
                elif self._path_is_within(old_name, src_norm):
                    rel = os.path.relpath(old_name, src_norm)
                    normalized = os.path.normpath(os.path.join(tgt_norm, rel))
                else:
                    continue
                self._rebind_open_buffer(idx, normalized)

    def _rebind_open_buffer(self, idx: int, normalized: str):
        new_filename_sig = self._signature_filename(normalized)
        new_file_signature = self._file_signature_or_none(normalized)
        b = self.buffers[idx]
        b.filename = normalized
        b.saved_file_signature = new_file_signature
        if isinstance(b.lines, MMapLineStore):
            b.lines.filename = normalized
        b.saved_signature = self._rebind_signature(
            b.saved_signature, new_filename_sig, new_file_signature
        )
        if idx == self.current_buffer:
            self.filename = normalized
            self._saved_file_signature = new_file_signature
            if isinstance(self.lines, MMapLineStore):
                self.lines.filename = normalized
            self._saved_signature = self._rebind_signature(
                self._saved_signature, new_filename_sig, new_file_signature
            )

    @staticmethod
    def _rebind_signature(signature, new_filename_sig,
                          new_file_signature: Optional[Tuple[str, str, int, int]]):
        if not (isinstance(signature, tuple) and signature):
            return signature
        sig = list(signature)
        sig[-1] = new_filename_sig
        if sig[0] == "file" and new_file_signature is not None and len(sig) >= 4:
            sig[1] = new_file_signature[1]
            sig[2] = new_file_signature[2]
            sig[3] = new_file_signature[3]
        return tuple(sig)

    def _handle_fb_op_prompt(self, key: int) -> bool:
        s = self.file_browser
        if s.op_kind.startswith("confirm:"):
            if key == 27 or key in (ord("n"), ord("N")):
                self._fb_cancel_prompt()
                return True
            if key in (ord("y"), ord("Y")):
                kind = s.op_kind[len("confirm:"):]
                payload = dict(s.op_payload)
                self._fb_cancel_prompt()
                if kind == "delete":
                    self._fb_perform_delete(payload.get("sources", []), recursive=False)
                elif kind == "delete_recursive":
                    self._fb_perform_delete(payload.get("sources", []), recursive=True)
                elif kind == "copy_overwrite":
                    self._fb_perform_copy(payload.get("sources", []),
                                          payload.get("dest", ""), overwrite=True,
                                          into_dir=payload.get("into_dir", False))
                elif kind == "move_overwrite":
                    self._fb_perform_move(payload.get("sources", []),
                                          payload.get("dest", ""), overwrite=True,
                                          into_dir=payload.get("into_dir", False))
                elif kind == "large_copy":
                    self._fb_start_copy_dest_prompt(
                        payload.get("sources", []),
                        payload.get("src_cwd", self._active_fb_panel().cwd),
                    )
                elif kind == "large_move":
                    self._fb_start_move_dest_prompt(
                        payload.get("sources", []),
                        payload.get("src_cwd", self._active_fb_panel().cwd),
                    )
                return True
            return True
        if key == 27:
            self._fb_cancel_prompt()
            return True
        if key in self._ENTER_KEYS:
            kind = s.op_kind
            if kind == "copy_dest":
                self._fb_finish_copy_prompt()
            elif kind == "move_dest":
                self._fb_finish_move_prompt()
            elif kind == "mkdir_name":
                self._fb_finish_mkdir_prompt()
            elif kind == "goto_dir":
                self._fb_finish_goto_prompt()
            else:
                self._fb_cancel_prompt()
            return True
        if key == ord("\t") and s.op_kind == "goto_dir":
            self._fb_complete_goto_dir()
            self._force_redraw = True
            return True
        edited = self._edit_line_key(s.op_text, s.op_cursor, key)
        if edited is not None:
            if s.op_kind == "goto_dir":
                self._fb_clear_op_completion()
            s.op_text, s.op_cursor = edited
            self._force_redraw = True
        return True

    def _handle_file_browser(self, key: int) -> bool:
        if self.file_browser.op_prompt:
            return self._handle_fb_op_prompt(key)
        if self.file_browser.grep_prompt:
            if key == 27:
                self.file_browser.grep_prompt = False
                self.file_browser.grep_field = "pattern"
                self.file_browser.grep_pattern = ""
                self.file_browser.grep_text = ""
                self.file_browser.grep_cursor = 0
                self._force_redraw = True
                return True
            if key in self._ENTER_KEYS:
                if self.file_browser.grep_field == "pattern":
                    pattern = self.file_browser.grep_text
                    if pattern:
                        self.file_browser.grep_pattern = pattern
                        self.file_browser.grep_field = "mask"
                        self.file_browser.grep_text = ""
                        self.file_browser.grep_cursor = 0
                    else:
                        self.file_browser.grep_prompt = False
                    self._force_redraw = True
                    return True
                file_mask = self.file_browser.grep_text.strip() or "*"
                pattern = self.file_browser.grep_pattern
                self.file_browser.grep_prompt = False
                self.file_browser.grep_field = "pattern"
                self.file_browser.grep_pattern = ""
                self.file_browser.grep_text = ""
                self.file_browser.grep_cursor = 0
                panel = self._active_fb_panel()
                selected = self._fb_selected_entry()
                if pattern:
                    target = (selected.path
                              if selected and selected.is_dir and selected.name != ".."
                              else panel.cwd)
                    self._run_file_browser_grep(
                        target,
                        pattern,
                        file_mask,
                        include_hidden=panel.show_hidden,
                    )
                self._force_redraw = True
                return True
            edited = self._edit_line_key(
                self.file_browser.grep_text, self.file_browser.grep_cursor, key)
            if edited is not None:
                self.file_browser.grep_text, self.file_browser.grep_cursor = edited
                self._force_redraw = True
            return True

        panel = self._active_fb_panel()
        entries = self._fb_entries(panel)
        text_rows = self._fb_visible_entry_rows(self._last_h or 24)
        if key in (27, curses.KEY_F10, ord("q")):
            self.mode = Mode.NORMAL
        elif key == curses.KEY_F1:
            self._fb_action_help()
        elif key == curses.KEY_F2:
            self._fb_action_grep()
        elif key == curses.KEY_F3:
            self._fb_action_view()
        elif key == curses.KEY_F4:
            self._fb_action_edit()
        elif key == curses.KEY_F5:
            self._fb_action_copy()
        elif key == curses.KEY_F6:
            self._fb_action_move()
        elif key == curses.KEY_F7:
            self._fb_action_mkdir()
        elif key == curses.KEY_F8:
            self._fb_action_delete()
        elif key == curses.KEY_F9:
            self._fb_cycle_sort_mode(panel)
        elif key in (ord("\t"), curses.KEY_BTAB):
            self.file_browser.active_panel = 1 - self.file_browser.active_panel
        elif key in (ord("j"), curses.KEY_DOWN):
            self._fb_move(1)
        elif key in (ord("k"), curses.KEY_UP):
            self._fb_move(-1)
        elif key in (ord("h"), curses.KEY_LEFT, curses.KEY_BACKSPACE, 127, 8):
            self._fb_enter_dir(os.path.dirname(panel.cwd) or panel.cwd)
        elif key in (ord("l"), curses.KEY_RIGHT, *self._ENTER_KEYS):
            if panel.selected:
                if self._open_marked_file_browser_entries(panel):
                    return True
                self._set_error("No files in selection (only directories marked)")
                return True
            entry = self._fb_selected_entry()
            if entry:
                if entry.is_dir:
                    self._fb_enter_dir(entry.path)
                else:
                    self._open_file_from_path(entry.path)
        elif key in (curses.KEY_IC, ord(" ")):
            entry = self._fb_selected_entry()
            if entry and entry.name != "..":
                if entry.path in panel.selected:
                    panel.selected.remove(entry.path)
                else:
                    panel.selected.add(entry.path)
                self._fb_move(1)
        elif key in (6, curses.KEY_NPAGE):
            self._fb_move(text_rows)
        elif key in (2, curses.KEY_PPAGE):
            self._fb_move(-text_rows)
        elif key in (curses.KEY_HOME, ord("g")):
            if key == ord("g"):
                self._fb_action_grep()
            else:
                panel.cursor = 0
        elif key in (curses.KEY_END, ord("G")):
            panel.cursor = max(0, len(entries) - 1)
        elif key == ord("."):
            panel.show_hidden = not panel.show_hidden
            panel.cursor = 0
            panel.top_line = 0
            self._invalidate_fb_entries(panel)
        elif key == ord("H"):
            self._fb_enter_dir(os.path.expanduser("~"))
        elif key == ord("c"):
            self._fb_action_chdir()
        elif key == ord(":"):
            self._fb_action_goto()
        elif key == ord("s"):
            self._fb_cycle_sort_mode(panel)
        elif key == ord("r"):
            panel.reverse_sort = not panel.reverse_sort
            self._invalidate_fb_entries(panel)
        elif key == 12:
            for fb_panel in self._fb_panels():
                self._invalidate_fb_entries(fb_panel)
            self._force_redraw = True
        self._clamp_fb_panel(panel)
        self._force_redraw = True
        return True

    @staticmethod
    def _fb_mask_matches(filename: str, file_mask: str) -> bool:
        masks = [part for part in re.split(r"[\s,;]+", file_mask.strip()) if part]
        if not masks:
            masks = ["*"]
        return any(fnmatch.fnmatch(filename, mask) for mask in masks)

    def _run_file_browser_grep(self, root: str, pattern: str, file_mask: str = "*",
                               include_hidden: bool = False):
        try:
            regex = re.compile(pattern)
            pattern_label = pattern
        except re.error:
            regex = re.compile(re.escape(pattern))
            pattern_label = f"{pattern} (plain text)"

        normalized_root = os.path.normpath(root)
        include_hidden = include_hidden or os.path.basename(normalized_root).startswith(".")
        results: List[GrepResult] = []
        # Bounded like the shell-command path (SHELL_COMMAND_TIMEOUT_SECONDS /
        # SHELL_COMMAND_MAX_OUTPUT_BYTES): an unbounded recursive walk run
        # synchronously in the key handler would otherwise freeze the whole
        # UI for as long as the tree takes to scan, with no way to cancel
        # (SIGINT is ignored for the session) and no cap on memory use.
        deadline = time.monotonic() + self.FB_GREP_TIMEOUT_SECONDS
        truncated = False
        for dirpath, dirnames, filenames in os.walk(root):
            if time.monotonic() >= deadline:
                truncated = True
                break
            if not include_hidden:
                dirnames[:] = [d for d in dirnames if not d.startswith(".")]
            for filename in sorted(filenames):
                if not include_hidden and filename.startswith("."):
                    continue
                if not self._fb_mask_matches(filename, file_mask):
                    continue
                if len(results) >= self.FB_GREP_MAX_RESULTS or time.monotonic() >= deadline:
                    truncated = True
                    break
                path = os.path.join(dirpath, filename)
                try:
                    with _open_regular_file(path, "r", encoding="utf-8", errors="replace") as fh:
                        line_no = 0
                        parts: List[str] = []
                        overlong = False
                        while True:
                            if time.monotonic() >= deadline:
                                truncated = True
                                break
                            # Bounded read: a file with no line breaks at
                            # all (or one absurdly long line) must not be
                            # able to block past the deadline in a single
                            # call the way `for line in fh` can -- that
                            # reads clear to the next '\n' or EOF regardless
                            # of size, and the old per-line modulo check
                            # never fires while still on line 1.
                            chunk = fh.readline(self.FB_GREP_MAX_LINE_BYTES)
                            if not chunk:
                                break
                            complete = (chunk.endswith("\n")
                                        or len(chunk) < self.FB_GREP_MAX_LINE_BYTES)
                            if not overlong:
                                parts.append(chunk)
                                if not complete:
                                    overlong = True
                            if complete:
                                line_no += 1
                                if not overlong:
                                    text = "".join(parts).rstrip("\n")
                                    if regex.search(text):
                                        results.append(GrepResult(path, line_no, text))
                                        if len(results) >= self.FB_GREP_MAX_RESULTS:
                                            truncated = True
                                            break
                                parts = []
                                overlong = False
                except (OSError, UnicodeError):
                    continue
                if truncated:
                    break
            if truncated:
                break

        self.grep_results = results
        self.grep_result_cursor = 0
        self.grep_result_top_line = 0
        self.grep_result_number = ""
        self.grep_result_label = f"{pattern_label} in {root} ({file_mask or '*'})"
        self.mode = Mode.GREP_RESULTS
        self.message = (f"{len(results)} match{'es' if len(results) != 1 else ''}"
                        + (" (truncated)" if truncated else ""))
        self.message_is_error = False
        self._force_redraw = True

    def _draw_grep_results(self, stdscr, height: int, width: int):
        results = self.grep_results
        text_rows = max(1, height - 2)
        self._clamp_list_view("grep_result_cursor", "grep_result_top_line",
                              len(results), text_rows)

        def draw_row(scr, srow, idx):
            result = results[idx]
            line = f"{result.filename}:{result.line_no}: {result.text}"
            attr = curses.A_REVERSE if idx == self.grep_result_cursor else curses.A_NORMAL
            self._add_curses_text(scr, srow, 0, line, attr)

        typed = f" number:{self.grep_result_number}" if self.grep_result_number else ""
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=f" GREP    {self.grep_result_label}",
            status_right=f" {self.grep_result_cursor + 1 if results else 0}/{len(results)}{typed} ",
            total=len(results), top_line=self.grep_result_top_line,
            draw_row=draw_row,
            bottom=lambda win: self._draw_overlay_bottom(
                win, width,
                self.message or "Enter opens match, digit(s)+Enter select by number, q/ESC close, j/k and PgUp/PgDn navigate",
                self.message_is_error),
        )

    def _open_grep_result(self, index: int):
        self.grep_result_number = ""
        if not 0 <= index < len(self.grep_results):
            self._set_error("No such match")
            return
        self.grep_result_cursor = index
        result = self.grep_results[index]
        self._open_file_from_path(result.filename, result.line_no)

    def _handle_grep_results(self, key: int) -> bool:
        return self._handle_list_overlay(
            key, "grep_result_cursor", len(self.grep_results),
            self._open_grep_result, "grep_result_number",
        )

    def _draw_functions(self, stdscr, height: int, width: int):
        funcs = self._filtered_function_list()
        text_rows = max(1, height - 2)
        self._clamp_list_view("function_list_cursor", "function_list_top_line",
                              len(funcs), text_rows)

        def draw_row(scr, srow, idx):
            lnum, label = funcs[idx]
            attr = curses.A_REVERSE if idx == self.function_list_cursor else curses.A_NORMAL
            self._add_curses_text(scr, srow, 0, f" {lnum + 1:5d}  {label}", attr)

        total = len(self.function_list)
        # Show "matching of total" in status when a filter is active
        if self.function_list_search:
            right_s = f" {self.function_list_cursor + 1 if funcs else 0}/{len(funcs)} of {total} "
        else:
            right_s = f" {self.function_list_cursor + 1 if funcs else 0}/{total} "

        def bottom(bottom_win):
            if self.function_list_searching:
                # Draw search prompt in NORMAL (no reverse) so cursor is visible
                prompt = f"/{self.function_list_search}"
                cursor_col = self._draw_prompt_line(bottom_win, prompt, len(prompt), width)
                return height - 1, cursor_col
            hint = "/ search  Enter jump  j/k navigate  q/ESC close"
            if self.function_list_search:
                hint = f"[/{self.function_list_search}]  " + hint
            self._draw_overlay_bottom(bottom_win, width, hint)
            return None

        fname = self.filename or "[No Name]"
        self._draw_overlay_frame(
            stdscr, height, width,
            status_left=f" FUNCS   {fname}",
            status_right=right_s,
            total=len(funcs), top_line=self.function_list_top_line,
            draw_row=draw_row, bottom=bottom,
        )

    def _handle_functions(self, key: int) -> bool:
        funcs = self._filtered_function_list()

        def _jump():
            if funcs:
                idx = max(0, min(self.function_list_cursor, len(funcs) - 1))
                lnum, label = funcs[idx]
                self.function_list_search = ""
                self.function_list_searching = False
                self.mode = Mode.NORMAL
                self._move(lnum, 0)
                self.cursor_col = self._first_nonblank()
                self.message = f"→ {label}  (line {lnum + 1})"
                self.message_is_error = False

        if self.function_list_searching:
            if key == 27:  # Esc — exit search mode, keep any active filter
                self.function_list_searching = False
            elif key in self._ENTER_KEYS:
                _jump()
            elif key in (curses.KEY_BACKSPACE, 127, 8):
                if self.function_list_search:
                    self.function_list_search = self.function_list_search[:-1]
                    self.function_list_cursor = 0
                else:
                    self.function_list_searching = False
            else:
                # Printable keys extend the filter — including j/k/g/G, which
                # only navigate outside search mode. Arrow/paging keys still
                # navigate while the prompt is open.
                ch = self._text_input_char(key)
                if ch is not None:
                    self.function_list_search += ch
                    self.function_list_cursor = 0  # reset to top of new filtered list
                else:
                    self._list_overlay_nav(key, "function_list_cursor", len(funcs))
        else:
            if key == ord("q"):
                # q always closes immediately
                self.function_list_search = ""
                self.function_list_searching = False
                self.mode = Mode.NORMAL
            elif key == 27:  # Esc — clear active filter first, then close on second press
                if self.function_list_search:
                    self.function_list_search = ""
                    self.function_list_cursor = 0
                else:
                    self.mode = Mode.NORMAL
            elif key == ord("/"):
                self.function_list_searching = True
            elif key in self._ENTER_KEYS:
                _jump()
            else:
                self._list_overlay_nav(key, "function_list_cursor", len(funcs))

        self._force_redraw = True
        return True

    def _run_shell_command(self, cmd: str):
        shell_cmd = cmd.strip()
        if shell_cmd == "!":
            shell_cmd = self.last_shell_cmd
        if not shell_cmd:
            self._set_error("No previous shell command")
            return

        shell = os.environ.get("SHELL", "/bin/sh")
        try:
            returncode, output, truncated, timed_out = self._run_shell_command_limited(
                shell_cmd, shell
            )
        except OSError as exc:
            self._set_error(str(exc))
            return

        self.last_shell_cmd = shell_cmd
        if output:
            lines, endings = self._split_bytes_with_line_endings(output)
        else:
            lines, endings = [], []
        if timed_out:
            if lines and endings and endings[-1] == "":
                endings[-1] = self.default_line_ending
            lines.append("[command timed out]")
            endings.append("")
        if truncated:
            if lines and endings and endings[-1] == "":
                endings[-1] = self.default_line_ending
            lines.append("[output truncated]")
            endings.append("")
        if returncode != 0 and not (truncated or timed_out):
            if lines and endings and endings[-1] == "":
                endings[-1] = self.default_line_ending
            lines.append(f"[exit {returncode}]")
            endings.append("")
        self._insert_lines_after_cursor(lines, endings)
        self.message = f':!{shell_cmd} {len(lines)}L inserted'
        self.message_is_error = returncode != 0 or truncated or timed_out

    def _run_shell_command_to_view(self, cmd: str):
        shell_cmd = cmd.strip() or self.last_shell_cmd
        if not shell_cmd:
            self._set_error("No previous shell command")
            return

        shell = os.environ.get("SHELL", "/bin/sh")
        try:
            returncode, output, truncated, timed_out = self._run_shell_command_limited(
                shell_cmd, shell
            )
        except OSError as exc:
            self._set_error(str(exc))
            return

        lines, _ = self._split_bytes_with_line_endings(output) if output else ([], [])
        if timed_out:
            lines.append("[command timed out]")
        if truncated:
            lines.append("[output truncated]")
        if returncode != 0 and not (truncated or timed_out):
            lines.append(f"[exit {returncode}]")
        self._open_shell_output(shell_cmd, lines)

    def _run_shell_command_limited(self, shell_cmd: str, shell: str) -> Tuple[int, bytes, bool, bool]:
        # stdin=DEVNULL keeps children from stealing keystrokes from curses
        # (or hanging on terminal reads until the timeout); the new session
        # gives the whole pipeline its own process group so a timeout kill
        # reaches grandchildren, not just the shell.
        proc = subprocess.Popen(
            shell_cmd,
            shell=True,
            executable=shell,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            selector = selectors.DefaultSelector()
            output = bytearray()
            truncated = False
            timed_out = False
            deadline = time.monotonic() + self.SHELL_COMMAND_TIMEOUT_SECONDS
            try:
                if proc.stdout is not None:
                    os.set_blocking(proc.stdout.fileno(), False)
                    selector.register(proc.stdout, selectors.EVENT_READ)
                while True:
                    now = time.monotonic()
                    if now >= deadline:
                        timed_out = True
                        self._terminate_shell_process(proc)
                        break
                    if proc.poll() is not None and not selector.get_map():
                        break
                    timeout = max(0.0, min(0.1, deadline - now))
                    events = selector.select(timeout)
                    if not events:
                        if proc.poll() is not None and not selector.get_map():
                            break
                        continue
                    for key, _ in events:
                        chunk = key.fileobj.read(8192)
                        if not chunk:
                            selector.unregister(key.fileobj)
                            continue
                        remaining = self.SHELL_COMMAND_MAX_OUTPUT_BYTES - len(output)
                        if remaining > 0:
                            output.extend(chunk[:remaining])
                        if len(chunk) > remaining:
                            truncated = True
                            self._terminate_shell_process(proc)
                            break
                    if truncated:
                        break
                if proc.stdout is not None:
                    while len(output) < self.SHELL_COMMAND_MAX_OUTPUT_BYTES:
                        chunk = proc.stdout.read(8192)
                        if not chunk:
                            break
                        remaining = self.SHELL_COMMAND_MAX_OUTPUT_BYTES - len(output)
                        output.extend(chunk[:remaining])
                        if len(chunk) > remaining:
                            truncated = True
                            break
            finally:
                selector.close()
                if proc.stdout is not None:
                    proc.stdout.close()
        finally:
            # Reap the child no matter what went wrong above -- including a
            # failure in os.set_blocking()/selector.register() before the
            # process was ever registered for polling. Without this, such a
            # failure would propagate straight out with the child still
            # running and never wait()'d, leaking an orphaned/zombie process.
            self._terminate_shell_process(proc)
        returncode = proc.wait()
        return returncode, bytes(output), truncated, timed_out

    @staticmethod
    def _signal_shell_process_group(proc: subprocess.Popen, sig: int):
        # start_new_session=True makes the child's pgid equal its pid, so the
        # group signal reaches backgrounded grandchildren too. Fall back to
        # signalling just the shell if the group is already gone or ours to
        # touch no longer (e.g. the pid was reaped and reused).
        try:
            os.killpg(proc.pid, sig)
            return
        except (ProcessLookupError, PermissionError, OSError):
            pass
        try:
            proc.send_signal(sig)
        except (ProcessLookupError, OSError):
            pass

    @classmethod
    def _terminate_shell_process(cls, proc: subprocess.Popen):
        # The group can outlive its leader. Always signal it, and escalate
        # even if waiting for the leader succeeds before its children exit.
        cls._signal_shell_process_group(proc, signal.SIGTERM)
        try:
            proc.wait(timeout=0.2)
        except subprocess.TimeoutExpired:
            pass
        cls._signal_shell_process_group(proc, signal.SIGKILL)
        proc.wait()

    # -----------------------------------------------------------------------
    # Ex-command execution
    # -----------------------------------------------------------------------

    def _insert_lines_after_cursor(self, inserted: List[str],
                                   inserted_endings: Optional[List[str]] = None) -> int:
        if not inserted:
            return 0
        inserted_endings = list(inserted_endings or [])
        self._push_undo()
        ins_at = self.cursor_row + 1
        if len(inserted_endings) != len(inserted):
            inserted_endings = [self.default_line_ending] * len(inserted)
            if ins_at + len(inserted) >= len(self.lines):
                inserted_endings[-1] = ""
        if (inserted_endings and inserted_endings[-1] == ""
                and ins_at < len(self.lines)):
            inserted_endings[-1] = self._line_separator_for_insert(ins_at)
        self._adjust_marks_for_line_insert(ins_at, len(inserted))
        self._insert_line_ending_values(ins_at, inserted_endings)
        self.lines[ins_at:ins_at] = inserted
        self.line_endings_trusted = True
        self._clamp_marks()
        self.modified = True
        self._force_redraw = True
        return len(inserted)

    def _insert_lines_after_row(self, row: int, inserted: List[str],
                                inserted_endings: Optional[List[str]] = None) -> int:
        old_row, old_col = self.cursor_row, self.cursor_col
        target = max(-1, min(len(self.lines) - 1, row))
        self.cursor_row = target
        inserted_count = self._insert_lines_after_cursor(inserted, inserted_endings)
        if old_row > target:
            old_row += inserted_count
        self.cursor_row, self.cursor_col = old_row, old_col
        self._clamp_cursor()
        return inserted_count

    def _read_file_after_row(self, fname: str, row: int) -> bool:
        full_fname = self._normalize_path(fname)
        if not full_fname:
            self._set_error("No file name")
            return True
        try:
            with _open_regular_file(full_fname) as fh:
                raw_insert = fh.read()
            if raw_insert:
                inserted, inserted_endings = self._split_bytes_with_line_endings(raw_insert)
            else:
                inserted, inserted_endings = [], []
            if inserted:
                self._insert_lines_after_row(row, inserted, inserted_endings)
            self.message = f'"{full_fname}" {len(inserted)}L appended'
        except OSError as exc:
            self._set_error(str(exc))
        return True

    def _set_error(self, msg: str):
        self.message          = msg
        self.message_is_error = True

    def _current_file_label(self) -> str:
        return self.filename or "[No Name]"

    def _has_unsaved_changes(self) -> bool:
        self._refresh_all_buffer_modified_flags()
        return any(b.modified for b in self.buffers)

    def _has_other_unsaved_changes(self) -> bool:
        self._refresh_all_buffer_modified_flags()
        return any(i != self.current_buffer and b.modified
                   for i, b in enumerate(self.buffers))

    def _check_unsaved_changes(self, action: str) -> bool:
        if self._has_unsaved_changes():
            self._set_error(f"No write since last change (use :{action}! to override)")
            return False
        return True

    def _current_buffer_is_modified(self) -> bool:
        self._refresh_modified()
        self._sync_current_buffer()
        return self.modified

    def _reset_view(self):
        self.cursor_row = 0
        self.cursor_col = 0
        self.top_line = 0
        self.left_col = 0
        self._force_redraw = True

    def _reload_current_file_preserve_position(self) -> bool:
        if not self.filename:
            self._set_error("No file name")
            return True
        if self._current_buffer_is_modified():
            self._set_error("No write since last change (use :edit! to force reload)")
            return True
        row, col = self.cursor_row, self.cursor_col
        top, left = self.top_line, self.left_col
        if self._load_file(self.filename):
            self.cursor_row = row
            self.cursor_col = col
            self.top_line = top
            self.left_col = left
            self._clamp_cursor()
            self._force_redraw = True
        return True

    def _new_buffer(self, reuse_current: bool = False):
        if not reuse_current:
            self._append_buffer(None, switch=True)
            return
        self._buffer_id = object()
        self.last_jump = None
        self.filename = None
        self.lines = [""]
        self.line_endings = [""]
        self.line_endings_trusted = False
        self._saved_signature = self._line_signature(
            self.lines, self.line_endings
        ) + (self.line_endings_trusted, None)
        self._saved_file_signature = None
        self.cursor_row = 0
        self.cursor_col = 0
        self.top_line = 0
        self.left_col = 0
        self.undo_stack = deque()
        self.redo_stack = deque()
        self.marks = {}
        self.auto_marks = {}
        self.log_type = None
        self.modified = False
        self.message = '"[No Name]" [New]'
        self._reset_view()

    def _parse_line_ref(self, text: str, default: Optional[int] = None) -> Optional[int]:
        ref = text.strip()
        if not ref:
            return default

        if ref == ".":
            return self.cursor_row
        if ref == "$":
            return len(self.lines) - 1
        if ref.isdigit():
            n = int(ref)
            if n == 0:
                self._set_error("Invalid address: 0")
                return None
            return max(0, min(len(self.lines) - 1, n - 1))
        if len(ref) == 2 and ref[0] == "'" and ref[1].isalpha():
            mark = self.marks.get(ref[1])
            if mark is None:
                self._set_error(f"Mark not set: {ref[1]}")
                return None
            return max(0, min(mark[0], len(self.lines) - 1))

        m = re.fullmatch(r"([.$]|\d+|'[A-Za-z])?([+-])(\d+)?", ref)
        if not m:
            return None

        base_ref, sign, amount_text = m.groups()
        if base_ref in (None, ""):
            base = self.cursor_row
        else:
            base = self._parse_line_ref(base_ref)
            if base is None:
                return None

        amount = int(amount_text) if amount_text else 1
        if sign == "+":
            return min(len(self.lines) - 1, base + amount)
        return max(0, base - amount)

    def _show_line(self, row: int):
        row = max(0, min(len(self.lines) - 1, row))
        self._move(row, self._first_nonblank(row))
        self.message = self.lines[row]

    def _active_register_name(self) -> str:
        return self.active_register or '"'

    def _clear_active_register(self):
        self.active_register = None

    def _clear_unused_active_register(self):
        if self.active_register:
            self._clear_active_register()

    def _store_register(self, text: List[str], is_lines: bool,
                        line_endings: Optional[List[str]] = None,
                        blockwise: bool = False):
        data = (list(text), is_lines)
        blockwise = blockwise and not is_lines
        self.yank_is_block = blockwise
        for name in ('"', self.active_register):
            if not name:
                continue
            if blockwise:
                self.block_registers.add(name)
            else:
                self.block_registers.discard(name)
        endings = (
            list(line_endings)
            if is_lines and line_endings is not None and len(line_endings) == len(text)
            else []
        )
        self.yank_buffer = list(text)
        self.yank_is_lines = is_lines
        self.yank_line_endings = endings
        self.registers['"'] = data
        self.register_line_endings['"'] = endings
        if self.active_register:
            self.registers[self.active_register] = data
            self.register_line_endings[self.active_register] = endings
        self._clear_active_register()

    def _resolve_put_source(self) -> Tuple[List[str], bool, List[str]]:
        """Resolve what a put/paste/visual-replace should read: the active
        register if one was selected (consuming it), otherwise the unnamed
        yank buffer. Shared by every site that needs this -- _put(),
        _put_count(), and _replace_visual_selection() -- so the active vs.
        unnamed register decision, and how each register's data is looked
        up, only has to be right in one place."""
        if self.active_register:
            name = self._active_register_name()
            put_buffer, put_is_lines = self.registers.get(name, ([], True))
            put_line_endings = list(self.register_line_endings.get(name, []))
            self._clear_active_register()
        else:
            put_buffer = list(self.yank_buffer)
            put_is_lines = self.yank_is_lines
            put_line_endings = list(self.yank_line_endings)
        return put_buffer, put_is_lines, put_line_endings

    @staticmethod
    def _put_source_is_empty(put_buffer: List[str], put_is_lines: bool) -> bool:
        if not put_buffer:
            return True
        return not put_is_lines and len(put_buffer) == 1 and put_buffer[0] == ""

    def _set_last_change(self, action):
        if not self._repeat_active:
            self._last_change = action

    def _repeat_last_change(self, count: int):
        if self._last_change is None:
            self.message = "No previous change"
            return
        self._repeat_active = True
        try:
            for _ in range(count):
                self._last_change()
        finally:
            self._repeat_active = False

    def _set_mark(self, name: str):
        if len(name) == 1 and name.isalpha():
            self.marks[name] = (self.cursor_row, self.cursor_col)
            self._sync_current_buffer()
            self._force_redraw = True

    def _delete_all_marks(self):
        self.marks = {}
        self.auto_marks = {}
        self._sync_current_buffer()
        self._force_redraw = True
        self.message = "All marks deleted"

    def _line_has_named_mark(self, row: int) -> bool:
        return any(mark_row == row for mark_row, _ in self.marks.values())

    def _set_auto_mark(self):
        """m. — toggle an auto-mark at the current line.

        Each new mark's id is one past the highest positive id already in
        use (mirroring how _run_global_command mints its negative temp-tag
        ids) rather than the creation-time row number: once edits shift an
        existing auto-mark's tracked line, that row number is free to be
        reused as *another* mark's creation row later in the same session,
        and since the id is the dict key, two marks sharing an id silently
        collapse into one entry -- the older mark's position is lost with
        no removal message, because it never went through the toggle-off
        branch below."""
        existing = [id_ for id_, cur in self.auto_marks.items() if cur == self.cursor_row]
        if existing:
            for id_ in existing:
                del self.auto_marks[id_]
            self.message = f"auto-mark removed from line {self.cursor_row + 1}"
            if self._line_has_named_mark(self.cursor_row):
                self.message += " (other marks remain)"
        else:
            next_id = max((k for k in self.auto_marks if k >= 0), default=0) + 1
            self.auto_marks[next_id] = self.cursor_row
            self.message = f"auto-mark set at line {self.cursor_row + 1}"
        self._sync_current_buffer()
        self._force_redraw = True

    def _jump_auto_mark_prev(self):
        """'[ — jump to the nearest auto-mark on a line before the cursor."""
        targets = [cur for cur in self.auto_marks.values() if cur < self.cursor_row]
        if not targets:
            self._set_error("No previous auto-mark")
            return
        target = max(targets)
        self.last_jump = (self.cursor_row, self.cursor_col)
        self._move(target, self._first_nonblank(target))

    def _jump_auto_mark_next(self):
        """'] — jump to the nearest auto-mark on a line after the cursor."""
        targets = [cur for cur in self.auto_marks.values() if cur > self.cursor_row]
        if not targets:
            self._set_error("No next auto-mark")
            return
        target = min(targets)
        self.last_jump = (self.cursor_row, self.cursor_col)
        self._move(target, self._first_nonblank(target))

    def _jump_to_mark(self, name: str, exact: bool):
        mark = self.marks.get(name)
        if mark is None:
            self._set_error(f"Mark not set: {name}")
            return
        self.last_jump = (self.cursor_row, self.cursor_col)
        row, col = mark
        row = max(0, min(row, len(self.lines) - 1))
        col = max(0, min(col, len(self.lines[row]) - 1 if self.lines[row] else 0))
        self._move(row, col if exact else self._first_nonblank(row))

    def _resolve_text_object(self, around: bool, obj: str) -> Optional[Tuple[int, int, int, int, bool]]:
        if obj != "w":
            return None

        row = self.cursor_row
        line = self.lines[row]
        if not line:
            return row, 0, row, 0, False

        col = min(self.cursor_col, max(0, len(line) - 1))
        if col < len(line) and line[col].isspace():
            while col < len(line) and line[col].isspace():
                col += 1
            if col >= len(line):
                col = max(0, len(line) - 1)

        start = col
        while start > 0 and self._is_word_char(line[start - 1]):
            start -= 1
        end = col
        while end < len(line) and self._is_word_char(line[end]):
            end += 1
        end = max(start, end - 1)

        if around:
            while end + 1 < len(line) and line[end + 1].isspace():
                end += 1
            if start == col:
                while start > 0 and line[start - 1].isspace():
                    start -= 1

        return row, start, row, end, False

    def _find_motion_target(self, cmd: str, char: str, cnt: int) -> Optional[int]:
        line = self.lines[self.cursor_row]
        col = self.cursor_col
        found = None
        for _ in range(cnt):
            if cmd == "f":
                idx = line.find(char, col + 1)
                if idx < 0:
                    return None
                found = col = idx
            elif cmd == "F":
                idx = line.rfind(char, 0, col)
                if idx < 0:
                    return None
                found = col = idx
            elif cmd == "t":
                idx = line.find(char, col + 1)
                if idx < 0:
                    return None
                found = col = idx  # track char pos so next iter skips past it
            elif cmd == "T":
                idx = line.rfind(char, 0, col)
                if idx < 0:
                    return None
                found = col = idx  # track char pos so next iter searches before it
        if cmd == "t" and found is not None:
            found -= 1
        elif cmd == "T" and found is not None:
            found += 1
        return found

    def _search_motion_target(self, pattern: str, forward: bool,
                              literal: bool = False) -> Optional[Tuple[int, int]]:
        start = (self.cursor_row, self.cursor_col)
        old_message, old_error = self.message, self.message_is_error
        old_pattern, old_forward = self.search_pattern, self._search_forward
        old_literal = self._search_literal
        self._search(pattern, forward, wrap_msg=False, literal=literal)
        if self.message_is_error:
            self.message = old_message
            self.message_is_error = old_error
            self.search_pattern = old_pattern
            self._search_forward = old_forward
            self._search_literal = old_literal
            self._move(*start)
            return None
        target = (self.cursor_row, self.cursor_col)
        self._move(*start)
        self.message = old_message
        self.message_is_error = old_error
        return target

    def _parse_range_prefix(self, cmd: str) -> Tuple[Optional[Tuple[int, int]], str]:
        text = cmd.lstrip()
        if not text.strip():
            return None, ""

        if text.startswith("%"):
            return (0, len(self.lines) - 1), text[1:].lstrip()

        idx = 0
        prefix = rest = None
        while idx < len(text):
            ch = text[idx]
            # A leading quote names a mark address ('a) — its letter is part
            # of the address, not the start of the command word, so skip it.
            if ch == "'" and idx + 1 < len(text) and text[idx + 1].isalpha():
                idx += 2
                continue
            if ch.isalpha() or ch in "&~":
                prefix = text[:idx].rstrip()
                rest = text[idx:]
                break
            idx += 1
        if prefix is None:
            return None, text

        if not prefix:
            return None, text

        if "," in prefix:
            left, right = prefix.split(",", 1)
            r1 = self._parse_line_ref(left, self.cursor_row)
            r2 = self._parse_line_ref(right, self.cursor_row)
            if r1 is None or r2 is None:
                return None, text
            return (min(r1, r2), max(r1, r2)), rest

        row = self._parse_line_ref(prefix, self.cursor_row)
        if row is None:
            return None, text
        return (row, row), rest

    def _split_ex_delimited(self, text: str, delim: str) -> Tuple[List[str], str]:
        parts: List[str] = []
        current: List[str] = []

        idx = 0
        while idx < len(text):
            ch = text[idx]
            if ch == "\\" and idx + 1 < len(text) and text[idx + 1] == delim:
                current.append(delim)
                idx += 2
                continue
            if ch == delim:
                parts.append("".join(current))
                return parts, text[idx + 1:]
            current.append(ch)
            idx += 1
        parts.append("".join(current))
        return parts, ""

    def _parse_substitute_cmd(self, cmd: str) -> Optional[Tuple[int, int, str, str, str, bool]]:
        range_rows, rest = self._parse_range_prefix(cmd)
        explicit_range = range_rows is not None
        rest_stripped = rest.strip()
        if rest_stripped.startswith("&"):
            if rest_stripped not in ("&", "&&"):
                self._set_error(f"Invalid substitute flag: {rest_stripped[1]}")
                return None
            if not self.last_sub_pattern:
                self._set_error("No previous substitution")
                return None
            r1, r2 = range_rows or (self.cursor_row, self.cursor_row)
            flags = self.last_sub_flags if rest_stripped.startswith("&&") else ""
            return r1, r2, self.last_sub_pattern, self.last_sub_repl, flags, explicit_range

        if rest.startswith("substitute") and (
                len(rest) == len("substitute") or
                not rest[len("substitute")].isalnum()):
            name = "substitute"
            body = rest[len(name):]
        elif rest.startswith("s") and (
                len(rest) == 1 or
                not rest[1].isalnum()):
            name = "s"
            body = rest[len(name):]
        elif rest_stripped == "~":
            if not self.last_sub_pattern:
                self._set_error("No previous substitution")
                return None
            r1, r2 = range_rows or (self.cursor_row, self.cursor_row)
            pattern = self.search_pattern or self.last_sub_pattern
            if not pattern:
                self._set_error("No previous search pattern")
                return None
            return r1, r2, pattern, self.last_sub_repl, self.last_sub_flags, explicit_range
        else:
            return None

        r1, r2 = range_rows or (self.cursor_row, self.cursor_row)
        body = body.lstrip()
        if not body:
            if not self.last_sub_pattern:
                self._set_error("No previous substitution")
                return None
            return r1, r2, self.last_sub_pattern, self.last_sub_repl, "", explicit_range

        delim = body[0]
        if delim.isalnum() or delim.isspace():
            return None

        pattern_parts, tail = self._split_ex_delimited(body[1:], delim)
        repl_parts, flags = self._split_ex_delimited(tail, delim)
        pattern = pattern_parts[0]
        repl = repl_parts[0]
        flags = flags.strip()
        invalid_flags = "".join(ch for ch in flags if ch not in "gic")
        if invalid_flags:
            self._set_error(f"Invalid substitute flag: {invalid_flags[0]}")
            return None

        if pattern == "":
            pattern = self.search_pattern or self.last_sub_pattern
            if not pattern:
                self._set_error("No previous search pattern")
                return None

        return r1, r2, pattern, repl, flags, explicit_range

    def _parse_global_cmd(self, cmd: str) -> Optional[Tuple[Tuple[int, int], str, str, bool]]:
        range_rows, rest = self._parse_range_prefix(cmd)
        name = body = None
        invert = False
        for candidate, candidate_invert in (("vglobal", True), ("global", False),
                                             ("v", True), ("g", False)):
            if rest.startswith(candidate) and (
                    len(rest) == len(candidate) or not rest[len(candidate)].isalnum()):
                name, invert = candidate, candidate_invert
                body = rest[len(candidate):]
                break
        if name is None:
            return None

        if body.startswith("!"):
            invert = not invert
            body = body[1:]
        if not body:
            return None
        delim = body[0]
        if delim.isalnum() or delim.isspace():
            return None

        parts, sub_cmd = self._split_ex_delimited(body[1:], delim)
        pattern = parts[0] or self.search_pattern
        if not pattern:
            self._set_error("No previous search pattern")
            return None

        r1, r2 = range_rows or (0, len(self.lines) - 1)
        return (r1, r2), pattern, sub_cmd.strip(), invert

    def _run_global_command(self, range_rows: Tuple[int, int], pattern: str,
                             sub_cmd: str, invert: bool) -> bool:
        regex = self._compile_pattern(pattern)
        if regex is None:
            self._set_error(f"Invalid pattern: {pattern}")
            return True

        r1, r2 = range_rows
        r1 = max(0, min(r1, len(self.lines) - 1))
        r2 = max(0, min(r2, len(self.lines) - 1))
        if r2 < r1:
            r1, r2 = r2, r1

        sub_cmd = sub_cmd or "p"
        # Track matching lines via temporary auto_marks entries (keyed by
        # negative ids so they can never collide with a real auto-mark,
        # which is always keyed by the row it was created on) so the row
        # positions stay correct as the sub-command inserts/deletes lines.
        # self.marks can't be used for this: _clamp_session_marks silently
        # drops any mark whose name isn't a single letter.
        # Start below the lowest id already in use so a sub-command that
        # itself runs a nested :g can't collide with this call's tags.
        next_id = min((k for k in self.auto_marks if k < 0), default=0) - 1
        tags = []
        for row in range(r1, r2 + 1):
            if bool(regex.search(self.lines[row])) != invert:
                self.auto_marks[next_id] = row
                tags.append(next_id)
                next_id -= 1

        if not tags:
            self._set_error(f"Pattern not found: {pattern}")
            return True

        origin_id = self._buffer_id
        self.search_pattern = pattern
        self._search_literal = False
        result = True
        try:
            for tag in tags:
                if self._buffer_id is not origin_id:
                    # sub_cmd switched buffers out from under us -- the
                    # remaining tags reference rows in a buffer that's no
                    # longer live in self.auto_marks. Stop rather than
                    # silently mutating the wrong buffer's marks.
                    self._set_error("Global command aborted: buffer changed")
                    result = True  # False is reserved for an explicit quit.
                    break
                if tag not in self.auto_marks:
                    continue  # this line was removed by an earlier iteration
                row = self.auto_marks.pop(tag)
                self.cursor_row = max(0, min(row, len(self.lines) - 1))
                self.cursor_col = 0
                if not self._execute_cmd(sub_cmd):
                    result = False
                    break
                if self._buffer_id is not origin_id:
                    self._set_error("Global command aborted: buffer changed")
                    break
        finally:
            if self._buffer_id is origin_id:
                target = self.auto_marks
            else:
                origin = next((b for b in self.buffers if b.buffer_id is origin_id), None)
                target = origin.auto_marks if origin is not None else {}
            for tag in tags:
                target.pop(tag, None)
        self._force_redraw = True
        return result

    def _parse_copy_ref(self, ref: str) -> Optional[int]:
        """:c-specific line reference. Per the user spec: % = current line,
        $ = last line, N = 1-indexed line number."""
        ref = ref.strip()
        if ref == "%":
            return self.cursor_row
        if ref == "$":
            return len(self.lines) - 1
        if ref.isdigit():
            return max(0, min(len(self.lines) - 1, int(ref) - 1))
        return None

    def _parse_copy_cmd(self, cmd: str) -> Optional[Tuple[int, int]]:
        """Recognise the :c family. Returns (r1, r2) for the lines to copy,
        or None if the command isn't a :c form. Supports:
          :*c              all lines
          :c   :%c   :$c   single line (current / current / last)
          :Nc              single line N
          :N,Mc            range; each ref may be N, %, or $
        """
        s = cmd.strip()
        if not s.endswith("c"):
            return None
        body = s[:-1].strip()
        if body == "*":
            return (0, len(self.lines) - 1)
        if body == "":
            return (self.cursor_row, self.cursor_row)
        if "," in body:
            left, _, right = body.partition(",")
            r1 = self._parse_copy_ref(left)
            r2 = self._parse_copy_ref(right)
            if r1 is None or r2 is None:
                return None
            return (min(r1, r2), max(r1, r2))
        line = self._parse_copy_ref(body)
        if line is None:
            return None
        return (line, line)

    def _copy_lines_to_register(self, r1: int, r2: int) -> bool:
        if not self.lines:
            self._set_error("Empty buffer")
            return True
        r1 = max(0, min(r1, len(self.lines) - 1))
        r2 = max(0, min(r2, len(self.lines) - 1))
        if r2 < r1:
            r1, r2 = r2, r1
        self._store_register(
            list(self.lines[r1:r2 + 1]),
            True,
            self._line_endings_for_range(r1, r2),
        )
        n = r2 - r1 + 1
        self.message = f"{n} line{'s' if n != 1 else ''} copied"
        self.message_is_error = False
        return True

    def _delete_lines_to_register(self, r1: int, r2: int) -> bool:
        if not self.lines:
            self._set_error("Empty buffer")
            return True
        r1 = max(0, min(r1, len(self.lines) - 1))
        r2 = max(0, min(r2, len(self.lines) - 1))
        if r2 < r1:
            r1, r2 = r2, r1
        deleted_endings = self._line_endings_for_range(r1, r2)
        self._push_undo()
        deleted = self._delete_range(r1, 0, r2, 0, True)
        self._store_register(deleted, True, deleted_endings)
        self.modified = True
        n = r2 - r1 + 1
        self.message = f"{n} line{'s' if n != 1 else ''} deleted"
        self.message_is_error = False
        self._force_redraw = True
        return True

    def _report_pwd(self):
        """Shared by bare :cd and :pwd: report the process's current
        directory, without letting a getcwd() failure (e.g. the directory
        was removed out from under a long-running session) surface as an
        opaque 'Command failed' rather than a normal status-bar error."""
        try:
            self.message = os.getcwd()
        except OSError as exc:
            self._set_error(str(exc))
            return
        self.message_is_error = False

    def _execute_cmd(self, raw: str) -> bool:
        """Execute an ex command.  Returns False to quit the editor."""
        cmd_preserve = raw.lstrip(":").lstrip()
        cmd = cmd_preserve.strip()
        self.message          = ""
        self.message_is_error = False

        if not cmd:
            return True

        def command_arg_from(text: str, *names: str) -> Optional[str]:
            for name in sorted(names, key=len, reverse=True):
                if (text.startswith(name)
                        and len(text) > len(name)
                        and text[len(name)].isspace()):
                    arg = text[len(name):].lstrip()
                    # Whitespace-only remainder means no argument was given;
                    # an empty filename would crash the file handlers.
                    return arg if arg else None
            return None

        def command_arg(*names: str) -> Optional[str]:
            return command_arg_from(cmd_preserve, *names)

        # Pure address / line reference
        addr = self._parse_line_ref(cmd)
        if addr is not None:
            self._move(addr, 0)
            self.cursor_col = self._first_nonblank()
            return True

        # Range with no command (e.g. :1,2 → move to last line of range).
        # An omitted endpoint (:,5 or :5,) defaults to the current line,
        # same as _parse_range_prefix's comma-splitting does -- without
        # that default here, ":,5" (jump to line 5 from the cursor) fell
        # through this whole dispatcher to "Unknown command".
        if "," in cmd:
            left, _, right = cmd.partition(",")
            r1 = self._parse_line_ref(left, self.cursor_row)
            r2 = self._parse_line_ref(right, self.cursor_row)
            if r1 is not None and r2 is not None:
                self._move(max(r1, r2), 0)
                self.cursor_col = self._first_nonblank()
                return True

        # :print / :p with optional address or range
        range_rows, print_rest = self._parse_range_prefix(cmd_preserve)
        print_rest = print_rest.strip()
        if range_rows is not None and print_rest in ("p", "print"):
            self._show_line(range_rows[1])
            return True

        if cmd in ("p", "print"):
            self._show_line(self.cursor_row)
            return True
        m = re.fullmatch(r"(.+?)\s*(?:p|print)", cmd)
        if m:
            addr = self._parse_line_ref(m.group(1))
            if addr is not None:
                self._show_line(addr)
                return True

        # :d / :delete / :N,Md — delete the addressed line(s) into the register
        if range_rows is not None and print_rest in ("d", "delete"):
            return self._delete_lines_to_register(*range_rows)
        if cmd in ("d", "delete"):
            return self._delete_lines_to_register(self.cursor_row, self.cursor_row)

        # :c / :*c / :Nc / :N,Mc — copy lines to the unnamed (and active) register.
        copy_range = self._parse_copy_cmd(cmd)
        if copy_range is not None:
            return self._copy_lines_to_register(*copy_range)

        if cmd.startswith("!"):
            self._run_shell_command(cmd[1:])
            return True

        # :sh / :shell [cmd] — run a command and show its output in a
        # scrollable read-only view, instead of inserting it into the buffer.
        arg = command_arg("sh", "shell")
        if arg is not None:
            self._run_shell_command_to_view(arg)
            return True
        if cmd in ("sh", "shell"):
            self._run_shell_command_to_view("")
            return True

        if cmd in ("h", "help"):
            self._open_help()
            return True

        if cmd == "hex":
            self._open_hex_view()
            return True

        if cmd == "le":
            self._open_line_endings_view()
            return True

        if cmd == "le-unix":
            self._set_default_line_endings("unix")
            self.message = "Default line endings: unix"
            return True

        if cmd == "le-win":
            self._set_default_line_endings("win")
            self.message = "Default line endings: windows"
            return True

        if cmd == "fb":
            self._open_file_browser()
            return True

        if cmd == "mdel":
            self._delete_all_marks()
            return True

        arg = command_arg("b64d")
        if arg is not None:
            self._load_base64_file(arg)
            return True

        arg = command_arg("b64e")
        if arg is not None:
            target = arg
            self._confirm_overwrite_or_run(
                target, lambda target=target: self._save_base64_file(target)
            )
            return True

        if cmd in ("buffers", "ls"):
            self._show_buffers()
            return True

        if cmd in ("rct", "recent"):
            self._show_recent_files()
            return True

        if cmd in ("fnc", "functions"):
            self._open_function_list()
            return True

        if cmd in ("bn", "bnext"):
            self._switch_buffer((self.current_buffer + 1) % len(self.buffers))
            return True

        if cmd in ("bp", "bprev", "bprevious"):
            self._switch_buffer((self.current_buffer - 1) % len(self.buffers))
            return True

        if cmd in ("bd", "bdelete"):
            self._delete_current_buffer(False)
            return True

        if cmd in ("bd!", "bdelete!"):
            self._delete_current_buffer(True)
            return True

        arg = command_arg("badd")
        if arg is not None:
            self._append_buffer(arg, switch=False)
            return True

        # :project name  :prj name  -- save current buffers as a named project
        # (if the section doesn't exist yet) or load one (if it does).
        if cmd in ("project", "prj"):
            self._set_error("Project name required")
            return True
        arg = command_arg("project", "prj")
        if arg is not None:
            self._cmd_project(arg)
            return True

        # :prj-del name  -- remove a named project section (no shortened form)
        if cmd == "prj-del":
            self._set_error("Project name required")
            return True
        arg = command_arg("prj-del")
        if arg is not None:
            self._cmd_project_del(arg)
            return True

        # :sessclr  -- clear the MRU file list from the session file, leaving
        # named project sections untouched.
        if cmd == "sessclr":
            self._cmd_sessclr()
            return True

        arg = command_arg("buffer", "b")
        if arg is not None:
            arg = arg.strip()
            if arg.isdigit():
                self._switch_buffer(int(arg) - 1)
            else:
                # Try exact filename match first, then substring match.
                exact = self._find_buffer_by_filename(arg)
                if exact is not None:
                    self._switch_buffer(exact)
                else:
                    matches = [
                        i for i, b in enumerate(self.buffers)
                        if b.filename and arg in b.filename
                    ]
                    if len(matches) == 1:
                        self._switch_buffer(matches[0])
                    elif len(matches) > 1:
                        self._set_error(f"More than one match for: {arg}")
                    else:
                        self._set_error(f"No buffer matching: {arg}")
            return True

        if cmd == "md5":
            token = hashlib.md5(uuid.uuid4().bytes).hexdigest()
            self._insert_text_at_cursor(token)
            return True

        if cmd == "guid":
            self._insert_text_at_cursor(str(uuid.uuid4()))
            return True

        if cmd == "pass":
            symbols = "!@#$%^&*()-_=+"
            required = [
                secrets.choice(string.ascii_uppercase),
                secrets.choice(string.ascii_lowercase),
                secrets.choice(string.digits),
                secrets.choice(symbols),
            ]
            alphabet = string.ascii_letters + string.digits + symbols
            required.extend(secrets.choice(alphabet) for _ in range(16))
            secrets.SystemRandom().shuffle(required)
            password = "".join(required)
            self._insert_text_at_cursor(password)
            return True

        if cmd == "secret":
            self._insert_text_at_cursor(secrets.token_urlsafe(32))
            return True

        if cmd == "dt-stamp":
            self._insert_text_at_cursor(datetime.now().strftime("%Y%m%d"))
            return True

        if cmd == "dt-utcstamp":
            self._insert_text_at_cursor(datetime.now(timezone.utc).strftime("%Y%m%d%H%M%S"))
            return True

        if cmd == "dt-dtstamp":
            self._insert_text_at_cursor(datetime.now().strftime("%Y%m%d%H%M%S"))
            return True

        if cmd == "dt-datetime":
            self._insert_text_at_cursor(datetime.now().strftime("%Y-%m-%d %H:%M:%S"))
            return True

        if cmd in ("lgt", "logtype"):
            if self.log_type:
                current = self.log_type
            elif self.log_type is None and self.filename and self.filename.lower().endswith(".log"):
                current = "generic (auto)"
            else:
                current = "off"
            self.message = f"logtype={current} (python|lnx_auth|http|flask|generic|off)"
            self.message_is_error = False
            return True
        arg = command_arg("lgt", "logtype")
        if arg is not None:
            arg = arg.strip().lower()
            if arg in ("off", "none", "clear"):
                self._set_log_type("")
            else:
                self._set_log_type(arg)
            return True

        # :q  :q!  :quit  :quit!
        if cmd in ("q", "quit"):
            if not self._check_unsaved_changes("quit"):
                return True
            return False
        if cmd in ("q!", "quit!"):
            return False

        range_rows, write_rest = self._parse_range_prefix(cmd_preserve)
        if range_rows is not None:
            arg = command_arg_from(write_rest, "w!", "write!")
            if arg is not None:
                target = arg
                if self.filename and self._paths_refer_to_same_file(target, self.filename):
                    self._set_error("Range write target must differ from current file")
                    return True
                self._write_line_range_to_file(range_rows[0], range_rows[1], target)
                return True
            arg = command_arg_from(write_rest, "w", "write")
            if arg is not None:
                target = arg
                if self.filename and self._paths_refer_to_same_file(target, self.filename):
                    self._set_error("Range write target must differ from current file")
                    return True
                self._confirm_overwrite_or_run(
                    target,
                    lambda start=range_rows[0], stop=range_rows[1], target=target: (
                        self._write_line_range_to_file(start, stop, target)
                    ),
                )
                return True
            if write_rest.strip() in ("w", "write", "w!", "write!"):
                self._set_error("Range write requires a file name")
                return True

        # :w  :write  :w!  :write!  :w <file>  :write <file>
        if cmd in ("w", "write", "w!", "write!"):
            self._save_file(force=cmd in ("w!", "write!"))
            return True

        # :wa  :wall  write every modified buffer
        if cmd in ("wa", "wall"):
            self._write_all_buffers()
            return True

        # :wo  write override (bypass the "unchanged" no-op skip and save anyway)
        if cmd in ("wo",):
            self._save_file(skip_unchanged_check=True)
            return True

        # :wnb  write, skipping the generation backup step
        if cmd in ("wnb",):
            self._save_file(skip_backup=True)
            return True
        arg = command_arg("w!", "write!")
        if arg is not None:
            target = arg
            if self.filename and self._paths_refer_to_same_file(target, self.filename):
                self._save_file(force=True)
                return True
            self._write_copy_without_renaming(target, self.filename)
            return True
        arg = command_arg("w", "write")
        if arg is not None:
            target = arg
            if self.filename and self._paths_refer_to_same_file(target, self.filename):
                self._save_file()
                return True
            self._confirm_overwrite_or_run(
                target,
                lambda target=target, original_filename=self.filename: (
                    self._write_copy_without_renaming(target, original_filename)
                ),
            )
            return True

        # :wq  :wq!  :x  :xit  :exit
        if cmd == "wq!":
            if self._save_file(force=True):
                return False
            return True
        if cmd == "wq":
            if self._save_file():
                if self._has_other_unsaved_changes():
                    self._set_error("No write since last change in another buffer (use :quit! to override)")
                    return True
                return False
            return True
        if cmd in ("x", "xit", "exit"):
            if self._current_buffer_is_modified():
                if not self._save_file():
                    return True
            if self._has_other_unsaved_changes():
                self._set_error("No write since last change in another buffer (use :quit! to override)")
                return True
            return False

        # :e  :edit  :e!  :edit!  :enew  :enew!
        if cmd in ("e", "edit"):
            if self._current_buffer_is_modified():
                self._set_error("No write since last change (use :edit! to override)")
                return True
            if self.filename:
                self._load_file(self.filename)
                self._reset_view()
            return True
        if cmd in ("e!", "edit!"):
            if self.filename:
                self._load_file(self.filename)
                self._reset_view()
            return True
        if cmd == "enew":
            if self._current_buffer_is_modified():
                self._set_error("No write since last change (use :enew! to override)")
                return True
            self._new_buffer()
            return True
        if cmd == "enew!":
            self._new_buffer(reuse_current=True)
            self._sync_current_buffer()
            return True
        arg = command_arg("e", "edit")
        if arg is not None:
            fname = arg
            if self.filename and self._paths_refer_to_same_file(fname, self.filename):
                if self._current_buffer_is_modified():
                    self._set_error("No write since last change (use :edit! to override)")
                    return True
                self._load_file(self.filename)
                self._reset_view()
                return True
            self._append_buffer(fname, switch=True, refresh_existing=True)
            return True
        arg = command_arg("e!", "edit!")
        if arg is not None:
            fname = arg
            if self.filename and self._paths_refer_to_same_file(fname, self.filename):
                self._load_file(self.filename)
                self._reset_view()
                return True
            self._replace_current_buffer_with_file(fname, force_reload_existing=True)
            return True

        # :rf reloads current file; :r <file> / :read <file> appends file contents.
        if cmd == "rf":
            return self._reload_current_file_preserve_position()
        read_text = cmd_preserve.lstrip()
        if read_text.startswith("0"):
            read_arg = command_arg_from(read_text[1:].lstrip(), "r", "read")
            if read_arg is not None:
                return self._read_file_after_row(read_arg, -1)
        range_rows, read_rest = self._parse_range_prefix(cmd_preserve)
        if range_rows is not None:
            read_arg = command_arg_from(read_rest, "r", "read")
            if read_arg is not None:
                return self._read_file_after_row(read_arg, range_rows[1])
        arg = command_arg("r", "read")
        if arg is not None:
            return self._read_file_after_row(arg, self.cursor_row)

        # :file / :f
        if cmd in ("f", "file"):
            flags = "[Modified]" if self._current_buffer_is_modified() else ""
            self.message = f'"{self._current_file_label()}" {len(self.lines)}L {flags}'.rstrip()
            return True
        arg = command_arg("f", "file")
        if arg is not None:
            normalized_name = self._normalize_path(arg)
            if self._find_buffer_by_filename(normalized_name, exclude_index=self.current_buffer) is not None:
                self._set_error(f"File already open in another buffer: {normalized_name}")
                return True
            self.filename = normalized_name
            self._refresh_modified()
            self._sync_current_buffer()
            self.message = f'"{self._current_file_label()}"'
            return True

        # :cd / :chdir  change the process working directory
        if cmd in ("cd", "chdir"):
            self._report_pwd()
            return True
        arg = command_arg("cd", "chdir")
        if arg is not None:
            target = os.path.abspath(os.path.expanduser(arg))
            if not self._validate_is_directory(target, arg):
                return True
            try:
                os.chdir(target)
            except OSError as exc:
                self._set_error(str(exc))
                return True
            self.message = self._safe_getcwd(fallback=target)
            self.message_is_error = False
            return True

        # :pwd  print the process working directory
        if cmd == "pwd":
            self._report_pwd()
            return True

        # :set
        if cmd == "set":
            # bare :set — show summary of all current settings
            nu  = "number" if self.show_line_numbers else "nonumber"
            et  = "expandtab" if self.expand_tab else "noexpandtab"
            bk  = "backup" if self.backup_enabled else "nobackup"
            vm  = "visualmarks" if self.visual_marks else "novisualmarks"
            mw  = "mdwrap" if self.markdown_wrap else "nomdwrap"
            self.message = (
                f"{nu}  tabstop={self.tab_stop}  shiftwidth={self.shift_width}"
                f"  undolevels={self.max_undo}  {et}  {bk}  {vm}  {mw}"
                f"  {'intellisense' if self.intellisense else 'nointellisense'}"
                f"  lnendings={self._default_line_ending_name()}"
                f"  scrolljump={self.vertical_scroll_jump}"
                f"  sidescrolljump={self.horizontal_scroll_jump}"
                f"  sessionfiles={self.session_max_files}"
                f"  linenumcolor={self.color_linenum}"
                f"  keywordcolor={self.color_keyword}  typecolor={self.color_type}  functioncolor={self.color_function}"
                f"  statusfg={self.color_status_fg}  statusbg={self.color_status_bg}"
                f"  bottomstatusfg={self.color_bottom_status_fg}  bottomstatusbg={self.color_bottom_status_bg}"
                f"  errorcolor={self.color_error}"
            )
            return True
        arg = command_arg("set")
        if arg is not None:
            opts = [opt for opt in arg.split() if opt]
            for opt in opts:
                err = self._apply_set_opt(opt)
                if err:
                    self._set_error(err)
                    break
            return True

        # :s, :%s, :.,$s, :&, :&&, :~
        sub = self._parse_substitute_cmd(cmd_preserve)
        if sub is not None:
            r1, r2, pattern, repl, flags, explicit_range = sub
            self._do_substitute(r1, r2, pattern, repl, flags,
                                explicit_range=explicit_range)
            return True
        if self.message_is_error:
            return True  # _parse_substitute_cmd already set a meaningful error

        # :g, :global, :v, :vglobal — run a sub-command on every line matching pattern
        glb = self._parse_global_cmd(cmd_preserve)
        if glb is not None:
            range_rows, pattern, sub_cmd, invert = glb
            return self._run_global_command(range_rows, pattern, sub_cmd, invert)
        if self.message_is_error:
            # Either _parse_global_cmd, or an earlier mark-address lookup
            # elsewhere in this chain, already reported a specific error.
            return True

        self._set_error(f"Unknown command: {cmd}")
        return True

    def _apply_split_replacement(self, r: int, new_lines: List[str]):
        """Replace self.lines[r] with new_lines, splitting into extra rows
        when a :s replacement contained an embedded newline. Marks and
        line_endings are kept in sync: all but the last resulting line
        become interior lines (default ending), and the last one inherits
        row r's original ending -- mirroring how _put splits a line.
        Line-ending entries must be inserted before self.lines grows, or
        _normalize_line_endings (called from _insert_line_ending_values)
        pads against the already-grown line count and desyncs the two
        parallel lists.
        """
        old_ending = self._line_ending_for_row(r)
        self._adjust_marks_for_line_replace(r, self.lines[r], "\n".join(new_lines))
        if len(new_lines) > 1:
            self._adjust_marks_for_line_insert(r + 1, len(new_lines) - 1)
            self._remap_marks_for_row_split(r, new_lines)
            self._normalize_line_endings()
            self.line_endings[r:r + 1] = (
                [self.default_line_ending] * (len(new_lines) - 1) + [old_ending]
            )
        self.lines[r:r + 1] = new_lines

    def _apply_split_lines(self, r: int, new_lines: List[str]):
        """Row/line-ending bookkeeping shared by every line-replace path,
        without the column-level mark adjustment that _apply_split_replacement
        does via _adjust_marks_for_line_replace. Callers that already know
        the exact edit spans (e.g. a multi-match :s///g pass) should adjust
        marks themselves via _adjust_marks_for_line_matches and call this
        directly instead -- _adjust_marks_for_line_replace's whole-line
        prefix/suffix diff can't distinguish several separate edits on one
        line from a single edit spanning all of them.
        """
        old_ending = self._line_ending_for_row(r)
        if len(new_lines) > 1:
            self._adjust_marks_for_line_insert(r + 1, len(new_lines) - 1)
            self._normalize_line_endings()
            self.line_endings[r:r + 1] = (
                [self.default_line_ending] * (len(new_lines) - 1) + [old_ending]
            )
        self.lines[r:r + 1] = new_lines

    def _do_substitute(self, r1: int, r2: int,
                       pattern: str, repl: str, flags: str,
                       explicit_range: bool = True):
        re_flags = re.IGNORECASE if "i" in flags else 0
        regex = self._compile_pattern(pattern, re_flags)
        if regex is None:
            self._set_error(f"Invalid pattern: {pattern}")
            return
        glob = "g" in flags
        if "c" in flags:
            self._do_substitute_confirm(r1, r2, regex, pattern, repl, flags, glob)
            return
        count = 0
        replacements: List[Tuple[int, List[str], List[Tuple[int, int, str]]]] = []
        original_cursor = (self.cursor_row, self.cursor_col)
        last_row = self.cursor_row
        try:
            for r in range(max(0, r1), min(len(self.lines), r2 + 1)):
                old = self.lines[r]
                if glob:
                    matches = list(regex.finditer(old))
                else:
                    first = regex.search(old)
                    matches = [first] if first else []
                if not matches:
                    continue
                count += len(matches)
                last_row = r
                parts: List[str] = []
                spans: List[Tuple[int, int, str]] = []
                last_end = 0
                for m in matches:
                    rep_text = m.expand(repl)
                    parts.append(old[last_end:m.start()])
                    parts.append(rep_text)
                    spans.append((m.start(), m.end(), rep_text))
                    last_end = m.end()
                parts.append(old[last_end:])
                new = "".join(parts)
                if new != old:
                    replacements.append((r, new.split("\n") if "\n" in new else [new], spans))
        except re.error as exc:
            self._set_error(f"Invalid replacement: {exc}")
            return
        if count:
            self.cursor_row, self.cursor_col = original_cursor
            if replacements:
                self._push_undo()
                line_offset = 0
                adjusted_last_row = last_row
                for orig_r, new_lines, spans in replacements:
                    r = orig_r + line_offset
                    self._adjust_marks_for_line_matches(r, spans)
                    self._apply_split_lines(r, new_lines)
                    self._remap_marks_for_row_split(r, new_lines)
                    if len(new_lines) > 1:
                        line_offset += len(new_lines) - 1
                    if orig_r == last_row:
                        adjusted_last_row = r + len(new_lines) - 1
                last_row = adjusted_last_row
                self._clamp_marks()
                self.modified = True
            self._force_redraw = True
            if explicit_range:
                self._set_last_change(
                    lambda r1=r1, r2=r2, pattern=pattern, repl=repl, flags=flags:
                    self._do_substitute(r1, r2, pattern, repl, flags))
            else:
                self._set_last_change(
                    lambda pattern=pattern, repl=repl, flags=flags:
                    self._do_substitute(self.cursor_row, self.cursor_row,
                                        pattern, repl, flags))
            self.cursor_row = last_row
            self._clamp_cursor()
            self.search_pattern = pattern
            self._search_literal = False
            self.last_sub_pattern = pattern
            self.last_sub_repl = repl
            self.last_sub_flags = flags
            self.message = f"{count} substitution{'s' if count != 1 else ''}"
        else:
            self._set_error("Pattern not found")

    def _do_substitute_confirm(self, r1: int, r2: int,
                               regex, pattern: str, repl: str, flags: str, glob: bool):
        """Interactive substitute with per-match confirm: y/n/a/q."""
        stdscr = getattr(self, "_stdscr", None)
        count = 0
        do_all = False
        undo_pushed = False
        last_row = self.cursor_row
        aborted = False

        # Match immutable original rows. Searching modified text can revisit
        # zero-width end matches forever or treat replacement-created rows as
        # new input. Map each original match onto the current edited tail.
        start_row = max(0, r1)
        original_rows = list(self.lines[start_row:min(len(self.lines), r2 + 1)])
        row_offset = 0
        try:
            for original_row, original in enumerate(original_rows, start_row):
                if aborted:
                    break
                r = original_row + row_offset
                col_offset = 0
                for m in regex.finditer(original):
                    start, end = m.start() + col_offset, m.end() + col_offset
                    replacement = m.expand(repl)
                    if do_all:
                        key = ord("y")
                    else:
                        self.cursor_row = r
                        self.cursor_col = start
                        self._sub_confirm_span = (r, start, end)
                        self._force_redraw = True
                        self.message = (
                            f'replace with "{replacement}"?  (y)es  (n)o  (a)ll  (q)uit'
                        )
                        self.message_is_error = False
                        if stdscr:
                            self.draw(stdscr)
                            try:
                                key = stdscr.get_wch()
                                if isinstance(key, str):
                                    key = ord(key)
                            except (curses.error, KeyboardInterrupt):
                                key = ord("q")
                        else:
                            key = ord("q")
                        self._sub_confirm_span = None

                    if key in (ord("q"), 27):
                        aborted = True
                        break
                    if key in (ord("y"), ord("a")):
                        do_all = do_all or key == ord("a")
                        line = self.lines[r]
                        new_full = line[:start] + replacement + line[end:]
                        new_parts = new_full.split("\n")
                        if new_full != line:
                            if not undo_pushed:
                                self._push_undo()
                                undo_pushed = True
                            self._adjust_marks_for_line_matches(
                                r, [(start, end, replacement)]
                            )
                            self._apply_split_lines(r, new_parts)
                            self._remap_marks_for_row_split(r, new_parts)
                        added_rows = len(new_parts) - 1
                        count += 1
                        last_row = r + added_rows
                        r += added_rows
                        row_offset += added_rows
                        if added_rows:
                            col_offset = len(replacement.rsplit("\n", 1)[-1]) - m.end()
                        else:
                            col_offset += len(replacement) - (m.end() - m.start())
                    if not glob:
                        break
        except re.error as exc:
            self._sub_confirm_span = None
            self._set_error(f"Invalid replacement: {exc}")
            return

        self._sub_confirm_span = None
        self.message = ""
        self.message_is_error = False
        self._force_redraw = True  # always redraw to clear any confirm highlight

        if count:
            if undo_pushed:
                self._clamp_marks()
                self.modified = True
            self.cursor_row = last_row
            self._clamp_cursor()
            self.search_pattern = pattern
            self._search_literal = False
            self.last_sub_pattern = pattern
            self.last_sub_repl = repl
            self.last_sub_flags = flags
            self.message = f"{count} substitution{'s' if count != 1 else ''}"
            # Dot-repeat re-runs the substitution silently (no confirm prompt).
            repeat_flags = "".join(f for f in flags if f != "c")
            self._set_last_change(
                lambda r1=r1, r2=r2, pattern=pattern, repl=repl, flags=repeat_flags:
                self._do_substitute(r1, r2, pattern, repl, flags)
            )
        else:
            self._set_error("Pattern not found" if not aborted else "Substitution aborted")

    # -----------------------------------------------------------------------
    # Normal-mode helpers
    # -----------------------------------------------------------------------

    def _count(self, default: int = 1) -> int:
        n = min(int(self._count_str), self.MAX_COUNT) if self._count_str else default
        self._count_str = ""
        return n

    def _begin_pending_op(self, op: str):
        self._pending_count = self._count()
        self._pending_op = op

    def _pending_counted(self) -> int:
        n = min(self._pending_count * self._count(), self.MAX_COUNT)
        self._pending_count = 1
        return n

    @staticmethod
    def _key_label(key) -> str:
        """Human-readable label for a key, for "unknown command" feedback."""
        if isinstance(key, str):
            return key
        if isinstance(key, int):
            if 32 <= key <= 126:
                return chr(key)
            try:
                return curses.keyname(key).decode("ascii", "replace")
            except (ValueError, curses.error):
                return f"<{key}>"
        return str(key)

    def _unknown_pending_command(self, prefix: str, key):
        """Report that a pending prefix (d/g/z/f/r/...) was cancelled because
        the following key didn't complete a known command, instead of just
        silently discarding that keystroke."""
        self._set_error(f"Unknown command: {prefix}{self._key_label(key)}")

    def _replace_chars(self, ch: str, cnt: int) -> bool:
        line = self.lines[self.cursor_row]
        c = self.cursor_col
        end = min(c + cnt, len(line))
        if c < len(line):
            replacement = ch * (end - c)
            if line[c:end] == replacement:
                return False
            new_line = line[:c] + replacement + line[end:]
            self._push_undo()
            self._adjust_marks_for_line_replace(self.cursor_row, line, new_line)
            self.lines[self.cursor_row] = new_line
            self._clamp_marks()
            self._move(self.cursor_row, end - 1)
            self.modified = True
            return True
        return False

    def _delete_chars(self, cnt: int):
        line = self.lines[self.cursor_row]
        c = self.cursor_col
        if c >= len(line):
            return
        self._push_undo()
        self._store_register([line[c:c + cnt]], False)
        self._adjust_marks_for_same_line_delete(self.cursor_row, c, min(c + cnt - 1, len(line) - 1))
        self.lines[self.cursor_row] = line[:c] + line[c + cnt:]
        self._clamp_marks()
        self._clamp_cursor()
        self.modified = True

    def _delete_chars_before(self, cnt: int):
        line = self.lines[self.cursor_row]
        c    = self.cursor_col
        take = min(c, cnt)
        if take <= 0:
            return
        self._push_undo()
        self._store_register([line[c - take:c]], False)
        self._adjust_marks_for_same_line_delete(self.cursor_row, c - take, c - 1)
        self.lines[self.cursor_row] = line[:c - take] + line[c:]
        self._clamp_marks()
        self.cursor_col = max(0, c - take)
        self.modified = True

    def _join_current_line(self, cnt: int):
        if self.cursor_row + 1 >= len(self.lines):
            return
        join_col = len(self.lines[self.cursor_row])
        self._push_undo()
        for _ in range(max(1, cnt - 1)):
            self._join_line(self.cursor_row)
        self._move(self.cursor_row, join_col)
        self.modified = True

    def _hash_lines_change(self, cnt: int) -> bool:
        r1 = self.cursor_row
        r2 = min(r1 + cnt - 1, len(self.lines) - 1)
        if not any(self.lines[r].strip() for r in range(r1, r2 + 1)):
            return False
        self._push_undo()
        self._insert_hash_lines(r1, cnt)
        self.modified = True
        self._move(r1, self._first_nonblank(r1))
        return True

    def _delete_hash_lines(self, cnt: int) -> bool:
        """Delete a leading '#' on `cnt` lines starting at the cursor row
        (used by the count-only N! command, e.g. `10!`). A line is only
        touched when '#' is its first non-blank character."""
        r1 = self.cursor_row
        r2 = min(r1 + cnt - 1, len(self.lines) - 1)
        targets = []
        for r in range(r1, r2 + 1):
            col = self._first_nonblank(r)
            old_line = self.lines[r]
            if col < len(old_line) and old_line[col] == "#":
                targets.append((r, col, old_line))
        if not targets:
            return False
        self._push_undo()
        for r, col, old_line in targets:
            new_line = old_line[:col] + old_line[col + 1:]
            self._adjust_marks_for_line_replace(r, old_line, new_line)
            self.lines[r] = new_line
        self._clamp_marks()
        self.modified = True
        self._move(r1, self._first_nonblank(r1))
        return True

    def _begin_substitute_chars(self, cnt: int):
        self._enter_insert()
        line = self.lines[self.cursor_row]
        c = self.cursor_col
        deleted = line[c:c + cnt]
        if deleted:
            self._store_register([deleted], False)
            self._adjust_marks_for_same_line_delete(self.cursor_row, c, min(c + cnt - 1, len(line) - 1))
            self.lines[self.cursor_row] = line[:c] + line[c + cnt:]
            self._clamp_marks()
            self.modified = True
        else:
            self._clear_unused_active_register()

    def _begin_substitute_lines(self, cnt: int):
        self._enter_insert()
        r1 = self.cursor_row
        r2 = min(len(self.lines) - 1, r1 + cnt - 1)
        if len(self.lines) == 1 and r1 == 0 and r2 == 0 and self.lines[0] == "":
            self._clear_unused_active_register()
            self.cursor_row = 0
            self.cursor_col = 0
            return
        replacement_ending = self._line_ending_for_row(r2)
        self._store_register(
            list(self.lines[r1:r2 + 1]),
            True,
            self._line_endings_for_range(r1, r2),
        )
        self._adjust_marks_for_line_delete(r1, r2)
        self._delete_line_endings(r1, r2 + 1)
        del self.lines[r1:r2 + 1]
        self._adjust_marks_for_line_insert(r1, 1)
        self._insert_line_endings(r1, 1, replacement_ending)
        self.lines.insert(r1, "")
        self._clamp_marks()
        self.cursor_row = r1
        self.cursor_col = 0
        self.modified = True
        self._force_redraw = True

    def _begin_visual_char_change_repeat(
        self, cnt: int, line_span: int = 0, end_col: Optional[int] = None
    ):
        if line_span <= 0:
            self._begin_substitute_chars(cnt)
            return

        self._enter_insert()
        r1 = self.cursor_row
        c1 = self.cursor_col
        r2 = min(len(self.lines) - 1, r1 + line_span)
        raw_c2 = c1 + cnt - 1 if end_col is None else end_col
        if r2 == r1:
            c2 = max(c1, min(raw_c2, max(0, len(self.lines[r2]) - 1)))
        else:
            c2 = min(raw_c2, max(0, len(self.lines[r2]) - 1))
        if not self._visual_selection_will_change(r1, c1, r2, c2, False):
            return
        deleted = self._delete_range(r1, c1, r2, c2, linewise=False)
        self._store_register(deleted, False)
        self.modified = True
        self._force_redraw = True

    def _repeat_visual_char_delete(
        self, cnt: int, line_span: int = 0, end_col: Optional[int] = None
    ):
        r1 = self.cursor_row
        c1 = self.cursor_col
        r2 = min(len(self.lines) - 1, r1 + max(0, line_span))
        raw_c2 = c1 + cnt - 1 if end_col is None else end_col
        if r2 == r1:
            c2 = max(c1, min(raw_c2, max(0, len(self.lines[r2]) - 1)))
        else:
            c2 = min(raw_c2, max(0, len(self.lines[r2]) - 1))
        if not self._visual_selection_will_change(r1, c1, r2, c2, False):
            return
        undo_state = self._capture_undo_state_for_edit()
        deleted = self._delete_range(r1, c1, r2, c2, linewise=False)
        self._append_undo_state(undo_state)
        self._store_register(deleted, False)
        self.modified = True
        self._force_redraw = True

    def _repeat_visual_toggle_case(
        self, cnt: int, line_span: int = 0, end_col: Optional[int] = None,
        linewise: bool = False
    ):
        # Mirrors _handle_visual's "~" branch: collect only the (row, new
        # text) pairs that actually differ within [r1, r2], the bounded
        # span of this one edit. The previous version copied the whole
        # buffer twice (`before`/`changed_lines`) and then re-scanned every
        # line to find which ones changed -- three O(n) passes per
        # dot-repeat regardless of file size, for an edit whose real cost
        # is proportional to line_span.
        r1 = self.cursor_row
        c1 = self.cursor_col
        r2 = min(len(self.lines) - 1, r1 + max(0, line_span))
        changes: List[Tuple[int, str]] = []
        if linewise:
            for r in range(r1, r2 + 1):
                new = self.lines[r].swapcase()
                if new != self.lines[r]:
                    changes.append((r, new))
        else:
            raw_c2 = c1 + cnt - 1 if end_col is None else end_col
            if r2 == r1:
                c2 = max(c1, min(raw_c2, max(0, len(self.lines[r2]) - 1)))
                ln = self.lines[r1]
                new = ln[:c1] + ln[c1:c2 + 1].swapcase() + ln[c2 + 1:]
                if new != ln:
                    changes.append((r1, new))
            else:
                c2 = min(raw_c2, max(0, len(self.lines[r2]) - 1))
                ln = self.lines[r1]
                new = ln[:c1] + ln[c1:].swapcase()
                if new != ln:
                    changes.append((r1, new))
                for r in range(r1 + 1, r2):
                    new = self.lines[r].swapcase()
                    if new != self.lines[r]:
                        changes.append((r, new))
                ln = self.lines[r2]
                new = ln[:c2 + 1].swapcase() + ln[c2 + 1:]
                if new != ln:
                    changes.append((r2, new))
        if changes:
            self._push_undo()
            for r, new in changes:
                self._adjust_marks_for_line_replace(r, self.lines[r], new)
                self.lines[r] = new
            self._clamp_marks()
            self.modified = True
            self._force_redraw = True

    def _begin_append_after_cursor(self):
        line = self.lines[self.cursor_row]
        self.cursor_col = min(self.cursor_col + 1, len(line))
        self._enter_insert()

    def _begin_insert_at_first_nonblank(self):
        self.cursor_col = self._first_nonblank()
        self._enter_insert()

    def _begin_append_to_line(self):
        self.cursor_col = len(self.lines[self.cursor_row])
        self._enter_insert()

    def _open_line_below(self):
        self._adjust_marks_for_line_insert(self.cursor_row + 1, 1)
        ending = "" if self.cursor_row + 1 == len(self.lines) else self.default_line_ending
        self._insert_line_endings(self.cursor_row + 1, 1, ending)
        self.lines.insert(self.cursor_row + 1, "")
        self._clamp_marks()
        self.cursor_row += 1
        self.cursor_col = 0
        self.modified = True
        self._force_redraw = True

    def _open_line_above(self):
        self._adjust_marks_for_line_insert(self.cursor_row, 1)
        self._insert_line_endings(self.cursor_row, 1)
        self.lines.insert(self.cursor_row, "")
        self._clamp_marks()
        self.cursor_col = 0
        self.modified = True
        self._force_redraw = True

    def _repeat_open_line_change(self, above: bool, repeat: int):
        if repeat <= 0:
            return
        self._push_undo()
        for _ in range(repeat):
            if above:
                self._open_line_above()
            else:
                self._open_line_below()

    def _begin_open_line_below(self):
        self._enter_insert()
        self._open_line_below()

    def _begin_open_line_above(self):
        self._enter_insert()
        self._open_line_above()

    def _toggle_case_range(self, cnt: int):
        line = self.lines[self.cursor_row]
        c    = self.cursor_col
        end  = min(c + cnt, len(line))
        if c < len(line):
            toggled = line[c:end].swapcase()
            if toggled != line[c:end]:
                self._push_undo()
                new_line = line[:c] + toggled + line[end:]
                self._adjust_marks_for_line_replace(self.cursor_row, line, new_line)
                self.lines[self.cursor_row] = new_line
                self._clamp_marks()
                self.modified = True
            self._move(self.cursor_row, min(end, len(self.lines[self.cursor_row]) - 1))

    def _begin_insert_session(self, mode: Mode):
        """Shared setup for entering INSERT or REPLACE: snapshot undo state
        and reset insert-replay bookkeeping. Caller sets self.mode and any
        mode-specific state afterward."""
        self._insert_pre_state = self._snapshot_undo_baseline()
        self._insert_pre_revision = self._content_revision
        self._insert_replay_keys = []
        self._insert_replay_mode = mode
        self._insert_replay_setup = None
        self._insert_empty_replay = None
        self._insert_repeat_count = 1
        self._block_insert = None

    def _enter_insert(self):
        self._begin_insert_session(Mode.INSERT)
        self._clear_intellisense_completion()
        self.mode = Mode.INSERT

    def _enter_replace(self):
        self._begin_insert_session(Mode.REPLACE)
        self._replace_overwritten = []
        self.mode = Mode.REPLACE

    def _repeat_insert_change(self, keys: List[Union[int, str]], mode: Mode,
                              setup: Optional[Callable[[], None]] = None,
                              repeat: int = 1):
        if not keys and setup is None:
            return
        for i in range(max(1, repeat)):
            if i == 0:
                if setup is not None:
                    setup()
                    if self.mode not in (Mode.INSERT, Mode.REPLACE):
                        # setup refused (e.g. a block A too wide to pad);
                        # don't replay the typed keys into NORMAL mode.
                        return
                else:
                    if mode == Mode.REPLACE:
                        self._enter_replace()
                    else:
                        self._enter_insert()
            else:
                # For o/O: open a new line for each additional repetition.
                # For i/a/I/A/R: just continue typing from the current position.
                if setup == self._begin_open_line_below:
                    self._open_line_below()
                elif setup == self._begin_open_line_above:
                    self._open_line_above()
                if mode == Mode.REPLACE:
                    # Each repeat replays its own key sequence from scratch;
                    # without this, a backspace recorded for this iteration
                    # could pop a stale entry left over from the previous
                    # one and restore the wrong character -- the same reset
                    # _enter_replace() gives the first iteration.
                    self._replace_overwritten = []
            for key in keys:
                if self.mode == Mode.REPLACE:
                    self._handle_replace_mode(key)
                else:
                    self._handle_insert(key)
        self._leave_insert()

    def _insert_state_changed(self) -> bool:
        """Return True if the buffer changed since the start of the insert session.
        Uses _content_revision as a fast path: if revision is unchanged and
        line_endings_trusted hasn't changed, the buffer is definitely clean.
        When revision changed, fall back to a full content comparison to handle
        the case where changes were made and then reverted within insert mode.
        """
        pre = self._insert_pre_state
        if pre is None:
            return False
        if self.line_endings_trusted != pre.line_endings_trusted:
            return True
        if self._content_revision == self._insert_pre_revision:
            return False
        return (
            list(self.lines) != pre.lines
            or list(self.line_endings) != pre.line_endings
        )

    def _leave_insert(self) -> None:
        block_cursor = self._finish_block_insert()
        original_repeat = self._insert_repeat_count
        if (
            self._insert_repeat_count > 1
            and not self._insert_replay_keys
            and self._insert_empty_replay is not None
            and self._insert_pre_state is not None
            and self._insert_state_changed()
        ):
            # Expand the count inline rather than delegating to
            # _insert_empty_replay: that helper calls _push_undo() itself
            # (needed when it's invoked standalone for dot-repeat), which
            # here would push a second, out-of-order undo snapshot on top
            # of the _insert_pre_state push below and corrupt undo/redo.
            for _ in range(self._insert_repeat_count - 1):
                if self._insert_replay_setup == self._begin_open_line_below:
                    self._open_line_below()
                elif self._insert_replay_setup == self._begin_open_line_above:
                    self._open_line_above()
        if self._insert_repeat_count > 1 and self._insert_replay_keys:
            keys = list(self._insert_replay_keys)
            repeat = self._insert_repeat_count
            for _ in range(repeat - 1):
                if self._insert_replay_setup == self._begin_open_line_below:
                    self._open_line_below()
                elif self._insert_replay_setup == self._begin_open_line_above:
                    self._open_line_above()
                for key in keys:
                    if self.mode == Mode.REPLACE:
                        self._handle_replace_mode(key)
                    else:
                        self._handle_insert(key)
            self._insert_replay_keys = keys
            self._insert_repeat_count = 1

        changed = False
        if self._insert_pre_state is not None:
            if self._insert_state_changed():
                changed = True
                self._append_undo_state(self._insert_pre_state)
            self._insert_pre_state = None
            self._refresh_modified()
        if changed and (
            self._insert_replay_keys
            or self._insert_replay_setup is not None
            or self._insert_empty_replay is not None
        ):
            keys = list(self._insert_replay_keys)
            mode = self._insert_replay_mode
            setup = self._insert_replay_setup
            empty_replay = self._insert_empty_replay
            repeat = original_repeat
            if not keys and empty_replay is not None:
                self._set_last_change(
                    lambda repeat=repeat, empty_replay=empty_replay:
                    empty_replay(repeat)
                )
            else:
                self._set_last_change(
                    lambda keys=keys, mode=mode, setup=setup, repeat=repeat:
                    self._repeat_insert_change(keys, mode, setup, repeat)
                )
        self._insert_replay_keys = []
        self._insert_replay_setup = None
        self._insert_empty_replay = None
        self._insert_repeat_count = 1
        self.mode = Mode.NORMAL
        if block_cursor is not None:
            self._block_rest_cursor(block_cursor[0], self._block_vcol(*block_cursor))
            return
        self.cursor_col = max(0, self.cursor_col - 1)
        self._clamp_cursor()

    def _put(self, after: bool, push_undo: bool = True):
        put_buffer, put_is_lines, put_line_endings = self._resolve_put_source()
        if self._put_source_is_empty(put_buffer, put_is_lines):
            self.message = "Nothing in register"
            self.message_is_error = True
            return
        if push_undo:
            self._push_undo()
        if put_is_lines:
            ins = self.cursor_row + (1 if after else 0)
            self._adjust_marks_for_line_insert(ins, len(put_buffer))
            inserted_endings = self._linewise_put_endings_for(put_buffer, put_line_endings, ins)
            if inserted_endings:
                self._insert_line_ending_values(ins, inserted_endings)
            else:
                self._insert_line_endings(ins, len(put_buffer))
            self.lines[ins:ins] = list(put_buffer)
            self._clamp_marks()
            self._move(ins, self._first_nonblank(ins))
        else:
            line = self.lines[self.cursor_row]
            col  = self.cursor_col + (1 if after else 0)
            col  = min(col, len(line))
            if len(put_buffer) == 1:
                text = put_buffer[0]
                self._adjust_marks_for_same_line_insert(self.cursor_row, col, len(text))
                self.lines[self.cursor_row] = line[:col] + text + line[col:]
                self._clamp_marks()
                self._move(self.cursor_row, col + len(text) - 1)
            else:
                prefix = line[:col]
                suffix = line[col:]
                inserted = (
                    [prefix + put_buffer[0]] +
                    list(put_buffer[1:-1]) +
                    [put_buffer[-1] + suffix]
                )
                start_row = self.cursor_row
                adjusted = {}
                extra_rows = len(inserted) - 1
                last_prefix_len = len(put_buffer[-1])
                for name, (mark_row, mark_col) in self._edit_positions().items():
                    if mark_row == start_row and mark_col >= col:
                        adjusted[name] = (start_row + extra_rows,
                                          last_prefix_len + mark_col - col)
                    elif mark_row > start_row:
                        adjusted[name] = (mark_row + extra_rows, mark_col)
                    else:
                        adjusted[name] = (mark_row, mark_col)
                self._set_edit_positions(adjusted)
                self.auto_marks = {
                    id_: cur + extra_rows if cur > start_row else cur
                    for id_, cur in self.auto_marks.items()
                }
                original_ending = self._line_ending_for_row(start_row)
                self._normalize_line_endings()
                self.lines[start_row:start_row + 1] = inserted
                self.line_endings[start_row:start_row + 1] = (
                    [self.default_line_ending] * (len(inserted) - 1) + [original_ending]
                )
                self._clamp_marks()
                self._move(start_row + len(inserted) - 1,
                           max(0, len(put_buffer[-1]) - 1))
        self.modified = True
        self._force_redraw = True
        self._set_last_change(
            lambda after=after, text=list(put_buffer), is_lines=put_is_lines,
                   endings=list(put_line_endings):
            self._repeat_put_text(after, text, is_lines, endings)
        )

    def _repeat_put_text(
        self, after: bool, text: List[str], is_lines: bool,
        line_endings: Optional[List[str]] = None
    ):
        saved_yank = list(self.yank_buffer)
        saved_is_lines = self.yank_is_lines
        saved_line_endings = list(self.yank_line_endings)
        saved_active = self.active_register
        try:
            self.active_register = None
            self.yank_buffer = list(text)
            self.yank_is_lines = is_lines
            self.yank_line_endings = list(line_endings or [])
            self._put(after)
        finally:
            self.yank_buffer = saved_yank
            self.yank_is_lines = saved_is_lines
            self.yank_line_endings = saved_line_endings
            self.active_register = saved_active

    @staticmethod
    def _repeat_charwise_payload(text: List[str], count: int) -> List[str]:
        if count <= 1:
            return list(text)
        if not text:
            return []
        repeated = list(text)
        for _ in range(count - 1):
            repeated[-1] += text[0]
            repeated.extend(text[1:])
        return repeated

    def _put_count(self, after: bool, cnt: int):
        put_buffer, put_is_lines, put_line_endings = self._resolve_put_source()
        if self._put_source_is_empty(put_buffer, put_is_lines):
            self.message = "Nothing in register"
            self.message_is_error = True
            return
        # A count multiplies the *entire* register contents, which can
        # itself be large (a big block yank) -- clamp the effective count
        # so cnt (already <= MAX_COUNT) can't combine with register size to
        # allocate an unbounded number of lines/chars and hang the editor.
        cnt = max(1, cnt)
        if put_is_lines:
            unit_size = max(1, len(put_buffer))
        else:
            unit_size = max(1, sum(len(s) for s in put_buffer))
        if unit_size * cnt > self.MAX_COUNT:
            cnt = max(1, self.MAX_COUNT // unit_size)
            self._set_error("Count too large for register contents; clamped")
        self._push_undo()
        if put_is_lines:
            inserted = list(put_buffer) * cnt
            ins = self.cursor_row + (1 if after else 0)
            self._adjust_marks_for_line_insert(ins, len(inserted))
            inserted_endings = self._linewise_put_endings_for(put_buffer, put_line_endings, ins, cnt)
            if inserted_endings:
                self._insert_line_ending_values(ins, inserted_endings)
            else:
                self._insert_line_endings(ins, len(inserted))
            self.lines[ins:ins] = inserted
            self._clamp_marks()
            last_ins = ins + len(put_buffer) * (cnt - 1)
            self._move(last_ins, self._first_nonblank(last_ins))
            self.modified = True
            self._force_redraw = True
            repeat_text = list(inserted)
            repeat_endings = list(inserted_endings)
        else:
            repeated = self._repeat_charwise_payload(put_buffer, max(1, cnt))
            saved_yank = list(self.yank_buffer)
            saved_is_lines = self.yank_is_lines
            saved_line_endings = list(self.yank_line_endings)
            try:
                self.yank_buffer = repeated
                self.yank_is_lines = False
                self.yank_line_endings = []
                self._put(after=after, push_undo=False)
            finally:
                self.yank_buffer = saved_yank
                self.yank_is_lines = saved_is_lines
                self.yank_line_endings = saved_line_endings
            repeat_text = list(repeated)
            repeat_endings = []
        self._set_last_change(
            lambda after=after, text=repeat_text, is_lines=put_is_lines,
                   endings=repeat_endings:
            self._repeat_put_text(after, text, is_lines, endings)
        )

    def _do_find(self, cmd: str, char: str, cnt: int, repeat: bool = False):
        line = self.lines[self.cursor_row]
        col  = self.cursor_col
        # Repeating 't' / 'T' starts at the resting position one off from the
        # previous target — bump past that target so ';' actually advances.
        if repeat and cmd == "t" and col + 1 < len(line) and line[col + 1] == char:
            col += 1
        elif repeat and cmd == "T" and col - 1 >= 0 and line[col - 1] == char:
            col -= 1
        for _ in range(cnt):
            if cmd == "f":
                idx = line.find(char, col + 1)
                if idx < 0:
                    return
                col = idx
            elif cmd == "F":
                idx = line.rfind(char, 0, col)
                if idx < 0:
                    return
                col = idx
            elif cmd == "t":
                idx = line.find(char, col + 1)
                if idx < 0:
                    return
                col = idx          # track char pos so next iter skips past it
            elif cmd == "T":
                idx = line.rfind(char, 0, col)
                if idx < 0:
                    return
                col = idx          # track char pos so next iter searches before it
        if cmd == "t":
            col -= 1
        elif cmd == "T":
            col += 1
        self._move(self.cursor_row, col)

    def _goto_matching(self):
        match = self._find_matching_bracket(self.cursor_row, self.cursor_col)
        if match is not None:
            self._move(*match)

    # -----------------------------------------------------------------------
    # Operator + motion resolver (used by d / y / c / > / <)
    # -----------------------------------------------------------------------

    def _resolve_operator(self, op: str, cnt: int, key: OperatorMotion) -> bool:
        """
        Called when an operator (d/y/c/>/<) is pending and we receive a motion key.
        Returns True (always — caller should return True).
        """
        op_start = (self.cursor_row, self.cursor_col)

        def apply(r1, c1, r2, c2, linewise):
            # Most motion branches below hand apply() whatever (start, end)
            # order the motion naturally produces -- forward motions end up
            # ascending, but backward ones (b/B, F/T, a "?" search) leave
            # (r2, c2) *before* (r1, c1). _delete_range() swaps internally,
            # which is why d/c already work for these; _get_char_range()
            # (the "y" path) and _indent_lines() do not, so yb/yB/yF</
            # yT</y?pattern silently yanked "" instead of the motion's text,
            # and >b/<b silently indented nothing. Normalize once here so
            # every op (and any future one) gets a consistent range
            # regardless of which direction the motion moved.
            if (r1, c1) > (r2, c2):
                r1, c1, r2, c2 = r2, c2, r1, c1
            did_change = False
            if op == "y":
                text = list(self.lines[r1:r2 + 1]) if linewise else self._get_char_range(r1, c1, r2, c2)
                endings = self._line_endings_for_range(r1, r2) if linewise else None
                self._store_register(text, linewise, endings)
                # Land at the normalized start of the yanked range, like
                # d/c/>/< and visual-mode y already do -- op_start is only
                # the range start for forward motions. Backward motions
                # (yb, yF{c}, yk, y{, ...) normalize (r1,c1) to the earlier
                # position above, and real vim moves the cursor there too;
                # charwise lands on (r1, c1), linewise only corrects the
                # row and keeps the original column (matches vim's y{motion}
                # behavior for yj/yk/y{/ygg).
                self._move(r1, c1 if not linewise else op_start[1])
                n = r2 - r1 + 1 if linewise else 1
                self.message = f"{n} line{'s' if n > 1 else ''} yanked" if linewise else "yanked"
            elif op in ("d", "c"):
                self._move(*op_start)
                if op == "c":
                    self._enter_insert()
                else:
                    undo_state = self._capture_undo_state_for_edit()
                change_row = r1
                change_ending = self._line_ending_for_row(r2) if linewise else "\n"
                deleted_endings = self._line_endings_for_range(r1, r2) if linewise else None
                # _delete_range only ever leaves the buffer untouched in two
                # cases: deleting the sole empty line (linewise) or a
                # same-line charwise range that starts at/past the line's
                # end (e.g. d$/c$ on an empty line). _visual_selection_will_
                # change() already encodes exactly that O(1) check (shared
                # with visual-mode d/x/c/s/S) -- reuse it here instead of a
                # second inline copy of the same predicate, so a future fix
                # to one can't silently leave the other behind.
                noop = not self._visual_selection_will_change(r1, c1, r2, c2, linewise)
                deleted = self._delete_range(r1, c1, r2, c2, linewise)
                delete_changed = not noop
                if delete_changed:
                    if op == "d":
                        self._append_undo_state(undo_state)
                    self._store_register(deleted, linewise, deleted_endings)
                    self.modified      = True
                    self._force_redraw = True
                    did_change = True
                elif op in ("d", "c"):
                    self._clear_unused_active_register()
                if op == "c":
                    if linewise and delete_changed:
                        self._insert_linewise_change_target(
                            change_row, len(deleted), change_ending
                        )
                    self._insert_replay_setup = (
                        lambda op=op, cnt=cnt, key=key:
                        self._resolve_operator(op, cnt, key)
                    )
            elif op in (">", "<"):
                self._move(*op_start)
                if not self._indent_lines_would_change(r1, r2 if linewise else r2, op == "<"):
                    return
                self._push_undo()
                changed = self._indent_lines(r1, r2 if linewise else r2, op == "<")
                self._move(r1, self._first_nonblank(min(r1, len(self.lines) - 1)))
                self.modified      = True
                self._force_redraw = True
                did_change = changed
            if op != "y" and did_change:
                self._set_last_change(lambda op=op, cnt=cnt, key=key:
                                      self._resolve_operator(op, cnt, key))
            self._clamp_marks()

        # --- same-key linewise (dd, yy, cc, >>, <<) ---
        same = {"d": ord("d"), "y": ord("y"), "c": ord("c"),
                ">": ord(">"), "<": ord("<")}
        if key == same.get(op, -1):
            r1 = self.cursor_row
            r2 = min(len(self.lines) - 1, r1 + cnt - 1)
            apply(r1, 0, r2, len(self.lines[r2]), True)
            return True

        # --- word / end-of-word motions ---
        if key in (ord("w"), ord("W"), ord("e"), ord("E"),
                   ord("b"), ord("B")):
            r1, c1 = self.cursor_row, self.cursor_col
            big = key in (ord("W"), ord("E"), ord("B"))
            if key in (ord("w"), ord("W")):
                row, col = self._word_forward_target(r1, c1, cnt, big)
                self._move(row, col)
            elif key in (ord("b"), ord("B")):
                self._word_backward(cnt, big)
                row, col = self.cursor_row, self.cursor_col
            else:
                self._word_end(cnt, big)
                row, col = self.cursor_row, self.cursor_col
            r2, c2 = row, col
            # For 'dw'/'yw': end col is one before new cursor (exclusive in the text)
            if key in (ord("w"), ord("W")) and op in ("d", "c", ">", "<", "y"):
                if op == "c" and r2 == r1:
                    line = self.lines[r1]
                    while c2 > c1 and c2 < len(line) and line[c2 - 1].isspace():
                        c2 -= 1
                    c2 = max(c1, c2 - 1)
                elif r2 > r1 and c2 == 0:
                    # Cross-line: next word starts at col 0 of the next line.
                    # Use c2=-1 so _get_char_range/_delete_range stops at end of r1
                    # (lines[r2][:-1+1] == lines[r2][:0] == "", and the join is clean).
                    c2 = -1
                else:
                    c2 = max(0, c2 - 1)
            apply(r1, c1, r2, c2, False)
            return True

        # --- text objects: iw / aw ---
        if isinstance(key, TextObjectMotion):
            bounds = self._resolve_text_object(key.around, key.ch)
            if bounds is not None:
                apply(*bounds)
            else:
                self._clear_unused_active_register()
            return True

        # --- f/F/t/T motion as operator target ---
        if isinstance(key, FindMotion):
            r1, c1 = self.cursor_row, self.cursor_col
            c2 = self._find_motion_target(key.cmd, key.ch, cnt)
            if c2 is not None and c2 != c1:
                apply(r1, c1, r1, c2, False)
            else:
                self._clear_unused_active_register()
            return True

        # --- search motion as operator target ---
        if isinstance(key, SearchMotion):
            r1, c1 = self.cursor_row, self.cursor_col
            target = self._search_motion_target(
                key.pattern, key.cmd != "?", literal=key.cmd == "\\")
            if target is not None:
                r2, c2 = target
                apply(r1, c1, r2, c2, False)
            else:
                self._clear_unused_active_register()
            return True

        # --- $ end of line ---
        if key == ord("$"):
            r1, c1 = self.cursor_row, self.cursor_col
            r2 = min(len(self.lines) - 1, self.cursor_row + cnt - 1)
            c2 = max(0, len(self.lines[r2]) - 1)
            apply(r1, c1, r2, c2, False)
            return True

        # --- 0 / ^ start of line ---
        if key in (ord("0"), ord("^")):
            c2 = self._first_nonblank() if key == ord("^") else 0
            c1 = self.cursor_col
            r  = self.cursor_row
            if c1 > c2:
                apply(r, c2, r, c1 - 1, False)
            elif c1 < c2:
                apply(r, c1, r, c2 - 1, False)
            else:
                self._clear_unused_active_register()
            return True

        # --- j / k  (linewise with motion) ---
        if key in (ord("j"), curses.KEY_DOWN):
            r1 = self.cursor_row
            r2 = min(len(self.lines) - 1, r1 + cnt)
            apply(r1, 0, r2, len(self.lines[r2]), True)
            return True
        if key in (ord("k"), curses.KEY_UP):
            r2 = self.cursor_row
            r1 = max(0, r2 - cnt)
            apply(r1, 0, r2, len(self.lines[r2]), True)
            return True

        # --- G / gg ---
        if key == ord("G") or (isinstance(key, GotoMotion) and not key.to_top):
            r1 = self.cursor_row
            if isinstance(key, GotoMotion) and key.had_count:
                r2 = max(0, min(cnt - 1, len(self.lines) - 1))
            else:
                r2 = len(self.lines) - 1
            apply(min(r1, r2), 0, max(r1, r2), len(self.lines[max(r1, r2)]), True)
            return True

        if isinstance(key, GotoMotion) and key.to_top:
            r1 = self.cursor_row
            if key.had_count:
                r2 = max(0, min(cnt - 1, len(self.lines) - 1))
            else:
                r2 = 0
            apply(min(r1, r2), 0, max(r1, r2), len(self.lines[max(r1, r2)]), True)
            return True

        # Unknown motion — cancel silently
        self._clear_unused_active_register()
        self._unknown_pending_command(op, key)
        return True

    # -----------------------------------------------------------------------
    # Normal-mode key handler
    # -----------------------------------------------------------------------

    def _handle_normal(self, key: int, height: int, width: int) -> bool:
        """Returns False to quit (ZZ / ZQ)."""
        text_rows = self._editor_text_rows(height)
        self._clamp_cursor()

        # --- Digit accumulation ---
        if isinstance(key, int) and ord("1") <= key <= ord("9") and not self._pending_op:
            if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                self._count_str += chr(key)
            return True
        if key == ord("0") and self._count_str and not self._pending_op:
            if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                self._count_str += "0"
            return True

        # --- Pending: r  (replace char) ---
        if self._pending_op == "r":
            self._pending_op = ""
            ch = self._text_input_char(key)
            if ch is not None:
                cnt = self._pending_counted()
                if self._replace_chars(ch, cnt):
                    self._set_last_change(lambda ch=ch, cnt=cnt: self._replace_chars(ch, cnt))
            else:
                self._pending_count = 1
                self._unknown_pending_command("r", key)
            self._count_str = ""
            return True

        # --- Pending: <space>  (double-space inserts a space at the cursor) ---
        if self._pending_op == " ":
            self._pending_op = ""
            self._count_str = ""
            if key == ord(" "):
                self._insert_text_at_cursor(" ")
                self._set_last_change(lambda: self._insert_text_at_cursor(" "))
            else:
                self._unknown_pending_command(" ", key)
            return True

        if self._pending_op == '"':
            self._pending_op = ""
            if isinstance(key, int) and 32 <= key <= 126:
                self.active_register = chr(key)
            else:
                self._unknown_pending_command('"', key)
            return True

        if self._pending_op == "m":
            self._pending_op = ""
            if isinstance(key, int) and 32 <= key <= 126:
                ch = chr(key)
                if ch == ".":
                    self._set_auto_mark()
                else:
                    self._set_mark(ch)
            else:
                self._unknown_pending_command("m", key)
            return True

        if self._pending_op in ("'", "`"):
            pending = self._pending_op
            self._pending_op = ""
            if isinstance(key, int) and 32 <= key <= 126:
                mark = chr(key)
                if mark == pending:
                    if self.last_jump is not None:
                        dest = self.last_jump
                        self.last_jump = (self.cursor_row, self.cursor_col)
                        self._move(*dest)
                elif mark == "[":
                    self._jump_auto_mark_prev()
                elif mark == "]":
                    self._jump_auto_mark_next()
                else:
                    self._jump_to_mark(mark, pending == "`")
            else:
                self._unknown_pending_command(pending, key)
            return True

        if self._pending_op == "Z":
            self._pending_op = ""
            if key == ord("Z"):    # ZZ — write if modified, then quit (:x)
                return self._execute_cmd(":x") is not False
            if key == ord("Q"):    # ZQ — quit without saving (:q!)
                return self._execute_cmd(":q!") is not False
            self._unknown_pending_command("Z", key)
            return True

        if self._pending_op.startswith("textobj:"):
            op, kind = self._pending_op.split(":")[1:]
            self._pending_op = ""
            ch = self._text_input_char(key)
            if ch is not None:
                self._resolve_operator(
                    op, self._pending_counted(), TextObjectMotion(around=kind == "a", ch=ch))
            else:
                self._count_str = ""
                self._pending_count = 1
                self._unknown_pending_command(f"{op}{kind}", key)
            return True

        if self._pending_op.startswith("findop:"):
            op, cmd = self._pending_op.split(":")[1:]
            self._pending_op = ""
            ch = self._text_input_char(key)
            if ch is not None:
                self._last_find_char = ch
                self._last_find_cmd  = cmd
                self._resolve_operator(
                    op, self._pending_counted(), FindMotion(cmd=cmd, ch=ch))
            else:
                self._count_str = ""
                self._pending_count = 1
                self._unknown_pending_command(f"{op}{cmd}", key)
            return True

        # --- Pending: g  ---
        if self._pending_op == "g":
            self._pending_op = ""
            had_count = bool(self._count_str)
            cnt = self._count()
            if key == ord("g"):
                self._move(cnt - 1 if had_count else 0, 0)
                self.cursor_col = self._first_nonblank()
            elif key == ord("j"):
                if self._markdown_wrap_enabled():
                    self._move_screen_vertical(cnt)
                else:
                    self._move(self.cursor_row + cnt, self.cursor_col)
            elif key == ord("k"):
                if self._markdown_wrap_enabled():
                    self._move_screen_vertical(-cnt)
                else:
                    self._move(self.cursor_row - cnt, self.cursor_col)
            else:
                self._unknown_pending_command("g", key)
            return True

        # --- Pending: z  ---
        if self._pending_op == "z":
            self._pending_op = ""
            if self._markdown_wrap_enabled() and key in (ord("z"), ord("t"), ord("b")):
                self._hide_cursor_for_scroll()
                text_w = self._wrap_text_width()
                screen_row = {ord("z"): text_rows // 2, ord("t"): 0, ord("b"): text_rows - 1}[key]
                self._set_wrapped_view_top(self._advance_wrapped_position(
                    self._wrapped_cursor_position(text_w), -screen_row, text_w
                ))
                return True
            if key == ord("z"):
                self._hide_cursor_for_scroll()
                self.top_line = max(0, self.cursor_row - text_rows // 2)
            elif key == ord("t"):
                self._hide_cursor_for_scroll()
                self.top_line = self.cursor_row
            elif key == ord("b"):
                self._hide_cursor_for_scroll()
                self.top_line = max(0, self.cursor_row - text_rows + 1)
            else:
                self._unknown_pending_command("z", key)
            return True

        # --- Pending: f / F / t / T ---
        if self._pending_op in ("f", "F", "t", "T"):
            cmd = self._pending_op
            self._pending_op = ""
            ch = self._text_input_char(key)
            if ch is not None:
                self._last_find_char = ch
                self._last_find_cmd  = cmd
                self._do_find(cmd, ch, self._count())
            else:
                self._count_str = ""
                self._unknown_pending_command(cmd, key)
            return True

        # --- Pending: d / y / c / > / < (second key of gg motion) ---
        if self._pending_op.startswith("opg:"):
            op = self._pending_op[4:]
            self._pending_op = ""
            had_motion_count = bool(self._count_str)
            cnt = self._pending_counted()
            if key == ord("g"):
                self._resolve_operator(op, cnt, GotoMotion(to_top=True, had_count=had_motion_count))
            else:
                self._unknown_pending_command(f"{op}g", key)
            return True

        # --- Pending: d / y / c / > / < ---
        if self._pending_op in ("d", "y", "c", ">", "<"):
            op = self._pending_op
            if isinstance(key, int) and ord("1") <= key <= ord("9"):
                if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                    self._count_str += chr(key)
                return True
            if key == ord("0") and self._count_str:
                if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                    self._count_str += "0"
                return True
            if key in (ord("i"), ord("a")):
                self._pending_op = f"textobj:{op}:{chr(key)}"
                return True
            if key in (ord("f"), ord("F"), ord("t"), ord("T")):
                self._pending_op = f"findop:{op}:{chr(key)}"
                return True
            if key in (ord("/"), ord("?"), ord("\\")):
                self._start_cmd_buf(chr(key), ("operator_search", (op, self._pending_counted(), chr(key))))
                self._pending_op = ""
                return True
            if key == ord("g"):
                self._pending_op = f"opg:{op}"
                return True
            self._pending_op = ""
            had_motion_count = bool(self._count_str)
            cnt = self._pending_counted()
            motion_key = (
                GotoMotion(to_top=False, had_count=had_motion_count)
                if key == ord("G") else key
            )
            self._resolve_operator(op, cnt, motion_key)
            return True

        # ---- Regular commands ----
        cnt = min(int(self._count_str), self.MAX_COUNT) if self._count_str else 1
        register_commands = {
            ord("x"), ord("X"), ord("D"), ord("C"), ord("s"), ord("S"),
            ord("d"), ord("y"), ord("c"), ord("Y"), ord("p"), ord("P"),
            ord("+"),
        }
        if self.active_register and key not in register_commands:
            self._clear_active_register()

        if self._handle_wrapped_screen_key(key, cnt):
            self._count_str = ""
            return True

        # Movement
        if key == ord("h") or key == curses.KEY_LEFT:
            self._count_str = ""
            self._move(self.cursor_row, self.cursor_col - cnt)

        elif key == ord("j") or key == curses.KEY_DOWN:
            self._count_str = ""
            self._move_vertical(self.cursor_row + cnt)

        elif key == ord("k") or key == curses.KEY_UP:
            self._count_str = ""
            self._move_vertical(self.cursor_row - cnt)

        elif key == ord("l") or key == curses.KEY_RIGHT:
            self._count_str = ""
            self._move(self.cursor_row, self.cursor_col + cnt)

        elif key == ord("w"):
            self._count_str = ""
            self._word_forward(cnt)

        elif key == ord("W"):
            self._count_str = ""
            self._word_forward(cnt, big=True)

        elif key == ord("b"):
            self._count_str = ""
            self._word_backward(cnt)

        elif key == ord("B"):
            self._count_str = ""
            self._word_backward(cnt, big=True)

        elif key == ord("e"):
            self._count_str = ""
            self._word_end(cnt)

        elif key == ord("E"):
            self._count_str = ""
            self._word_end(cnt, big=True)

        elif key == ord("0"):
            self._count_str = ""
            self._move(self.cursor_row, 0)

        elif key == ord("^"):
            self._count_str = ""
            self._move(self.cursor_row, self._caret_line_start_col())

        elif key == ord("$"):
            self._count_str = ""
            r = min(len(self.lines) - 1, self.cursor_row + cnt - 1)
            self._move(r, max(0, len(self.lines[r]) - 1))

        elif key == ord("G"):
            n = int(self._count_str) - 1 if self._count_str else len(self.lines) - 1
            self._count_str = ""
            self._move(n, 0)
            self.cursor_col = self._first_nonblank()

        elif key == ord("g"):
            self._pending_op = "g"

        elif key == ord(" "):
            self._pending_op = " "

        elif key == ord("H"):
            self._count_str = ""
            r = min(self.top_line + cnt - 1, len(self.lines) - 1)
            self._move(r, self._first_nonblank(r))

        elif key == ord("M"):
            self._count_str = ""
            r = min(self.top_line + text_rows // 2, len(self.lines) - 1)
            self._move(r, self._first_nonblank(r))

        elif key == ord("L"):
            self._count_str = ""
            r = min(self.top_line + text_rows - 1, len(self.lines) - 1)
            self._move(r, self._first_nonblank(r))

        elif key == ord("{"):
            self._count_str = ""
            self._para_backward(cnt)

        elif key == ord("}"):
            self._count_str = ""
            self._para_forward(cnt)

        # Scrolling
        elif key in (6, curses.KEY_NPAGE):    # Ctrl-F / PageDown
            self._count_str = ""
            self._hide_cursor_for_scroll()
            self.top_line = min(len(self.lines) - 1,
                                self.top_line + text_rows * cnt)
            self._move(self.top_line, 0)

        elif key in (2, curses.KEY_PPAGE):    # Ctrl-B / PageUp
            self._count_str = ""
            self._hide_cursor_for_scroll()
            self.top_line = max(0, self.top_line - text_rows * cnt)
            self._move(self.top_line, 0)

        elif key == 4:                         # Ctrl-D
            self._count_str = ""
            self._hide_cursor_for_scroll()
            half = max(1, text_rows // 2) * cnt
            self.top_line = min(len(self.lines) - 1, self.top_line + half)
            self._move_vertical(min(self.cursor_row + half, len(self.lines) - 1))

        elif key == 21:                        # Ctrl-U
            self._count_str = ""
            self._hide_cursor_for_scroll()
            half = max(1, text_rows // 2) * cnt
            self.top_line = max(0, self.top_line - half)
            self._move_vertical(max(self.cursor_row - half, 0))

        elif key == 5:                         # Ctrl-E scroll down
            self._count_str = ""
            self._hide_cursor_for_scroll()
            jump = max(1, self.vertical_scroll_jump) * cnt
            self.top_line = min(len(self.lines) - 1, self.top_line + jump)

        elif key == 25:                        # Ctrl-Y scroll up
            self._count_str = ""
            self._hide_cursor_for_scroll()
            jump = max(1, self.vertical_scroll_jump) * cnt
            self.top_line = max(0, self.top_line - jump)

        # f / F / t / T
        elif key == ord("f"):
            self._pending_op = "f"
        elif key == ord("F"):
            self._pending_op = "F"
        elif key == ord("t"):
            self._pending_op = "t"
        elif key == ord("T"):
            self._pending_op = "T"

        elif key == ord(";"):
            had_count = bool(self._count_str)
            self._count_str = ""
            if had_count:
                if self._hash_lines_change(cnt):
                    self._set_last_change(lambda cnt=cnt: self._hash_lines_change(cnt))
            elif self._last_find_char:
                self._do_find(self._last_find_cmd, self._last_find_char, cnt, repeat=True)

        elif key == ord(","):
            self._count_str = ""
            if self._last_find_char:
                rev = {"f": "F", "F": "f", "t": "T", "T": "t"}
                self._do_find(rev[self._last_find_cmd],
                              self._last_find_char, cnt, repeat=True)

        elif key == ord("!"):
            self._count_str = ""
            if self._delete_hash_lines(cnt):
                self._set_last_change(lambda cnt=cnt: self._delete_hash_lines(cnt))

        # --- Insert / Replace entry ---
        elif key == ord("i"):
            self._count_str = ""
            self._enter_insert()
            self._insert_repeat_count = cnt

        elif key == ord("a"):
            self._count_str = ""
            self._begin_append_after_cursor()
            self._insert_replay_setup = self._begin_append_after_cursor
            self._insert_repeat_count = cnt

        elif key == ord("I"):
            self._count_str = ""
            self._begin_insert_at_first_nonblank()
            self._insert_replay_setup = self._begin_insert_at_first_nonblank
            self._insert_repeat_count = cnt

        elif key == ord("A"):
            self._count_str = ""
            self._begin_append_to_line()
            self._insert_replay_setup = self._begin_append_to_line
            self._insert_repeat_count = cnt

        elif key == ord("o"):
            self._count_str = ""
            self._begin_open_line_below()
            self._insert_replay_setup = self._begin_open_line_below
            self._insert_empty_replay = lambda repeat: self._repeat_open_line_change(False, repeat)
            self._insert_repeat_count = cnt

        elif key == ord("O"):
            self._count_str = ""
            self._begin_open_line_above()
            self._insert_replay_setup = self._begin_open_line_above
            self._insert_empty_replay = lambda repeat: self._repeat_open_line_change(True, repeat)
            self._insert_repeat_count = cnt

        elif key == ord("r"):
            self._begin_pending_op("r")

        elif key == ord("R"):
            self._count_str = ""
            self._enter_replace()
            self._insert_repeat_count = cnt

        # --- Delete / Change shortcuts ---
        elif key == ord("x"):
            if self.cursor_col >= len(self.lines[self.cursor_row]):
                self._clear_unused_active_register()
                self._count_str = ""
                return True
            self._delete_chars(cnt)
            self._count_str = ""
            self._set_last_change(lambda cnt=cnt: self._delete_chars(cnt))

        elif key == ord("X"):
            if min(self.cursor_col, cnt) <= 0:
                self._clear_unused_active_register()
                self._count_str = ""
                return True
            self._delete_chars_before(cnt)
            self._count_str = ""
            self._set_last_change(lambda cnt=cnt: self._delete_chars_before(cnt))

        elif key == ord("D"):
            self._resolve_operator("d", cnt, ord("$"))
            self._count_str = ""

        elif key == ord("C"):
            self._resolve_operator("c", cnt, ord("$"))
            self._count_str = ""

        elif key == ord("s"):
            self._begin_substitute_chars(cnt)
            self._insert_replay_setup = lambda cnt=cnt: self._begin_substitute_chars(cnt)
            self._count_str = ""

        elif key == ord("S"):
            self._begin_substitute_lines(cnt)
            self._insert_replay_setup = lambda cnt=cnt: self._begin_substitute_lines(cnt)
            self._count_str = ""

        # --- Operators (set pending) ---
        elif key == ord("d"):
            self._begin_pending_op("d")

        elif key == ord("y"):
            self._begin_pending_op("y")

        elif key == ord("c"):
            self._begin_pending_op("c")

        # --- Yank whole lines ---
        elif key == ord("Y"):
            self._count_str    = ""
            r1 = self.cursor_row
            r2 = min(len(self.lines) - 1, r1 + cnt - 1)
            self._store_register(
                list(self.lines[r1:r2 + 1]),
                True,
                self._line_endings_for_range(r1, r2),
            )
            n = r2 - r1 + 1
            self.message = f"{n} line{'s' if n > 1 else ''} yanked"

        # --- Put / paste ---
        elif key == ord("p"):
            self._count_str = ""
            if self._pending_put_is_block():
                self._put_block(after=True, count=cnt)
            else:
                self._put_count(after=True, cnt=cnt)

        elif key == ord("P"):
            self._count_str = ""
            if self._pending_put_is_block():
                self._put_block(after=False, count=cnt)
            else:
                self._put_count(after=False, cnt=cnt)

        # --- Undo / redo ---
        elif key == ord("u"):
            self._count_str = ""
            for _ in range(cnt):
                if not self.undo_stack:
                    break
                self._undo()

        elif key == 18:    # Ctrl-R
            self._count_str = ""
            for _ in range(cnt):
                if not self.redo_stack:
                    break
                self._redo()

        # --- Join ---
        elif key == ord("J"):
            if self.cursor_row + 1 >= len(self.lines):
                self._count_str = ""
                return True
            join_col = len(self.lines[self.cursor_row])
            self._push_undo()
            for _ in range(max(1, cnt - 1)):
                self._join_line(self.cursor_row)
            self._move(self.cursor_row, join_col)
            self._count_str = ""
            self.modified = True
            self._set_last_change(lambda cnt=cnt: self._join_current_line(cnt))

        # --- Toggle case ---
        elif key == ord("~"):
            line = self.lines[self.cursor_row]
            c    = self.cursor_col
            end  = min(c + cnt, len(line))
            if c < len(line):
                # swapcase(), not a manual isupper()/upper() toggle -- the
                # manual form mishandles Unicode titlecase digraphs (e.g.
                # 'ǅ'.isupper() is False so it gets upper()'d to 'Ǆ' instead
                # of swapcase()'s 'ǅ' -> lower() -> 'ǆ'). Visual-mode '~'
                # and its dot-repeat already use swapcase(); match them so
                # normal- and visual-mode toggle-case agree on every input.
                toggled = line[c:end].swapcase()
                if toggled != line[c:end]:
                    self._push_undo()
                    old_line = self.lines[self.cursor_row]
                    new_line = line[:c] + toggled + line[end:]
                    self._adjust_marks_for_line_replace(self.cursor_row, old_line, new_line)
                    self.lines[self.cursor_row] = line[:c] + toggled + line[end:]
                    self._clamp_marks()
                    self.modified = True
                    self._set_last_change(lambda cnt=cnt: self._toggle_case_range(cnt))
                self._move(self.cursor_row, min(end, len(self.lines[self.cursor_row]) - 1))
            self._count_str = ""

        # --- Indent ---
        elif key == ord(">"):
            self._begin_pending_op(">")

        elif key == ord("<"):
            self._begin_pending_op("<")

        # --- Search ---
        elif key == ord("/"):
            self._count_str = ""
            self._start_cmd_buf("/")

        elif key == ord("?"):
            self._count_str = ""
            self._start_cmd_buf("?")

        elif key == ord("\\"):
            self._count_str = ""
            self._start_cmd_buf("\\")

        elif key == ord("n"):
            self._count_str = ""
            if self.search_pattern:
                self._search_repeated(self.search_pattern, self._search_forward, cnt,
                                      literal=self._search_literal)

        elif key == ord("N"):
            self._count_str = ""
            if self.search_pattern:
                self._search_repeated(self.search_pattern, not self._search_forward, cnt,
                                      literal=self._search_literal)

        elif key == ord("*"):
            self._count_str = ""
            self._search_word_under_cursor(forward=True)

        elif key == ord("+"):
            self._count_str = ""
            self._copy_word_under_cursor_to_register()

        elif key == ord("#"):
            self._count_str = ""
            self._search_word_under_cursor(forward=False)

        # --- Matching bracket ---
        elif key == ord("%"):
            self._count_str = ""
            self._goto_matching()

        # --- z commands ---
        elif key == ord("z"):
            self._count_str  = ""
            self._pending_op = "z"

        # --- Command line ---
        elif key == ord(":"):
            self._count_str = ""
            self._start_cmd_buf(":")

        elif key == curses.KEY_F1:
            self._count_str = ""
            self._pending_op = ""
            self._open_help()

        elif key == ord('"'):
            self._pending_op = '"'

        elif key == ord("m"):
            self._count_str = ""
            self._pending_op = "m"

        elif key == ord("'"):
            self._count_str = ""
            self._pending_op = "'"

        elif key == ord("`"):
            self._count_str = ""
            self._pending_op = "`"

        elif key == ord("."):
            self._count_str = ""
            self._repeat_last_change(cnt)

        # --- Save/quit (ZZ, ZQ) ---
        elif key == ord("Z"):
            self._count_str = ""
            self._pending_op = "Z"

        # --- Visual mode ---
        elif key == ord("v"):
            self._count_str = ""
            self.mode         = Mode.VISUAL
            self.visual_start = (self.cursor_row, self.cursor_col)

        elif key == ord("V"):
            self._count_str = ""
            self.mode         = Mode.VISUAL_LINE
            self.visual_start = (self.cursor_row, self.cursor_col)

        # --- File info (Ctrl-G) ---
        elif key == 7:
            self._count_str = ""
            pct  = int(100 * (self.cursor_row + 1) / len(self.lines))
            self.message = (
                f'"{self.filename or "[No Name]"}"'
                f' {len(self.lines)}L '
                f'-- {self.cursor_row + 1}/{len(self.lines)} ({pct}%) --'
            )

        # --- Home / End ---
        elif key == curses.KEY_HOME:
            self._count_str = ""
            self._move(self.cursor_row, 0)

        elif key == curses.KEY_END:
            self._count_str = ""
            self._move(self.cursor_row, max(0, len(self.lines[self.cursor_row]) - 1))

        elif key == 27:    # ESC
            self._count_str  = ""
            self._pending_op = ""
            self._pending_count = 1
            self.message     = ""

        else:
            self._count_str = ""

        self._clamp_marks()
        return True

    # -----------------------------------------------------------------------
    # Insert / Replace mode handlers
    # -----------------------------------------------------------------------

    @staticmethod
    def _is_completion_word_char(ch: str) -> bool:
        return ch == "_" or ch.isalnum()

    def _intellisense_word_bounds(self) -> Optional[Tuple[int, int, str]]:
        line = self.lines[self.cursor_row]
        cursor = max(0, min(self.cursor_col, len(line)))
        start = cursor
        while start > 0 and self._is_completion_word_char(line[start - 1]):
            start -= 1
        prefix = line[start:cursor]
        if not prefix:
            return None
        return start, cursor, prefix

    def _clear_intellisense_completion(self):
        self._intellisense_completion_matches = []
        self._intellisense_completion_index = 0
        self._intellisense_completion_prefix = ""
        self._intellisense_completion_complete = False

    def _line_completion_words(self, line: str) -> Tuple[str, ...]:
        if len(line) > self.MAX_INTELLISENSE_LINE_CHARS:
            # A pathologically long line (minified bundle, a single huge
            # JSON/log line) would otherwise cost one full regex scan per
            # keystroke with no bound -- skip it instead of blocking, and
            # skip the cache too so its text is never retained as a key.
            return ()
        cached = self._intellisense_line_words.get(line)
        if cached is None:
            cached = tuple(
                match.group(0)
                for match in self._RE_INTELLISENSE_WORD.finditer(line)
            )
            if len(self._intellisense_line_words) >= 4096:
                for key in list(self._intellisense_line_words)[:2048]:
                    del self._intellisense_line_words[key]
            self._intellisense_line_words[line] = cached
        return cached

    def _set_intellisense_completion_matches(
            self, matches: List[str], prefix: str, complete: bool = True):
        if (
                matches != self._intellisense_completion_matches
                or prefix != self._intellisense_completion_prefix):
            self._intellisense_completion_matches = matches
            self._intellisense_completion_index = 0
        elif matches:
            self._intellisense_completion_index = (
                self._intellisense_completion_index + 1
            ) % len(matches)
        self._intellisense_completion_prefix = prefix
        self._intellisense_completion_complete = complete
        self.message = ""
        self.message_is_error = False

    def _refresh_intellisense_completion(self):
        if not self.intellisense:
            self._clear_intellisense_completion()
            return
        bounds = self._intellisense_word_bounds()
        if bounds is None:
            self._clear_intellisense_completion()
            return
        start, end, prefix = bounds
        if (
                self._intellisense_completion_complete
                and self._intellisense_completion_prefix
                and prefix.startswith(self._intellisense_completion_prefix)
                and prefix != self._intellisense_completion_prefix):
            # Narrowing an exhaustive match set (self._intellisense_completion_complete)
            # to a longer prefix is itself exhaustive -- including when it narrows
            # down to nothing. Recording that empty-but-exhaustive result below
            # (instead of clearing it) is what lets this fast path keep firing on
            # every subsequent keystroke of a word that matches nothing elsewhere
            # in the buffer, instead of falling through to the full scan each time.
            matches = [
                word for word in self._intellisense_completion_matches
                if word.startswith(prefix) and word != prefix
            ]
            self._set_intellisense_completion_matches(matches, prefix)
            return

        current_row = self.cursor_row
        current_span = (start, end)
        matches: List[str] = []
        seen = set()
        complete = True
        for row, line in enumerate(self.lines):
            if row >= self.MAX_INTELLISENSE_SCAN_LINES:
                # Bound the per-keystroke cost on huge buffers: scanning
                # every line on every keystroke would otherwise make typing
                # cost grow linearly with file size with no cap.
                complete = False
                break
            if row == current_row:
                if len(line) > self.MAX_INTELLISENSE_LINE_CHARS:
                    # Same bound as _line_completion_words -- the cursor
                    # row bypasses that cache (it needs live match-span
                    # comparison), so it needs its own length gate too.
                    words = ()
                else:
                    # The word being typed is excluded by exact span, so the
                    # cursor row needs match positions and skips the word cache.
                    words = (
                        match.group(0)
                        for match in self._RE_INTELLISENSE_WORD.finditer(line)
                        if match.span() != current_span
                    )
            else:
                words = self._line_completion_words(line)
            for word in words:
                if not word.startswith(prefix) or word == prefix or word in seen:
                    continue
                seen.add(word)
                matches.append(word)
                if len(matches) >= self.MAX_INTELLISENSE_MATCHES:
                    complete = False
                    break
            if len(matches) >= self.MAX_INTELLISENSE_MATCHES:
                break

        matches.sort(key=lambda item: (item.lower(), item))
        # Record the result even when matches is empty -- see the comment
        # in the fast path above for why that matters for performance.
        self._set_intellisense_completion_matches(matches, prefix, complete)

    def _cycle_intellisense_completion(self) -> bool:
        if not self.intellisense:
            return False
        bounds = self._intellisense_word_bounds()
        if bounds is None:
            self._clear_intellisense_completion()
            return False
        _, _, prefix = bounds
        if (
                self._intellisense_completion_matches
                and prefix == self._intellisense_completion_prefix):
            self._set_intellisense_completion_matches(
                self._intellisense_completion_matches, prefix,
                self._intellisense_completion_complete
            )
            return True
        self._refresh_intellisense_completion()
        return bool(self._intellisense_completion_matches)

    def _accept_intellisense_completion(self) -> bool:
        if not self._intellisense_completion_matches:
            return False
        bounds = self._intellisense_word_bounds()
        if bounds is None:
            self._clear_intellisense_completion()
            return False
        _, _, prefix = bounds
        if prefix != self._intellisense_completion_prefix:
            self._clear_intellisense_completion()
            return False
        self._intellisense_completion_index = max(
            0,
            min(
                self._intellisense_completion_index,
                len(self._intellisense_completion_matches) - 1,
            ),
        )
        replacement = self._intellisense_completion_matches[self._intellisense_completion_index]
        suffix = replacement[len(prefix):]
        if not suffix:
            self._clear_intellisense_completion()
            return False
        self._insert_replay_keys.extend(suffix)
        self._insert_char(suffix)
        self._refresh_intellisense_completion()
        return True

    @staticmethod
    def _text_input_char(key) -> Optional[str]:
        if isinstance(key, str):
            return key if len(key) == 1 and key.isprintable() else None
        if not isinstance(key, int):
            return None
        if 32 <= key < getattr(curses, "KEY_MIN", 256):
            ch = chr(key)
            if ch.isprintable():
                return ch
        return None

    def _edit_line_key(self, text: str, cursor: int, key,
                       min_cursor: int = 0) -> Optional[Tuple[str, int]]:
        """Apply one editing key to a single-line input field. Returns the
        new (text, cursor), or None if the key is not a line-editing key."""
        if key == curses.KEY_LEFT:
            return text, max(min_cursor, cursor - 1)
        if key == curses.KEY_RIGHT:
            return text, min(len(text), cursor + 1)
        if key == curses.KEY_HOME:
            return text, min_cursor
        if key == curses.KEY_END:
            return text, len(text)
        if key == curses.KEY_DC:
            if cursor < len(text):
                return text[:cursor] + text[cursor + 1:], cursor
            return text, cursor
        if key in (curses.KEY_BACKSPACE, 127, 8):
            if cursor > min_cursor:
                return text[:cursor - 1] + text[cursor:], cursor - 1
            return text, cursor
        ch = self._text_input_char(key)
        if ch is not None:
            return text[:cursor] + ch + text[cursor:], cursor + 1
        return None

    def _handle_insert(self, key: Union[int, str]) -> bool:
        if key == 27:                                       # ESC
            self._clear_intellisense_completion()
            self._leave_insert()
        elif key == 1:                                      # Ctrl-A
            self._insert_replay_keys.append(key)
            self.cursor_col = 0
            self._refresh_intellisense_completion()
        elif key == 5:                                      # Ctrl-E
            self._insert_replay_keys.append(key)
            self.cursor_col = len(self.lines[self.cursor_row])
            self._refresh_intellisense_completion()
        elif key == 14:                                     # Ctrl-N
            self._cycle_intellisense_completion()
        elif key in (0, 25, 31):                            # Ctrl-Space / Ctrl-Y / Ctrl-/
            self._accept_intellisense_completion()
        elif key in (curses.KEY_BACKSPACE, 127, 8):
            self._insert_replay_keys.append(key)
            self._backspace()
            self._refresh_intellisense_completion()
        elif key in self._ENTER_KEYS:
            self._insert_replay_keys.append(key)
            self._newline()
            self._clear_intellisense_completion()
        elif key is self._PASTE_NEWLINE:
            self._insert_replay_keys.append(key)
            self._newline(auto_indent=False)
            self._clear_intellisense_completion()
        elif key == ord("\t"):
            if self._intellisense_completion_matches:
                self._accept_intellisense_completion()
            else:
                self._insert_replay_keys.append(key)
                self._insert_indent_at_cursor()
                self._clear_intellisense_completion()
        elif key == curses.KEY_BTAB:
            self._insert_replay_keys.append(key)
            self._detab_before_cursor()
            self._refresh_intellisense_completion()
        elif key == curses.KEY_LEFT:
            self._insert_replay_keys.append(key)
            self._move_insert_cursor(self.cursor_row, self.cursor_col - 1)
            self._refresh_intellisense_completion()
        elif key == curses.KEY_RIGHT:
            self._insert_replay_keys.append(key)
            self._move_insert_cursor(self.cursor_row, self.cursor_col + 1)
            self._refresh_intellisense_completion()
        elif key == curses.KEY_UP:
            self._insert_replay_keys.append(key)
            self._move_screen_vertical(-1)
            self._refresh_intellisense_completion()
        elif key == curses.KEY_DOWN:
            self._insert_replay_keys.append(key)
            self._move_screen_vertical(1)
            self._refresh_intellisense_completion()
        elif key == curses.KEY_HOME:
            self._insert_replay_keys.append(key)
            self.cursor_col = 0
            self._refresh_intellisense_completion()
        elif key == curses.KEY_END:
            self._insert_replay_keys.append(key)
            self.cursor_col = len(self.lines[self.cursor_row])
            self._refresh_intellisense_completion()
        elif key == curses.KEY_NPAGE:
            self._insert_replay_keys.append(key)
            self._page_move_keep_col(1)
            self._refresh_intellisense_completion()
        elif key == curses.KEY_PPAGE:
            self._insert_replay_keys.append(key)
            self._page_move_keep_col(-1)
            self._refresh_intellisense_completion()
        elif key in (curses.KEY_DC, 4):                      # Delete / Ctrl-D
            self._insert_replay_keys.append(key)
            self._delete_char_under_insert_cursor()
            self._refresh_intellisense_completion()
        elif isinstance(key, PasteSegment) or (isinstance(key, str) and len(key) > 1):
            # A pasted line segment recorded by _insert_pasted_text() for
            # `.`/count-repeat replay -- get_wch() itself never delivers a
            # multi-character string, so this can't collide with a real key.
            self._insert_replay_keys.append(key)
            self._insert_char(key)
            self._refresh_intellisense_completion()
        else:
            ch = self._text_input_char(key)
            if ch is not None:
                self._insert_replay_keys.append(key if isinstance(key, str) else ord(ch))
                self._insert_char(ch)
                self._refresh_intellisense_completion()
        self._clamp_marks()
        return True

    def _handle_replace_mode(self, key: Union[int, str]) -> bool:
        if key == 27:
            self._clear_intellisense_completion()
            self._leave_insert()
        elif key == 1:                                      # Ctrl-A
            self._insert_replay_keys.append(key)
            self.cursor_col = 0
        elif key == 5:                                      # Ctrl-E
            self._insert_replay_keys.append(key)
            self.cursor_col = len(self.lines[self.cursor_row])
        elif key == ord("\t"):
            self._insert_replay_keys.append(key)
            self._insert_indent_at_cursor()
        elif key == curses.KEY_BTAB:
            self._insert_replay_keys.append(key)
            self._detab_before_cursor()
        elif key in (curses.KEY_DC, 4):                      # Delete / Ctrl-D
            self._insert_replay_keys.append(key)
            self._delete_char_under_insert_cursor()
        elif key == curses.KEY_LEFT:
            self._insert_replay_keys.append(key)
            self._move_insert_cursor(self.cursor_row, self.cursor_col - 1)
        elif key == curses.KEY_RIGHT:
            self._insert_replay_keys.append(key)
            self._move_insert_cursor(self.cursor_row, self.cursor_col + 1)
        elif key == curses.KEY_UP:
            self._insert_replay_keys.append(key)
            self._move_screen_vertical(-1)
        elif key == curses.KEY_DOWN:
            self._insert_replay_keys.append(key)
            self._move_screen_vertical(1)
        elif key == curses.KEY_HOME:
            self._insert_replay_keys.append(key)
            self.cursor_col = 0
        elif key == curses.KEY_END:
            self._insert_replay_keys.append(key)
            self.cursor_col = len(self.lines[self.cursor_row])
        elif key == curses.KEY_NPAGE:
            self._insert_replay_keys.append(key)
            self._page_move_keep_col(1)
        elif key == curses.KEY_PPAGE:
            self._insert_replay_keys.append(key)
            self._page_move_keep_col(-1)
        elif key in self._ENTER_KEYS:
            self._insert_replay_keys.append(key)
            self._newline()
        elif key is self._PASTE_NEWLINE:
            self._insert_replay_keys.append(key)
            self._newline(auto_indent=False)
        elif key in (curses.KEY_BACKSPACE, 127, 8):
            self._insert_replay_keys.append(key)
            if (self._replace_overwritten and
                    self._replace_overwritten[-1][0] == self.cursor_row and
                    self._replace_overwritten[-1][1] == self.cursor_col - 1):
                row, col, original = self._replace_overwritten.pop()
                if original is None:
                    # This column was appended past the original end of line —
                    # nothing to restore, so undo the append instead.
                    self._adjust_marks_for_same_line_delete(row, col, col)
                    self._adjust_replace_overwritten_for_same_line_delete(row, col, col)
                    line = self.lines[row]
                    self.lines[row] = line[:col] + line[col + 1:]
                else:
                    line = self.lines[row]
                    self.lines[row] = line[:col] + original + line[col + 1:]
                self._clamp_marks()
                self.cursor_col = col
                self.modified = True
            else:
                self._backspace()
        elif isinstance(key, PasteSegment) or (isinstance(key, str) and len(key) > 1):
            # A pasted line segment recorded by _replace_pasted_text() for
            # `.`/count-repeat replay -- see the matching branch in
            # _handle_insert for why this can't collide with a real key.
            self._insert_replay_keys.append(key)
            for ch in key:
                self._replace_overwrite_char(ch)
        else:
            ch = self._text_input_char(key)
            if ch is not None:
                self._insert_replay_keys.append(key if isinstance(key, str) else ord(ch))
                self._replace_overwrite_char(ch)
        self._clamp_marks()
        return True

    def _insert_pasted_text(self, text: str) -> None:
        """Insert a bracketed paste's text at the cursor in INSERT mode.
        Unlike typing, line breaks in the pasted text never copy the
        current line's indent -- that's what keeps a multi-line paste from
        marching further right on every line the way it would if each
        embedded newline ran through the normal auto-indenting Enter path.

        Each line segment is recorded as a single multi-character replay
        entry (rather than one entry per character) so `.`/count-repeat
        replay it via the plain _insert_char() branch in _handle_insert --
        going character-by-character would run a literal pasted tab through
        the Tab key's indent-expansion branch instead of inserting it
        as-is, diverging from what the live paste just did."""
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        if not text:
            return
        segments = text.split("\n")
        for i, segment in enumerate(segments):
            if i > 0:
                self._insert_replay_keys.append(self._PASTE_NEWLINE)
                self._newline(auto_indent=False)
            if segment:
                self._insert_replay_keys.append(PasteSegment(segment))
                self._insert_char(segment)
        self._clear_intellisense_completion()
        self._clamp_marks()

    def _replace_overwrite_char(self, ch: str) -> None:
        """Overwrite the character at the cursor with `ch` -- Replace mode's
        core edit primitive, recording enough to undo it with backspace."""
        line = self.lines[self.cursor_row]
        c    = self.cursor_col
        if c < len(line):
            self._replace_overwritten.append((self.cursor_row, c, line[c]))
            self.lines[self.cursor_row] = line[:c] + ch + line[c + 1:]
        else:
            self._adjust_marks_for_line_replace(self.cursor_row, line, line + ch)
            self._replace_overwritten.append((self.cursor_row, c, None))
            self.lines[self.cursor_row] = line + ch
        self.cursor_col += 1
        self.modified = True

    def _replace_pasted_text(self, text: str) -> None:
        """REPLACE-mode counterpart to _insert_pasted_text: pasted characters
        overwrite existing text the same way typing does in Replace mode,
        and embedded newlines split the line without copying its indent."""
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        if not text:
            return
        segments = text.split("\n")
        for i, segment in enumerate(segments):
            if i > 0:
                self._insert_replay_keys.append(self._PASTE_NEWLINE)
                self._newline(auto_indent=False)
            if segment:
                self._insert_replay_keys.append(PasteSegment(segment))
                for ch in segment:
                    self._replace_overwrite_char(ch)
        self._clamp_marks()

    def _insert_indent_at_cursor(self):
        self._insert_char(self._indent_str())

    def _adjust_replace_overwritten_for_same_line_delete(self, row: int, c1: int, c2: int):
        """Keep Replace mode's backspace-undo entries pointed at the right
        columns when a same-line character delete (plain backspace, or
        Delete/Ctrl-D not at EOL) shifts the row -- mirrors the shift
        _adjust_marks_for_same_line_delete does for marks. Without this, a
        later backspace can match a stale entry by coincidence and splice
        the wrong original character into the wrong (already-shifted)
        column, corrupting the line."""
        removed = max(0, c2 - c1 + 1)
        if removed <= 0:
            return
        kept = []
        for r, c, orig in self._replace_overwritten:
            if r == row:
                if c > c2:
                    c -= removed
                elif c >= c1:
                    continue  # the tracked position itself was just deleted
            kept.append((r, c, orig))
        self._replace_overwritten = kept

    def _delete_char_under_insert_cursor(self) -> bool:
        line = self.lines[self.cursor_row]
        if self.cursor_col >= len(line):
            if self.cursor_row + 1 >= len(self.lines):
                return False
            joined_ending = self._line_ending_for_row(self.cursor_row + 1)
            next_row = self.cursor_row + 1
            head_len = len(line)
            adjusted = {}
            for name, (mark_row, mark_col) in self._edit_positions().items():
                if mark_row == next_row:
                    adjusted[name] = (self.cursor_row, head_len + mark_col)
                elif mark_row > next_row:
                    adjusted[name] = (mark_row - 1, mark_col)
                else:
                    adjusted[name] = (mark_row, mark_col)
            self._set_edit_positions(adjusted)
            self.auto_marks = {
                id_: self.cursor_row if cur == next_row else cur - 1 if cur > next_row else cur
                for id_, cur in self.auto_marks.items()
            }
            # Shift Replace mode's backspace-undo entries the same way, so
            # a later backspace can't match a stale entry against a row
            # that shifted into this index after the join.
            self._replace_overwritten = [
                (self.cursor_row, head_len + c, orig) if r == next_row
                else (r - 1, c, orig) if r > next_row
                else (r, c, orig)
                for (r, c, orig) in self._replace_overwritten
            ]
            self.lines[self.cursor_row] = line + self.lines[next_row]
            self._normalize_line_endings()
            self.line_endings[self.cursor_row] = joined_ending
            self._delete_line_endings(next_row, next_row + 1)
            del self.lines[next_row]
            self._clamp_marks()
            self.modified = True
            self._force_redraw = True
            return True
        self._adjust_marks_for_same_line_delete(
            self.cursor_row, self.cursor_col, self.cursor_col
        )
        self._adjust_replace_overwritten_for_same_line_delete(
            self.cursor_row, self.cursor_col, self.cursor_col
        )
        self.lines[self.cursor_row] = (
            line[:self.cursor_col] + line[self.cursor_col + 1:]
        )
        self._clamp_marks()
        self.modified = True
        return True

    def _detab_before_cursor(self) -> bool:
        if self.cursor_col <= 0:
            return False
        line = self.lines[self.cursor_row]
        before = line[:self.cursor_col]
        remove = 0
        indent = self._indent_str()
        if indent and before.endswith(indent):
            remove = len(indent)
        elif before.endswith("\t"):
            remove = 1
        else:
            limit = min(self.shift_width, self.cursor_col)
            while remove < limit and line[self.cursor_col - remove - 1] == " ":
                remove += 1
        if remove <= 0:
            return False
        start = self.cursor_col - remove
        self._adjust_marks_for_same_line_delete(self.cursor_row, start, self.cursor_col - 1)
        self._adjust_replace_overwritten_for_same_line_delete(self.cursor_row, start, self.cursor_col - 1)
        self.lines[self.cursor_row] = line[:start] + line[self.cursor_col:]
        self.cursor_col = start
        self._clamp_marks()
        self.modified = True
        return True

    def _backspace(self):
        if self.cursor_col > 0:
            line = self.lines[self.cursor_row]
            self._adjust_marks_for_same_line_delete(self.cursor_row, self.cursor_col - 1, self.cursor_col - 1)
            self._adjust_replace_overwritten_for_same_line_delete(
                self.cursor_row, self.cursor_col - 1, self.cursor_col - 1
            )
            self.lines[self.cursor_row] = (
                line[:self.cursor_col - 1] + line[self.cursor_col:]
            )
            self._clamp_marks()
            self.cursor_col -= 1
            self.modified = True
        elif self.cursor_row > 0:
            prev_len = len(self.lines[self.cursor_row - 1])
            join_row = self.cursor_row
            adjusted = {}
            for name, (mark_row, mark_col) in self._edit_positions().items():
                if mark_row == self.cursor_row:
                    adjusted[name] = (self.cursor_row - 1, prev_len + mark_col)
                elif mark_row > self.cursor_row:
                    adjusted[name] = (mark_row - 1, mark_col)
                else:
                    adjusted[name] = (mark_row, mark_col)
            self._set_edit_positions(adjusted)
            self.auto_marks = {
                id_: self.cursor_row - 1 if cur == self.cursor_row else cur - 1 if cur > self.cursor_row else cur
                for id_, cur in self.auto_marks.items()
            }
            # Shift Replace mode's backspace-undo entries the same way as
            # _delete_char_under_insert_cursor's join does, so a later
            # backspace can't match a stale entry against a row that
            # shifted into this index after the join.
            self._replace_overwritten = [
                (join_row - 1, prev_len + c, orig) if r == join_row
                else (r - 1, c, orig) if r > join_row
                else (r, c, orig)
                for (r, c, orig) in self._replace_overwritten
            ]
            joined_ending = self._line_ending_for_row(self.cursor_row)
            self.lines[self.cursor_row - 1] += self.lines[self.cursor_row]
            self._normalize_line_endings()
            self.line_endings[self.cursor_row - 1] = joined_ending
            self._delete_line_endings(self.cursor_row, self.cursor_row + 1)
            del self.lines[self.cursor_row]
            self._clamp_marks()
            self.cursor_row    -= 1
            self.cursor_col     = prev_len
            self.modified       = True
            self._force_redraw  = True

    def _newline(self, auto_indent: bool = True):
        line   = self.lines[self.cursor_row]
        split_row = self.cursor_row
        split_col = self.cursor_col
        if auto_indent:
            # Auto-indent: copy leading whitespace
            stripped = line.lstrip(" \t")
            indent = line[:len(line) - len(stripped)]
            inserted_indent = indent if split_col >= len(indent) else ""
        else:
            inserted_indent = ""
        adjusted = {}
        for name, (mark_row, mark_col) in self._edit_positions().items():
            if mark_row == split_row and mark_col >= split_col:
                adjusted[name] = (split_row + 1, len(inserted_indent) + mark_col - split_col)
            elif mark_row > split_row:
                adjusted[name] = (mark_row + 1, mark_col)
            else:
                adjusted[name] = (mark_row, mark_col)
        self._set_edit_positions(adjusted)
        self.auto_marks = {
            id_: cur + 1 if cur > split_row or (cur == split_row and split_col == 0) else cur
            for id_, cur in self.auto_marks.items()
        }
        # Replace mode's backspace-undo entries reference (row, col) pairs
        # the same way marks do, and need the same shift -- otherwise a
        # later backspace can match a stale entry against an unrelated row
        # that has since shifted into that index.
        self._replace_overwritten = [
            (split_row + 1, len(inserted_indent) + c - split_col, orig)
            if r == split_row and c >= split_col
            else (r + 1, c, orig) if r > split_row
            else (r, c, orig)
            for (r, c, orig) in self._replace_overwritten
        ]
        current_ending = self._line_ending_for_row(self.cursor_row)
        self._normalize_line_endings()
        self.line_endings[self.cursor_row:self.cursor_row + 1] = [
            self.default_line_ending,
            current_ending,
        ]
        self.lines[self.cursor_row] = line[:self.cursor_col]
        self.lines.insert(self.cursor_row + 1, inserted_indent + line[self.cursor_col:])
        self._clamp_marks()
        self.cursor_row    += 1
        self.cursor_col     = len(inserted_indent)
        self.modified       = True
        self._force_redraw  = True

    # -----------------------------------------------------------------------
    # Visual mode handler
    # -----------------------------------------------------------------------

    def _handle_visual(self, key: int) -> bool:
        r1, c1, r2, c2 = self._visual_bounds()
        result = self._handle_visual_key(key)
        if self.visual_marks and self.mode not in VISUAL_MODES:
            # Mirrors vim's v_'< / v_'> -- the bounds of whatever selection
            # was just exited (by an operation, ESC, or a mode switch into
            # INSERT via c/s/S) become marks '< and '>, regardless of which
            # key caused the exit.  Off unless :set visualmarks.
            self.marks["<"] = (r1, c1)
            self.marks[">"] = (r2, c2)
            self._sync_current_buffer()
        return result

    # Visual-block keys that don't move the cursor's column, so a `$` block
    # keeps stretching to each row's end across them.
    _BLOCK_EOL_KEEP_KEYS = frozenset((
        ord("j"), ord("k"), curses.KEY_DOWN, curses.KEY_UP,
        6, 2, 4, 21, curses.KEY_NPAGE, curses.KEY_PPAGE,
        ord('"'), ord("g"), ord("r"),
    ))

    def _handle_visual_key(self, key: int) -> bool:
        if self.mode != Mode.VISUAL_BLOCK:
            return self._handle_visual_key_inner(key)
        prev_pending = self._pending_op
        result = self._handle_visual_key_inner(key)
        if self.mode != Mode.VISUAL_BLOCK:
            return result
        if key == ord("$") and not prev_pending:
            self._block_to_eol = True
        elif isinstance(key, int) and ord("0") <= key <= ord("9") and self._count_str:
            pass
        elif not prev_pending and key in self._BLOCK_EOL_KEEP_KEYS:
            pass
        elif prev_pending == "g" and key in (ord("j"), ord("k")):
            pass
        elif prev_pending == '"':
            pass
        else:
            self._block_to_eol = False
        if self._block_to_eol:
            # Like vim's curswant=MAXCOL: ride the line end on j/k.
            line = self.lines[self.cursor_row]
            self.cursor_col = max(0, len(line) - 1)
        return result

    def _handle_visual_key_inner(self, key: int) -> bool:
        # Per-row redraw is driven by `_last_visual_rows` (set after each draw)
        # combined with the current visual range in the draw loop, so the
        # selection updates correctly without forcing a full-screen redraw on
        # every keystroke.

        if isinstance(key, int) and ord("1") <= key <= ord("9") and not self._pending_op:
            if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                self._count_str += chr(key)
            return True
        if key == ord("0") and self._count_str and not self._pending_op:
            if len(self._count_str) < self.MAX_COUNT_STR_LEN:
                self._count_str += "0"
            return True

        if self._pending_op == "g":
            self._pending_op = ""
            cnt = self._pending_count
            had_count = cnt != 1
            self._pending_count = 1
            if key == ord("g"):
                row = cnt - 1 if had_count else 0
                self._move(row, self._first_nonblank(max(0, min(len(self.lines) - 1, row))))
            elif key == ord("j"):
                self._move_screen_vertical(cnt)
            elif key == ord("k"):
                self._move_screen_vertical(-cnt)
            else:
                self._unknown_pending_command("g", key)
            return True

        if self._pending_op in ("f", "F", "t", "T"):
            cmd = self._pending_op
            self._pending_op = ""
            cnt = self._pending_count
            self._pending_count = 1
            ch = self._text_input_char(key)
            if ch is not None:
                self._last_find_char = ch
                self._last_find_cmd = cmd
                self._do_find(cmd, ch, cnt)
            else:
                self._unknown_pending_command(cmd, key)
            return True

        if self._pending_op == '"':
            self._pending_op = ""
            if isinstance(key, int) and 32 <= key <= 126:
                self.active_register = chr(key)
            else:
                self._unknown_pending_command('"', key)
            return True

        if self._pending_op == "r":
            self._pending_op = ""
            ch = self._text_input_char(key)
            if ch is not None:
                r1, r2, vl, vr = self._visual_block_bounds()
                self.mode = Mode.NORMAL
                self._block_transform(r1, r2, vl, vr, "r", ch)
            elif key == 27:
                self._clear_active_register()
                self.mode = Mode.NORMAL
            else:
                self._unknown_pending_command("r", key)
            if self.mode != Mode.VISUAL_BLOCK:
                self._clear_active_register()
            return True

        had_count = bool(self._count_str)
        cnt = self._count()

        if self._handle_wrapped_screen_key(key, cnt):
            return True

        # Movement
        if key == ord("h") or key == curses.KEY_LEFT:
            self._move(self.cursor_row, self.cursor_col - cnt)
        elif key == ord("j") or key == curses.KEY_DOWN:
            self._move_vertical(self.cursor_row + cnt)
        elif key == ord("k") or key == curses.KEY_UP:
            self._move_vertical(self.cursor_row - cnt)
        elif key == ord("l") or key == curses.KEY_RIGHT:
            self._move(self.cursor_row, self.cursor_col + cnt)
        elif key == ord("w"):
            self._word_forward(cnt)
        elif key == ord("W"):
            self._word_forward(cnt, big=True)
        elif key == ord("b"):
            self._word_backward(cnt)
        elif key == ord("B"):
            self._word_backward(cnt, big=True)
        elif key == ord("e"):
            self._word_end(cnt)
        elif key == ord("E"):
            self._word_end(cnt, big=True)
        elif key == ord("0"):
            self._move(self.cursor_row, 0)
        elif key == ord("^"):
            self._move(self.cursor_row, self._caret_line_start_col())
        elif key == ord("$"):
            row = min(len(self.lines) - 1, self.cursor_row + cnt - 1)
            self._move(row, max(0, len(self.lines[row]) - 1))
        elif key == ord("G"):
            row = cnt - 1 if had_count else len(self.lines) - 1
            self._move(row, self._first_nonblank(max(0, min(len(self.lines) - 1, row))))
        elif key == ord("g"):
            self._pending_count = cnt
            self._pending_op = "g"
        elif key == ord("{"):
            self._para_backward(cnt)
        elif key == ord("}"):
            self._para_forward(cnt)
        elif key == ord("H"):
            self._move(min(self.top_line + cnt - 1, len(self.lines) - 1), 0)
            self.cursor_col = self._first_nonblank()
        elif key == ord("M"):
            row = min(self.top_line + self._editor_text_rows(self._last_h) // 2, len(self.lines) - 1)
            self._move(row, self._first_nonblank(row))
        elif key == ord("L"):
            text_rows = self._editor_text_rows(self._last_h)
            row = min(self.top_line + text_rows - 1, len(self.lines) - 1)
            self._move(row, self._first_nonblank(row))
        elif key in (6, curses.KEY_NPAGE):
            self._hide_cursor_for_scroll()
            text_rows = self._editor_text_rows(self._last_h)
            self.top_line = min(len(self.lines) - 1, self.top_line + text_rows * cnt)
            self._move(min(self.cursor_row + text_rows * cnt, len(self.lines) - 1), self.cursor_col)
        elif key in (2, curses.KEY_PPAGE):
            self._hide_cursor_for_scroll()
            text_rows = self._editor_text_rows(self._last_h)
            self.top_line = max(0, self.top_line - text_rows * cnt)
            self._move(max(self.cursor_row - text_rows * cnt, 0), self.cursor_col)
        elif key == 4:
            self._hide_cursor_for_scroll()
            half = max(1, self._editor_text_rows(self._last_h) // 2) * cnt
            self.top_line = min(len(self.lines) - 1, self.top_line + half)
            self._move(min(self.cursor_row + half, len(self.lines) - 1), self.cursor_col)
        elif key == 21:
            self._hide_cursor_for_scroll()
            half = max(1, self._editor_text_rows(self._last_h) // 2) * cnt
            self.top_line = max(0, self.top_line - half)
            self._move(max(self.cursor_row - half, 0), self.cursor_col)
        elif key == ord("f"):
            self._pending_count = cnt
            self._pending_op = "f"
        elif key == ord("F"):
            self._pending_count = cnt
            self._pending_op = "F"
        elif key == ord("t"):
            self._pending_count = cnt
            self._pending_op = "t"
        elif key == ord("T"):
            self._pending_count = cnt
            self._pending_op = "T"
        elif key == ord(";"):
            if self._last_find_char:
                self._do_find(self._last_find_cmd, self._last_find_char, cnt, repeat=True)
        elif key == ord(","):
            if self._last_find_char:
                rev = {"f": "F", "F": "f", "t": "T", "T": "t"}
                self._do_find(rev[self._last_find_cmd], self._last_find_char, cnt, repeat=True)
        elif key == ord("n"):
            if self.search_pattern:
                self._search_repeated(self.search_pattern, self._search_forward, cnt,
                                      literal=self._search_literal)
        elif key == ord("N"):
            if self.search_pattern:
                self._search_repeated(self.search_pattern, not self._search_forward, cnt,
                                      literal=self._search_literal)
        elif key == ord("*"):
            self._search_word_under_cursor(forward=True)
        elif key == ord("#"):
            self._search_word_under_cursor(forward=False)
        elif key == ord("%"):
            self._goto_matching()
        elif key == ord("/"):
            self._start_cmd_buf("/")
        elif key == ord("?"):
            self._start_cmd_buf("?")
        elif key == ord("\\"):
            self._start_cmd_buf("\\")
        elif key == ord("o"):
            self._swap_visual_anchor()
        elif key == ord("O"):
            if self.mode == Mode.VISUAL_BLOCK:
                self._visual_block_swap_horizontal()
            else:
                self._swap_visual_anchor()
        elif key in (curses.KEY_HOME, 1):                   # Home / Ctrl-A
            self._move(self.cursor_row, 0)
        elif key in (curses.KEY_END, 5):                    # End / Ctrl-E
            self._move(self.cursor_row, max(0, len(self.lines[self.cursor_row]) - 1))

        # Operations
        elif self.mode == Mode.VISUAL_BLOCK and self._handle_visual_block_op(key):
            pass

        elif key in (ord("d"), ord("x")):
            r1, c1, r2, c2 = self._visual_bounds()
            linewise = (self.mode == Mode.VISUAL_LINE)
            if self._visual_selection_will_change(r1, c1, r2, c2, linewise):
                deleted_endings = self._line_endings_for_range(r1, r2) if linewise else None
                self._push_undo()
                deleted = self._delete_range(r1, c1, r2, c2, linewise)
                self._store_register(deleted, linewise, deleted_endings)
                self.modified      = True
                self._force_redraw = True
                if linewise:
                    nlines = r2 - r1 + 1
                    self._set_last_change(lambda n=nlines: self._resolve_operator("d", n, ord("d")))
                elif r1 == r2:
                    nchars = max(0, c2 - c1 + 1)
                    self._set_last_change(lambda n=nchars: self._delete_chars(n))
                else:
                    line_span = r2 - r1
                    self._set_last_change(
                        lambda span=line_span, end=c2:
                        self._repeat_visual_char_delete(0, span, end)
                    )
            self.mode = Mode.NORMAL

        elif key == ord("y"):
            r1, c1, r2, c2 = self._visual_bounds()
            linewise = (self.mode == Mode.VISUAL_LINE)
            text = list(self.lines[r1:r2 + 1]) if linewise else self._get_char_range(r1, c1, r2, c2)
            endings = self._line_endings_for_range(r1, r2) if linewise else None
            self._store_register(text, linewise, endings)
            self.message = "yanked"
            dest_col = self._first_nonblank(r1) if linewise else c1
            self._move(r1, dest_col)
            self.mode = Mode.NORMAL

        elif key in (ord("c"), ord("s"), ord("S")):
            # s is vim's synonym for c; S changes whole lines regardless of
            # the current visual flavour.
            r1, c1, r2, c2 = self._visual_bounds()
            linewise = (self.mode == Mode.VISUAL_LINE) or key == ord("S")
            self._enter_insert()
            change_row = r1
            change_ending = self._line_ending_for_row(r2) if linewise else "\n"
            deleted_endings = self._line_endings_for_range(r1, r2) if linewise else None
            will_change = self._visual_selection_will_change(r1, c1, r2, c2, linewise)
            if will_change:
                deleted = self._delete_range(r1, c1, r2, c2, linewise)
                self._store_register(deleted, linewise, deleted_endings)
                if linewise:
                    self._insert_linewise_change_target(change_row, len(deleted), change_ending)
                    nlines = r2 - r1 + 1
                    self._insert_replay_setup = lambda n=nlines: self._begin_substitute_lines(n)
                elif r1 == r2:
                    nchars = max(0, c2 - c1 + 1)
                    self._insert_replay_setup = lambda n=nchars: self._begin_visual_char_change_repeat(n)
                else:
                    line_span = r2 - r1
                    self._insert_replay_setup = (
                        lambda span=line_span, end=c2:
                        self._begin_visual_char_change_repeat(0, span, end)
                    )
                self.modified      = True
                self._force_redraw = True
            else:
                self._insert_replay_setup = lambda: self._enter_insert()

        elif key == ord(">"):
            r1, c1, r2, c2 = self._visual_bounds()
            if r1 <= r2 and len(self.lines) > 0:
                # Indent always changes a non-empty range.
                indent_cnt = self._clamped_indent_repeat_count(r1, r2, cnt)
                self._push_undo()
                for _ in range(indent_cnt):
                    self._indent_lines(r1, r2, False)
                self._move(r1, self._first_nonblank(r1))
                self.modified      = True
                self._force_redraw = True
                nlines = r2 - r1 + 1
                self._set_last_change(
                    lambda n=nlines, c=indent_cnt: self._repeat_visual_indent(n, c, False)
                )
            self.mode = Mode.NORMAL

        elif key == ord("<"):
            r1, c1, r2, c2 = self._visual_bounds()
            # Snapshot first, mutate, then commit the undo only if any of the
            # cnt passes actually dedented something. Avoids the two-pass
            # `_indent_lines_would_change` + `_indent_lines` walk.
            undo_state = self._capture_undo_state_for_edit()
            changed = False
            for _ in range(cnt):
                if self._indent_lines(r1, r2, True):
                    changed = True
                else:
                    break
            if changed:
                self._append_undo_state(undo_state)
                self._move(r1, self._first_nonblank(r1))
                self.modified      = True
                self._force_redraw = True
                nlines = r2 - r1 + 1
                self._set_last_change(
                    lambda n=nlines, c=cnt: self._repeat_visual_indent(n, c, True)
                )
            self.mode = Mode.NORMAL

        elif key == ord("~"):
            r1, c1, r2, c2 = self._visual_bounds()
            linewise = (self.mode == Mode.VISUAL_LINE)
            changes: List[Tuple[int, str]] = []  # (row, new_text)
            if linewise:
                for r in range(r1, r2 + 1):
                    new = self.lines[r].swapcase()
                    if new != self.lines[r]:
                        changes.append((r, new))
            elif r1 == r2:
                ln = self.lines[r1]
                new = ln[:c1] + ln[c1:c2 + 1].swapcase() + ln[c2 + 1:]
                if new != ln:
                    changes.append((r1, new))
            else:
                ln = self.lines[r1]
                new = ln[:c1] + ln[c1:].swapcase()
                if new != ln:
                    changes.append((r1, new))
                for r in range(r1 + 1, r2):
                    new = self.lines[r].swapcase()
                    if new != self.lines[r]:
                        changes.append((r, new))
                ln = self.lines[r2]
                new = ln[:c2 + 1].swapcase() + ln[c2 + 1:]
                if new != ln:
                    changes.append((r2, new))
            if changes:
                self._push_undo()
                for r, new in changes:
                    self._adjust_marks_for_line_replace(r, self.lines[r], new)
                    self.lines[r] = new
                self._clamp_marks()
                self.modified      = True
                self._force_redraw = True
                if linewise:
                    self._set_last_change(
                        lambda span=r2 - r1:
                        self._repeat_visual_toggle_case(0, span, linewise=True)
                    )
                elif r1 == r2:
                    self._set_last_change(
                        lambda cnt=max(0, c2 - c1 + 1):
                        self._toggle_case_range(cnt)
                    )
                else:
                    self._set_last_change(
                        lambda span=r2 - r1, end=c2:
                        self._repeat_visual_toggle_case(0, span, end)
                    )
            self.mode          = Mode.NORMAL

        elif key == ord("J"):
            r1, c1, r2, c2 = self._visual_bounds()
            # A single-line selection still joins with the following line,
            # same as plain normal-mode J -- only refuse when there's no
            # next line to join with at all (r1 is the last line and the
            # selection doesn't already span past it).
            if r1 != r2 or r1 + 1 < len(self.lines):
                joins = max(r2 - r1, 1)
                self._push_undo()
                for _ in range(joins):
                    self._join_line(r1)
                self._move(r1, self._first_nonblank(min(r1, len(self.lines) - 1)))
                self.modified      = True
                self._force_redraw = True
                self._set_last_change(lambda cnt=joins + 1: self._join_current_line(cnt))
            self.mode = Mode.NORMAL

        elif key == ord("p"):
            self._replace_visual_selection(after=False, exchange=True)

        elif key == ord("P"):
            self._replace_visual_selection(after=False, exchange=False)

        # Toggle between VISUAL / VISUAL_LINE
        elif key == ord("v"):
            if self.mode == Mode.VISUAL:
                self._clear_active_register()
                self.mode = Mode.NORMAL
            else:
                self.mode = Mode.VISUAL

        elif key == ord("V"):
            if self.mode == Mode.VISUAL_LINE:
                self._clear_active_register()
                self.mode = Mode.NORMAL
            else:
                self.mode = Mode.VISUAL_LINE

        elif key in self._BLOCK_VISUAL_KEYS:    # Ctrl-V / Ctrl-X
            if self.mode == Mode.VISUAL_BLOCK:
                self._clear_active_register()
                self.mode = Mode.NORMAL
            else:
                self.mode = Mode.VISUAL_BLOCK
                self._block_to_eol = False

        elif key == ord('"'):
            self._pending_op = '"'

        elif key == ord(":"):
            # Prefill an ex range covering the selection (vim's :'<,'>).
            r1, _, r2, _ = self._visual_bounds()
            self.mode = Mode.NORMAL
            self._start_cmd_buf(f":{r1 + 1},{r2 + 1}")

        elif key == 27:    # ESC
            self._count_str = ""
            self._pending_op = ""
            self._clear_active_register()
            self.mode    = Mode.NORMAL
            self.message = ""

        else:
            self._count_str = ""
            self._pending_op = ""

        # An armed "<letter> register is meant to persist through selection-
        # extending movement (see test_visual_register_prefix_ignored_for_
        # movement) but must not outlive the visual selection it was armed
        # for. y/d/x/c/s/S/p/P already clear it themselves via
        # _store_register()/_put()/_replace_visual_selection() -- except
        # d/x/c/s/S skip that call entirely when the selection turns out to
        # be a no-op (e.g. selecting an empty line), and >/</~/J/: never
        # touch it at all. Any of those leaves the register armed after
        # this key has dropped us out of visual mode, silently hijacking
        # whatever unrelated register-sensitive command (p, y, d, ...) the
        # user happens to press next in NORMAL mode. Catch every such exit
        # here instead of chasing it branch by branch.
        if self.active_register and self.mode not in VISUAL_MODES:
            self._clear_active_register()

        self._clamp_marks()
        return True

    def _handle_visual_block_op(self, key: int) -> bool:
        """Operators with a blockwise meaning in Ctrl-V mode. Returns False
        for keys the shared visual handling covers (> < J : and modes)."""
        if key not in (ord("d"), ord("x"), ord("y"), ord("c"), ord("s"),
                       ord("I"), ord("A"), ord("r"), ord("~"), ord("p"), ord("P")):
            return False
        if key == ord("r"):
            self._pending_op = "r"
            return True
        r1, r2, vl, vr = self._visual_block_bounds()
        if key in (ord("p"), ord("P")):
            self._replace_visual_block(exchange=key == ord("p"))
            return True
        self.mode = Mode.NORMAL
        if key in (ord("d"), ord("x")):
            self._block_delete(r1, r2, vl, vr)
        elif key == ord("y"):
            self._block_yank(r1, r2, vl, vr)
        elif key == ord("~"):
            self._block_transform(r1, r2, vl, vr, "~")
        else:
            kind = {ord("I"): "I", ord("A"): "A"}.get(key, "c")
            self._block_begin_insert(kind, r1, r2, vl, vr)
        return True

    # -----------------------------------------------------------------------
    # Command-buffer handler  (: / ?)
    # -----------------------------------------------------------------------

    _FILENAME_EX_COMMANDS = {
        "b64d", "b64e", "badd",
        "e", "edit", "file", "f",
        "r", "read",
        "w", "write",
        "cd", "chdir",
    }
    _FILENAME_BANG_EX_COMMANDS = {"e", "edit", "w", "write"}
    _DIR_ONLY_EX_COMMANDS = {"cd", "chdir"}

    _SET_OPTIONS: List[str] = sorted([
        "expandtab", "noexpandtab",
        "backup", "nobackup", "invbackup",
        "visualmarks", "novisualmarks", "invvisualmarks",
        "number", "nonumber", "nu", "nonu", "invnumber", "invnu",
        "mdwrap", "nomdwrap", "invmdwrap",
        "intellisense", "nointellisense", "autocomplete", "noautocomplete",
        "tabstop=", "ts=",
        "shiftwidth=", "sw=",
        "undolevels=", "ul=",
        "lnendings=", "lineendings=",
        "scrolljump=", "sj=",
        "sidescrolljump=", "ssj=",
        "sessionfiles=", "sessfiles=",
        "linenumcolor=", "commentcolor=", "stringcolor=", "keywordcolor=",
        "numbercolor=", "typecolor=", "builtincolor=", "functioncolor=",
        "operatorcolor=", "preproccolor=",
        "statusfgcolor=", "statusfg=", "statusbgcolor=", "statusbg=",
        "bottomstatusfgcolor=", "bottomstatusfg=",
        "bottomstatusbgcolor=", "bottomstatusbg=",
        "errorcolor=", "errorfg=",
    ])

    def _set_opt_completion_bounds(self) -> Optional[Tuple[int, int, str]]:
        """Returns (start, end, prefix) for :set option completion, or None."""
        if not self._cmd_buf.startswith(":"):
            return None
        text = self._cmd_buf[1:]
        cursor = max(0, min(self._cmd_cursor - 1, len(text)))
        before_cursor = text[:cursor]
        m = re.match(r'\s*set\s+', before_cursor)
        if not m:
            return None
        opt_text = before_cursor[m.end():]
        last_space = opt_text.rfind(' ')
        if last_space >= 0:
            prefix = opt_text[last_space + 1:]
            prefix_offset = m.end() + last_space + 1
        else:
            prefix = opt_text
            prefix_offset = m.end()
        return 1 + prefix_offset, self._cmd_cursor, prefix

    def _clear_set_completion(self):
        self._set_completion_matches = []
        self._set_completion_index = 0
        self._set_completion_prefix = ""

    def _complete_set_opt(self, forward: bool = True) -> bool:
        """Tab-complete a :set option; returns True if in :set context, False otherwise."""
        bounds = self._set_opt_completion_bounds()
        if bounds is None:
            self._clear_set_completion()
            return False
        start, end, current_prefix = bounds

        if self._set_completion_matches:
            currently_inserted = self._cmd_buf[start:end]
            if currently_inserted in self._set_completion_matches:
                if forward:
                    self._set_completion_index = (self._set_completion_index + 1) % len(self._set_completion_matches)
                else:
                    self._set_completion_index = (self._set_completion_index - 1) % len(self._set_completion_matches)
                replacement = self._set_completion_matches[self._set_completion_index]
                self._cmd_buf = self._cmd_buf[:start] + replacement + self._cmd_buf[end:]
                self._cmd_cursor = start + len(replacement)
                self._cmd_history_index = None
                self._cmd_history_draft = self._cmd_buf
                self._show_set_completion()
                return True

        matches = [opt for opt in self._SET_OPTIONS if opt.startswith(current_prefix)]
        if not matches:
            self._clear_set_completion()
            self._set_error("No matching set option")
            return True
        self._set_completion_matches = matches
        self._set_completion_prefix = current_prefix
        self._set_completion_index = 0 if forward else len(matches) - 1
        replacement = matches[self._set_completion_index]
        self._cmd_buf = self._cmd_buf[:start] + replacement + self._cmd_buf[end:]
        self._cmd_cursor = start + len(replacement)
        self._cmd_history_index = None
        self._cmd_history_draft = self._cmd_buf
        self._show_set_completion()
        return True

    def _show_set_completion(self):
        matches = self._set_completion_matches
        idx = self._set_completion_index
        parts = []
        for i, m in enumerate(matches[:8]):
            parts.append(f"[{m}]" if i == idx else m)
        more = " ..." if len(matches) > 8 else ""
        self.message = "  ".join(parts) + more
        self.message_is_error = False

    def _filename_completion_bounds(self) -> Optional[Tuple[int, int, str, bool, str]]:
        if not self._cmd_buf.startswith(":"):
            return None
        text = self._cmd_buf[1:]
        cursor = max(0, min(self._cmd_cursor - 1, len(text)))
        before_cursor = text[:cursor]
        # _parse_range_prefix() always returns command_text as a trailing
        # substring of before_cursor (it only ever strips a leading range
        # and/or whitespace), whether or not it found a range -- so the
        # length-subtraction offset is valid unconditionally. Gating it on
        # "a range was found" left command_offset at 0 whenever the command
        # had leading whitespace but no range (e.g. ": w", ":  e"), since
        # _parse_range_prefix() internally lstrips before failing to find a
        # range: command_text would already have that whitespace stripped
        # off while command_offset stayed 0, so every offset computed from
        # it below pointed too far right, letting the command letter itself
        # get treated as (and overwritten by) the filename prefix.
        range_rows, command_text = self._parse_range_prefix(before_cursor)
        command_offset = len(before_cursor) - len(command_text)
        m = re.match(r"\s*(\S+)", command_text)
        if not m:
            return None
        cmd = m.group(1).lower()
        if cmd.endswith("!"):
            cmd_base = cmd[:-1]
            if cmd_base not in self._FILENAME_BANG_EX_COMMANDS:
                return None
        else:
            cmd_base = cmd
        if cmd_base not in self._FILENAME_EX_COMMANDS:
            return None
        if cursor < command_offset + m.end():
            return None

        between = text[command_offset + m.end():cursor]
        needs_space = not between
        arg_start = command_offset + m.end() + (len(between) - len(between.lstrip()))
        prefix = text[arg_start:cursor]
        return 1 + arg_start, self._cmd_cursor, prefix, needs_space, cmd_base

    def _clear_filename_completion(self):
        self._filename_completion_matches = []
        self._filename_completion_index = 0
        self._filename_completion_prefix = ""
        self._filename_completion_needs_space = False

    def _set_filename_completion_matches(
            self, matches: List[str], prefix: str, needs_space: bool):
        self._cmd_history_index = None
        self._cmd_history_draft = self._cmd_buf
        if matches != self._filename_completion_matches or prefix != self._filename_completion_prefix:
            self._filename_completion_matches = matches
            self._filename_completion_index = 0
        elif matches:
            self._filename_completion_index = (
                self._filename_completion_index + 1
            ) % len(matches)
        self._filename_completion_prefix = prefix
        self._filename_completion_needs_space = needs_space
        preview = "  ".join(matches[:5])
        more = " ..." if len(matches) > 5 else ""
        self.message = preview + more
        self.message_is_error = False

    def _accept_filename_completion_match(self) -> bool:
        if not self._filename_completion_matches:
            return False
        bounds = self._filename_completion_bounds()
        if bounds is None:
            self._clear_filename_completion()
            return False
        start, end, prefix, needs_space, _cmd_base = bounds
        if prefix != self._filename_completion_prefix:
            self._clear_filename_completion()
            return False

        self._filename_completion_index = max(
            0,
            min(
                self._filename_completion_index,
                len(self._filename_completion_matches) - 1,
            ),
        )
        replacement = self._filename_completion_matches[self._filename_completion_index]
        if needs_space:
            replacement = " " + replacement
        self._cmd_buf = self._cmd_buf[:start] + replacement + self._cmd_buf[end:]
        self._cmd_cursor = start + len(replacement)
        self._cmd_history_index = None
        self._cmd_history_draft = self._cmd_buf
        self.message = ""
        self.message_is_error = False
        self._clear_filename_completion()
        return True

    @staticmethod
    def _list_path_completions(prefix: str, dirs_only: bool = False) -> List[str]:
        """List filesystem completions for a (possibly ~-prefixed, possibly
        relative) path fragment, in the same textual style as `prefix`."""
        expanded = os.path.expanduser(prefix)
        dirname, basename = os.path.split(expanded)
        search_dir = dirname or "."

        matches = []
        # os.scandir's DirEntry.is_dir() uses the file type the directory
        # read already returned on most platforms/filesystems, avoiding a
        # second stat() syscall per entry that os.listdir()+os.path.isdir()
        # would pay -- material on large directories (build output,
        # node_modules, log dirs), which Tab-completion here scans
        # synchronously on the single UI thread.
        with os.scandir(search_dir) as it:  # may raise OSError
            for entry in it:
                name = entry.name
                if not name.startswith(basename):
                    continue
                try:
                    is_dir = entry.is_dir()
                except OSError:
                    is_dir = False
                if dirs_only and not is_dir:
                    continue
                suffix = "/" if is_dir else ""
                if dirname:
                    candidate = os.path.join(dirname, name) + suffix
                else:
                    candidate = name + suffix
                if prefix.startswith("~") and expanded.startswith(os.path.expanduser("~")):
                    home = os.path.expanduser("~")
                    if candidate.startswith(home):
                        candidate = "~" + candidate[len(home):]
                matches.append(candidate)

        matches.sort(key=lambda item: (not item.endswith("/"), item.lower()))
        return matches

    def _complete_cmd_filename(self) -> bool:
        bounds = self._filename_completion_bounds()
        if bounds is None:
            self._clear_filename_completion()
            return False
        start, end, prefix, needs_space, cmd_base = bounds
        dirs_only = cmd_base in self._DIR_ONLY_EX_COMMANDS
        try:
            matches = self._list_path_completions(prefix, dirs_only=dirs_only)
        except OSError as exc:
            self._clear_filename_completion()
            self._set_error(str(exc))
            return True

        if not matches:
            self._clear_filename_completion()
            self._set_error("No file match")
            return True

        if len(matches) == 1:
            self._clear_filename_completion()
            replacement = matches[0]
        else:
            replacement = os.path.commonprefix(matches)
            if replacement == prefix:
                self._set_filename_completion_matches(matches, prefix, needs_space)
                return True
            self._clear_filename_completion()

        if needs_space:
            replacement = " " + replacement
        self._cmd_buf = self._cmd_buf[:start] + replacement + self._cmd_buf[end:]
        self._cmd_cursor = start + len(replacement)
        self._cmd_history_index = None
        self._cmd_history_draft = self._cmd_buf
        self.message = ""
        self.message_is_error = False
        return True

    def _handle_cmd_buf(self, key: int) -> Optional[bool]:
        """
        Returns None  → still accumulating input
        Returns True  → finished, continue editing
        Returns False → finished, quit editor
        """
        self._clamp_marks()
        if key == 27:
            self._clear_cmd_buf()
            self.message = ""
            self.message_is_error = False
            return True

        if key in self._ENTER_KEYS:
            buf           = self._cmd_buf
            context       = self._cmd_context
            self._record_cmd_history(buf)
            self._clear_cmd_buf()
            self.message  = ""
            self.message_is_error = False

            if buf.startswith("/") or buf.startswith("?") or buf.startswith("\\"):
                forward = buf[0] != "?"
                literal = buf[0] == "\\"
                pattern = buf[1:]
                if context and context[0] == "help_search":
                    motion = pattern or self.help_search_pattern
                    self._search_help(motion, forward)
                elif context and context[0] == "operator_search":
                    op, cnt, cmd = context[1]
                    motion = pattern or self.search_pattern
                    if motion:
                        self._resolve_operator(op, cnt, SearchMotion(cmd=cmd, pattern=motion))
                    else:
                        self._set_error("No previous search pattern")
                else:
                    if pattern:
                        self._search(pattern, forward, literal=literal)
                    elif self.search_pattern:
                        self._search(self.search_pattern, forward, literal=self._search_literal)
                    else:
                        self._set_error("No previous search pattern")
            else:
                try:
                    result = self._execute_cmd(buf)
                except Exception as exc:
                    # A bug in one ex command must not take down the whole
                    # session; report it like any other command failure and
                    # keep editing (unsaved buffers stay intact).
                    self._set_error(f"Command failed: {exc}")
                    result = True
                if result is False:
                    return False
            return True

        if key == ord("\t"):
            if not self._complete_set_opt(forward=True):
                if not self._complete_cmd_filename():
                    self.message = ""
                    self.message_is_error = False
            self._cmd_history_index = None
            self._cmd_history_draft = self._cmd_buf
            return None

        if key == curses.KEY_BTAB:
            if not self._complete_set_opt(forward=False):
                self.message = ""
                self.message_is_error = False
            self._cmd_history_index = None
            self._cmd_history_draft = self._cmd_buf
            return None

        if key == ord(">") and self._accept_filename_completion_match():
            return None

        if key == curses.KEY_UP:
            self._clear_filename_completion()
            self._clear_set_completion()
            self._recall_cmd_history(-1)
            return None

        if key == curses.KEY_DOWN:
            self._clear_filename_completion()
            self._clear_set_completion()
            self._recall_cmd_history(1)
            return None

        if (key in (curses.KEY_BACKSPACE, 127, 8)
                and self._cmd_cursor <= 1 and len(self._cmd_buf) <= 1):
            # Backspacing over the prompt character cancels the command line
            # -- but only when there's nothing typed after it. Cursor <= 1
            # alone isn't enough: the user can land there with Left/Home
            # while the buffer still holds typed text (e.g. ":s/foo/bar/g"
            # with the cursor walked back to just after the ':'), and a
            # backspace there must not silently discard it.
            self._clear_cmd_buf()
            return None

        edited = self._edit_line_key(self._cmd_buf, self._cmd_cursor, key,
                                     min_cursor=1)
        if edited is not None:
            self._clear_filename_completion()
            self._clear_set_completion()
            changed = edited[0] != self._cmd_buf
            self._cmd_buf, self._cmd_cursor = edited
            if changed:
                self._cmd_history_index = None
                self._cmd_history_draft = self._cmd_buf

        return None

    # -----------------------------------------------------------------------
    # Main loop
    # -----------------------------------------------------------------------

    def _enable_bracketed_paste(self) -> None:
        try:
            sys.stdout.write(self._BRACKETED_PASTE_ON)
            sys.stdout.flush()
        except OSError:
            pass

    def _disable_bracketed_paste(self) -> None:
        try:
            sys.stdout.write(self._BRACKETED_PASTE_OFF)
            sys.stdout.flush()
        except OSError:
            pass

    def _read_key(self, stdscr):
        """Block until a key is available and return it (normalizing a
        single-byte wide char to its ordinal, same as get_wch()'s callers
        already expect). Shared by the main loop and by bracketed-paste
        reading, so both see identical key values."""
        while True:
            if self._pending_keys:
                return self._pending_keys.popleft()
            try:
                if hasattr(stdscr, "get_wch"):
                    key = stdscr.get_wch()
                    if isinstance(key, str) and len(key) == 1 and ord(key) < 128:
                        key = ord(key)
                else:
                    key = stdscr.getch()
                return key
            except KeyboardInterrupt:
                continue
            except curses.error as exc:
                # get_wch()/getch() can be interrupted mid-read by our
                # SIGTSTP handler (no SA_RESTART), surfacing as
                # "no input" instead of retrying the read. Any other
                # curses error is a real problem and should propagate.
                if str(exc) == "no input":
                    continue
                raise

    def _read_key_or_none(self, stdscr):
        """Like _read_key(), but for use while stdscr.timeout() is set to a
        finite value: returns None instead of blocking when nothing arrives
        before the timeout expires."""
        if self._pending_keys:
            return self._pending_keys.popleft()
        try:
            if hasattr(stdscr, "get_wch"):
                key = stdscr.get_wch()
                if isinstance(key, str) and len(key) == 1 and ord(key) < 128:
                    key = ord(key)
            else:
                key = stdscr.getch()
        except KeyboardInterrupt:
            return None
        except curses.error as exc:
            if str(exc) == "no input":
                return None
            raise
        return None if key == -1 else key

    def _match_escape_tail(self, stdscr, expected: str, timeout_ms: Optional[int]) -> bool:
        """After an ESC (27) has just been read, check whether `expected`
        (e.g. "[200~") follows immediately. On a full match, consumes those
        keys and returns True. On a mismatch -- including a timeout, when
        timeout_ms is given -- pushes back everything read so it is
        dispatched normally, and returns False. With timeout_ms=None, reads
        block, for reading a bracketed paste's known-to-be-coming end
        marker rather than distinguishing paste from a bare Escape press."""
        if timeout_ms is not None and not hasattr(stdscr, "timeout"):
            # A window that can't be put in timeout mode can't be probed
            # without risking a block on input that may never come; treat
            # this as "not a paste" so a bare ESC still behaves exactly as
            # it always has on such windows (some test doubles included).
            return False
        consumed = []
        if timeout_ms is not None:
            stdscr.timeout(timeout_ms)
        try:
            for want in expected:
                key = self._read_key(stdscr) if timeout_ms is None else self._read_key_or_none(stdscr)
                if key is None:
                    break
                consumed.append(key)
                if isinstance(key, str):
                    ch = key
                elif isinstance(key, int) and 0 <= key < 0x110000:
                    ch = chr(key)
                else:
                    ch = None
                if ch != want:
                    break
            else:
                return True
        finally:
            if timeout_ms is not None:
                stdscr.timeout(-1)
        for key in reversed(consumed):
            self._pending_keys.appendleft(key)
        return False

    def _read_bracketed_paste_body(self, stdscr) -> str:
        """Read and return everything up to (not including) the bracketed
        paste's end marker. Called right after the start marker has already
        been consumed by _match_escape_tail()."""
        chars = []
        while True:
            key = self._read_key(stdscr)
            if key == 27 and self._match_escape_tail(stdscr, self._PASTE_END_TAIL, None):
                break
            if key == curses.KEY_RESIZE:
                self._force_redraw = True
                continue
            if isinstance(key, str):
                chars.append(key)
            elif isinstance(key, int) and 0 <= key < 0x110000:
                chars.append(chr(key))
        return "".join(chars)

    def _handle_bracketed_paste(self, text: str, stdscr) -> bool:
        """Apply a completed bracketed paste. In INSERT/REPLACE mode the
        text is inserted literally (see _insert_pasted_text) so it can't
        march itself further right on every embedded newline.

        In NORMAL/VISUAL/VISUAL_LINE mode with no command line already
        open, the text is *also* inserted literally at the cursor rather
        than replayed as keystrokes: pasted text is untrusted external
        input (e.g. clipboard content from a web page), and replaying it
        through the normal per-key dispatch would let it open and submit
        a ':' command -- including ':!<shell command>' -- or a shell
        filter with the editing user's privileges, with no confirmation.
        This is the classic terminal "pastejacking" vector.

        Command/search and overlay text fields receive literal text directly.
        Pasted controls cannot submit a prompt, confirm an operation, or
        escape into another mode. Non-editable overlays ignore paste.
        Returns False if the program should exit."""
        if not text:
            return True
        if self._pending_confirmation is not None:
            return True
        if self._cmd_buf:
            literal = self._paste_prompt_text(text)
            cursor = self._cmd_cursor
            self._cmd_buf = self._cmd_buf[:cursor] + literal + self._cmd_buf[cursor:]
            self._cmd_cursor += len(literal)
            self._clear_filename_completion()
            self._clear_set_completion()
            self._cmd_history_index = None
            self._cmd_history_draft = self._cmd_buf
            return True
        if self.mode == Mode.INSERT:
            self._insert_pasted_text(text)
            self._refresh_intellisense_completion()
            return True
        if self.mode == Mode.REPLACE:
            self._replace_pasted_text(text)
            return True
        if not self._cmd_buf and self.mode in (Mode.NORMAL, *VISUAL_MODES):
            self._paste_literal_outside_insert(text)
            return True
        literal = self._paste_prompt_text(text)
        if self.mode == Mode.FILE_BROWSER:
            s = self.file_browser
            if s.op_prompt:
                if s.op_kind.startswith("confirm:"):
                    return True
                s.op_text = s.op_text[:s.op_cursor] + literal + s.op_text[s.op_cursor:]
                s.op_cursor += len(literal)
                self._fb_clear_op_completion()
            elif s.grep_prompt:
                s.grep_text = s.grep_text[:s.grep_cursor] + literal + s.grep_text[s.grep_cursor:]
                s.grep_cursor += len(literal)
        elif self.mode == Mode.FUNCTIONS and self.function_list_searching:
            self.function_list_search += literal
            self.function_list_cursor = 0
        self._force_redraw = True
        return True

    @staticmethod
    def _paste_prompt_text(text: str) -> str:
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        return "".join(" " if ch in "\n\t" else ch for ch in text
                       if ch.isprintable() or ch in "\n\t")

    def _paste_literal_outside_insert(self, text: str) -> None:
        """Insert a bracketed paste's text literally at the cursor for
        NORMAL/VISUAL/VISUAL_LINE mode -- see _handle_bracketed_paste for
        why this must not be replayed as keystrokes/commands. Mirrors
        _insert_pasted_text's line-splice logic (no auto-indent growth on
        embedded newlines) without its INSERT-mode-only bookkeeping
        (dot-repeat key recording, intellisense), which don't apply here."""
        text = text.replace("\r\n", "\n").replace("\r", "\n")
        if not text:
            return
        self.mode = Mode.NORMAL
        self._push_undo()
        segments = text.split("\n")
        for i, segment in enumerate(segments):
            if i > 0:
                self._newline(auto_indent=False)
            if segment:
                self._insert_char(segment)
        self._clamp_marks()
        self._clamp_cursor()
        self.modified = True
        self._force_redraw = True

    def _dispatch_key(self, key: Union[int, str], stdscr) -> bool:
        """Handle one already-read key exactly as the main loop would.
        Returns False if the program should exit. Factored out so
        bracketed-paste replay outside insert/replace mode (see
        _handle_bracketed_paste) can feed pasted characters through the
        same path as normally typed ones."""
        if self._pending_confirmation is not None:
            if self._handle_pending_confirmation(key):
                return True

        if self._is_ignored_control_key(key):
            return True

        if key == curses.KEY_RESIZE:
            self._force_redraw = True
            return True

        # Clear one-shot message on any keypress
        if self.message and key != 27 and self._pending_confirmation is None:
            self.message          = ""
            self.message_is_error = False

        # Command buffer takes precedence
        if self._cmd_buf:
            result = self._handle_cmd_buf(key)
            if result is False:
                return False
            return True

        # Mode dispatch
        height, width = stdscr.getmaxyx()
        if self.mode == Mode.NORMAL:
            if not self._handle_normal(key, height, width):
                return False
        elif self.mode == Mode.INSERT:
            self._handle_insert(key)
        elif self.mode == Mode.REPLACE:
            self._handle_replace_mode(key)
        elif self.mode in VISUAL_MODES:
            self._handle_visual(key)
        elif self.mode == Mode.HELP:
            self._handle_help(key)
        elif self.mode == Mode.HEX:
            self._handle_hex(key)
        elif self.mode == Mode.LINE_ENDINGS:
            self._handle_line_endings(key)
        elif self.mode == Mode.SHELL:
            self._handle_shell(key)
        elif self.mode == Mode.BUFFER_LIST:
            self._handle_buffer_list(key)
        elif self.mode == Mode.RECENT_FILES:
            self._handle_recent_files(key)
        elif self.mode == Mode.FILE_BROWSER:
            self._handle_file_browser(key)
        elif self.mode == Mode.GREP_RESULTS:
            self._handle_grep_results(key)
        elif self.mode == Mode.FUNCTIONS:
            self._handle_functions(key)
        return True

    def edit(self, stdscr: curses.window) -> None:
        self._stdscr = stdscr
        try:
            curses.curs_set(1)
        except curses.error:
            pass
        stdscr.keypad(True)
        curses.noecho()
        self._enable_bracketed_paste()
        try:
            curses.start_color()
            curses.use_default_colors()
        except curses.error:
            pass
        self._reinit_colors()

        old_signal_handlers = []
        for sig_name in ("SIGINT", "SIGQUIT"):
            sig = getattr(signal, sig_name, None)
            if sig is None:
                continue
            try:
                old_signal_handlers.append((sig, signal.getsignal(sig)))
                signal.signal(sig, signal.SIG_IGN)
            except (OSError, RuntimeError, ValueError):
                pass

        def _suspend(signum, frame):
            # Hand the terminal back to the shell in its own (cooked) mode
            # before actually stopping, then restore curses' raw/keypad mode
            # and flush any half-typed escape sequences once we resume —
            # otherwise arrow keys can arrive as bare "ESC [ A/B/C/D" bytes
            # that normal mode interprets as real commands (e.g. "D").
            try:
                curses.def_prog_mode()
                curses.endwin()
            except curses.error:
                pass
            try:
                os.kill(os.getpid(), signal.SIGSTOP)
            except OSError:
                pass
            try:
                curses.reset_prog_mode()
                curses.flushinp()
            except curses.error:
                pass
            self._force_redraw = True
            try:
                stdscr.refresh()
            except curses.error:
                pass

        sigtstp = getattr(signal, "SIGTSTP", None)
        if sigtstp is not None:
            try:
                old_signal_handlers.append((sigtstp, signal.getsignal(sigtstp)))
                signal.signal(sigtstp, _suspend)
            except (OSError, RuntimeError, ValueError):
                pass

        try:
            while True:
                # A paging/scrolling command requests the repaint of the moved
                # view to run with the cursor hidden; re-show it as soon as
                # the frame is complete so it is only invisible while the
                # scroll itself is being painted.
                hide_cursor = self._hide_cursor_next_draw
                self._hide_cursor_next_draw = False
                if hide_cursor:
                    try:
                        curses.curs_set(0)
                    except curses.error:
                        hide_cursor = False
                self.draw(stdscr)
                if hide_cursor:
                    try:
                        curses.curs_set(1)
                    except curses.error:
                        pass

                key = self._read_key(stdscr)

                # A lone ESC that turns out to be the start of a terminal
                # bracketed-paste marker: consume the whole paste here,
                # regardless of mode, rather than letting it fall through
                # to ordinary ESC handling.
                if key == 27 and self._match_escape_tail(stdscr, self._PASTE_START_TAIL, 25):
                    paste_text = self._read_bracketed_paste_body(stdscr)
                    if not self._handle_bracketed_paste(paste_text, stdscr):
                        break
                    continue

                if not self._dispatch_key(key, stdscr):
                    break
        except Exception:
            # A bug anywhere in dispatch would otherwise lose every unsaved
            # edit; dump modified buffers so main() can point the user at
            # the recovery files, then let the exception propagate.
            self.crash_dump_paths = self._dump_crash_recovery()
            raise
        finally:
            self._disable_bracketed_paste()
            try:
                self._save_session()
            except Exception:
                # A crash already in flight must not be replaced by a
                # secondary failure here (e.g. corrupted mark/cursor state
                # from the same bug that triggered the crash) -- see
                # _dump_crash_recovery's same "never raise while unwinding"
                # contract.
                pass
            for sig, old_handler in reversed(old_signal_handlers):
                try:
                    signal.signal(sig, old_handler)
                except (OSError, RuntimeError, ValueError):
                    pass


ViEditor = ViiEditor


# ---------------------------------------------------------------------------
# Entry point
# ---------------------------------------------------------------------------

def _parse_session_line(line: str) -> Optional[Tuple[str, int, int, dict[str, Tuple[int, int]], dict[int, int]]]:
    """Parse one session record.

    Current records use a JSON string for the path followed by row, column, an
    optional JSON mark map, and an optional JSON auto-mark map. Legacy records
    used a raw path; rsplit keeps those readable even when the raw path itself
    contains tabs.
    """
    marks_text = ""
    auto_marks_text = ""
    if line.startswith('"'):
        try:
            path, end = json.JSONDecoder().raw_decode(line)
        except (TypeError, ValueError, json.JSONDecodeError):
            return None
        if not isinstance(path, str):
            return None
        rest = line[end:]
        if not rest.startswith("\t"):
            return None
        fields = rest[1:].split("\t")
        if len(fields) not in (2, 3, 4):
            return None
        row_text, col_text = fields[0], fields[1]
        if len(fields) >= 3:
            marks_text = fields[2]
        if len(fields) == 4:
            auto_marks_text = fields[3]
    else:
        parts = line.rsplit("\t", 2)
        if len(parts) != 3:
            return None
        path, row_text, col_text = parts

    try:
        row = int(row_text)
        col = int(col_text)
    except ValueError:
        return None

    marks: dict[str, Tuple[int, int]] = {}
    if marks_text:
        try:
            raw_marks = json.loads(marks_text)
        except (TypeError, ValueError, json.JSONDecodeError):
            return None
        if isinstance(raw_marks, dict):
            for name, pos in raw_marks.items():
                if not (isinstance(name, str) and len(name) == 1 and name.isalpha()):
                    continue
                if not (isinstance(pos, list) and len(pos) == 2):
                    continue
                mark_row, mark_col = pos
                if isinstance(mark_row, int) and isinstance(mark_col, int):
                    marks[name] = (mark_row, mark_col)

    auto_marks: dict[int, int] = {}
    if auto_marks_text:
        try:
            raw_auto = json.loads(auto_marks_text)
        except (TypeError, ValueError, json.JSONDecodeError):
            raw_auto = {}
        if isinstance(raw_auto, dict):
            for key, cur in raw_auto.items():
                try:
                    id_ = int(key)
                except (ValueError, TypeError):
                    continue
                if isinstance(cur, int):
                    auto_marks[id_] = cur

    if not path:
        return None
    return path, row, col, marks, auto_marks


def _read_session_filenames() -> List[str]:
    """Return file paths from the session file that still exist on disk."""
    paths: List[str] = []
    seen: set[str] = set()
    try:
        with open(ViiEditor.SESSION_PATH, "r", encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.rstrip("\n")
                if not line or line.startswith("#"):
                    continue
                parsed = _parse_session_line(line)
                if parsed is None:
                    continue
                path, _, _, _, _ = parsed
                normalized = ViiEditor._normalize_path(path)
                if normalized and normalized not in seen and os.path.isfile(normalized):
                    seen.add(normalized)
                    paths.append(normalized)
    except OSError:
        pass
    return paths


def _resolve_project_filenames(name: str) -> Tuple[Optional[List[str]], Optional[str]]:
    """(filenames, error) for project *name*. Exactly one of the two is None.

    Distinguishes "no such project" from "couldn't read the session file" --
    _read_project_sections raises on a genuine read failure (as opposed to
    the file simply not existing yet), and collapsing that into "no such
    project" would send someone chasing a typo instead of a permissions or
    I/O problem.
    """
    try:
        sections = ViiEditor._read_project_sections(ViiEditor.SESSION_PATH)
    except OSError as exc:
        return None, f"could not read {ViiEditor.SESSION_PATH}: {exc}"
    if name not in sections:
        return None, f"no such project: {name}"
    paths: List[str] = []
    seen: set[str] = set()
    for p in sections[name]:
        normalized = ViiEditor._normalize_path(p)
        if normalized and normalized not in seen and os.path.isfile(normalized):
            seen.add(normalized)
            paths.append(normalized)
    return paths, None


_CLI_FLAG_ATTRS = {
    "-ns": "no_session_save",
    "--no-session-save": "no_session_save",
    "-nb": "no_backup",
    "--no-backup": "no_backup",
    "-ro": "read_only",
    "--read-only": "read_only",
}


def _parse_cli_flags(argv: List[str]) -> Tuple[dict, List[str]]:
    """Pull -ns/-nb/-ro (and their long -- forms) out of argv, wherever they
    appear, leaving the rest (e.g. -p name, or filenames) untouched."""
    flags = {"no_session_save": False, "no_backup": False, "read_only": False}
    remaining: List[str] = []
    for arg in argv:
        attr = _CLI_FLAG_ATTRS.get(arg)
        if attr is not None:
            flags[attr] = True
        else:
            remaining.append(arg)
    return flags, remaining


def _resolve_startup_filenames(argv: List[str]) -> Tuple[Optional[List[str]], Optional[str]]:
    """Turn sys.argv[1:] into (filenames, error). Exactly one of the two is None."""
    if argv and argv[0] == "-p":
        if len(argv) != 2 or not argv[1]:
            return None, "-p requires exactly one project name"
        name = argv[1]
        filenames, error = _resolve_project_filenames(name)
        if error is not None:
            return None, error
        if not filenames:
            return None, f"project '{name}' has no existing files"
        return filenames, None
    if argv:
        return argv, None
    return _read_session_filenames(), None


def main() -> int:
    flags, remaining_argv = _parse_cli_flags(sys.argv[1:])
    filenames, error = _resolve_startup_filenames(remaining_argv)
    if error is not None:
        print(f"Error: {error}", file=sys.stderr)
        return 1

    curses.set_escdelay(20)
    editor = ViiEditor(filenames)
    # Applied after __init__ (and its ~/.viirc load) so these always win.
    if flags["no_backup"]:
        editor.backup_enabled = False
    if flags["no_session_save"] or flags["read_only"]:
        editor.session_save_enabled = False
    if flags["read_only"]:
        editor.read_only = True
    try:
        curses.wrapper(editor.edit)
    except Exception as exc:
        print(f"Error: {exc}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        for dump_path in getattr(editor, "crash_dump_paths", []):
            print(f"Unsaved changes saved to: {dump_path}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
