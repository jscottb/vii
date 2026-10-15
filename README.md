# vii or `7`

A vi/vim-like terminal text editor in a single Python file, built on `curses`
and nothing but the Python standard library.

```
python3 vi_editor.py notes.md main.c
```

If you know vi, you already know most of vii: modal editing, operators and
motions, counts, registers, marks, visual modes, `.` repeat, and `:` ex commands.
On top of that it adds a file browser, multiple buffers, recent files and saved
projects, a grep results view, a hex view, syntax highlighting, and generation
backups on every save.

## Requirements

- Python 3.12 or newer
- A POSIX system with `curses`: Linux, macOS, or Windows via WSL
- No third-party packages

## Installing

There's nothing to build. Run the script directly, or put it on your `PATH`:

```
chmod +x vi_editor.py
ln -s "$PWD/vi_editor.py" ~/bin/vii
```

## Starting the editor

```
vii file ...          open one or more files, each in its own buffer
vii                   reopen the files from your last session
vii -p name           open the files of a saved project (see :project)
```

| Option | Effect |
| --- | --- |
| `-ns`, `--no-session-save` | don't update `~/.vii_session` on exit |
| `-nb`, `--no-backup` | don't write generation backups when saving |
| `-ro`, `--read-only` | refuse all saves (also implies `-ns`) |

Inside the editor, `:help` (or `:h`) opens a searchable reference of every key
and command. It's the authoritative list; this README covers the highlights.

## Editing

The usual vi modes and commands work as expected:

- **Movement:** `h j k l`, word motions `w b e` (and `W B E`), `0 ^ $`, `gg G`,
  `H M L`, `{ }`, `f F t T ; ,`, `%`, and paging with `Ctrl-F/B/D/U`.
- **Operators:** `d y c > <` combine with any motion, with `f`/`t`/search
  motions, and with the `iw`/`aw` text objects. Counts multiply, so `2d3w`
  deletes six words.
- **Insert and replace:** `i a I A o O`, `r R`, `s S`, `C D`, `x X`, `J`, `~`.
- **Undo, redo, repeat:** `u`, `Ctrl-R`, and `.`.
- **Registers and marks:** named registers `"a`–`"z`, marks `ma` with `'a` and
  `` `a ``, plus `m.` to toggle an automatic line mark and `'[` / `']` to jump
  between them.
- **Search:** `/pattern` and `?pattern` use Python regular expressions;
  `\text` searches for literal text, ignoring case. `n N * #` work as in vim.
- **Substitute:** `:s/pat/repl/[gic]`, with ranges such as `:%s` and `:N,Ms`, and
  a `c` flag that asks before each change.
- **Global commands:** `:g/pat/cmd` and `:v/pat/cmd`.

Insert mode adds a few conveniences: Enter keeps the current indentation,
Shift-Tab dedents, pasted text is inserted literally, and `Ctrl-N` completes
words from the buffer.

### Visual modes

| Key | Selects |
| --- | --- |
| `v` | characters |
| `V` | whole lines |
| `Ctrl-V` or `Ctrl-M` | a rectangular block |

The same keys switch between modes, and pressing the current mode's key leaves
it. `Ctrl-M` is there for terminals that use `Ctrl-V` for paste. Because a
terminal sends Enter and `Ctrl-M` as the same key, Enter also starts block mode
from normal mode.

All motions extend the selection. `d y c > < ~ J` act on it, `p` / `P`
replace it with a register, and `:` opens the command line with the selected
lines as the range.

Block mode works by screen columns, so tabs and wide characters line up the
way they look:

- `I` / `A` insert before or after the block, and `c` changes it. You type on
  the first row, and the text is copied to every row when you press Esc.
- `$` stretches every row of the block to its own line end, so `$A` appends to
  the end of each line.
- `r{char}` fills the block with one character.
- A yanked or deleted block is pasted with `p` / `P` as a column, with short
  lines padded so text to the right stays aligned.

## Files, buffers, and views

| Command | What it does |
| --- | --- |
| `:e file`, `:w`, `:wa`, `:q`, `:wq`, `:x` | open, write, quit |
| `:ls`, `:b N`, `:bn`, `:bp`, `:bd` | list and switch buffers |
| `:rct` | recent files |
| `:project name` (`:prj`) | save the open files as a named project, or load one |
| `:fb` | two-panel file browser with copy, move, mkdir, delete, and grep |
| `:fnc` | list the functions, classes, or headings in the current file and jump to one |
| `:hex` | read-only hex view |
| `:le` | show the line ending of every line; `:le-unix` / `:le-win` set the default |
| `:!cmd`, `:sh cmd` | insert a shell command's output, or show it in a scrollable view |
| `:r file`, `:N,Mw file` | read a file in, or write a range of lines out |

Some smaller utilities:

- `:guid`, `:pass`, `:secret`, `:md5`, and the `:dt-*` commands insert generated
  values at the cursor.
- `:b64e` / `:b64d` base64-encode the buffer to a file, or decode a file into the
  buffer.
- `:lgt type` formats log files for easier reading. Files ending in `.log`
  are highlighted automatically.

## Syntax highlighting

Highlighting is chosen from the file extension:

| Language | Extensions |
| --- | --- |
| C / C++ | `.c .h .cc .cpp .cxx .hpp` |
| Python | `.py .pyw` |
| Go | `.go` |
| C# | `.cs` |
| Vala | `.vala .vapi` |
| Tcl | `.tcl` |
| SQL | `.sql` |
| Markdown | `.md .markdown` (soft-wrapped by default; `:set nomdwrap` turns it off) |
| Lisp / Scheme | `.lisp .lsp .cl .el .scm` |
| Forth | `.fs .fth .4th .forth` |

Log views support `python`, `lnx_auth`, `http`, `flask`, and `generic` formats
through `:lgt`.

## Configuration

Settings use the same syntax as `:set` and are read from `~/.viirc` at startup.
A commented default file is created on first run. Lines starting with `"` are
comments.

```
set number
set shiftwidth=4
set tabstop=8
set expandtab
set undolevels=200
set linenumcolor=cyan
```

Run `:set` with no arguments to see every current value. The main options:

| Option | Meaning |
| --- | --- |
| `number` / `nonumber` | line numbers |
| `tabstop=N`, `shiftwidth=N`, `expandtab` | tab width, indent step, spaces vs. tabs |
| `lnendings=unix\|win` | line endings for new text |
| `undolevels=N` | undo history depth |
| `backup` / `nobackup` | generation backups on save |
| `mdwrap` / `nomdwrap` | Markdown soft wrapping |
| `intellisense` | buffer-word completion in insert mode |
| `visualmarks` | set `'<` and `'>` when leaving visual mode |
| `scrolljump=N`, `sidescrolljump=N` | scroll step sizes |
| `sessionfiles=N` | how many recent files to remember |
| `*color=name` | colors for syntax and UI elements (see `:help`) |

## Safety and files on disk

- **Atomic saves.** Each save goes to a temporary file in the same directory,
  which then replaces the original. Permissions and ownership are kept, and
  symlinks are followed to the real file.
- **Generation backups.** Each save also keeps a backup of the earlier
  version in `.vii_backups/` next to the file. Turn this off with
  `:set nobackup`, `-nb`, or `:wnb` for a single write.
- **Line endings are preserved.** Files with mixed LF / CRLF endings, or with
  no final newline, are written back exactly as they were read.
- **Large files.** Files of 8 MiB or more are memory-mapped and decoded
  lazily, so they open quickly. The first edit loads them fully.
- **Crash recovery.** If the editor crashes, each modified buffer is written
  to `<file>.vii_crash` (or `~/.vii_crash_noname_<n>` for unnamed buffers)
  before it exits.

| Path | Contents |
| --- | --- |
| `~/.viirc` | startup settings |
| `~/.vii_session` | recent files, cursor positions, marks, and saved projects |
| `<dir>/.vii_backups/` | generation backups of files saved in `<dir>` |


## Development

I started vii as a weekend project - It's my (I think) 12th editor I have written,
the third vi style editor, and the second editor I've done in Python. The others
were in Asm (early one), and C for most of them.

The whole editor lives in `vi_editor.py`, almost all of it in the `ViiEditor`
class. The tests in `test_vi_editor.py` use `unittest` and run under pytest:

```
python -m pytest test_vi_editor.py -q
ruff check vi_editor.py test_vi_editor.py
```

When you add a command or key binding, update `HELP_LINES` in `vi_editor.py` so
`:help` stays accurate. 


## Goals

I was to start a new project at my place of work. For most of my editor-using life,
emacs-like editors have always been my choice. My preference was always lite-style
editors, so not full-blown Emacs (nothing personal :) The system I was to be working
on was RHE, via a few hops to get to the actual terminal -- modern secure life /-(
I could have used vim or emacs, but they both offer a few issues via my access path.

Getting an outside editor in to compile and install is a modern no-no, so I remembered
the weekend vi I did that was in one file with no outside dependencies. The problem was, 
it wasn't finished and left abandoned like most weekend projects. I had most of
the modes done, memory-mapped file access, ':s//', orcish undo (very heavy-handed!) 
So I thought, "Hey, I'll finish it with AI." 

I had about a month before I started the new project, so I hammered and chiseled away 
at the prompt (a lot of them). There were a few setbacks, and "arguments", but it 
finally started to come together. As of Oct 2026, that was about ten months ago.  

Should I have just bit the bullet and used vim?  Probably so... :)


## License

Open and free to the public for any use.
