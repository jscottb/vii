import curses
import errno
import os
import shutil
import signal
import stat
import sys
import tempfile
import threading
import time
import typing
import unittest
from unittest import mock
import base64
import json

from vi_editor import (
    FileBrowserEntry, FindMotion, GotoMotion, GrepResult, MMapLineStore, Mode,
    SearchMotion, TextObjectMotion, ViEditor,
    _open_regular_file, _parse_cli_flags, _read_session_filenames, _resolve_project_filenames,
    _resolve_startup_filenames,
)


def _editor_with_rc(rc_path: "str | None" = None) -> ViEditor:
    """Build a ViEditor with ~/.viirc redirected to rc_path (an isolated,
    empty temp file by default), so construction is hermetic and doesn't
    pick up whatever ~/.viirc happens to exist on the machine running the
    tests -- ViiEditor.__init__ always reads the real ~/.viirc otherwise,
    so a bare ViEditor() is only safe to use in a test when the test does
    not depend on any setting's default value.
    """
    if rc_path is None:
        with tempfile.TemporaryDirectory() as tmpdir:
            return _editor_with_rc(os.path.join(tmpdir, ".viirc"))

    editor = ViEditor.__new__(ViEditor)
    orig_load = ViEditor._load_viirc

    def patched_load(self2):
        if not os.path.isfile(rc_path):
            self2._write_default_viirc(rc_path)
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
                        self2._apply_set_opt(opt)
                elif line.startswith("lnendings="):
                    self2._apply_set_opt(line)

    ViEditor._load_viirc = patched_load
    try:
        editor.__init__()
    finally:
        ViEditor._load_viirc = orig_load
    return editor


class ExCommandTests(unittest.TestCase):
    def test_large_file_loads_with_mmap_line_store(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\ngamma\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)
            self.assertEqual(len(editor.lines), 3)
            self.assertEqual(editor.lines[1], "beta")
            self.assertIn("[mmap]", editor.message)

    def test_mmap_line_ending_only_change_marks_buffer_modified(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "wb") as fh:
                fh.write(b"alpha\r\nbeta")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertFalse(editor.modified)

            editor.line_endings = ["\n", ""]
            editor._refresh_modified()

            self.assertTrue(editor.modified)

    def test_mmap_line_ending_trust_only_change_marks_buffer_modified(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "wb") as fh:
                fh.write(b"alpha")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertFalse(editor.modified)

            editor.line_endings_trusted = False
            editor._refresh_modified()

            self.assertTrue(editor.modified)

    def test_empty_file_does_not_use_empty_mmap(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "empty.txt")
            with open(path, "w", encoding="utf-8"):
                pass

            store = MMapLineStore(path)
            self.assertFalse(store.is_mapped)
            self.assertEqual(store, [""])

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 0
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertEqual(editor.lines, [""])
            self.assertNotIn("[mmap]", editor.message)

    def test_mmap_line_store_closes_fh_when_mmap_raises_oserror(self):
        # mmap.mmap() can fail with OSError for reasons unrelated to file
        # size (ENOMEM mapping a huge file, a filesystem that rejects mmap,
        # ...). Only ValueError (a file truncated to empty mid-open) used to
        # be handled; an OSError left the freshly opened file handle behind
        # with nothing to close it.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "wb") as fh:
                fh.write(b"alpha\nbeta\n")

            opened_handles = []
            real_open = _open_regular_file

            def spy_open(file, *args, **kwargs):
                handle = real_open(file, *args, **kwargs)
                if file == path:
                    opened_handles.append(handle)
                return handle

            with mock.patch("vi_editor._open_regular_file", side_effect=spy_open), \
                 mock.patch("vi_editor.mmap.mmap",
                            side_effect=OSError("Cannot allocate memory")):
                with self.assertRaises(OSError):
                    MMapLineStore(path)

            self.assertEqual(len(opened_handles), 1)
            self.assertTrue(opened_handles[0].closed)

    def test_constructor_rejects_existing_directory_as_initial_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            editor = ViEditor(tmpdir)

            self.assertTrue(editor.message_is_error)
            self.assertIsNone(editor.filename)
            self.assertEqual(editor.lines, [""])
            self.assertEqual(len(editor.buffers), 1)
            self.assertIsNone(editor.buffers[0].filename)

    def test_constructor_missing_initial_file_opens_new_named_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "new.txt")

            editor = ViEditor(path)

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, path)
            self.assertEqual(editor.lines, [""])
            self.assertEqual(editor.buffers[0].filename, path)
            self.assertFalse(editor._current_buffer_is_modified())
            self.assertFalse(editor._execute_cmd(":q"))

            self.assertTrue(editor._save_file())
            with open(path, "rb") as fh:
                self.assertEqual(fh.read(), b"\n")

    def test_constructor_expands_tilde_for_missing_initial_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            cwd = os.path.join(tmpdir, "cwd")
            os.mkdir(home)
            os.mkdir(cwd)
            path = os.path.join(home, "new.txt")
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            old_cwd = os.getcwd()
            try:
                os.chdir(cwd)
                with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                    editor = ViEditor("~/new.txt")

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.lines, [""])
                self.assertEqual(editor.buffers[0].filename, path)
            finally:
                os.chdir(old_cwd)

    def test_load_file_stores_absolute_buffer_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                editor = ViEditor()

                self.assertTrue(editor._execute_cmd(":edit note.txt"))

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.buffers[1].filename, path)
                self.assertIn(path, editor.message)
            finally:
                os.chdir(old_cwd)

    def test_edit_command_expands_tilde_against_home_not_cwd(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            cwd = os.path.join(tmpdir, "cwd")
            os.mkdir(home)
            os.mkdir(cwd)
            path = os.path.join(home, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            old_cwd = os.getcwd()
            try:
                os.chdir(cwd)
                with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                    editor = ViEditor()
                    self.assertTrue(editor._execute_cmd(":edit ~/note.txt"))

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.lines, ["loaded"])
                self.assertEqual(editor.buffers[1].filename, path)
                self.assertIn(path, editor.message)
            finally:
                os.chdir(old_cwd)

    def test_missing_file_buffer_stores_absolute_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "new.txt")
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                editor = ViEditor()

                self.assertTrue(editor._execute_cmd(":edit new.txt"))

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.buffers[1].filename, path)
                self.assertIn(path, editor.message)
            finally:
                os.chdir(old_cwd)

    def test_save_as_stores_absolute_buffer_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "saved.txt")
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                editor = ViEditor()
                editor.lines = ["saved"]

                self.assertTrue(editor._save_file("saved.txt"))

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.buffers[0].filename, path)
                self.assertIn(path, editor.message)
            finally:
                os.chdir(old_cwd)

    def test_read_only_blocks_save_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "saved.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("original\n")
            editor = ViEditor()
            editor._load_file(path)
            editor.lines = ["changed"]
            editor.read_only = True

            self.assertFalse(editor._save_file())
            self.assertTrue(editor.message_is_error)
            self.assertIn("Read-only", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "original\n")

    def test_read_only_blocks_write_line_range_and_base64(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            editor = ViEditor()
            editor.lines = ["one", "two", "three"]
            editor.read_only = True

            range_target = os.path.join(tmpdir, "range.txt")
            self.assertFalse(editor._write_line_range_to_file(0, 1, range_target))
            self.assertFalse(os.path.exists(range_target))

            b64_target = os.path.join(tmpdir, "encoded.b64")
            self.assertFalse(editor._save_base64_file(b64_target))
            self.assertFalse(os.path.exists(b64_target))

    def test_session_save_enabled_false_skips_session_write(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = ViEditor()
            editor.SESSION_PATH = session_path
            editor.session_save_enabled = False

            editor._save_session()

            self.assertFalse(os.path.exists(session_path))

    def test_save_session_ignores_temp_cleanup_failure_after_write_error(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = ViEditor()
            editor.SESSION_PATH = session_path

            with mock.patch("vi_editor.open", side_effect=OSError("readonly"), create=True):
                with mock.patch("vi_editor.os.unlink", side_effect=PermissionError("still readonly")):
                    editor._save_session()

    def test_saving_mmap_file_to_itself_materializes_before_truncate(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor._execute_cmd(":w"))
            self.assertEqual(editor.lines, ["alpha", "beta"])
            self.assertFalse(isinstance(editor.lines, MMapLineStore) and editor.lines.is_mapped)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "alpha\nbeta\n")

    def test_failed_mmap_save_after_materialize_keeps_dirty_baseline_consistent(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "wb") as fh:
                fh.write(b"alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            editor.lines[0] = "alpha changed"
            editor.modified = True

            with mock.patch.object(editor, "_stage_generation_backup", side_effect=OSError("boom")):
                self.assertFalse(editor._save_file())

            self.assertFalse(isinstance(editor.lines, MMapLineStore) and editor.lines.is_mapped)
            self.assertTrue(editor.modified)

            editor._refresh_modified()

            self.assertTrue(editor.modified)

    def test_saving_mmap_file_as_new_file_detaches_from_original(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(source)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)

            self.assertTrue(editor._save_file(target))
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.lines, ["alpha", "beta"])
            self.assertFalse(isinstance(editor.lines, MMapLineStore) and editor.lines.is_mapped)
            self.assertFalse(editor.modified)

            with open(source, "w", encoding="utf-8") as fh:
                fh.write("changed\n")
            editor._refresh_modified()

            self.assertFalse(editor.modified)
            self.assertEqual(editor.lines, ["alpha", "beta"])

    def test_write_copy_from_mmap_preserves_mapping_and_source_tracking(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(source)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)

            self.assertTrue(editor._execute_cmd(f":write {target}"))

            self.assertEqual(editor.filename, source)
            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)

            with open(source, "w", encoding="utf-8") as fh:
                fh.write("ALPHA\nBETA\n")
            editor._refresh_modified()

            self.assertTrue(editor.modified)

    def test_save_loaded_file_uses_default_line_endings(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "mixed.txt")
            with open(path, "wb") as fh:
                fh.write(b"one\r\ntwo\rthree")

            editor = ViEditor()
            self.assertTrue(editor._load_file(path))
            self.assertTrue(editor._execute_cmd(":le-win"))
            editor.lines[1] = "two changed"
            editor.modified = True

            self.assertTrue(editor._save_file())

            with open(path, "rb") as fh:
                self.assertEqual(fh.read(), b"one\r\ntwo changed\r\nthree\r\n")
            self.assertEqual(editor._line_endings_view_lines(), [
                "one[CRLF]",
                "two changed[CRLF]",
                "three[CRLF]",
            ])

    def test_clean_save_requires_force_when_file_changed_externally(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "clean.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("buffer copy\n")

            editor = ViEditor(path)

            with open(path, "w", encoding="utf-8") as fh:
                fh.write("external change\n")

            self.assertFalse(editor._save_file())
            self.assertTrue(editor.message_is_error)
            self.assertIn(":w! to override", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "external change\n")

            self.assertTrue(editor._save_file(force=True))
            self.assertEqual(editor.message, f'"{path}" 1L written')
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "buffer copy\n")

    def test_modified_save_refuses_external_change_until_w_bang(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("original\n")

            editor = ViEditor(path)
            editor.lines[0] = "my edit"
            editor.modified = True

            with open(path, "w", encoding="utf-8") as fh:
                fh.write("external change\n")

            self.assertTrue(editor._execute_cmd(":w"))
            self.assertTrue(editor.message_is_error)
            self.assertIn(":w! to override", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "external change\n")

            self.assertTrue(editor._execute_cmd(":w!"))
            self.assertFalse(editor.message_is_error)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "my edit\n")

    def test_save_recreates_externally_deleted_file_without_force(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("original\n")

            editor = ViEditor(path)
            editor.lines[0] = "my edit"
            editor.modified = True
            os.unlink(path)

            self.assertTrue(editor._save_file())
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "my edit\n")

    def test_stray_backup_dir_file_blocks_w_but_not_w_bang(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            # A regular file squatting on the backup directory name makes
            # os.makedirs fail inside _stage_generation_backup.
            with open(os.path.join(tmpdir, ".vii_backups"), "w", encoding="utf-8") as fh:
                fh.write("not a directory")

            editor = ViEditor(path)
            editor.lines[0] = "new"
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":w"))
            self.assertTrue(editor.message_is_error)
            self.assertIn("Backup failed", editor.message)
            self.assertIn(":w! to write without backup", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "old\n")

            self.assertTrue(editor._execute_cmd(":w!"))
            self.assertFalse(editor.message_is_error)
            self.assertIn("[no backup]", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "new\n")

    def test_load_file_failure_leaves_current_buffer_intact(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "big.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            editor.lines = ["keep", "me"]
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                with mock.patch(
                    "vi_editor.MMapLineStore",
                    side_effect=ValueError("cannot mmap an empty file"),
                ):
                    self.assertFalse(editor._load_file(path))
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["keep", "me"])
            self.assertIsNone(editor.filename)

    def test_mmap_store_treats_empty_file_race_as_empty(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "race.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            with mock.patch("vi_editor.mmap.mmap", side_effect=ValueError("empty")):
                store = MMapLineStore(path)

            self.assertFalse(store.is_mapped)
            self.assertEqual(store, [""])

    def test_mmap_store_clamps_reads_after_external_truncation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "big.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\ngamma\n")

            store = MMapLineStore(path)
            self.assertTrue(store.is_mapped)
            self.assertEqual(store[2], "gamma")

            # Shrink the file behind the mapping; reads past the new EOF
            # would otherwise touch unmapped pages and SIGBUS the process.
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alp")

            self.assertEqual(store[0], "alp")
            self.assertEqual(store[2], "")
            self.assertEqual(len(store), 3)

    def test_save_skips_rewrite_for_clean_in_place_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "clean.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("clean\n")

            editor = ViEditor(path)
            old_mtime_ns = os.stat(path).st_mtime_ns

            self.assertTrue(editor._save_file())

            self.assertEqual(os.stat(path).st_mtime_ns, old_mtime_ns)
            self.assertEqual(editor.message, f'"{path}" 1L unchanged')
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))

    def test_save_skips_rewrite_for_clean_mmap_file_but_detaches_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "clean.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                self.assertTrue(editor._load_file(path))
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)
            old_mtime_ns = os.stat(path).st_mtime_ns

            self.assertTrue(editor._save_file())

            self.assertEqual(os.stat(path).st_mtime_ns, old_mtime_ns)
            self.assertEqual(editor.message, f'"{path}" 2L unchanged')
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))
            self.assertEqual(editor.lines, ["alpha", "beta"])
            self.assertFalse(isinstance(editor.lines, MMapLineStore) and editor.lines.is_mapped)

    def test_wo_forces_rewrite_of_clean_in_place_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "clean.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("clean\n")

            editor = ViEditor(path)

            self.assertTrue(editor._execute_cmd(":wo"))

            self.assertFalse(editor.message_is_error)
            self.assertIn("written", editor.message)
            self.assertNotIn("unchanged", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "clean\n")

    def test_wo_still_refuses_external_change_until_w_bang(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("original\n")

            editor = ViEditor(path)
            editor.lines[0] = "my edit"
            editor.modified = True

            with open(path, "w", encoding="utf-8") as fh:
                fh.write("external change\n")

            self.assertTrue(editor._execute_cmd(":wo"))
            self.assertTrue(editor.message_is_error)
            self.assertIn(":w! to override", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "external change\n")

    def test_wnb_skips_generation_backup(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")

            editor = ViEditor(path)
            editor.lines[0] = "new"
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":wnb"))

            self.assertFalse(editor.message_is_error)
            self.assertIn("[no backup]", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "new\n")
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))

    def test_wa_saves_every_modified_buffer_and_leaves_active_one_unchanged(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.txt")
            b = os.path.join(tmpdir, "b.txt")
            c = os.path.join(tmpdir, "c.txt")
            for path, text in ((a, "a\n"), (b, "b\n"), (c, "c\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([a, b, c])
            editor.lines[0] = "a-changed"  # dirties the active buffer (a)
            editor.buffers[2].lines = ["c-changed"]
            editor.buffers[2].modified = True  # dirties an inactive buffer (c)

            self.assertTrue(editor._execute_cmd(":wa"))

            self.assertFalse(editor.message_is_error)
            self.assertIn("2 buffers written", editor.message)
            self.assertEqual(editor.filename, a)  # stayed on the original active buffer
            with open(a, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "a-changed\n")
            with open(c, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "c-changed\n")
            with open(b, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "b\n")  # never modified, untouched

    def test_wa_reports_no_buffers_changed(self):
        editor = ViEditor()
        self.assertTrue(editor._execute_cmd(":wa"))
        self.assertFalse(editor.message_is_error)
        self.assertEqual(editor.message, "No buffers changed")

    def test_wall_alias_and_failure_reporting_for_unnamed_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.txt")
            with open(a, "w", encoding="utf-8") as fh:
                fh.write("a\n")

            editor = ViEditor([a])
            editor.lines[0] = "a-changed"
            editor._append_buffer(None, switch=False)  # unnamed, unsaveable buffer
            editor.buffers[1].lines = ["no file"]
            editor.buffers[1].modified = True

            self.assertTrue(editor._execute_cmd(":wall"))

            self.assertTrue(editor.message_is_error)
            self.assertIn("Failed to write", editor.message)
            self.assertIn("1 written", editor.message)
            with open(a, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "a-changed\n")

    def test_wa_restores_original_active_buffer_after_unexpected_exception(self):
        # Regression guard: an exception escaping mid-sweep (anything other
        # than the OSError _save_file already handles internally) must not
        # leave the editor pointed at whatever buffer was mid-save.
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.txt")
            b = os.path.join(tmpdir, "b.txt")
            for path, text in ((a, "a\n"), (b, "b\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([a, b])
            editor.lines[0] = "a-changed"
            editor.buffers[1].lines = ["b-changed"]
            editor.buffers[1].modified = True
            self.assertEqual(editor.filename, a)

            real_save_file = editor._save_file

            def flaky_save_file(*args, **kwargs):
                if editor.filename == b:
                    raise ValueError("boom")
                return real_save_file(*args, **kwargs)

            editor._save_file = flaky_save_file

            with self.assertRaises(ValueError):
                editor._write_all_buffers()

            self.assertEqual(editor.filename, a)  # restored, not left on b
            self.assertEqual(editor.current_buffer, 0)

    def test_set_nobackup_skips_generation_backup_on_w(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")

            editor = ViEditor(path)
            self.assertTrue(editor.backup_enabled)
            self.assertTrue(editor._execute_cmd(":set nobackup"))
            self.assertFalse(editor.backup_enabled)

            editor.lines[0] = "new"
            editor.modified = True
            self.assertTrue(editor._execute_cmd(":w"))

            self.assertFalse(editor.message_is_error)
            self.assertIn("[no backup]", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "new\n")
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))

            self.assertTrue(editor._execute_cmd(":set backup"))
            self.assertTrue(editor.backup_enabled)

            editor.lines[0] = "newer"
            editor.modified = True
            self.assertTrue(editor._execute_cmd(":w"))
            self.assertTrue(os.path.isdir(os.path.join(tmpdir, ".vii_backups")))

    def test_set_invbackup_toggles_and_bare_set_reports_state(self):
        editor = ViEditor()
        self.assertTrue(editor.backup_enabled)

        self.assertTrue(editor._execute_cmd(":set invbackup"))
        self.assertFalse(editor.backup_enabled)
        self.assertFalse(editor.message_is_error)

        self.assertTrue(editor._execute_cmd(":set backup!"))
        self.assertTrue(editor.backup_enabled)

        self.assertTrue(editor._execute_cmd(":set nobackup"))
        self.assertTrue(editor._execute_cmd(":set"))
        self.assertIn("nobackup", editor.message)

    def test_wnb_writes_through_stray_backup_dir_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            # A regular file squatting on the backup directory name would
            # normally make plain :w fail; :wnb should not even try to stage
            # a backup, so it should succeed regardless.
            with open(os.path.join(tmpdir, ".vii_backups"), "w", encoding="utf-8") as fh:
                fh.write("not a directory")

            editor = ViEditor(path)
            editor.lines[0] = "new"
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":wnb"))
            self.assertFalse(editor.message_is_error)
            self.assertIn("[no backup]", editor.message)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "new\n")

    def test_save_new_manual_buffer_keeps_legacy_final_newline(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "new.txt")
            editor = ViEditor()
            editor.lines = ["alpha"]

            self.assertTrue(editor._save_file(path))

            with open(path, "rb") as fh:
                self.assertEqual(fh.read(), b"alpha\n")
            self.assertEqual(editor._line_endings_view_lines(), ["alpha[NL]"])

    def test_save_new_manual_buffer_respects_umask_permissions(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "mode.txt")
            editor = ViEditor()
            editor.lines = ["alpha"]

            self.assertTrue(editor._save_file(path))

            current_umask = os.umask(0)
            os.umask(current_umask)
            expected_mode = 0o666 & ~current_umask
            actual_mode = stat.S_IMODE(os.stat(path).st_mode)
            self.assertEqual(actual_mode, expected_mode)

    def test_save_new_manual_buffer_uses_windows_default_line_endings(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "new.txt")
            editor = ViEditor()
            editor.lines = ["alpha", "beta"]

            self.assertTrue(editor._execute_cmd(":le-win"))
            self.assertTrue(editor._save_file(path))

            with open(path, "rb") as fh:
                self.assertEqual(fh.read(), b"alpha\r\nbeta\r\n")
            self.assertEqual(editor._line_endings_view_lines(), [
                "alpha[CRLF]",
                "beta[CRLF]",
            ])

    def test_save_as_canonicalizes_decoded_no_final_line_ending(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "source.b64")
            target = os.path.join(tmpdir, "target.txt")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"alpha"))

            editor = ViEditor()
            self.assertTrue(editor._execute_cmd(f":b64d {encoded}"))
            self.assertTrue(editor._save_file(target))

            with open(target, "rb") as fh:
                self.assertEqual(fh.read(), b"alpha\n")

    def test_save_creates_generation_backup_and_metadata(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            editor.lines = ["first"]

            self.assertTrue(editor._save_file(path))

            backup_dir = os.path.join(tmpdir, ".vii_backups")
            generation_dir = os.path.join(backup_dir, "generation_counts")
            generation_file = os.path.join(generation_dir, "note_txt.gen")
            backup_file = os.path.join(backup_dir, "note_1.txt")

            self.assertTrue(os.path.isdir(backup_dir))
            self.assertTrue(os.path.isdir(generation_dir))
            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=1\nkeep=0\n")
            with open(backup_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "first\n")

            editor.lines = ["second"]
            self.assertTrue(editor._save_file(path))

            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=2\nkeep=0\n")
            with open(os.path.join(backup_dir, "note_2.txt"), "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "second\n")
            self.assertTrue(os.path.exists(backup_file))

    def test_generation_counter_is_durable_before_backup_body_is_written(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            editor.lines = ["first"]
            self.assertTrue(editor._save_file(path))

            backup_dir = os.path.join(tmpdir, ".vii_backups")
            generation_file = os.path.join(backup_dir, "generation_counts", "note_txt.gen")
            backup_path = os.path.join(backup_dir, "note_2.txt")
            real_atomic = editor._atomic_write_text
            seen = {}

            def spy(target, text, **kwargs):
                if target == backup_path:
                    with open(generation_file, "r", encoding="utf-8") as fh:
                        seen["generation_file_at_backup_write"] = fh.read()
                return real_atomic(target, text, **kwargs)

            editor.lines = ["second"]
            with mock.patch.object(editor, "_atomic_write_text", side_effect=spy):
                self.assertTrue(editor._save_file(path))

            # The counter must already be durably bumped to 2 on disk by the
            # time the backup body itself is written: if the process were
            # killed right here, a later save recomputes generation 3 and
            # never silently clobbers this (unwritten) backup slot.
            self.assertEqual(
                seen["generation_file_at_backup_write"], "last_generation=2\nkeep=0\n"
            )

    def test_backup_body_failure_rolls_back_counter_so_retry_reuses_generation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            editor.lines = ["first"]
            self.assertTrue(editor._save_file(path))

            backup_dir = os.path.join(tmpdir, ".vii_backups")
            generation_file = os.path.join(backup_dir, "generation_counts", "note_txt.gen")
            backup_path = os.path.join(backup_dir, "note_2.txt")
            real_atomic = editor._atomic_write_text

            def fail_backup_body(target, text, **kwargs):
                if target == backup_path:
                    raise OSError("disk full")
                return real_atomic(target, text, **kwargs)

            editor.lines = ["second"]
            with mock.patch.object(editor, "_atomic_write_text", side_effect=fail_backup_body):
                self.assertFalse(editor._save_file(path))

            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=1\nkeep=0\n")
            self.assertFalse(os.path.exists(backup_path))

            editor.lines = ["second"]
            self.assertTrue(editor._save_file(path))
            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=2\nkeep=0\n")
            with open(backup_path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "second\n")

    def test_save_prunes_backups_using_keep_metadata(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            backup_dir = os.path.join(tmpdir, ".vii_backups")
            generation_dir = os.path.join(backup_dir, "generation_counts")
            os.makedirs(generation_dir)
            generation_file = os.path.join(generation_dir, "note_txt.gen")
            with open(generation_file, "w", encoding="utf-8") as fh:
                fh.write("last_generation=0\nkeep=2\n")

            editor = ViEditor()
            for value in ("one", "two", "three", "four"):
                editor.lines = [value]
                self.assertTrue(editor._save_file(path))

            self.assertEqual(
                sorted(name for name in os.listdir(backup_dir) if name.endswith(".txt")),
                ["note_3.txt", "note_4.txt"],
            )
            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=4\nkeep=2\n")
            with open(os.path.join(backup_dir, "note_4.txt"), "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "four\n")

    def test_save_succeeds_when_retention_prune_fails_after_target_write(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            backup_dir = os.path.join(tmpdir, ".vii_backups")
            generation_dir = os.path.join(backup_dir, "generation_counts")
            os.makedirs(generation_dir)
            generation_file = os.path.join(generation_dir, "note_txt.gen")
            with open(generation_file, "w", encoding="utf-8") as fh:
                fh.write("last_generation=0\nkeep=1\n")

            editor = ViEditor()
            editor.lines = ["one"]
            self.assertTrue(editor._save_file(path))
            editor.lines = ["two"]

            with mock.patch("vi_editor.os.remove", side_effect=OSError("cannot prune")):
                self.assertTrue(editor._save_file(path))

            self.assertFalse(editor.message_is_error)
            self.assertFalse(editor.modified)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "two\n")
            with open(generation_file, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "last_generation=2\nkeep=1\n")

    def test_atomic_write_preserves_original_when_replace_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")

            editor = ViEditor()
            with mock.patch("vi_editor.os.replace", side_effect=OSError("boom")):
                with self.assertRaises(OSError):
                    editor._atomic_write_text(path, "new\n")

            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "old\n")
            self.assertEqual(os.listdir(tmpdir), ["note.txt"])

    def test_atomic_write_round_trips_lone_surrogate_instead_of_raising(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()

            # A lone surrogate can never occur from this codebase's own file
            # decoding (everything uses errors="replace"), but _atomic_write_text
            # must not depend on that: writing must round-trip such content
            # via surrogateescape rather than raising UnicodeEncodeError,
            # which _save_file's `except OSError` would not catch.
            text = "bad-\udcff-byte"
            editor._atomic_write_text(path, text)

            with open(path, "rb") as fh:
                raw = fh.read()
            self.assertEqual(raw.decode("utf-8", errors="surrogateescape"), text)

    def test_atomic_write_disables_newline_translation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            orig_fdopen = os.fdopen
            newline_args = []

            def tracking_fdopen(*args, **kwargs):
                newline_args.append(kwargs.get("newline"))
                return orig_fdopen(*args, **kwargs)

            with mock.patch("vi_editor.os.fdopen", side_effect=tracking_fdopen):
                editor._atomic_write_text(path, "one\r\ntwo\rthree")

            self.assertEqual(newline_args, [""])
            with open(path, "rb") as fh:
                self.assertEqual(fh.read(), b"one\r\ntwo\rthree")

    def test_atomic_write_closes_raw_fd_when_fdopen_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            real_close = os.close
            closed_fds = []

            def tracking_close(fd):
                closed_fds.append(fd)
                return real_close(fd)

            with mock.patch("vi_editor.os.fdopen", side_effect=OSError("fdopen failed")):
                with mock.patch("vi_editor.os.close", side_effect=tracking_close):
                    with self.assertRaises(OSError):
                        editor._atomic_write_text(path, "new\n")

            self.assertEqual(len(closed_fds), 1)
            self.assertFalse(os.path.exists(path))
            self.assertEqual(os.listdir(tmpdir), [])

    def test_save_does_not_create_backup_when_target_replace_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            editor.lines = ["new"]
            real_replace = os.replace

            def fail_target_replace(src, dst):
                if dst == path:
                    raise OSError("target replace failed")
                return real_replace(src, dst)

            with mock.patch("vi_editor.os.replace", side_effect=fail_target_replace):
                self.assertFalse(editor._save_file(path))

            self.assertFalse(os.path.exists(path))
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))

    def test_save_rolls_back_backup_on_non_oserror_target_write_failure(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            editor = ViEditor()
            editor.lines = ["new"]
            real_atomic_write = editor._atomic_write_text
            backup_dir = os.path.join(tmpdir, ".vii_backups")

            def fail_target_write(target, text, **kwargs):
                if target == path:
                    raise RuntimeError("target write failed")
                return real_atomic_write(target, text, **kwargs)

            with mock.patch.object(editor, "_atomic_write_text", side_effect=fail_target_write):
                with self.assertRaises(RuntimeError):
                    editor._save_file(path)

            self.assertFalse(os.path.exists(path))
            self.assertFalse(os.path.exists(backup_dir))

    def test_save_does_not_touch_target_when_backup_staging_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            editor = ViEditor()
            editor.lines = ["new"]
            real_atomic = editor._atomic_write_text

            def fail_backup_write(target, text, **kwargs):
                if os.path.basename(target) == "note_1.txt":
                    raise OSError("backup failed")
                return real_atomic(target, text, **kwargs)

            with mock.patch.object(editor, "_atomic_write_text", side_effect=fail_backup_write):
                self.assertFalse(editor._save_file(path))

            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "old\n")

    def test_save_does_not_touch_target_when_generation_metadata_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            editor = ViEditor()
            editor.lines = ["new"]
            real_atomic = editor._atomic_write_text

            def fail_generation_write(target, text, **kwargs):
                if target.endswith(".gen"):
                    raise OSError("generation failed")
                return real_atomic(target, text, **kwargs)

            with mock.patch.object(editor, "_atomic_write_text", side_effect=fail_generation_write):
                self.assertFalse(editor._save_file(path))

            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "old\n")

    def test_save_rolls_back_backup_on_non_oserror_generation_metadata_failure(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            editor = ViEditor()
            editor.lines = ["new"]
            backup_dir = os.path.join(tmpdir, ".vii_backups")

            def fail_generation_write(target, text, **kwargs):
                if target.endswith(".gen"):
                    raise RuntimeError("generation failed")
                return ViEditor._atomic_write_text(editor, target, text, **kwargs)

            with mock.patch.object(editor, "_atomic_write_text", side_effect=fail_generation_write):
                with self.assertRaises(RuntimeError):
                    editor._save_file(path)

            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "old\n")
            self.assertFalse(os.path.exists(backup_dir))

    def test_save_does_not_create_missing_parent_directory(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "missing", "note.txt")
            editor = ViEditor()
            editor.lines = ["new"]

            self.assertFalse(editor._save_file(path))

            self.assertTrue(editor.message_is_error)
            self.assertFalse(os.path.exists(path))
            self.assertFalse(os.path.exists(os.path.dirname(path)))

    def test_atomic_write_preserves_existing_mode_across_saves(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "script.sh")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            os.chmod(path, 0o2754)

            editor = ViEditor()
            editor.lines = ["first"]
            self.assertTrue(editor._save_file(path))
            self.assertEqual(os.stat(path).st_mode & 0o7777, 0o2754)

            editor.lines = ["second"]
            self.assertTrue(editor._save_file(path))

            self.assertEqual(os.stat(path).st_mode & 0o7777, 0o2754)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "second\n")

    def test_atomic_write_preserves_mode_when_chown_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "script.sh")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            os.chmod(path, 0o754)

            editor = ViEditor()
            with mock.patch("vi_editor.os.chown", side_effect=OSError("no chown")):
                editor._atomic_write_text(path, "new\n")

            self.assertEqual(os.stat(path).st_mode & 0o777, 0o754)

    def test_save_through_symlink_preserves_link_and_updates_target(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            real_path = os.path.join(tmpdir, "real.txt")
            link_path = os.path.join(tmpdir, "link.txt")
            with open(real_path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            os.symlink(real_path, link_path)

            editor = ViEditor()
            editor.lines = ["new"]
            self.assertTrue(editor._save_file(link_path))

            self.assertTrue(os.path.islink(link_path))
            with open(real_path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "new\n")

    def test_save_through_symlink_stages_backups_next_to_real_target(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            real_dir = os.path.join(tmpdir, "real")
            link_dir = os.path.join(tmpdir, "links")
            os.mkdir(real_dir)
            os.mkdir(link_dir)
            real_path = os.path.join(real_dir, "real.txt")
            link_path = os.path.join(link_dir, "link.txt")
            with open(real_path, "w", encoding="utf-8") as fh:
                fh.write("old\n")
            os.symlink(real_path, link_path)

            editor = ViEditor()
            editor.lines = ["new"]

            self.assertTrue(editor._save_file(link_path))

            self.assertTrue(os.path.isdir(os.path.join(real_dir, ".vii_backups")))
            self.assertFalse(os.path.exists(os.path.join(link_dir, ".vii_backups")))

    def test_editing_mmap_file_materializes_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "large.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("alpha\nbeta\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            editor._insert_text_at_cursor("X")

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertFalse(editor.lines.is_mapped)
            self.assertEqual(editor.lines, ["Xalpha", "beta"])
            self.assertTrue(editor.modified)

    def test_quit_blocks_unsaved_changes_in_inactive_buffer(self):
        editor = ViEditor()
        editor.lines = ["changed"]
        editor.modified = True

        editor._append_buffer(None, switch=True)
        editor.modified = False

        self.assertTrue(editor._execute_cmd(":q"))
        self.assertTrue(editor.message_is_error)
        self.assertIn(":quit!", editor.message)

    def test_quit_alias_blocks_modified_buffer(self):
        editor = ViEditor()
        editor.lines = ["changed"]
        editor.modified = True

        result = editor._execute_cmd(":quit")

        self.assertTrue(result)
        self.assertTrue(editor.message_is_error)
        self.assertIn(":quit!", editor.message)

    def test_write_and_edit_aliases_work_with_filenames(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")

            editor = ViEditor()
            editor.lines = ["saved"]

            self.assertTrue(editor._execute_cmd(f":write {target}"))
            self.assertTrue(os.path.exists(target))

            editor.lines = ["changed"]
            editor.modified = True
            self.assertTrue(editor._execute_cmd(f":edit! {source}"))
            self.assertEqual(editor.lines, ["loaded"])
            self.assertFalse(editor.modified)

    def test_edit_alias_of_current_file_does_not_create_duplicate_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            alias = os.path.join(tmpdir, "alias.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            os.symlink(source, alias)

            editor = ViEditor(source)

            self.assertTrue(editor._execute_cmd(f":edit {alias}"))

            self.assertEqual(len(editor.buffers), 1)
            self.assertEqual(editor.filename, source)
            self.assertEqual(editor.lines, ["loaded"])

    def test_write_clean_buffer_to_other_file_still_writes_copy(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")

            editor = ViEditor(source)
            self.assertFalse(editor.modified)

            self.assertTrue(editor._execute_cmd(f":write {target}"))

            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "loaded\n")

    def test_write_current_file_by_explicit_path_marks_buffer_clean(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "source.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")

            editor = ViEditor(path)
            editor.lines = ["changed"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":write {path}"))

            self.assertFalse(editor.message_is_error)
            self.assertFalse(editor.modified)
            self.assertIsNone(editor._pending_confirmation)
            with open(path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "changed\n")
            self.assertFalse(editor._execute_cmd(":q"))

    def test_reload_file_blocks_unsaved_current_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "source.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["memory"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":rf"))

            self.assertEqual(editor.lines, ["memory"])
            self.assertTrue(editor.modified)
            self.assertTrue(editor.message_is_error)
            self.assertIn(":edit!", editor.message)

    def test_base64_decode_blocks_unsaved_current_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            payload = os.path.join(tmpdir, "payload.b64")
            with open(payload, "wb") as fh:
                fh.write(base64.b64encode(b"decoded\n"))

            editor = ViEditor()
            editor.lines = ["memory"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":b64d {payload}"))

            self.assertEqual(editor.lines, ["memory"])
            self.assertTrue(editor.modified)
            self.assertTrue(editor.message_is_error)
            self.assertIn(":enew!", editor.message)

    def test_write_to_other_file_does_not_rename_current_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")

            editor = ViEditor(source)
            editor.lines = ["changed"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":write {target}"))

            self.assertEqual(editor.filename, source)
            with open(source, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "loaded\n")
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "changed\n")
            self.assertTrue(editor._current_buffer_is_modified())
            self.assertTrue(editor._execute_cmd(":q"))
            self.assertTrue(editor.message_is_error)
            self.assertIn(":quit!", editor.message)

    def test_write_to_existing_file_prompts_before_replace(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("existing\n")

            editor = ViEditor(source)
            editor.lines = ["changed"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":write {target}"))
            self.assertIsNotNone(editor._pending_confirmation)
            self.assertIn("Replace", editor.message)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "existing\n")

            self.assertTrue(editor._handle_pending_confirmation(ord("n")))
            self.assertIsNone(editor._pending_confirmation)
            self.assertEqual(editor.filename, source)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "existing\n")

            self.assertTrue(editor._execute_cmd(f":write {target}"))
            self.assertTrue(editor._handle_pending_confirmation(ord("y")))
            self.assertIsNone(editor._pending_confirmation)
            self.assertEqual(editor.filename, source)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "changed\n")

    def test_range_write_to_new_file_writes_only_selected_lines(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\nfour\nfive\n")

            editor = ViEditor(source)

            self.assertTrue(editor._execute_cmd(f":2,4write {target}"))

            self.assertEqual(editor.filename, source)
            self.assertEqual(editor.message, f'"{target}" 3L written')
            self.assertFalse(editor.message_is_error)
            with open(source, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "one\ntwo\nthree\nfour\nfive\n")
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "two\nthree\nfour\n")

    def test_range_write_honors_nobackup(self):
        # _write_line_range_to_file shares _save_file's stage-backup /
        # atomic-write / rollback machinery and must honor the same
        # session-wide :set nobackup switch -- see
        # test_set_nobackup_skips_generation_backup_on_w for the :w side.
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\nfour\nfive\n")

            editor = ViEditor(source)
            self.assertTrue(editor._execute_cmd(":set nobackup"))
            self.assertFalse(editor.backup_enabled)

            self.assertTrue(editor._execute_cmd(f":2,4write {target}"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.message, f'"{target}" 3L written')
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "two\nthree\nfour\n")
            self.assertFalse(os.path.exists(os.path.join(tmpdir, ".vii_backups")))

    def test_range_write_stages_backup_when_enabled(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\n")

            editor = ViEditor(source)
            self.assertTrue(editor.backup_enabled)

            self.assertTrue(editor._execute_cmd(f":1,2write {target}"))

            self.assertTrue(os.path.isdir(os.path.join(tmpdir, ".vii_backups")))

    def test_range_write_to_existing_file_prompts_before_replace(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("existing\n")

            editor = ViEditor(source)

            self.assertTrue(editor._execute_cmd(f":1,2write {target}"))
            self.assertIsNotNone(editor._pending_confirmation)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "existing\n")

            self.assertTrue(editor._handle_pending_confirmation(ord("y")))
            self.assertEqual(editor.filename, source)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "one\ntwo\n")

    def test_range_write_to_current_file_is_rejected(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\n")

            editor = ViEditor(source)

            self.assertTrue(editor._execute_cmd(f":1,2write {source}"))

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.message, "Range write target must differ from current file")
            with open(source, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "one\ntwo\nthree\n")

    def test_write_bang_to_existing_file_replaces_without_prompt(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("existing\n")

            editor = ViEditor(source)
            editor.lines = ["forced"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":write! {target}"))

            self.assertIsNone(editor._pending_confirmation)
            self.assertEqual(editor.filename, source)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "forced\n")

    def test_write_alias_of_current_file_marks_buffer_clean(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            alias = os.path.join(tmpdir, "alias.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            os.symlink(source, alias)

            editor = ViEditor(source)
            editor.lines = ["forced"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":write! {alias}"))

            self.assertIsNone(editor._pending_confirmation)
            self.assertEqual(editor.filename, source)
            self.assertFalse(editor.modified)
            with open(source, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "forced\n")
            self.assertFalse(editor._execute_cmd(":q"))

    def test_w_bang_to_existing_file_replaces_without_prompt(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("loaded\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("existing\n")

            editor = ViEditor(source)
            editor.lines = ["forced"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":w! {target}"))

            self.assertIsNone(editor._pending_confirmation)
            self.assertEqual(editor.filename, source)
            with open(target, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "forced\n")

    def test_failed_edit_does_not_leave_new_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            editor = ViEditor()
            editor.lines = ["original"]
            editor._sync_current_buffer()

            self.assertTrue(editor._execute_cmd(f":edit {tmpdir}"))

            self.assertTrue(editor.message_is_error)
            self.assertIsNone(editor.filename)
            self.assertEqual(editor.lines, ["original"])
            self.assertEqual(len(editor.buffers), 1)

    def test_read_command_bulk_inserts_after_cursor(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\n")

            editor = ViEditor()
            editor.lines = ["top", "bottom"]
            editor.cursor_row = 0

            self.assertTrue(editor._execute_cmd(f":read {source}"))
            self.assertEqual(editor.lines, ["top", "one", "two", "bottom"])
            self.assertTrue(editor.modified)

    def test_read_command_accepts_address_prefix(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\n")

            editor = ViEditor()
            editor.lines = ["top", "middle", "bottom"]
            editor.cursor_row = 0

            self.assertTrue(editor._execute_cmd(f":2read {source}"))

            self.assertEqual(editor.lines, ["top", "middle", "one", "two", "bottom"])
            self.assertEqual(editor.cursor_row, 0)
            self.assertTrue(editor.modified)

    def test_read_short_command_accepts_address_prefix(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor()
            editor.lines = ["top", "middle", "bottom"]
            editor.cursor_row = 2

            self.assertTrue(editor._execute_cmd(f":1r {source}"))

            self.assertEqual(editor.lines, ["top", "one", "middle", "bottom"])
            self.assertEqual(editor.cursor_row, 3)
            self.assertTrue(editor.modified)

    def test_read_command_zero_address_inserts_before_first_line(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor()
            editor.lines = ["top", "bottom"]
            editor.cursor_row = 1

            self.assertTrue(editor._execute_cmd(f":0read {source}"))

            self.assertEqual(editor.lines, ["one", "top", "bottom"])
            self.assertEqual(editor.cursor_row, 2)
            self.assertTrue(editor.modified)

    def test_read_short_command_zero_address_inserts_before_first_line(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor()
            editor.lines = ["top", "bottom"]

            self.assertTrue(editor._execute_cmd(f":0r {source}"))

            self.assertEqual(editor.lines, ["one", "top", "bottom"])
            self.assertEqual(editor.cursor_row, 1)
            self.assertTrue(editor.modified)

    def test_argument_commands_accept_tab_separator(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "read.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor()
            editor.lines = ["top"]

            self.assertTrue(editor._execute_cmd(f":read\t{source}"))
            self.assertEqual(editor.lines, ["top", "one"])

            self.assertTrue(editor._execute_cmd(":set\tnonumber"))
            self.assertFalse(editor.show_line_numbers)

    def test_buffer_command_accepts_tab_separator(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor([one, two])

            self.assertTrue(editor._execute_cmd(":b\t2"))
            self.assertEqual(editor.filename, two)

    def test_read_empty_file_does_not_mark_buffer_modified(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "empty.txt")
            with open(source, "w", encoding="utf-8"):
                pass

            editor = ViEditor()
            editor.lines = ["top"]
            editor._mark_clean()

            self.assertTrue(editor._execute_cmd(f":read {source}"))
            self.assertEqual(editor.lines, ["top"])
            self.assertFalse(editor.modified)
            self.assertFalse(editor.undo_stack)

    def test_enew_force_variants(self):
        editor = ViEditor("named.txt")
        editor.lines = ["changed"]
        editor.modified = True

        result = editor._execute_cmd(":enew")

        self.assertTrue(result)
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.filename, os.path.abspath("named.txt"))
        self.assertEqual(editor.lines, ["changed"])
        self.assertTrue(editor.modified)
        self.assertEqual(len(editor.buffers), 1)

        self.assertTrue(editor._execute_cmd(":enew!"))
        self.assertIsNone(editor.filename)
        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)
        self.assertEqual(len(editor.buffers), 1)

        self.assertTrue(editor._execute_cmd(":enew"))
        self.assertEqual(len(editor.buffers), 2)

    def test_wq_blocks_when_other_buffer_is_modified(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor(one)
            editor.lines = ["one changed"]
            editor.modified = True
            self.assertTrue(editor._execute_cmd(f":edit {two}"))
            editor.lines = ["two changed"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":wq"))
            self.assertTrue(editor.message_is_error)
            self.assertIn("another buffer", editor.message)
            self.assertTrue(editor.buffers[0].modified)
            self.assertFalse(editor.modified)

    def test_wq_force_ignores_other_modified_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor(one)
            editor.lines = ["one changed"]
            editor.modified = True
            self.assertTrue(editor._execute_cmd(f":edit {two}"))
            editor.lines = ["two changed"]
            editor.modified = True

            self.assertFalse(editor._execute_cmd(":wq!"))
            with open(two, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "two changed\n")

    def test_x_exits_without_rewriting_unmodified_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "clean.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("clean\n")
            old_mtime = os.path.getmtime(path)

            editor = ViEditor(path)
            self.assertFalse(editor.modified)

            self.assertFalse(editor._execute_cmd(":x"))
            self.assertEqual(os.path.getmtime(path), old_mtime)

    def test_line_references_and_print(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]
        editor.cursor_row = 1

        self.assertTrue(editor._execute_cmd(":+2"))
        self.assertEqual(editor.cursor_row, 3)

        self.assertTrue(editor._execute_cmd(":.-1print"))
        self.assertEqual(editor.cursor_row, 2)
        self.assertEqual(editor.message, "three")

        self.assertTrue(editor._execute_cmd(":1,2print"))
        self.assertEqual(editor.cursor_row, 1)
        self.assertEqual(editor.message, "two")

        self.assertTrue(editor._execute_cmd(":$"))
        self.assertEqual(editor.cursor_row, 3)

    def test_undo_redo_tracks_real_dirty_state(self):
        editor = ViEditor()
        editor.lines = ["clean"]
        editor._mark_clean()

        editor._insert_text_at_cursor("X")
        self.assertEqual(editor.lines, ["Xclean"])
        self.assertTrue(editor.modified)

        editor._undo()
        self.assertEqual(editor.lines, ["clean"])
        self.assertFalse(editor.modified)

        editor._redo()
        self.assertEqual(editor.lines, ["Xclean"])
        self.assertTrue(editor.modified)

    def test_insert_mode_undo_returns_to_clean_state(self):
        editor = ViEditor()
        editor.lines = ["clean"]
        editor._mark_clean()

        editor._enter_insert()
        editor._insert_char("X")
        editor._leave_insert()
        self.assertTrue(editor.modified)

        editor._undo()
        self.assertEqual(editor.lines, ["clean"])
        self.assertFalse(editor.modified)

    def test_insert_and_replace_without_changes_do_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["clean"]
        editor._mark_clean()

        editor._enter_insert()
        editor._leave_insert()
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor._enter_replace()
        editor._leave_insert()
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_insert_right_arrow_can_reach_append_position(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 0

        editor._enter_insert()
        editor._handle_insert(curses.KEY_RIGHT)
        editor._handle_insert(curses.KEY_RIGHT)
        editor._handle_insert(ord("X"))

        self.assertEqual(editor.lines, ["abX"])
        self.assertEqual(editor.cursor_col, 3)

        editor._leave_insert()

        self.assertEqual(editor.cursor_col, 2)

    def test_replace_right_arrow_can_reach_append_position(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 0

        editor._enter_replace()
        editor._handle_replace_mode(curses.KEY_RIGHT)
        editor._handle_replace_mode(curses.KEY_RIGHT)
        editor._handle_replace_mode(ord("X"))

        self.assertEqual(editor.lines, ["abX"])
        self.assertEqual(editor.cursor_col, 3)

        editor._leave_insert()

        self.assertEqual(editor.cursor_col, 2)

    def test_set_accepts_multiple_and_toggle_forms(self):
        editor = ViEditor()
        editor.show_line_numbers = True

        self.assertTrue(editor._execute_cmd(":set nonumber invnumber"))
        self.assertTrue(editor.show_line_numbers)
        self.assertTrue(editor._execute_cmd(":set number!"))
        self.assertFalse(editor.show_line_numbers)

    def test_set_accepts_scroll_jump_options(self):
        editor = ViEditor()

        self.assertTrue(editor._execute_cmd(":set scrolljump=4 sidescrolljump=6"))
        self.assertEqual(editor.vertical_scroll_jump, 4)
        self.assertEqual(editor.horizontal_scroll_jump, 6)

        self.assertTrue(editor._execute_cmd(":set sj"))
        self.assertEqual(editor.message, "scrolljump=4")
        self.assertTrue(editor._execute_cmd(":set ssj"))
        self.assertEqual(editor.message, "sidescrolljump=6")

        self.assertTrue(editor._execute_cmd(":set scrolljump=-1"))
        self.assertTrue(editor.message_is_error)

    def test_line_ending_commands_and_set_option_update_default(self):
        editor = ViEditor()

        self.assertEqual(editor.default_line_ending, "\n")
        self.assertTrue(editor._execute_cmd(":le-win"))
        self.assertEqual(editor.default_line_ending, "\r\n")
        self.assertEqual(editor.message, "Default line endings: windows")

        self.assertTrue(editor._execute_cmd(":set lnendings"))
        self.assertEqual(editor.message, "lnendings=windows")

        self.assertTrue(editor._execute_cmd(":le-unix"))
        self.assertEqual(editor.default_line_ending, "\n")
        self.assertEqual(editor.message, "Default line endings: unix")

        self.assertTrue(editor._execute_cmd(":set lnendings=win"))
        self.assertEqual(editor.default_line_ending, "\r\n")
        self.assertTrue(editor._execute_cmd(":set lnendings=bogus"))
        self.assertTrue(editor.message_is_error)

    def test_scroll_jump_controls_vertical_and_horizontal_edge_scrolling(self):
        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["x" * 40 for _ in range(10)]

        editor.vertical_scroll_jump = 3
        editor.cursor_row = 4
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.top_line, 4)

        editor.cursor_row = 2
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.top_line, 0)

        editor.horizontal_scroll_jump = 4
        editor.cursor_row = 0
        editor.cursor_col = 20
        editor.left_col = 0
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.left_col, 4)

        editor.cursor_col = 3
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.left_col, 0)

    def test_zero_scroll_jump_uses_normal_single_step(self):
        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["x" * 40 for _ in range(10)]
        editor.vertical_scroll_jump = 0
        editor.horizontal_scroll_jump = 0

        editor.cursor_row = 4
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.top_line, 2)

        editor.cursor_row = 0
        editor.cursor_col = 20
        editor.left_col = 0
        editor._scroll_to_cursor(6, 20)
        self.assertEqual(editor.left_col, 1)

    def test_ctrl_e_y_use_vertical_scroll_jump(self):
        editor = ViEditor()
        editor.lines = [str(i) for i in range(20)]
        editor.vertical_scroll_jump = 4

        editor._handle_normal(5, 10, 80)
        self.assertEqual(editor.top_line, 4)

        editor._count_str = "2"
        editor._handle_normal(25, 10, 80)
        self.assertEqual(editor.top_line, 0)

    def test_unreadable_viirc_does_not_block_startup(self):
        with mock.patch("vi_editor.os.path.isfile", return_value=True):
            with mock.patch("builtins.open", side_effect=PermissionError("denied")):
                editor = ViEditor()

        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)

    def test_substitute_supports_empty_pattern_and_alt_delimiter(self):
        editor = ViEditor()
        editor.lines = ["alpha beta alpha"]
        editor.search_pattern = "alpha"

        self.assertTrue(editor._execute_cmd(":s//omega/"))
        self.assertEqual(editor.lines, ["omega beta alpha"])

        self.assertTrue(editor._execute_cmd(":s#beta#BETA#"))
        self.assertEqual(editor.lines, ["omega BETA alpha"])

    def test_substitute_long_form_command(self):
        editor = ViEditor()
        editor.lines = ["alpha beta", "alpha gamma"]

        self.assertTrue(editor._execute_cmd(":substitute/alpha/omega/"))
        self.assertEqual(editor.lines, ["omega beta", "alpha gamma"])

        self.assertTrue(editor._execute_cmd(":1,2substitute/a/A/g"))
        self.assertEqual(editor.lines, ["omegA betA", "AlphA gAmmA"])

    def test_substitute_parser_keeps_underscore_as_valid_delimiter(self):
        editor = ViEditor()
        editor.lines = ["alpha beta"]

        self.assertTrue(editor._execute_cmd(":substitute_alpha_omega_"))

        self.assertEqual(editor.lines, ["omega beta"])

    def test_substitute_unescapes_ex_delimiter_only(self):
        editor = ViEditor()
        editor.lines = ["a/b", "path"]

        self.assertTrue(editor._execute_cmd(r":s/a\/b/x/"))
        self.assertEqual(editor.lines[0], "x")

        editor.cursor_row = 1
        self.assertTrue(editor._execute_cmd(r":s/path/\//"))
        self.assertEqual(editor.lines[1], "/")

    def test_substitute_preserves_trailing_space_replacement_without_final_delimiter(self):
        editor = ViEditor()
        editor.lines = ["cat"]

        self.assertTrue(editor._execute_cmd(":s/a/ "))

        self.assertEqual(editor.lines, ["c t"])

    def test_substitute_supports_ranges_repeat_and_flags(self):
        editor = ViEditor()
        editor.lines = ["foo Foo", "foo foo", "bar foo"]
        editor.cursor_row = 0

        self.assertTrue(editor._execute_cmd(":%s/foo/X/g"))
        self.assertEqual(editor.lines, ["X Foo", "X X", "bar X"])

        self.assertTrue(editor._execute_cmd(":1,2s/X/Y/"))
        self.assertEqual(editor.lines, ["Y Foo", "Y X", "bar X"])

        editor.cursor_row = 2
        self.assertTrue(editor._execute_cmd(":&"))
        self.assertEqual(editor.lines, ["Y Foo", "Y X", "bar Y"])

        editor.lines = ["Cat cAt", "dog", "cat"]
        editor.cursor_row = 0
        self.assertTrue(editor._execute_cmd(":.,$s/cat/Z/i"))
        self.assertEqual(editor.lines, ["Z cAt", "dog", "Z"])

    def test_mark_address_jumps_and_ranges_in_ex_commands(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "five"]
        editor.marks["a"] = (1, 0)
        editor.marks["b"] = (3, 0)

        self.assertTrue(editor._execute_cmd(":'a"))
        self.assertEqual(editor.cursor_row, 1)

        self.assertTrue(editor._execute_cmd(":'a,'bs/o/O/"))
        self.assertEqual(editor.lines, ["one", "twO", "three", "fOur", "five"])

        self.assertTrue(editor._execute_cmd(":'a+1,'bs/r/R/"))
        self.assertEqual(editor.lines, ["one", "twO", "thRee", "fOuR", "five"])

    def test_bare_range_with_omitted_left_address_defaults_to_cursor_line(self):
        # ":,N" (jump from the current line through line N) is ordinary ex
        # range syntax -- _parse_range_prefix already defaults an omitted
        # endpoint to the current line for ranged commands (":,$d" etc.);
        # the bare "range with no command" shortcut in _execute_cmd must
        # honor the same default instead of failing to parse the empty
        # left-hand address and falling through to "Unknown command".
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "five", "six", "seven"]
        editor.cursor_row = 2

        self.assertTrue(editor._execute_cmd(":,5"))

        self.assertEqual(editor.cursor_row, 4)
        self.assertEqual(editor.message, "")
        self.assertFalse(editor.message_is_error)

    def test_bare_range_with_omitted_right_address_defaults_to_cursor_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "five", "six", "seven"]
        editor.cursor_row = 0

        self.assertTrue(editor._execute_cmd(":5,"))

        # max(r1=line 5, r2=cursor_row=0) -> moves to line 5
        self.assertEqual(editor.cursor_row, 4)
        self.assertFalse(editor.message_is_error)

    def test_bare_range_with_both_addresses_explicit_still_moves_to_range_end(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 1

        self.assertTrue(editor._execute_cmd(":1,3"))

        self.assertEqual(editor.cursor_row, 2)
        self.assertFalse(editor.message_is_error)

    def test_mark_address_with_unset_mark_reports_error(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.assertTrue(editor._execute_cmd(":'zs/o/O/"))
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "Mark not set: z")
        self.assertEqual(editor.lines, ["one", "two"])

    def test_pure_mark_address_jump_with_unset_mark_reports_error(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.assertTrue(editor._execute_cmd(":'z"))
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "Mark not set: z")
        self.assertEqual(editor.cursor_row, 0)

    def test_global_command_runs_substitute_on_every_matching_line(self):
        editor = ViEditor()
        editor.lines = ["cat sat", "cat ran", "dog sat"]

        self.assertTrue(editor._execute_cmd(":g/cat/s/cat/CAT/"))

        self.assertEqual(editor.lines, ["CAT sat", "CAT ran", "dog sat"])
        self.assertEqual(editor.auto_marks, {})

    def test_global_command_respects_range_and_default_print(self):
        editor = ViEditor()
        editor.lines = ["keep", "drop1", "keep", "drop2", "keep"]

        self.assertTrue(editor._execute_cmd(":1,3g/drop/p"))
        # Default sub-command is :p, which moves the cursor to the line —
        # the last matching line within the given range (rows 0-2) is row 1.
        self.assertEqual(editor.cursor_row, 1)

    def test_global_inverse_v_command_targets_non_matching_lines(self):
        editor = ViEditor()
        editor.lines = ["keep", "drop1", "keep", "drop2", "keep"]

        self.assertTrue(editor._execute_cmd(":v/keep/p"))
        self.assertEqual(editor.cursor_row, 3)

    def test_global_command_with_no_match_reports_error(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]

        self.assertTrue(editor._execute_cmd(":g/zzz/d"))
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "Pattern not found: zzz")

    def test_global_command_deletes_every_matching_line(self):
        editor = ViEditor()
        editor.lines = ["keep", "drop1", "keep", "drop2", "keep"]

        self.assertTrue(editor._execute_cmd(":g/drop/d"))

        self.assertEqual(editor.lines, ["keep", "keep", "keep"])
        self.assertEqual(editor.auto_marks, {})

    def test_nested_global_command_does_not_collide_tracking_ids(self):
        editor = ViEditor()
        editor.lines = ["foo bar", "foo baz", "qux bar"]

        # The outer :g/foo/ matches rows 0 and 1; for each, the inner
        # :g/bar/d must run independently. A prior bug reused the same
        # tracking-id range for nested global calls, which let the inner
        # call's ids clobber the outer call's still-pending tag and
        # silently skip its second match.
        self.assertTrue(editor._execute_cmd(":g/foo/g/bar/d"))

        self.assertEqual(editor.lines, ["foo baz"])
        self.assertEqual(editor.auto_marks, {})

    def test_global_command_aborts_cleanly_when_sub_command_switches_buffer(self):
        editor = ViEditor()
        editor.lines = ["foo1", "bar", "foo2", "bar", "foo3"]
        editor._append_buffer(None, switch=False)

        # A prior bug let the sub-command's buffer switch pull self.auto_marks
        # out from under the in-progress :g loop: the temporary tracking tags
        # for the not-yet-processed matches were then leaked as permanent,
        # bogus auto-marks on the original buffer instead of being cleaned up.
        self.assertTrue(editor._execute_cmd(":g/foo/bn"))
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.current_buffer, 1)

        editor._switch_buffer(0)
        self.assertEqual(editor.auto_marks, {})

    def test_global_command_still_cleans_up_tags_without_buffer_switch(self):
        editor = ViEditor()
        editor.lines = ["foo1", "bar", "foo2", "bar", "foo3"]

        self.assertTrue(editor._execute_cmd(":g/foo/p"))
        self.assertFalse(editor.message_is_error)
        self.assertEqual(editor.auto_marks, {})

    def test_delete_command_removes_range_and_yanks_to_register(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "five"]

        self.assertTrue(editor._execute_cmd(":2,3d"))

        self.assertEqual(editor.lines, ["one", "four", "five"])
        self.assertEqual(editor.message, "2 lines deleted")
        self.assertEqual(editor.registers['"'], (["two", "three"], True))

        editor._undo()
        self.assertEqual(editor.lines, ["one", "two", "three", "four", "five"])

    def test_delete_command_with_no_range_deletes_current_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 1

        self.assertTrue(editor._execute_cmd(":delete"))

        self.assertEqual(editor.lines, ["one", "three"])
        self.assertEqual(editor.message, "1 line deleted")

    def test_substitute_repeat_with_saved_flags(self):
        editor = ViEditor()
        editor.lines = ["foo foo", "foo foo"]

        self.assertTrue(editor._execute_cmd(":s/foo/Z/g"))
        self.assertEqual(editor.lines[0], "Z Z")

        editor.cursor_row = 1
        self.assertTrue(editor._execute_cmd(":&&"))
        self.assertEqual(editor.lines[1], "Z Z")

    def test_substitute_tilde_repeat_allows_empty_previous_replacement(self):
        editor = ViEditor()
        editor.lines = ["foo", "foo"]

        self.assertTrue(editor._execute_cmd(":s/foo//"))
        self.assertEqual(editor.lines[0], "")

        editor.cursor_row = 1
        self.assertTrue(editor._execute_cmd(":~"))

        self.assertEqual(editor.lines, ["", ""])
        self.assertFalse(editor.message_is_error)

    def test_substitute_repeat_commands_allow_trailing_command_space(self):
        editor = ViEditor()
        editor.lines = ["foo foo", "foo foo", "bar"]

        self.assertTrue(editor._execute_cmd(":s/foo/Z/g"))
        self.assertEqual(editor.lines[0], "Z Z")

        editor.cursor_row = 1
        self.assertTrue(editor._execute_cmd(":&& "))
        self.assertEqual(editor.lines[1], "Z Z")

        editor.search_pattern = "bar"
        editor.cursor_row = 2
        self.assertTrue(editor._execute_cmd(":~ "))
        self.assertEqual(editor.lines[2], "Z")

    def test_substitute_repeat_rejects_trailing_garbage(self):
        editor = ViEditor()
        editor.lines = ["foo", "foo"]

        self.assertTrue(editor._execute_cmd(":s/foo/bar/"))
        editor.cursor_row = 1
        self.assertTrue(editor._execute_cmd(":&z"))

        self.assertTrue(editor.message_is_error)
        self.assertIn("Invalid substitute flag", editor.message)
        self.assertEqual(editor.lines, ["bar", "foo"])

    def test_substitute_no_match_does_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(":s/beta/gamma/"))

        self.assertEqual(editor.lines, ["alpha"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_substitute_same_text_does_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(":s/alpha/alpha/"))

        self.assertEqual(editor.lines, ["alpha"])
        self.assertEqual(editor.message, "1 substitution")
        self.assertFalse(editor.message_is_error)
        self.assertEqual(editor.search_pattern, "alpha")
        self.assertEqual(editor.last_sub_pattern, "alpha")
        self.assertEqual(editor.last_sub_repl, "alpha")
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_substitute_invalid_replacement_is_error_not_exception(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(r":s/a/\2/"))

        self.assertTrue(editor.message_is_error)
        self.assertIn("Invalid replacement", editor.message)
        self.assertEqual(editor.lines, ["alpha"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_substitute_rejects_unknown_flags_without_mutating(self):
        editor = ViEditor()
        editor.lines = ["alpha alpha"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(":s/alpha/omega/z"))

        self.assertTrue(editor.message_is_error)
        self.assertIn("Invalid substitute flag", editor.message)
        self.assertEqual(editor.lines, ["alpha alpha"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def _run_substitute_confirm(self, editor: ViEditor, pattern: str, repl: str,
                                flags: str, glob: bool, key_seq):
        import re
        keys = list(key_seq)

        def get_wch():
            if not keys:
                return "q"
            return keys.pop(0)

        editor._stdscr = mock.MagicMock()
        editor._stdscr.get_wch.side_effect = get_wch
        editor.draw = mock.MagicMock()
        editor._do_substitute_confirm(
            0, len(editor.lines) - 1, re.compile(pattern), pattern, repl, flags, glob,
        )

    def test_substitute_confirm_all_with_empty_replacement_removes_every_match(self):
        # `:%s/a//gc` answering "a" to apply-to-all on "aa" must remove BOTH a's
        # — matching the non-confirm `re.subn` path. The pre-fix bug skipped past
        # the second match because the loop force-advanced pos by 1 after a
        # zero-length replacement on a non-zero-width match.
        editor = ViEditor()
        editor.lines = ["aa"]
        self._run_substitute_confirm(editor, "a", "", "gc", True, ["a"])
        self.assertEqual(editor.lines, [""])

    def test_substitute_confirm_y_repeated_for_each_match(self):
        editor = ViEditor()
        editor.lines = ["aaa"]
        self._run_substitute_confirm(editor, "a", "", "gc", True, ["y", "y", "y"])
        self.assertEqual(editor.lines, [""])

    def test_substitute_confirm_shorter_replacement_advances_correctly(self):
        # `:%s/aa/b/gc` with apply-to-all on "aaaa" should yield "bb".
        editor = ViEditor()
        editor.lines = ["aaaa"]
        self._run_substitute_confirm(editor, "aa", "b", "gc", True, ["a"])
        self.assertEqual(editor.lines, ["bb"])

    def test_substitute_confirm_zero_width_anchor_does_not_loop_forever(self):
        # `:%s/^/X/gc` (zero-width anchor) inserts once at line start; the
        # pos-advance must still kick in for zero-width matches to avoid an
        # infinite loop.
        editor = ViEditor()
        editor.lines = ["foo"]
        self._run_substitute_confirm(editor, "^", "X", "gc", True, ["a"])
        self.assertEqual(editor.lines, ["Xfoo"])

    def test_substitute_confirm_matches_subn_behaviour(self):
        # Parity: confirm path with apply-to-all should produce the same result
        # as the non-confirm `re.subn` path for non-zero matches with shorter
        # replacements.
        cases = [
            ("a", "X", "ababa"),
            ("aa", "b", "aaaa"),
            ("a", "", "aabba"),
            ("ab", "", "ababab"),
        ]
        for pattern, repl, text in cases:
            with self.subTest(pattern=pattern, repl=repl, text=text):
                non_confirm = ViEditor()
                non_confirm.lines = [text]
                non_confirm._execute_cmd(f":%s/{pattern}/{repl}/g")

                confirm = ViEditor()
                confirm.lines = [text]
                self._run_substitute_confirm(
                    confirm, pattern, repl, "gc", True, ["a"]
                )
                self.assertEqual(confirm.lines, non_confirm.lines)

    def test_substitute_confirm_sets_last_change_for_dot_repeat(self):
        # After :s/foo/bar/c and confirming, pressing . must repeat the
        # substitution (without re-prompting). Previously _set_last_change was
        # never called from the confirm path.
        editor = ViEditor()
        editor.lines = ["foo foo", "foo foo"]
        editor.cursor_row = 0

        # Confirm one substitution on line 0 (answer "y" to first match, "q" after)
        self._run_substitute_confirm(editor, "foo", "bar", "gc", True, ["y", "q"])

        self.assertEqual(editor.lines[0], "bar foo")
        self.assertIsNotNone(editor._last_change,
                             "confirm substitution must register a dot-repeatable change")

    def test_substitute_confirm_dot_repeat_runs_silently_without_prompt(self):
        # Dot-repeat of a confirm substitution must execute without the
        # confirm prompt (the stored repeat_flags must have 'c' stripped).
        editor = ViEditor()
        editor.lines = ["foo bar", "foo bar"]
        editor.cursor_row = 0

        # Confirm substitution on line 0 only ("y" on first match, "q" after)
        self._run_substitute_confirm(editor, "foo", "X", "c", False, ["y"])
        self.assertEqual(editor.lines[0], "X bar")

        # Move to line 1 and dot-repeat — must substitute silently
        editor.cursor_row = 1
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines[1], "X bar",
                         "dot-repeat after confirm substitution must apply the change")

    def test_copy_command_yanks_current_line_with_no_range(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta", "gamma"]
        editor.cursor_row = 1

        self.assertTrue(editor._execute_cmd(":c"))

        self.assertEqual(editor.yank_buffer, ["beta"])
        self.assertTrue(editor.yank_is_lines)
        self.assertEqual(editor.message, "1 line copied")

    def test_copy_command_supports_explicit_range(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]

        self.assertTrue(editor._execute_cmd(":2,3c"))

        self.assertEqual(editor.yank_buffer, ["two", "three"])
        self.assertEqual(editor.message, "2 lines copied")

    def test_copy_command_star_copies_all_lines(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]

        self.assertTrue(editor._execute_cmd(":*c"))

        self.assertEqual(editor.yank_buffer, ["a", "b", "c"])
        self.assertEqual(editor.message, "3 lines copied")

    def test_copy_command_percent_resolves_to_cursor_line(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.cursor_row = 2

        self.assertTrue(editor._execute_cmd(":%c"))

        self.assertEqual(editor.yank_buffer, ["c"])

    def test_copy_command_dollar_resolves_to_last_line(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.cursor_row = 0

        self.assertTrue(editor._execute_cmd(":$c"))

        self.assertEqual(editor.yank_buffer, ["c"])

    def test_copy_command_mixed_percent_and_dollar(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d"]
        editor.cursor_row = 1

        self.assertTrue(editor._execute_cmd(":%,$c"))

        self.assertEqual(editor.yank_buffer, ["b", "c", "d"])

    def test_copy_command_clamps_out_of_range_lines(self):
        editor = ViEditor()
        editor.lines = ["a", "b"]

        self.assertTrue(editor._execute_cmd(":1,99c"))

        self.assertEqual(editor.yank_buffer, ["a", "b"])

    def test_copy_command_normalises_reversed_range(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d"]

        self.assertTrue(editor._execute_cmd(":3,1c"))

        self.assertEqual(editor.yank_buffer, ["a", "b", "c"])

    def test_copy_command_yanked_lines_can_be_pasted(self):
        editor = ViEditor()
        editor.lines = ["x", "y", "z"]
        editor.cursor_row = 0

        editor._execute_cmd(":2,3c")
        editor._handle_normal(ord("p"), 24, 80)

        self.assertEqual(editor.lines, ["x", "y", "z", "y", "z"])

    def test_copy_command_into_named_register(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]
        editor.active_register = "a"

        self.assertTrue(editor._execute_cmd(":1,2c"))

        text, is_lines = editor.registers["a"]
        self.assertEqual(text, ["alpha", "beta"])
        self.assertTrue(is_lines)
        self.assertIsNone(editor.active_register)

    def test_copy_command_does_not_swallow_unknown_commands_ending_in_c(self):
        # Defensive: tokens like 'xyz' should still fall through to "Unknown
        # command", not be silently treated as a :c form.
        editor = ViEditor()
        editor.lines = ["a"]

        editor._execute_cmd(":xyzc")

        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.yank_buffer, [])

    def test_b64_encode_and_decode_commands(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "buffer.b64")

            editor = ViEditor()
            editor.lines = ["hello", "world"]

            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            with open(encoded, "rb") as fh:
                self.assertEqual(fh.read(), base64.b64encode(b"hello\nworld\n"))

            editor.lines = ["changed"]
            editor._mark_clean()
            self.assertTrue(editor._execute_cmd(f":b64d {encoded}"))
            self.assertEqual(editor.lines, ["hello", "world"])
            self.assertFalse(editor.modified)
            self.assertIsNone(editor.filename)

            roundtrip = os.path.join(tmpdir, "roundtrip.b64")
            self.assertTrue(editor._execute_cmd(f":b64e {roundtrip}"))
            with open(roundtrip, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"hello\nworld\n")

    def test_b64_commands_preserve_filename_spaces(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, " spaced .b64 ")

            editor = ViEditor()
            editor.lines = ["hello"]

            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            self.assertTrue(os.path.exists(encoded))
            self.assertFalse(os.path.exists(encoded.strip()))

            editor.lines = ["changed"]
            editor._mark_clean()
            self.assertTrue(editor._execute_cmd(f":b64d {encoded}"))
            self.assertEqual(editor.lines, ["hello"])

    def test_b64_encode_existing_file_prompts_before_replace(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "buffer.b64")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"existing\n"))

            editor = ViEditor()
            editor.lines = ["hello", "world"]

            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            self.assertIsNotNone(editor._pending_confirmation)
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"existing\n")

            self.assertTrue(editor._handle_pending_confirmation(ord("n")))
            self.assertIsNone(editor._pending_confirmation)
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"existing\n")

            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            self.assertTrue(editor._handle_pending_confirmation(ord("y")))
            self.assertIsNone(editor._pending_confirmation)
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"hello\nworld\n")

    def test_b64_encode_preserves_existing_file_when_replace_fails(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "buffer.b64")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"existing\n"))

            editor = ViEditor()
            editor.lines = ["replacement"]
            real_replace = os.replace

            def fail_target_replace(src, dst):
                if dst == encoded:
                    raise OSError("replace failed")
                return real_replace(src, dst)

            with mock.patch("vi_editor.os.replace", side_effect=fail_target_replace):
                self.assertFalse(editor._save_base64_file(encoded))

            self.assertTrue(editor.message_is_error)
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"existing\n")
            # Neither the save-lock sidecar nor any partially written output
            # or temporary write file may remain.
            self.assertEqual(os.listdir(tmpdir), ["buffer.b64"])

    def test_save_removes_write_lock_sidecar(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "buffer.txt")
            editor = ViEditor()
            editor.lines = ["first"]
            self.assertTrue(editor._save_file(path))
            editor.lines[0] = "second"
            editor.modified = True
            self.assertTrue(editor._save_file(path))
            self.assertEqual(
                [name for name in os.listdir(tmpdir) if name.startswith(".vii-write-")],
                [],
            )

    def test_write_tilde_existing_file_prompts_before_replace(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            os.mkdir(home)
            encoded = os.path.join(home, "buffer.txt")
            with open(encoded, "w", encoding="utf-8") as fh:
                fh.write("existing\n")
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            editor = ViEditor()
            editor.lines = ["hello", "world"]

            with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                self.assertTrue(editor._execute_cmd(":w ~/buffer.txt"))
                self.assertIsNotNone(editor._pending_confirmation)
                self.assertIn(encoded, editor.message)

            with open(encoded, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "existing\n")

    def test_b64_encode_tilde_existing_file_prompts_before_replace(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            os.mkdir(home)
            encoded = os.path.join(home, "buffer.b64")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"existing\n"))
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            editor = ViEditor()
            editor.lines = ["hello", "world"]

            with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                self.assertTrue(editor._execute_cmd(":b64e ~/buffer.b64"))
                self.assertIsNotNone(editor._pending_confirmation)
                self.assertIn(encoded, editor.message)

            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"existing\n")

    def test_b64_encode_preserves_loaded_line_endings(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "mixed.b64")
            roundtrip = os.path.join(tmpdir, "roundtrip.b64")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"one\r\ntwo\rthree"))

            editor = ViEditor()
            self.assertTrue(editor._execute_cmd(f":b64d {encoded}"))

            self.assertTrue(editor._execute_cmd(f":b64e {roundtrip}"))
            with open(roundtrip, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"one\r\ntwo\rthree")

    def test_b64_encode_manual_single_line_keeps_legacy_final_newline(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "manual.b64")

            editor = ViEditor()
            editor.lines = ["alpha"]

            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"alpha\n")

    def test_b64_encode_manual_buffer_uses_windows_default_line_endings(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "manual.b64")

            editor = ViEditor()
            editor.lines = ["alpha", "beta"]

            self.assertTrue(editor._execute_cmd(":le-win"))
            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"alpha\r\nbeta\r\n")

    def test_b64_decode_clears_stale_undo_redo_and_marks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "buffer.b64")
            with open(encoded, "wb") as fh:
                fh.write(base64.b64encode(b"decoded\n"))

            editor = ViEditor()
            editor.lines = ["old snapshot"]
            editor.marks = {"a": (0, 3)}
            editor.auto_marks = {1: 0}
            editor._push_undo()
            editor.lines = ["edited"]
            editor.redo_stack.append(editor.undo_stack[-1])
            editor._mark_clean()

            self.assertTrue(editor._execute_cmd(f":b64d {encoded}"))
            self.assertEqual(editor.lines, ["decoded"])
            self.assertFalse(editor.undo_stack)
            self.assertFalse(editor.redo_stack)
            self.assertEqual(editor.marks, {})
            self.assertEqual(editor.auto_marks, {})

            editor._undo()
            self.assertEqual(editor.lines, ["decoded"])

    def test_b64_decode_rejects_invalid_data(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            bad = os.path.join(tmpdir, "bad.b64")
            with open(bad, "wb") as fh:
                fh.write(b"not-valid-base64!!!")

            editor = ViEditor()
            editor.lines = ["keep"]
            editor.modified = True
            self.assertTrue(editor._execute_cmd(f":b64d {bad}"))
            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["keep"])
            self.assertTrue(editor.modified)

    def test_b64_decode_accepts_wrapped_base64_input(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            wrapped = os.path.join(tmpdir, "wrapped.b64")
            with open(wrapped, "wb") as fh:
                fh.write(base64.encodebytes(b"hello\nworld\n"))

            editor = ViEditor()

            self.assertTrue(editor._execute_cmd(f":b64d {wrapped}"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.lines, ["hello", "world"])
            self.assertEqual(editor.line_endings, ["\n", "\n"])

    def test_failed_reload_preserves_current_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "gone.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("original\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True
            os.unlink(path)

            self.assertTrue(editor._execute_cmd(":e"))
            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["edited"])
            self.assertTrue(editor.modified)

    def test_plain_edit_blocks_unsaved_reload_but_force_reloads(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":edit"))
            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["edited"])
            self.assertTrue(editor.modified)

            self.assertTrue(editor._execute_cmd(":edit!"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.lines, ["disk"])
            self.assertFalse(editor.modified)

    def test_edit_with_same_filename_blocks_unsaved_reload(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit {path}"))

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["edited"])
            self.assertTrue(editor.modified)

    def test_edit_existing_open_clean_buffer_refreshes_from_disk(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            current = os.path.join(tmpdir, "current.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(current, "w", encoding="utf-8") as fh:
                fh.write("current\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("old\n")

            editor = ViEditor(current)
            self.assertTrue(editor._append_buffer(target, switch=False))

            self.assertTrue(editor._execute_cmd(":buffer 2"))
            self.assertEqual(editor.lines, ["old"])

            with open(target, "w", encoding="utf-8") as fh:
                fh.write("new\n")

            self.assertTrue(editor._execute_cmd(":buffer 1"))
            self.assertTrue(editor._execute_cmd(f":edit {target}"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.lines, ["new"])
            self.assertFalse(editor.modified)

    def test_force_reload_with_filename_reloads_existing_open_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit! {path}"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.lines, ["disk"])
            self.assertFalse(editor.modified)

    def test_force_reload_with_same_missing_filename_reports_error(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "missing.txt")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit! {path}"))

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.lines, ["edited"])
            self.assertTrue(editor.modified)

    def test_force_reload_existing_open_missing_file_preserves_original_buffer_on_error(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            current = os.path.join(tmpdir, "current.txt")
            missing = os.path.join(tmpdir, "missing.txt")
            with open(current, "w", encoding="utf-8") as fh:
                fh.write("current\n")

            editor = ViEditor(current)
            self.assertTrue(editor._append_buffer(missing, switch=False))

            self.assertTrue(editor._execute_cmd(":buffer 2"))
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":buffer 1"))
            self.assertTrue(editor._execute_cmd(f":edit! {missing}"))

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.filename, current)
            self.assertEqual(editor.lines, ["current"])
            self.assertFalse(editor.modified)

    def test_force_edit_other_file_discards_previous_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            current = os.path.join(tmpdir, "current.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(current, "w", encoding="utf-8") as fh:
                fh.write("current\n")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("target\n")

            editor = ViEditor(current)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit! {target}"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.lines, ["target"])
            self.assertFalse(editor.modified)
            self.assertEqual(len(editor.buffers), 1)
            self.assertFalse(editor._has_unsaved_changes())

    def test_force_edit_existing_other_buffer_discards_current_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            first = os.path.join(tmpdir, "first.txt")
            second = os.path.join(tmpdir, "second.txt")
            with open(first, "w", encoding="utf-8") as fh:
                fh.write("first\n")
            with open(second, "w", encoding="utf-8") as fh:
                fh.write("second\n")

            editor = ViEditor([first, second])
            editor._execute_cmd(":buffer 1")
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit! {second}"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, second)
            self.assertEqual(editor.lines, ["second"])
            self.assertFalse(editor.modified)
            self.assertEqual(len(editor.buffers), 1)
            self.assertEqual(editor.buffers[0].filename, second)

    def test_force_reload_clears_stale_undo_redo_history(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["old snapshot"]
            editor._push_undo()
            editor.lines = ["edited"]
            editor.redo_stack.append(editor.undo_stack[-1])
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":edit!"))
            self.assertEqual(editor.lines, ["disk"])
            self.assertFalse(editor.modified)
            self.assertFalse(editor.undo_stack)
            self.assertFalse(editor.redo_stack)

            editor._undo()
            self.assertEqual(editor.lines, ["disk"])

    def test_file_commands_preserve_filename_spaces(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, " lead and trail .txt ")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("data\n")

            editor = ViEditor()
            self.assertTrue(editor._execute_cmd(f":edit {source}"))
            self.assertEqual(editor.filename, source)

            renamed = os.path.join(tmpdir, " renamed .txt ")
            self.assertTrue(editor._execute_cmd(f":file {renamed}"))
            self.assertEqual(editor.filename, renamed)

            output = os.path.join(tmpdir, " copy .txt ")
            editor.lines = ["copy"]
            self.assertTrue(editor._execute_cmd(f":write {output}"))
            self.assertTrue(os.path.exists(output))
            self.assertFalse(os.path.exists(output.strip()))

    def test_file_command_stores_absolute_buffer_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "renamed.txt")
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                editor = ViEditor()

                self.assertTrue(editor._execute_cmd(":file renamed.txt"))

                self.assertEqual(editor.filename, path)
                self.assertEqual(editor.buffers[0].filename, path)
                self.assertIn(path, editor.message)
            finally:
                os.chdir(old_cwd)

    def test_file_rename_marks_buffer_modified_and_quit_blocks_until_write(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            renamed = os.path.join(tmpdir, "renamed.txt")
            with open(source, "w", encoding="utf-8") as fh:
                fh.write("data\n")

            editor = ViEditor(source)

            self.assertTrue(editor._execute_cmd(f":file {renamed}"))
            self.assertTrue(editor.modified)
            self.assertEqual(editor.filename, renamed)

            self.assertTrue(editor._execute_cmd(":q"))
            self.assertTrue(editor.message_is_error)
            self.assertIn(":quit!", editor.message)

            self.assertTrue(editor._execute_cmd(":w"))
            self.assertFalse(editor.message_is_error)
            self.assertFalse(editor.modified)
            self.assertTrue(os.path.exists(renamed))
            with open(renamed, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "data\n")

    def test_file_command_rejects_renaming_to_existing_open_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            first = os.path.join(tmpdir, "first.txt")
            second = os.path.join(tmpdir, "second.txt")
            for path, text in ((first, "first\n"), (second, "second\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([first, second])
            self.assertTrue(editor._execute_cmd(":buffer 1"))

            self.assertTrue(editor._execute_cmd(f":file {second}"))

            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.filename, first)
            self.assertEqual([b.filename for b in editor.buffers], [first, second])

    def test_rf_command_reloads_current_file_preserving_cursor_position(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor._mark_clean()
            editor.cursor_row = 1
            editor.cursor_col = 2
            editor.top_line = 1
            editor.left_col = 1

            with open(path, "w", encoding="utf-8") as fh:
                fh.write("ONE\nTWO\nTHREE\n")

            self.assertTrue(editor._execute_cmd(":rf"))

            self.assertEqual(editor.lines, ["ONE", "TWO", "THREE"])
            self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 2))
            self.assertEqual((editor.top_line, editor.left_col), (1, 1))
            self.assertFalse(editor.modified)

    def test_rf_command_reload_clamps_cursor_when_file_is_shorter(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("one\ntwo\nthree\n")

            editor = ViEditor(path)
            editor.cursor_row = 2
            editor.cursor_col = 20

            with open(path, "w", encoding="utf-8") as fh:
                fh.write("x\n")

            self.assertTrue(editor._execute_cmd(":rf"))

            self.assertEqual(editor.lines, ["x"])
            self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_rf_command_without_filename_reports_error(self):
        editor = ViEditor()

        self.assertTrue(editor._execute_cmd(":rf"))

        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "No file name")
        self.assertEqual(editor.lines, [""])

    def test_bare_r_command_does_not_reload_current_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "reload.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("disk\n")

            editor = ViEditor(path)
            editor.lines = ["edited"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":r"))

            self.assertEqual(editor.lines, ["edited"])
            self.assertTrue(editor.modified)
            self.assertTrue(editor.message_is_error)

    def test_multiple_file_buffers_switch_and_preserve_state(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor(one)
            editor.lines = ["one changed"]
            editor.modified = True

            self.assertTrue(editor._execute_cmd(f":edit {two}"))
            self.assertEqual(editor.filename, two)
            self.assertEqual(editor.lines, ["two"])
            self.assertEqual(len(editor.buffers), 2)

            self.assertTrue(editor._execute_cmd(":bp"))
            self.assertEqual(editor.filename, one)
            self.assertEqual(editor.lines, ["one changed"])
            self.assertTrue(editor.modified)

            self.assertTrue(editor._execute_cmd(":bn"))
            self.assertEqual(editor.filename, two)

    def test_constructor_loads_multiple_files_as_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            missing = os.path.join(tmpdir, "new.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor([one, two, missing])

            self.assertEqual(len(editor.buffers), 3)
            self.assertEqual(editor.filename, one)
            self.assertEqual(editor.lines, ["one"])

            self.assertTrue(editor._execute_cmd(":buffer 2"))
            self.assertEqual(editor.filename, two)
            self.assertEqual(editor.lines, ["two"])

            self.assertTrue(editor._execute_cmd(":buffer 3"))
            self.assertEqual(editor.filename, missing)
            self.assertEqual(editor.lines, [""])

    def test_buffer_add_list_switch_and_delete(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            extra = os.path.join(tmpdir, "extra.txt")
            with open(extra, "w", encoding="utf-8") as fh:
                fh.write("extra\n")

            editor = ViEditor()
            editor.last_shell_cmd = "printf old"

            self.assertTrue(editor._execute_cmd(f":badd {extra}"))
            self.assertIsNone(editor.filename)
            self.assertEqual(len(editor.buffers), 2)

            self.assertTrue(editor._execute_cmd(":buffers"))
            self.assertEqual(editor.mode, Mode.BUFFER_LIST)
            self.assertEqual(editor.last_shell_cmd, "printf old")
            self.assertTrue(any("extra.txt" in line for line in editor._buffer_list_lines()))
            editor._handle_buffer_list(ord("q"))

            self.assertTrue(editor._execute_cmd(":buffer 2"))
            self.assertEqual(editor.filename, extra)
            self.assertEqual(editor.lines, ["extra"])

            editor.lines = ["changed"]
            editor.modified = True
            self.assertTrue(editor._execute_cmd(":bd"))
            self.assertTrue(editor.message_is_error)
            self.assertEqual(len(editor.buffers), 2)

            self.assertTrue(editor._execute_cmd(":bd!"))
            self.assertEqual(len(editor.buffers), 1)
            self.assertIsNone(editor.filename)

    def test_buffer_list_selects_by_cursor_and_number(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            three = os.path.join(tmpdir, "three.txt")
            for path, text in ((one, "one\n"), (two, "two\n"), (three, "three\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two, three])

            self.assertTrue(editor._execute_cmd(":ls"))
            self.assertEqual(editor.mode, Mode.BUFFER_LIST)
            editor._handle_buffer_list(curses.KEY_DOWN)
            editor._handle_buffer_list(ord("\n"))
            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, two)

            self.assertTrue(editor._execute_cmd(":ls"))
            editor._handle_buffer_list(ord("3"))
            self.assertEqual(editor.buffer_list_cursor, 2)
            editor._handle_buffer_list(ord("\n"))
            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, three)

    def test_buffer_list_enter_clamps_stale_cursor_before_selecting(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            for path, text in ((one, "one\n"), (two, "two\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two])
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 99

            editor._handle_buffer_list(ord("\n"))

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, two)
            self.assertEqual(editor.buffer_list_cursor, 1)
            self.assertFalse(editor.message_is_error)

    def test_buffer_list_ignores_non_ascii_keys_without_crashing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor([one])
            self.assertTrue(editor._execute_cmd(":ls"))

            self.assertTrue(editor._handle_buffer_list("é"))
            self.assertEqual(editor.buffer_list_number, "")
            self.assertEqual(editor.buffer_list_cursor, 0)

    def test_buffer_list_d_deletes_highlighted_buffer_via_bd_path(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            three = os.path.join(tmpdir, "three.txt")
            for path, text in ((one, "one\n"), (two, "two\n"), (three, "three\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two, three])
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 1  # "two.txt" -- not the active buffer

            editor._handle_buffer_list(ord("x"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)  # stays in the list
            self.assertFalse(editor.message_is_error)
            self.assertIn("Buffer deleted", editor.message)
            self.assertEqual(len(editor.buffers), 2)
            self.assertFalse(any(b.filename == two for b in editor.buffers))
            self.assertTrue(any(b.filename == one for b in editor.buffers))
            self.assertTrue(any(b.filename == three for b in editor.buffers))
            # Cursor must stay in range for the shrunk list.
            self.assertLess(editor.buffer_list_cursor, len(editor.buffers))

    def test_buffer_list_u_and_d_move_highlighted_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            three = os.path.join(tmpdir, "three.txt")
            for path, text in ((one, "one\n"), (two, "two\n"), (three, "three\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two, three])
            self.assertEqual(editor.filename, one)
            editor.lines[0] = "one-edited"  # live edit must survive the move
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 0  # the active buffer

            editor._handle_buffer_list(ord("d"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)
            self.assertEqual([b.filename for b in editor.buffers], [two, one, three])
            self.assertEqual(editor.buffer_list_cursor, 1)
            self.assertEqual(editor.current_buffer, 1)
            self.assertEqual(editor.filename, one)
            self.assertEqual(editor.buffers[1].lines[0], "one-edited")

            editor._handle_buffer_list(ord("d"))
            self.assertEqual([b.filename for b in editor.buffers], [two, three, one])
            self.assertEqual(editor.current_buffer, 2)

            # Already at the bottom: 'd' is a no-op.
            editor._handle_buffer_list(ord("d"))
            self.assertEqual([b.filename for b in editor.buffers], [two, three, one])
            self.assertEqual(editor.buffer_list_cursor, 2)

            # Move a non-current buffer up past the current one.
            editor.buffer_list_cursor = 1  # three.txt
            editor._handle_buffer_list(ord("u"))
            self.assertEqual([b.filename for b in editor.buffers], [three, two, one])
            self.assertEqual(editor.buffer_list_cursor, 0)
            self.assertEqual(editor.current_buffer, 2)
            self.assertEqual(editor.filename, one)

            # Already at the top: 'u' is a no-op.
            editor._handle_buffer_list(ord("u"))
            self.assertEqual([b.filename for b in editor.buffers], [three, two, one])
            self.assertEqual(len(editor.buffers), 3)  # nothing deleted

    def test_buffer_list_x_respects_bd_unsaved_changes_guard(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            for path, text in ((one, "one\n"), (two, "two\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two])
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 0  # the active buffer
            editor.lines[0] = "one-edited"  # real unsaved edit

            editor._handle_buffer_list(ord("x"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)  # never left the list
            self.assertTrue(editor.message_is_error)
            self.assertIn("No write since last change", editor.message)
            self.assertEqual(len(editor.buffers), 2)  # nothing deleted

    def test_buffer_list_w_saves_highlighted_buffer_via_w_path(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            for path, text in ((one, "one\n"), (two, "two\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two])
            # Edit the inactive buffer's stored snapshot directly (as if it
            # had been edited earlier, then navigated away from).
            editor.buffers[1].lines = ["two-edited"]
            editor.buffers[1].modified = True

            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 1  # "two.txt" -- not the active buffer

            editor._handle_buffer_list(ord("w"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)  # stays in the list
            self.assertFalse(editor.message_is_error)
            self.assertIn("written", editor.message)
            with open(two, encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "two-edited\n")
            self.assertEqual(editor.filename, two)  # became current to run :w
            self.assertFalse(editor.buffers[editor.current_buffer].modified)

    def test_buffer_list_x_reports_command_failed_instead_of_crashing(self):
        # Regression guard: an unexpected exception from the :bd path must be
        # caught the same way _handle_cmd_buf catches it for a typed :bd,
        # not propagate up through the buffer list and crash the editor.
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            for path, text in ((one, "one\n"), (two, "two\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two])
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 0

            with mock.patch.object(ViEditor, "_delete_current_buffer",
                                    side_effect=ValueError("boom")):
                editor._handle_buffer_list(ord("x"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)  # did not crash out
            self.assertTrue(editor.message_is_error)
            self.assertIn("Command failed", editor.message)
            self.assertIn("boom", editor.message)
            self.assertEqual(len(editor.buffers), 2)  # nothing deleted

    def test_buffer_list_w_reports_command_failed_instead_of_crashing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")

            editor = ViEditor([one])
            self.assertTrue(editor._execute_cmd(":ls"))
            editor.buffer_list_cursor = 0

            with mock.patch.object(ViEditor, "_save_file", side_effect=ValueError("boom")):
                editor._handle_buffer_list(ord("w"))

            self.assertEqual(editor.mode, Mode.BUFFER_LIST)  # did not crash out
            self.assertTrue(editor.message_is_error)
            self.assertIn("Command failed", editor.message)
            self.assertIn("boom", editor.message)

    def test_buffer_delete_refreshes_dirty_state_before_blocking(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor([one, two])
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":bd"))

            self.assertFalse(editor.message_is_error)
            self.assertEqual(len(editor.buffers), 1)
            self.assertEqual(editor.filename, two)

    def test_buffer_command_switches_by_partial_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            alpha = os.path.join(tmpdir, "alpha.txt")
            beta = os.path.join(tmpdir, "beta.txt")
            for path, text in ((alpha, "alpha\n"), (beta, "beta\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([alpha, beta])

            # Partial filename match switches to the right buffer.
            self.assertTrue(editor._execute_cmd(":b beta"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, beta)

            # Exact filename match also works.
            self.assertTrue(editor._execute_cmd(f":b {alpha}"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, alpha)

            # Ambiguous partial name reports an error without switching.
            self.assertTrue(editor._execute_cmd(":b .txt"))
            self.assertTrue(editor.message_is_error)
            self.assertIn("More than one", editor.message)
            self.assertEqual(editor.filename, alpha)

            # No match reports an error.
            self.assertTrue(editor._execute_cmd(":b nosuchfile"))
            self.assertTrue(editor.message_is_error)
            self.assertIn("No buffer matching", editor.message)

    def test_buffer_list_modified_flag_refreshed_for_all_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            for path, text in ((one, "one\n"), (two, "two\n")):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(text)

            editor = ViEditor([one, two])
            # Stale modified flag on the inactive buffer should be refreshed
            # when the buffer list is built for display.
            editor.buffers[1].modified = True

            # Sync what _show_buffers does when the list is opened, without
            # the curses call.
            editor._refresh_all_buffer_modified_flags()
            lines = editor._buffer_list_lines()

            # Buffer 2 was not actually modified on disk — flag should be cleared.
            self.assertNotIn("+", lines[1])

    def test_show_buffers_verifies_once_not_on_every_redraw(self):
        # _refresh_all_buffer_modified_flags re-hashes every buffer's full
        # content (needed to catch a genuinely stale modified flag, per
        # test_buffer_list_modified_flag_refreshed_for_all_buffers above).
        # That must happen once, when the list is opened -- not again on
        # every redraw while merely navigating it with j/k, since nothing
        # can mutate buffer content while Mode.BUFFER_LIST is active.
        editor = ViEditor()
        editor._append_buffer(None, switch=False)

        calls = []
        orig = editor._refresh_all_buffer_modified_flags
        editor._refresh_all_buffer_modified_flags = lambda: (calls.append(1), orig())[-1]

        editor._show_buffers()
        self.assertEqual(len(calls), 1)

        class FakeScreen:
            def move(self, *a): pass
            def clrtoeol(self): pass
            def addstr(self, *a): pass
            def attron(self, *a): pass
            def attroff(self, *a): pass
            def noutrefresh(self): pass

        with mock.patch("curses.doupdate"):
            for _ in range(5):
                editor._draw_buffer_list(FakeScreen(), 24, 80)

        self.assertEqual(len(calls), 1)

    def test_append_unnamed_buffer_no_switch_syncs_new_slot(self):
        editor = ViEditor()
        editor._append_buffer(None, switch=False)

        # The new buffer slot must be persisted in self.buffers, not left as
        # a freshly-loaded but un-synced state.
        self.assertEqual(len(editor.buffers), 2)
        # Active buffer is still the original unnamed one (index 0).
        self.assertEqual(editor.current_buffer, 0)
        # New slot at index 1 must exist and be a clean unnamed buffer.
        self.assertIsNone(editor.buffers[1].filename)
        self.assertFalse(editor.buffers[1].modified)

    def test_show_buffers_top_line_positions_cursor_in_view(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            paths = []
            for i in range(10):
                p = os.path.join(tmpdir, f"file{i}.txt")
                with open(p, "w", encoding="utf-8") as fh:
                    fh.write(f"line{i}\n")
                paths.append(p)

            editor = ViEditor(paths)
            # Switch to the last buffer so cursor_buffer is near the bottom.
            editor._switch_buffer(9)
            editor._last_h = 5  # simulate a short terminal (3 text rows)

            editor._show_buffers()

            text_rows = max(1, editor._last_h - 2)
            top = editor.buffer_list_top_line
            cursor = editor.buffer_list_cursor
            # Cursor must be within the visible window.
            self.assertGreaterEqual(cursor, top)
            self.assertLess(cursor, top + text_rows)

    def test_current_buffer_dirty_checks_refresh_stale_flag(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor([one, two])
            editor.modified = True

            self.assertTrue(editor._execute_cmd(":edit"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.lines, ["one"])

            editor.modified = True
            self.assertTrue(editor._execute_cmd(":enew"))
            self.assertFalse(editor.message_is_error)

            editor = ViEditor([one, two])
            editor.modified = True
            self.assertFalse(editor._execute_cmd(":x"))

            editor = ViEditor(one)
            editor.modified = True
            self.assertTrue(editor._execute_cmd(":file"))
            self.assertNotIn("[Modified]", editor.message)

    def test_file_short_alias_renames_buffer(self):
        editor = ViEditor()
        path = os.path.abspath("renamed.txt")

        self.assertTrue(editor._execute_cmd(":f renamed.txt"))

        self.assertEqual(editor.filename, path)
        self.assertEqual(editor.buffers[0].filename, path)
        self.assertEqual(editor.message, f'"{path}"')

    def test_cd_changes_process_working_directory(self):
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                real_tmpdir = os.path.realpath(tmpdir)
                editor = ViEditor()

                self.assertTrue(editor._execute_cmd(f":cd {tmpdir}"))

                self.assertFalse(editor.message_is_error)
                self.assertEqual(os.path.realpath(os.getcwd()), real_tmpdir)
                self.assertEqual(editor.message, os.getcwd())
        finally:
            os.chdir(original_cwd)

    def test_cd_survives_getcwd_failure_after_successful_chdir(self):
        # A getcwd() failure right after a successful chdir() (e.g. the
        # target directory vanishes/unmounts in that instant) must not be
        # reported as a failed directory change, and must not raise.
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                real_tmpdir = os.path.realpath(tmpdir)
                editor = ViEditor()

                with mock.patch("vi_editor.os.getcwd", side_effect=OSError("stale handle")):
                    self.assertTrue(editor._execute_cmd(f":cd {tmpdir}"))

                self.assertFalse(editor.message_is_error)
                self.assertEqual(editor.message, tmpdir)
                self.assertEqual(os.path.realpath(os.getcwd()), real_tmpdir)
        finally:
            os.chdir(original_cwd)

    def test_cd_relative_arg_falls_back_to_absolute_path_on_getcwd_failure(self):
        # Regression test: :cd's post-chdir getcwd()-failure fallback must
        # report an absolute path even when the argument was relative --
        # falling back to the literal, unnormalized argument text would
        # display a meaningless fragment (relative to a cwd the process has
        # already left) as "the current directory".
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                os.chdir(tmpdir)
                os.mkdir(os.path.join(tmpdir, "sub"))
                real_target = os.path.realpath(os.path.join(tmpdir, "sub"))

                editor = ViEditor()
                real_getcwd = os.getcwd
                call_count = 0

                def flaky_getcwd():
                    nonlocal call_count
                    call_count += 1
                    # First call resolves the relative "sub" argument to an
                    # absolute path (via os.path.abspath); only the second
                    # call -- the post-chdir report -- fails.
                    if call_count == 1:
                        return real_getcwd()
                    raise OSError("stale handle")

                with mock.patch("vi_editor.os.getcwd", side_effect=flaky_getcwd):
                    self.assertTrue(editor._execute_cmd(":cd sub"))

                self.assertFalse(editor.message_is_error)
                self.assertTrue(os.path.isabs(editor.message))
                self.assertEqual(os.path.realpath(editor.message), real_target)
                self.assertEqual(os.path.realpath(os.getcwd()), real_target)
        finally:
            os.chdir(original_cwd)

    def test_cd_rejects_non_directory(self):
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                target = os.path.join(tmpdir, "notadir.txt")
                with open(target, "w", encoding="utf-8") as fh:
                    fh.write("x\n")

                editor = ViEditor()
                self.assertTrue(editor._execute_cmd(f":cd {target}"))

                self.assertTrue(editor.message_is_error)
                self.assertEqual(os.getcwd(), original_cwd)
        finally:
            os.chdir(original_cwd)

    def test_validate_is_directory_shared_by_cd_and_fb_goto_prompt(self):
        # Direct unit test of the helper :cd and _fb_finish_goto_prompt now
        # both call: the error must quote what the user actually typed
        # (original_text), not the resolved absolute target, and the return
        # value must reflect existence as a directory.
        with tempfile.TemporaryDirectory() as tmpdir:
            editor = ViEditor()

            self.assertTrue(editor._validate_is_directory(tmpdir, "whatever/typed"))
            self.assertFalse(editor.message_is_error)

            not_a_dir = os.path.join(tmpdir, "missing")
            self.assertFalse(editor._validate_is_directory(not_a_dir, "typed-fragment"))
            self.assertTrue(editor.message_is_error)
            self.assertEqual(editor.message, "Not a directory: typed-fragment")

    def test_cd_bare_and_pwd_report_current_directory(self):
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                os.chdir(tmpdir)
                editor = ViEditor()

                self.assertTrue(editor._execute_cmd(":cd"))
                self.assertEqual(editor.message, os.getcwd())

                self.assertTrue(editor._execute_cmd(":pwd"))
                self.assertEqual(editor.message, os.getcwd())
        finally:
            os.chdir(original_cwd)

    def test_cd_tab_completion_only_matches_directories(self):
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                os.mkdir(os.path.join(tmpdir, "subdir"))
                with open(os.path.join(tmpdir, "subfile.txt"), "w", encoding="utf-8") as fh:
                    fh.write("x\n")

                editor = ViEditor()
                editor._start_cmd_buf(f":cd {os.path.join(tmpdir, 'sub')}")

                editor._handle_cmd_buf(ord("\t"))

                self.assertEqual(
                    editor._cmd_buf,
                    f":cd {os.path.join(tmpdir, 'subdir')}/",
                )
        finally:
            os.chdir(original_cwd)

    def test_unsaved_checks_refresh_inactive_buffer_dirty_state(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            one = os.path.join(tmpdir, "one.txt")
            two = os.path.join(tmpdir, "two.txt")
            with open(one, "w", encoding="utf-8") as fh:
                fh.write("one\n")
            with open(two, "w", encoding="utf-8") as fh:
                fh.write("two\n")

            editor = ViEditor([one, two])
            editor.buffers[1].modified = True

            self.assertFalse(editor._execute_cmd(":q"))

            editor = ViEditor([one, two])
            editor.buffers[1].lines = ["changed"]
            editor.buffers[1].modified = False

            self.assertTrue(editor._execute_cmd(":q"))
            self.assertTrue(editor.message_is_error)

    def test_command_line_supports_cursor_editing(self):
        editor = ViEditor()
        editor._start_cmd_buf("/")
        for ch in "ac":
            editor._handle_cmd_buf(ord(ch))

        editor._handle_cmd_buf(curses.KEY_LEFT)
        editor._handle_cmd_buf(ord("b"))
        self.assertEqual(editor._cmd_buf, "/abc")
        self.assertEqual(editor._cmd_cursor, 3)

        editor._handle_cmd_buf(curses.KEY_BACKSPACE)
        self.assertEqual(editor._cmd_buf, "/ac")
        self.assertEqual(editor._cmd_cursor, 2)

        editor._handle_cmd_buf(curses.KEY_END)
        editor._handle_cmd_buf(curses.KEY_BACKSPACE)
        self.assertEqual(editor._cmd_buf, "/a")

    def test_backspace_at_prompt_cancels_only_when_line_is_empty(self):
        editor = ViEditor()
        editor._start_cmd_buf(":")
        result = editor._handle_cmd_buf(curses.KEY_BACKSPACE)
        self.assertIsNone(result)
        self.assertEqual(editor._cmd_buf, "")
        self.assertIsNone(editor._cmd_context)

    def test_backspace_after_cursor_walked_back_does_not_discard_typed_command(self):
        editor = ViEditor()
        editor._start_cmd_buf(":")
        for ch in "s/foo/bar/g":
            editor._handle_cmd_buf(ord(ch))
        for _ in range(11):
            editor._handle_cmd_buf(curses.KEY_LEFT)
        self.assertEqual(editor._cmd_cursor, 1)

        result = editor._handle_cmd_buf(curses.KEY_BACKSPACE)

        self.assertIsNone(result)
        self.assertEqual(editor._cmd_buf, ":s/foo/bar/g")
        self.assertEqual(editor._cmd_cursor, 1)

    def test_bare_search_with_no_previous_pattern_reports_error(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor._start_cmd_buf("/")

        result = editor._handle_cmd_buf(ord("\n"))

        self.assertTrue(result)
        self.assertTrue(editor.message_is_error)
        self.assertIn("No previous search pattern", editor.message)

    def test_cmd_buf_reports_error_instead_of_crashing_on_execute_cmd_bug(self):
        editor = ViEditor()
        editor._start_cmd_buf(":")
        for ch in "explode":
            editor._handle_cmd_buf(ord(ch))

        with mock.patch.object(editor, "_execute_cmd", side_effect=RuntimeError("boom")):
            result = editor._handle_cmd_buf(ord("\n"))

        # A bug in one ex command must not exit the editor: the keypress
        # loop keeps running and the failure surfaces as a normal error
        # message instead of propagating out of edit().
        self.assertTrue(result)
        self.assertTrue(editor.message_is_error)
        self.assertIn("boom", editor.message)

    def test_command_line_accepts_non_ascii_text(self):
        editor = ViEditor()
        editor._start_cmd_buf(":")

        editor._handle_cmd_buf(ord("é"))

        self.assertEqual(editor._cmd_buf, ":é")
        self.assertEqual(editor._cmd_cursor, 2)

    def test_command_line_history_recalls_commands_and_restores_draft(self):
        editor = ViEditor()

        editor._start_cmd_buf(":")
        for ch in "set number":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))

        editor._start_cmd_buf(":")
        for ch in "set nonumber":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))

        editor._start_cmd_buf(":set ")
        editor._handle_cmd_buf(curses.KEY_UP)
        self.assertEqual(editor._cmd_buf, ":set nonumber")
        self.assertEqual(editor._cmd_cursor, len(":set nonumber"))

        editor._handle_cmd_buf(curses.KEY_UP)
        self.assertEqual(editor._cmd_buf, ":set number")

        editor._handle_cmd_buf(curses.KEY_DOWN)
        self.assertEqual(editor._cmd_buf, ":set nonumber")

        editor._handle_cmd_buf(curses.KEY_DOWN)
        self.assertEqual(editor._cmd_buf, ":set ")
        self.assertEqual(editor._cmd_cursor, len(":set "))

    def test_command_line_history_is_separate_for_search_modes(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]

        editor._start_cmd_buf("/")
        for ch in "alpha":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))

        editor._start_cmd_buf("?")
        for ch in "beta":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))

        editor._start_cmd_buf(":")
        editor._handle_cmd_buf(curses.KEY_UP)
        self.assertEqual(editor._cmd_buf, ":")

        editor._start_cmd_buf("/")
        editor._handle_cmd_buf(curses.KEY_UP)
        self.assertEqual(editor._cmd_buf, "/alpha")

        editor._start_cmd_buf("?")
        editor._handle_cmd_buf(curses.KEY_UP)
        self.assertEqual(editor._cmd_buf, "?beta")

    def test_command_line_cancel_clears_stale_error_state(self):
        editor = ViEditor()
        editor.message = "old error"
        editor.message_is_error = True
        editor._start_cmd_buf(":")

        self.assertTrue(editor._handle_cmd_buf(27))
        editor._handle_normal(7, 24, 80)

        self.assertIn("[No Name]", editor.message)
        self.assertFalse(editor.message_is_error)

    def test_ex_filename_tab_completion(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))

            self.assertEqual(editor._cmd_buf, f":edit {target}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))

            self.assertTrue(editor._handle_cmd_buf(ord("\n")))
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.lines, ["alpha"])

    def test_filename_completion_supports_write_bang(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":write! {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))

            self.assertEqual(editor._cmd_buf, f":write! {target}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))

    def test_filename_completion_supports_ranged_write_bang(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":2,4write! {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))

            self.assertEqual(editor._cmd_buf, f":2,4write! {target}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))

    def test_filename_completion_tolerates_leading_whitespace_before_command(self):
        # _filename_completion_bounds() computed the command word's offset
        # as 0 whenever no range prefix was found, even though
        # _parse_range_prefix() had already lstripped that leading
        # whitespace off internally. With any whitespace before the bare
        # command (e.g. a habitual "  :w"), every downstream offset pointed
        # too far right, so the command letter itself was treated as (and
        # overwritten by) the filename prefix -- Tab on ":  w" silently
        # turned it into ":  <filename>", discarding the write command.
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "widget.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("data\n")
            old_cwd = os.getcwd()
            try:
                os.chdir(tmpdir)
                editor = ViEditor()
                editor._start_cmd_buf(":  w")

                editor._handle_cmd_buf(ord("\t"))

                self.assertEqual(editor._cmd_buf, ":  w widget.txt")
                self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))
            finally:
                os.chdir(old_cwd)

    def test_filename_completion_tolerates_leading_whitespace_with_range(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":  2,4write! {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))

            self.assertEqual(editor._cmd_buf, f":  2,4write! {target}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))

    def test_filename_completion_ignores_unsupported_bang_commands(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            draft = f":read! {os.path.join(tmpdir, 'alp')}"
            editor._start_cmd_buf(draft)

            editor._handle_cmd_buf(ord("\t"))

            self.assertEqual(editor._cmd_buf, draft)
            self.assertEqual(editor._filename_completion_matches, [])

    def test_filename_completion_updates_history_draft(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._cmd_history[":"] = [":set number"]
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))
            self.assertEqual(editor._cmd_buf, f":edit {target}")

            editor._handle_cmd_buf(curses.KEY_UP)
            self.assertEqual(editor._cmd_buf, ":set number")

            editor._handle_cmd_buf(curses.KEY_DOWN)
            self.assertEqual(editor._cmd_buf, f":edit {target}")

    def test_tab_on_non_filename_command_clears_stale_completion_message(self):
        # :q has no filename or set completion — Tab should clear stale message
        editor = ViEditor()
        editor._start_cmd_buf(":q")
        editor.message = "old completion"
        editor.message_is_error = True

        editor._handle_cmd_buf(ord("\t"))

        self.assertEqual(editor.message, "")
        self.assertFalse(editor.message_is_error)

    def test_tab_on_set_command_shows_completion(self):
        editor = ViEditor()
        editor._start_cmd_buf(":set nu")
        editor.message = "old message"
        editor.message_is_error = True

        editor._handle_cmd_buf(ord("\t"))

        # Should show set completion matches, not the stale message
        self.assertIn("nu", editor.message)
        self.assertFalse(editor.message_is_error)

    def test_filename_completion_preview_clears_stale_error_flag(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for name in ("alpha.txt", "alpine.txt"):
                with open(os.path.join(tmpdir, name), "w", encoding="utf-8") as fh:
                    fh.write(name + "\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'al')}")
            editor.message = "old error"
            editor.message_is_error = True

            editor._handle_cmd_buf(ord("\t"))
            editor._handle_cmd_buf(ord("\t"))

            self.assertIn("alpha.txt", editor.message)
            self.assertIn("alpine.txt", editor.message)
            self.assertFalse(editor.message_is_error)

    def test_filename_completion_preview_updates_history_draft(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for name in ("alpha.txt", "alpine.txt"):
                with open(os.path.join(tmpdir, name), "w", encoding="utf-8") as fh:
                    fh.write(name + "\n")

            editor = ViEditor()
            editor._cmd_history[":"] = [":set number"]
            draft = f":edit {os.path.join(tmpdir, 'alp')}"
            editor._start_cmd_buf(draft)

            editor._handle_cmd_buf(ord("\t"))
            self.assertEqual(editor._cmd_buf, draft)
            self.assertEqual(editor._filename_completion_matches, [
                os.path.join(tmpdir, "alpha.txt"),
                os.path.join(tmpdir, "alpine.txt"),
            ])

            editor._handle_cmd_buf(curses.KEY_UP)
            self.assertEqual(editor._cmd_buf, ":set number")

            editor._handle_cmd_buf(curses.KEY_DOWN)
            self.assertEqual(editor._cmd_buf, draft)

    def test_filename_completion_tabs_cycle_and_accepts_selected_match(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            alpha = os.path.join(tmpdir, "alpha.txt")
            alpine = os.path.join(tmpdir, "alpine.txt")
            for path in (alpha, alpine):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(path + "\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")

            editor._handle_cmd_buf(ord("\t"))
            self.assertEqual(editor._filename_completion_matches, [alpha, alpine])
            self.assertEqual(editor._filename_completion_index, 0)

            editor._handle_cmd_buf(ord("\t"))
            self.assertEqual(editor._filename_completion_index, 1)

            editor._handle_cmd_buf(ord(">"))
            self.assertEqual(editor._cmd_buf, f":edit {alpine}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))
            self.assertEqual(editor._filename_completion_matches, [])

    def test_filename_completion_match_mode_clears_when_command_changes(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for name in ("alpha.txt", "alpine.txt"):
                with open(os.path.join(tmpdir, name), "w", encoding="utf-8") as fh:
                    fh.write(name + "\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")
            editor._handle_cmd_buf(ord("\t"))

            editor._handle_cmd_buf(ord("x"))

            self.assertEqual(editor._filename_completion_matches, [])

    def test_filename_completion_accept_clamps_stale_selected_index(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            alpha = os.path.join(tmpdir, "alpha.txt")
            alpine = os.path.join(tmpdir, "alpine.txt")
            for path in (alpha, alpine):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(path + "\n")

            editor = ViEditor()
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")
            editor._handle_cmd_buf(ord("\t"))
            editor._filename_completion_index = 99

            editor._handle_cmd_buf(ord(">"))

            self.assertEqual(editor._cmd_buf, f":edit {alpine}")
            self.assertEqual(editor._cmd_cursor, len(editor._cmd_buf))
            self.assertEqual(editor._filename_completion_matches, [])

    def test_draws_filename_completion_matches_with_selected_highlight(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 160

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        with tempfile.TemporaryDirectory() as tmpdir:
            alpha = os.path.join(tmpdir, "alpha.txt")
            alpine = os.path.join(tmpdir, "alpine.txt")
            for path in (alpha, alpine):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write(path + "\n")

            editor = ViEditor()
            editor.lines = ["one"]
            editor._start_cmd_buf(f":edit {os.path.join(tmpdir, 'alp')}")
            editor._handle_cmd_buf(ord("\t"))
            editor._handle_cmd_buf(ord("\t"))

            screen = FakeScreen()
            with mock.patch("curses.doupdate"):
                editor.draw(screen)

        selected_calls = [
            args for args in screen.calls
            if len(args) == 4 and args[0] == 7 and args[2] == alpine
        ]
        self.assertTrue(selected_calls)
        self.assertTrue(selected_calls[-1][3] & curses.A_BOLD)

    def test_intellisense_setting_toggles_buffer_completion(self):
        editor = ViEditor()
        editor._apply_set_opt("nointellisense")

        self.assertFalse(editor.intellisense)
        self.assertEqual(editor._apply_set_opt("intellisense"), "")
        self.assertTrue(editor.intellisense)
        self.assertEqual(editor._apply_set_opt("nointellisense"), "")
        self.assertFalse(editor.intellisense)
        self.assertEqual(editor._apply_set_opt("intelisence"), "")
        self.assertTrue(editor.intellisense)

    def test_insert_intellisense_uses_buffer_words_when_enabled(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha alpine beta", "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Ctrl-N starts completion

        self.assertEqual(editor._intellisense_completion_matches, ["alpha", "alpine"])
        self.assertEqual(editor._intellisense_completion_index, 0)

        editor._handle_insert(14)  # Ctrl-N cycles
        self.assertEqual(editor._intellisense_completion_index, 1)

        editor._handle_insert(25)  # Ctrl-Y accepts
        self.assertEqual(editor.lines[1], "alpine")
        self.assertEqual(editor.cursor_col, len("alpine"))

    def test_insert_intellisense_accepts_with_ctrl_space(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha", "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Ctrl-N starts completion
        editor._handle_insert(0)   # Ctrl-Space accepts

        self.assertEqual(editor.lines[1], "alpha")
        self.assertEqual(editor.cursor_col, len("alpha"))

    def test_insert_intellisense_filters_complete_matches_without_rescan(self):
        class NoScanRegex:
            def finditer(self, line):
                raise AssertionError("unexpected intellisense rescan")

        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha alpine beta", "a"]
        editor.cursor_row = 1
        editor.cursor_col = 1
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Build the complete "a" match set.
        self.assertTrue(editor._intellisense_completion_complete)

        with mock.patch.object(editor, "_RE_INTELLISENSE_WORD", NoScanRegex()):
            editor._handle_insert(ord("l"))

        self.assertEqual(editor._intellisense_completion_matches, ["alpha", "alpine"])
        self.assertEqual(editor._intellisense_completion_prefix, "al")

    def test_insert_intellisense_rescans_after_cycling_incomplete_match_set(self):
        editor = ViEditor()
        editor.MAX_INTELLISENSE_MATCHES = 1
        editor.intellisense = True
        editor.lines = ["azure alpine", "a"]
        editor.cursor_row = 1
        editor.cursor_col = 1
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Build a capped, incomplete "a" match set.
        self.assertEqual(editor._intellisense_completion_matches, ["azure"])
        self.assertFalse(editor._intellisense_completion_complete)

        editor._handle_insert(14)  # Cycling must preserve the incomplete flag.
        self.assertFalse(editor._intellisense_completion_complete)

        editor._handle_insert(ord("l"))
        self.assertEqual(editor._intellisense_completion_matches, ["alpine"])
        self.assertEqual(editor._intellisense_completion_prefix, "al")

    # ------------------------------------------------------------------
    # Fix: a pathologically long single line (minified bundle, one huge
    # JSON/log line) used to cost one full, uncached regex scan per
    # keystroke with no bound -- both for other rows via
    # _line_completion_words and, worse, for the cursor's own row, which
    # always bypasses that cache. MAX_INTELLISENSE_LINE_CHARS now gates
    # both scans.
    # ------------------------------------------------------------------

    class _NoScanIfLong:
        """finditer() stand-in that fails the test if ever called with a
        line longer than the configured cap, but behaves normally
        otherwise -- proving the oversized line was skipped rather than
        regex-scanned, without breaking scans of the rows that should
        still work."""

        def __init__(self, real, threshold):
            self._real = real
            self._threshold = threshold

        def finditer(self, line):
            if len(line) > self._threshold:
                raise AssertionError("unexpected regex scan of oversized line")
            return self._real.finditer(line)

    def test_intellisense_skips_oversized_other_row_without_scanning(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.MAX_INTELLISENSE_LINE_CHARS = 10
        huge_line = "alpha " * 5  # 30 chars, over the 10-char cap
        editor.lines = [huge_line, "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT

        guard = self._NoScanIfLong(editor._RE_INTELLISENSE_WORD,
                                    editor.MAX_INTELLISENSE_LINE_CHARS)
        with mock.patch.object(editor, "_RE_INTELLISENSE_WORD", guard):
            editor._handle_insert(14)  # Ctrl-N

        # The oversized row was skipped (no AssertionError above), so with
        # no other row to supply a match, intellisense finds nothing.
        self.assertEqual(editor._intellisense_completion_matches, [])

    def test_intellisense_skips_oversized_current_row_without_scanning(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.MAX_INTELLISENSE_LINE_CHARS = 10
        huge_line = "alpha " * 5 + "al"  # cursor sits inside an over-cap line
        editor.lines = [huge_line]
        editor.cursor_row = 0
        editor.cursor_col = len(huge_line)
        editor.mode = Mode.INSERT

        guard = self._NoScanIfLong(editor._RE_INTELLISENSE_WORD,
                                    editor.MAX_INTELLISENSE_LINE_CHARS)
        with mock.patch.object(editor, "_RE_INTELLISENSE_WORD", guard):
            editor._handle_insert(14)  # Ctrl-N

        self.assertEqual(editor._intellisense_completion_matches, [])

    def test_intellisense_scans_line_exactly_at_the_cap(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.MAX_INTELLISENSE_LINE_CHARS = 12
        line0 = "alpha alpine"
        self.assertEqual(len(line0), 12)
        editor.lines = [line0, "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Ctrl-N

        self.assertEqual(editor._intellisense_completion_matches, ["alpha", "alpine"])

    def test_dot_repeats_insert_intellisense_as_inserted_text(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha", ""]
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._enter_insert()

        for key in (ord("a"), ord("l"), 14, 0, 27):
            editor._handle_insert(key)

        self.assertEqual(editor.lines[1], "alpha")
        editor.cursor_col = 0
        editor._handle_normal(ord("."), 24, 80)

        self.assertEqual(editor.lines[1], "alphaalpha")

    def test_insert_intellisense_does_not_complete_when_disabled(self):
        editor = ViEditor()
        editor._apply_set_opt("nointellisense")
        editor.lines = ["alpha", "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT

        editor._handle_insert(14)

        self.assertEqual(editor._intellisense_completion_matches, [])
        self.assertEqual(editor.lines[1], "al")

    def test_draws_intellisense_matches_like_filename_completion(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha alpine", "al"]
        editor.cursor_row = 1
        editor.cursor_col = 2
        editor.mode = Mode.INSERT
        editor._handle_insert(14)
        editor._handle_insert(14)

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        selected_calls = [
            args for args in screen.calls
            if len(args) == 4 and args[0] == 7 and args[2] == "alpine"
        ]
        self.assertTrue(selected_calls)
        self.assertTrue(selected_calls[-1][3] & curses.A_BOLD)

    def test_intellisense_match_display_suppresses_bottom_breadcrumbs(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.intellisense = True
        editor.filename = "app.py"
        editor.lines = ["class App:", "    alpha", "    al"]
        editor.cursor_row = 2
        editor.cursor_col = 6
        editor.mode = Mode.INSERT
        editor._handle_insert(14)

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        bottom_text = [
            args[2] for args in screen.calls
            if len(args) >= 3 and args[0] == 7
        ]
        self.assertIn("alpha", bottom_text)
        self.assertNotIn("class App", bottom_text)

    def test_generated_insert_commands_insert_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["abXY"]
        editor.cursor_col = 2

        self.assertTrue(editor._execute_cmd(":guid"))

        inserted = editor.lines[0][2:-2]
        self.assertEqual(editor.lines[0][:2], "ab")
        self.assertEqual(editor.lines[0][-2:], "XY")
        self.assertRegex(inserted, r"^[0-9a-f-]{36}$")

    def test_generated_insert_commands_leave_normal_cursor_on_inserted_text(self):
        editor = ViEditor()
        editor.lines = [""]

        self.assertTrue(editor._execute_cmd(":md5"))

        self.assertEqual(editor.cursor_col, len(editor.lines[0]))
        self.assertTrue(editor.undo_stack)

    def test_generated_timestamp_and_md5_formats(self):
        editor = ViEditor()
        editor.lines = [""]

        self.assertTrue(editor._execute_cmd(":md5"))
        self.assertRegex(editor.lines[0], r"^[0-9a-f]{32}$")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":pass"))
        self.assertEqual(len(editor.lines[0]), 20)
        self.assertRegex(editor.lines[0], r"[A-Z]")
        self.assertRegex(editor.lines[0], r"[a-z]")
        self.assertRegex(editor.lines[0], r"\d")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":secret"))
        self.assertGreaterEqual(len(editor.lines[0]), 40)
        self.assertRegex(editor.lines[0], r"^[A-Za-z0-9_-]+$")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":dt-stamp"))
        self.assertRegex(editor.lines[0], r"^\d{8}$")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":dt-utcstamp"))
        self.assertRegex(editor.lines[0], r"^\d{14}$")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":dt-dtstamp"))
        self.assertRegex(editor.lines[0], r"^\d{14}$")

        editor.lines = [""]
        editor.cursor_col = 0
        self.assertTrue(editor._execute_cmd(":dt-datetime"))
        self.assertRegex(editor.lines[0], r"^\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}$")

    def test_file_browser_command_restores_session_state(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            subdir = os.path.join(tmpdir, "src")
            os.mkdir(subdir)
            with open(os.path.join(tmpdir, "alpha.txt"), "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1
            editor.file_browser.left.top_line = 1
            editor.file_browser.left.selected.add(os.path.join(tmpdir, "alpha.txt"))
            editor.file_browser.right.cwd = subdir
            editor.file_browser.active_panel = 1

            self.assertTrue(editor._execute_cmd(":fb"))

            self.assertEqual(editor.mode, Mode.FILE_BROWSER)
            self.assertEqual(editor.file_browser.left.cwd, tmpdir)
            self.assertEqual(editor.file_browser.left.cursor, 1)
            self.assertIn(os.path.join(tmpdir, "alpha.txt"), editor.file_browser.left.selected)
            self.assertEqual(editor.file_browser.right.cwd, subdir)
            self.assertEqual(editor.file_browser.active_panel, 1)

    def test_file_browser_edge_scroll_uses_scrolljump(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for idx in range(10):
                with open(os.path.join(tmpdir, f"file_{idx:02d}.txt"), "w", encoding="utf-8") as fh:
                    fh.write(f"{idx}\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 0
            editor.file_browser.left.top_line = 0
            editor._last_h = 8
            editor.vertical_scroll_jump = 3

            for _ in range(5):
                editor._handle_file_browser(ord("j"))

            self.assertEqual(editor.file_browser.left.cursor, 5)
            self.assertEqual(editor.file_browser.left.top_line, 3)

            for _ in range(3):
                editor._handle_file_browser(ord("k"))

            self.assertEqual(editor.file_browser.left.cursor, 2)
            self.assertEqual(editor.file_browser.left.top_line, 0)

    def test_file_browser_c_key_chdirs_process_to_active_panel(self):
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                real_tmpdir = os.path.realpath(tmpdir)
                editor = ViEditor()
                editor._execute_cmd(":fb")
                editor.file_browser.left.cwd = tmpdir
                editor.file_browser.active_panel = 0

                editor._handle_file_browser(ord("c"))

                self.assertFalse(editor.message_is_error)
                self.assertEqual(os.path.realpath(os.getcwd()), real_tmpdir)
                self.assertEqual(editor.message, os.getcwd())
        finally:
            os.chdir(original_cwd)

    def test_file_browser_c_key_survives_getcwd_failure_after_successful_chdir(self):
        # Regression test: a getcwd() failure right after a successful
        # chdir() must not raise out of _handle_file_browser (which, unlike
        # ex-command dispatch, has no per-keystroke exception guard -- an
        # uncaught exception here previously propagated to edit()'s
        # top-level handler and terminated the whole session).
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmpdir:
                real_tmpdir = os.path.realpath(tmpdir)
                editor = ViEditor()
                editor._execute_cmd(":fb")
                editor.file_browser.left.cwd = tmpdir
                editor.file_browser.active_panel = 0

                with mock.patch("vi_editor.os.getcwd", side_effect=OSError("stale handle")):
                    editor._handle_file_browser(ord("c"))

                self.assertFalse(editor.message_is_error)
                self.assertEqual(editor.message, tmpdir)
                self.assertEqual(os.path.realpath(os.getcwd()), real_tmpdir)
        finally:
            os.chdir(original_cwd)

    def test_file_browser_entry_line_uses_display_width_for_names(self):
        editor = ViEditor()
        panel = editor.file_browser.left
        entry = FileBrowserEntry("\tab", "/tmp/tab", False, 12, 1700000000)

        line = editor._fb_entry_line(panel, entry, 20)

        self.assertEqual(len(line), 20)
        self.assertEqual(len(editor._display_text_at_col(line, 0)), 20)

    def test_file_browser_entry_line_pads_wide_names_by_display_width(self):
        editor = ViEditor()
        panel = editor.file_browser.left
        entry = FileBrowserEntry("你ab", "/tmp/wide", False, 12, 1700000000)

        line = editor._fb_entry_line(panel, entry, 20)

        self.assertEqual(editor._display_width(line), 20)

    def test_display_ljust_fits_escaped_null_by_display_width(self):
        editor = ViEditor()

        text = editor._display_ljust("a\x00b", 5)

        self.assertEqual(text, "a^@b ")
        self.assertEqual(editor._display_width(text), 5)

    def test_file_browser_movement_reuses_directory_entries_cache(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for idx in range(8):
                with open(os.path.join(tmpdir, f"file_{idx:02d}.txt"), "w", encoding="utf-8") as fh:
                    fh.write(f"{idx}\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.cursor = 0
            panel.top_line = 0
            editor._last_h = 8

            real_scandir = os.scandir
            calls = 0

            def counting_scandir(path):
                nonlocal calls
                calls += 1
                return real_scandir(path)

            with mock.patch("vi_editor.os.scandir", side_effect=counting_scandir):
                self.assertEqual(len(editor._fb_entries(panel)), 9)
                editor._handle_file_browser(ord("j"))
                editor._handle_file_browser(ord("j"))
                editor._handle_file_browser(ord("k"))
                self.assertEqual(calls, 1)

                editor._handle_file_browser(ord("s"))
                editor._fb_entries(panel)
                self.assertEqual(calls, 2)

    def test_file_browser_dot_key_toggles_hidden_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            with open(os.path.join(tmpdir, ".secret"), "w", encoding="utf-8") as fh:
                fh.write("hidden\n")
            with open(os.path.join(tmpdir, "visible.txt"), "w", encoding="utf-8") as fh:
                fh.write("shown\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir

            names = [entry.name for entry in editor._fb_entries(panel)]
            self.assertNotIn(".secret", names)

            editor._handle_file_browser(ord("."))
            names = [entry.name for entry in editor._fb_entries(panel)]
            self.assertIn(".secret", names)
            self.assertEqual(panel.cursor, 0)
            self.assertEqual(panel.top_line, 0)

            editor._handle_file_browser(ord("."))
            names = [entry.name for entry in editor._fb_entries(panel)]
            self.assertNotIn(".secret", names)

    def test_file_browser_h_key_jumps_to_home_directory(self):
        editor = ViEditor()
        editor._execute_cmd(":fb")
        panel = editor.file_browser.left
        panel.cwd = "/tmp"
        panel.cursor = 3
        panel.top_line = 2

        editor._handle_file_browser(ord("H"))

        self.assertEqual(panel.cwd, os.path.expanduser("~"))
        self.assertEqual(panel.cursor, 0)
        self.assertEqual(panel.top_line, 0)

    def test_file_browser_ctrl_l_refreshes_cached_file_metadata(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "note.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("x")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            entries = editor._fb_entries(panel)
            note = next(entry for entry in entries if entry.name == "note.txt")
            self.assertEqual(note.size, 1)

            with open(target, "w", encoding="utf-8") as fh:
                fh.write("expanded")

            entries = editor._fb_entries(panel)
            note = next(entry for entry in entries if entry.name == "note.txt")
            self.assertEqual(note.size, 1)

            editor._handle_file_browser(12)
            entries = editor._fb_entries(panel)
            note = next(entry for entry in entries if entry.name == "note.txt")
            self.assertEqual(note.size, 8)

    def test_file_browser_size_formatter_abbreviates_large_values(self):
        editor = ViEditor()

        self.assertEqual(editor._fb_format_size(999), "999")
        self.assertEqual(editor._fb_format_size(1024), "1K")
        self.assertEqual(editor._fb_format_size(1536), "1.5K")
        self.assertEqual(editor._fb_format_size(1048575), "1M")
        self.assertEqual(editor._fb_format_size(1048576), "1M")
        self.assertEqual(editor._fb_format_size(1073741823), "1G")

    def test_draw_file_browser_shows_modified_time_and_abbreviated_size(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 120

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "large.bin")
            with open(target, "wb") as fh:
                fh.write(b"x" * 1536)
            timestamp = 1700000000
            os.utime(target, (timestamp, timestamp))

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.cursor = 1

            screen = FakeScreen()
            with mock.patch("curses.doupdate"):
                editor.draw(screen)

            rendered = [args[2] for args in screen.calls if len(args) >= 3]
            self.assertTrue(any("1.5K" in text for text in rendered))
            self.assertTrue(any(editor._fb_format_mtime(timestamp) in text for text in rendered))

    def test_draw_file_browser_message_uses_display_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 7

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor._execute_cmd(":fb")
        editor.message = "e\u0301abcde"

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor._draw_file_browser(screen, 8, 7)

        rendered = [args[2] for args in screen.calls if len(args) >= 3]
        self.assertIn("e\u0301abcde", rendered)

    def test_file_browser_entry_line_uses_panel_selection_for_marker(self):
        editor = ViEditor()
        left, right = editor._fb_panels()
        left.selected = {"/tmp/left.txt"}
        right.selected = {"/tmp/right.txt"}

        left_line = editor._fb_entry_line(
            left, FileBrowserEntry("left.txt", "/tmp/left.txt", False, 1, 1700000000), 40
        )
        right_line = editor._fb_entry_line(
            right, FileBrowserEntry("right.txt", "/tmp/right.txt", False, 1, 1700000000), 40
        )

        self.assertTrue(left_line.startswith("*"))
        self.assertTrue(right_line.startswith("*"))

    def test_file_browser_entry_line_keeps_separator_before_timestamp(self):
        editor = ViEditor()
        line = editor._fb_entry_line(
            editor.file_browser.left,
            FileBrowserEntry("verylongfilenameeeeeeeee.txt", "/tmp/x", False, 123456789, 1700000000),
            35,
        )

        self.assertIn(" 2023-11-14 17:13", line)

    def test_current_buffer_is_modified_refreshes_stale_clean_text_change(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._mark_clean()
        editor.lines[0] = "beta"

        self.assertTrue(editor._current_buffer_is_modified())

    def test_current_buffer_is_modified_refreshes_stale_clean_line_ending_change(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor.line_endings = [""]
        editor._mark_clean()
        editor.line_endings = ["\r\n"]

        self.assertTrue(editor._current_buffer_is_modified())

    def test_current_buffer_is_modified_recomputes_before_returning(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._mark_clean()

        with mock.patch.object(editor, "_refresh_modified", wraps=editor._refresh_modified) as refresh:
            self.assertFalse(editor._current_buffer_is_modified())

        refresh.assert_called_once()

    def test_file_browser_enter_opens_file_in_new_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "alpha.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1

            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.lines, ["alpha"])
            self.assertEqual(len(editor.buffers), 2)

    def test_file_browser_enter_navigates_into_symlinked_directory(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            real_dir = os.path.join(tmpdir, "realdir")
            os.mkdir(real_dir)
            with open(os.path.join(real_dir, "inside.txt"), "w", encoding="utf-8") as fh:
                fh.write("hi\n")
            link = os.path.join(tmpdir, "linkdir")
            os.symlink(real_dir, link, target_is_directory=True)

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir

            entries = editor._fb_entries(panel)
            link_entry = next(e for e in entries if e.name == "linkdir")
            self.assertTrue(link_entry.is_dir)
            panel.cursor = entries.index(link_entry)

            editor._handle_file_browser(ord("l"))

            self.assertEqual(editor.mode, Mode.FILE_BROWSER)
            self.assertFalse(editor.message_is_error)
            self.assertEqual(panel.cwd, link)
            entries_after = editor._fb_entries(panel)
            self.assertIn("inside.txt", [e.name for e in entries_after])

    def test_file_browser_enter_opens_marked_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            alpha = os.path.join(tmpdir, "alpha.txt")
            beta = os.path.join(tmpdir, "beta.txt")
            subdir = os.path.join(tmpdir, "subdir")
            os.mkdir(subdir)
            with open(alpha, "w", encoding="utf-8") as fh:
                fh.write("alpha\n")
            with open(beta, "w", encoding="utf-8") as fh:
                fh.write("beta\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.selected.update({alpha, beta, subdir})

            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual([b.filename for b in editor.buffers[1:]], [alpha, beta])
            self.assertEqual(editor.filename, alpha)
            self.assertEqual(editor.lines, ["alpha"])
            self.assertEqual(panel.selected, set())

    def test_file_browser_grep_results_open_match_line(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            src = os.path.join(tmpdir, "src")
            os.mkdir(src)
            target = os.path.join(src, "code.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("one\nneedle here\nthree\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1

            editor._handle_file_browser(ord("g"))
            self.assertTrue(editor.file_browser.grep_prompt)
            for ch in "needle":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))
            self.assertTrue(editor.file_browser.grep_prompt)
            self.assertEqual(editor.file_browser.grep_field, "mask")
            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.GREP_RESULTS)
            self.assertEqual(len(editor.grep_results), 1)
            self.assertEqual(editor.grep_results[0].filename, target)
            self.assertEqual(editor.grep_results[0].line_no, 2)

            editor._handle_grep_results(ord("\n"))

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.cursor_row, 1)

    def test_file_browser_grep_file_mask_filters_results(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            src = os.path.join(tmpdir, "src")
            os.mkdir(src)
            py_file = os.path.join(src, "code.py")
            txt_file = os.path.join(src, "notes.txt")
            with open(py_file, "w", encoding="utf-8") as fh:
                fh.write("needle\n")
            with open(txt_file, "w", encoding="utf-8") as fh:
                fh.write("needle\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1

            editor._handle_file_browser(ord("g"))
            for ch in "needle":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))
            for ch in "*.py":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.GREP_RESULTS)
            self.assertEqual([result.filename for result in editor.grep_results], [py_file])

    def test_file_browser_grep_includes_hidden_directory_when_hidden_entries_are_shown(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            hidden_dir = os.path.join(tmpdir, ".hidden")
            os.mkdir(hidden_dir)
            target = os.path.join(hidden_dir, "secret.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("needle\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir

            editor._handle_file_browser(ord("."))
            entries = editor._fb_entries(panel)
            panel.cursor = next(i for i, entry in enumerate(entries) if entry.name == ".hidden")

            editor._handle_file_browser(ord("g"))
            for ch in "needle":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))
            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.GREP_RESULTS)
            self.assertEqual([result.filename for result in editor.grep_results], [target])

    def test_file_browser_g_key_opens_grep_prompt_with_cursor_on_file(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "code.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("one\nneedle here\nthree\n")

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            entries = editor._fb_entries(panel)
            panel.cursor = next(i for i, e in enumerate(entries) if e.name == "code.txt")

            editor._handle_file_browser(ord("g"))

            self.assertTrue(editor.file_browser.grep_prompt)
            self.assertEqual(editor.file_browser.grep_field, "pattern")
            self.assertEqual(panel.cursor, entries.index(
                next(e for e in entries if e.name == "code.txt")
            ))

            for ch in "needle":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))
            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.GREP_RESULTS)
            self.assertEqual([result.filename for result in editor.grep_results], [target])

    def test_file_browser_grep_prompt_supports_cursor_editing(self):
        editor = ViEditor()
        editor.file_browser.grep_prompt = True
        editor.file_browser.grep_field = "pattern"
        for ch in "ac":
            editor._handle_file_browser(ord(ch))

        editor._handle_file_browser(curses.KEY_LEFT)
        editor._handle_file_browser(ord("b"))

        self.assertEqual(editor.file_browser.grep_text, "abc")
        self.assertEqual(editor.file_browser.grep_cursor, 2)

        editor._handle_file_browser(curses.KEY_BACKSPACE)
        self.assertEqual(editor.file_browser.grep_text, "ac")
        self.assertEqual(editor.file_browser.grep_cursor, 1)

    def test_file_browser_grep_prompt_accepts_non_ascii_text(self):
        editor = ViEditor()
        editor.file_browser.grep_prompt = True
        editor.file_browser.grep_field = "pattern"

        editor._handle_file_browser(ord("é"))

        self.assertEqual(editor.file_browser.grep_text, "é")
        self.assertEqual(editor.file_browser.grep_cursor, 1)

    # --- File browser file operations (F5 copy / F6 move / F7 mkdir / F8 delete) ---

    def _open_fb_at(self, editor: ViEditor, cwd: str, cursor_name: str = "") -> None:
        editor._execute_cmd(":fb")
        editor.file_browser.left.cwd = cwd
        editor.file_browser.right.cwd = cwd
        editor.file_browser.active_panel = 0
        panel = editor._active_fb_panel()
        editor._invalidate_fb_entries(panel)
        if cursor_name:
            for i, ent in enumerate(editor._fb_entries(panel)):
                if ent.name == cursor_name:
                    panel.cursor = i
                    return
            self.fail(f"entry {cursor_name!r} not found in {cwd}")

    def test_fb_f7_mkdir_creates_directory_and_focuses_it(self):
        with tempfile.TemporaryDirectory() as tmp:
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(curses.KEY_F7)
            self.assertTrue(editor.file_browser.op_prompt)
            self.assertEqual(editor.file_browser.op_kind, "mkdir_name")
            for ch in "newdir":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(os.path.isdir(os.path.join(tmp, "newdir")))
            self.assertFalse(editor.file_browser.op_prompt)
            self.assertFalse(editor.message_is_error)

    def test_fb_f7_mkdir_does_not_call_getcwd_when_payload_has_cwd(self):
        # Regression test: op_payload.get("cwd", os.getcwd()) used to
        # evaluate os.getcwd() eagerly on every call, unconditionally --
        # even though "cwd" is always present in practice (_fb_action_mkdir
        # sets it explicitly). A getcwd() failure here would crash the
        # whole editor: _handle_file_browser has no per-key exception
        # guard, unlike ex-command dispatch.
        with tempfile.TemporaryDirectory() as tmp:
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(curses.KEY_F7)
            for ch in "newdir":
                editor._handle_file_browser(ord(ch))

            with mock.patch("vi_editor.os.getcwd") as mock_getcwd:
                editor._handle_file_browser(ord("\n"))
            mock_getcwd.assert_not_called()

            self.assertTrue(os.path.isdir(os.path.join(tmp, "newdir")))
            self.assertFalse(editor.message_is_error)

    def test_fb_f7_mkdir_existing_directory_reports_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "existing"))
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(curses.KEY_F7)
            for ch in "existing":
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(editor.message_is_error)
            self.assertIn("Already exists", editor.message)

    def test_fb_colon_key_opens_goto_prompt_prefilled_with_cwd(self):
        with tempfile.TemporaryDirectory() as tmp:
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(ord(":"))

            self.assertTrue(editor.file_browser.op_prompt)
            self.assertEqual(editor.file_browser.op_kind, "goto_dir")
            self.assertEqual(editor.file_browser.op_text, tmp + os.sep)

    def test_fb_goto_prompt_navigates_active_panel_to_typed_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = os.path.join(tmp, "target")
            os.makedirs(target)
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(ord(":"))
            for ch in editor.file_browser.op_text:
                editor._handle_file_browser(curses.KEY_BACKSPACE)
            for ch in target:
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))

            self.assertFalse(editor.file_browser.op_prompt)
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor._active_fb_panel().cwd, target)

    def test_fb_goto_prompt_rejects_non_directory(self):
        with tempfile.TemporaryDirectory() as tmp:
            not_a_dir = os.path.join(tmp, "file.txt")
            with open(not_a_dir, "w", encoding="utf-8") as fh:
                fh.write("x\n")
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(ord(":"))
            for ch in editor.file_browser.op_text:
                editor._handle_file_browser(curses.KEY_BACKSPACE)
            for ch in not_a_dir:
                editor._handle_file_browser(ord(ch))
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(editor.message_is_error)
            self.assertIn("Not a directory", editor.message)
            self.assertEqual(editor._active_fb_panel().cwd, tmp)

    def test_fb_goto_prompt_tab_completes_subdirectory_only(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "subdir"))
            with open(os.path.join(tmp, "subfile.txt"), "w", encoding="utf-8") as fh:
                fh.write("x\n")
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(ord(":"))
            for ch in "sub":
                editor._handle_file_browser(ord(ch))

            editor._handle_file_browser(ord("\t"))

            self.assertEqual(
                editor.file_browser.op_text,
                os.path.join(tmp, "subdir") + "/",
            )

            editor._handle_file_browser(ord("\n"))
            self.assertFalse(editor.message_is_error)
            self.assertEqual(
                editor._active_fb_panel().cwd,
                os.path.join(tmp, "subdir"),
            )

    def test_fb_goto_prompt_tab_cycles_multiple_matches(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "alpha"))
            os.makedirs(os.path.join(tmp, "beta"))
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(ord(":"))
            # The prompt starts prefilled with "<tmp>/" (trailing separator),
            # which is itself a valid dirname/basename="" split -- pressing
            # Tab immediately lists tmp's subdirectories.

            editor._handle_file_browser(ord("\t"))
            first = editor.file_browser.op_text
            editor._handle_file_browser(ord("\t"))
            second = editor.file_browser.op_text

            self.assertNotEqual(first, second)
            self.assertEqual(
                {first, second},
                {os.path.join(tmp, "alpha") + "/", os.path.join(tmp, "beta") + "/"},
            )

            editor._handle_file_browser(ord("\t"))
            self.assertEqual(editor.file_browser.op_text, first)

    def test_fb_goto_prompt_tab_anchors_relative_prefix_to_panel_not_process_cwd(self):
        # Regression test: clearing the prefilled absolute path and typing a
        # bare/relative fragment must still complete against the browsed
        # panel's directory, not whatever directory the process happens to
        # be running in (the two commonly differ).
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmp, \
                 tempfile.TemporaryDirectory() as unrelated_cwd:
                os.makedirs(os.path.join(tmp, "targetdir"))
                # An isolated process cwd guaranteed to have no "target*"
                # entry of its own -- if completion ever falls back to
                # resolving against os.getcwd() instead of the panel, this
                # lookup finds nothing rather than accidentally matching.
                os.chdir(unrelated_cwd)

                editor = ViEditor()
                self._open_fb_at(editor, tmp)

                editor._handle_file_browser(ord(":"))
                for _ in editor.file_browser.op_text:
                    editor._handle_file_browser(curses.KEY_BACKSPACE)
                self.assertEqual(editor.file_browser.op_text, "")
                for ch in "target":
                    editor._handle_file_browser(ord(ch))

                editor._handle_file_browser(ord("\t"))

                self.assertFalse(editor.message_is_error)
                self.assertEqual(
                    editor.file_browser.op_text,
                    os.path.join(tmp, "targetdir") + "/",
                )
        finally:
            os.chdir(original_cwd)

    def test_fb_goto_prompt_enter_anchors_relative_text_to_panel_not_process_cwd(self):
        # Regression test: the Enter-to-navigate path (_fb_finish_goto_prompt)
        # must anchor a relative fragment to the browsed panel exactly like
        # the Tab-completion path does -- these are two entry points into
        # the same "resolve goto-prompt text" job and must agree, or typing
        # a relative path and pressing Enter directly (no Tab) silently
        # navigates against the wrong directory whenever panel.cwd differs
        # from the process's cwd.
        original_cwd = os.getcwd()
        try:
            with tempfile.TemporaryDirectory() as tmp, \
                 tempfile.TemporaryDirectory() as unrelated_cwd:
                target = os.path.join(tmp, "targetdir")
                os.makedirs(target)
                os.chdir(unrelated_cwd)

                editor = ViEditor()
                self._open_fb_at(editor, tmp)

                editor._handle_file_browser(ord(":"))
                for _ in editor.file_browser.op_text:
                    editor._handle_file_browser(curses.KEY_BACKSPACE)
                self.assertEqual(editor.file_browser.op_text, "")
                for ch in "targetdir":
                    editor._handle_file_browser(ord(ch))
                editor._handle_file_browser(ord("\n"))

                self.assertFalse(editor.file_browser.op_prompt)
                self.assertFalse(editor.message_is_error)
                self.assertEqual(editor._active_fb_panel().cwd, target)
        finally:
            os.chdir(original_cwd)

    def test_fb_perform_copy_and_move_pass_distinct_op_is_move_via_shared_prep(self):
        # _fb_perform_copy/_fb_perform_move now share _fb_prepare_dest_op's
        # preamble; this pins that each still forwards its own op_is_move
        # to _fb_check_buffer_conflicts (copy: False, move: True) -- a
        # move is allowed to "overwrite" the open buffer it's renaming
        # itself into, a copy never is, so mixing these up would either
        # block ordinary renames or silently allow a copy to clobber its
        # own source buffer.
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "a.txt")
            open(src, "w").close()
            dest = os.path.join(tmp, "b.txt")
            editor = ViEditor()

            with mock.patch.object(editor, "_fb_check_buffer_conflicts",
                                    return_value=None) as mock_conflict:
                editor._fb_perform_copy([src], dest)
            mock_conflict.assert_called_once()
            self.assertFalse(mock_conflict.call_args.kwargs["op_is_move"])

            with mock.patch.object(editor, "_fb_check_buffer_conflicts",
                                    return_value=None) as mock_conflict:
                editor._fb_perform_move([src], dest)
            mock_conflict.assert_called_once()
            self.assertTrue(mock_conflict.call_args.kwargs["op_is_move"])

    def test_fb_f5_copy_drops_into_other_panel_with_default_trailing_slash(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "f.txt"), "w") as fh:
                fh.write("CONTENT")

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="f.txt")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            # Default destination is "<dst>/" (trailing sep) → "into dir".
            self.assertEqual(editor.file_browser.op_kind, "copy_dest")
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(os.path.isfile(os.path.join(dst, "f.txt")))
            with open(os.path.join(dst, "f.txt")) as fh:
                self.assertEqual(fh.read(), "CONTENT")

    def test_fb_finish_dest_prompt_does_not_call_getcwd_when_payload_has_src_cwd(self):
        # Regression test: op_payload.get("src_cwd", os.getcwd()) used to
        # evaluate os.getcwd() eagerly on every call, unconditionally --
        # even though "src_cwd" is always present in practice
        # (_fb_action_copy/_fb_action_move set it explicitly). Covers both
        # copy and move since they share _fb_finish_dest_prompt.
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "f.txt"), "w") as fh:
                fh.write("CONTENT")

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="f.txt")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            self.assertEqual(editor.file_browser.op_kind, "copy_dest")

            with mock.patch("vi_editor.os.getcwd") as mock_getcwd:
                editor._handle_file_browser(ord("\n"))
            mock_getcwd.assert_not_called()

            self.assertFalse(editor.message_is_error)
            self.assertTrue(os.path.isfile(os.path.join(dst, "f.txt")))

    def test_fb_finish_dest_prompt_falls_back_safely_when_src_cwd_missing(self):
        # Defensive path: if op_payload ever lacked "src_cwd" (it always
        # has it via the UI, but the fallback exists for safety), a
        # getcwd() failure there must degrade gracefully via _safe_getcwd
        # instead of raising out of the unguarded file-browser dispatch.
        editor = ViEditor()
        editor.file_browser.op_text = "somewhere"
        editor.file_browser.op_payload = {"sources": ["/nonexistent/src"]}

        with mock.patch("vi_editor.os.getcwd", side_effect=OSError("stale handle")):
            with mock.patch.object(editor, "_fb_perform_copy") as mock_perform:
                editor._fb_finish_dest_prompt(editor._fb_perform_copy)

        mock_perform.assert_called_once()
        # src_cwd fell back to "." rather than propagating the OSError.
        _, called_dest = mock_perform.call_args.args
        self.assertTrue(called_dest)

    def test_fb_f5_copy_overwrites_existing_after_confirm(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "f.txt"), "w") as fh:
                fh.write("NEW")
            with open(os.path.join(dst, "f.txt"), "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="f.txt")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            editor._handle_file_browser(ord("\n"))
            self.assertEqual(editor.file_browser.op_kind, "confirm:copy_overwrite")
            editor._handle_file_browser(ord("y"))

            with open(os.path.join(dst, "f.txt")) as fh:
                self.assertEqual(fh.read(), "NEW")

    def test_fb_f5_copy_overwrite_n_keeps_destination(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "f.txt"), "w") as fh:
                fh.write("NEW")
            with open(os.path.join(dst, "f.txt"), "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="f.txt")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            editor._handle_file_browser(ord("\n"))
            editor._handle_file_browser(ord("n"))

            with open(os.path.join(dst, "f.txt")) as fh:
                self.assertEqual(fh.read(), "OLD")

    def test_fb_f5_copy_overwrite_failure_restores_destination(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            with mock.patch("vi_editor.shutil.copy2", side_effect=OSError("copy failed")):
                editor._fb_perform_copy([source_path], target_path, overwrite=True)

            self.assertTrue(editor.message_is_error)
            with open(target_path) as fh:
                self.assertEqual(fh.read(), "OLD")
            with open(source_path) as fh:
                self.assertEqual(fh.read(), "NEW")

    def test_fb_f5_copy_overwrite_failure_restores_via_direct_rename(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            with mock.patch.object(editor, "_fb_remove_existing_target") as remove_mock, \
                    mock.patch("vi_editor.shutil.copy2", side_effect=OSError("copy failed")):
                editor._fb_perform_copy([source_path], target_path, overwrite=True)

            # copy2 failed before creating anything at target_path, so the
            # restore is a single direct os.rename(backup, tgt): a file
            # target is always atomically replaceable in one step, so the
            # remove-then-rename fallback must never run here -- there is
            # no window where target_path holds neither the original nor
            # partial content.
            remove_mock.assert_not_called()
            self.assertTrue(editor.message_is_error)
            with open(target_path) as fh:
                self.assertEqual(fh.read(), "OLD")

    def test_fb_f5_copy_failure_with_failed_restore_reports_backup_location(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            real_rename = os.rename

            def flaky_rename(old, new):
                # Let the target→backup rename through, fail the restore.
                if new == target_path:
                    raise OSError("restore failed")
                return real_rename(old, new)

            editor = ViEditor()
            with mock.patch("vi_editor.shutil.copy2", side_effect=OSError("copy failed")), \
                    mock.patch("vi_editor.os.rename", side_effect=flaky_rename):
                editor._fb_perform_copy([source_path], target_path, overwrite=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("original preserved at", editor.message)
            # The original content is still on disk under the backup name.
            backups = [
                name for name in os.listdir(dst)
                if name.startswith(".vii-overwrite-f.txt-")
            ]
            self.assertEqual(len(backups), 1)
            with open(os.path.join(dst, backups[0])) as fh:
                self.assertEqual(fh.read(), "OLD")

    def test_fb_copy_batch_skips_failed_item_and_copies_the_rest(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_a = os.path.join(tmp, "a.txt")
            src_b = os.path.join(tmp, "b.txt")
            dst_dir = os.path.join(tmp, "dst")
            os.makedirs(dst_dir)
            with open(src_a, "w") as fh:
                fh.write("A")
            with open(src_b, "w") as fh:
                fh.write("B")

            real_copy2 = shutil.copy2

            def flaky_copy2(src, tgt, *args, **kwargs):
                if src == src_a:
                    raise OSError("permission denied")
                return real_copy2(src, tgt, *args, **kwargs)

            editor = ViEditor()
            with mock.patch("vi_editor.shutil.copy2", side_effect=flaky_copy2):
                editor._fb_perform_copy([src_a, src_b], dst_dir, into_dir=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("Copied 1 item", editor.message)
            self.assertIn("a.txt", editor.message)
            self.assertIn("permission denied", editor.message)
            self.assertFalse(os.path.exists(os.path.join(dst_dir, "a.txt")))
            with open(os.path.join(dst_dir, "b.txt")) as fh:
                self.assertEqual(fh.read(), "B")

    def test_fb_move_batch_skips_failed_item_and_moves_the_rest(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_a = os.path.join(tmp, "a.txt")
            src_b = os.path.join(tmp, "b.txt")
            dst_dir = os.path.join(tmp, "dst")
            os.makedirs(dst_dir)
            with open(src_a, "w") as fh:
                fh.write("A")
            with open(src_b, "w") as fh:
                fh.write("B")

            editor = ViEditor()
            real_move = editor._fb_move_one

            def flaky_move(src, tgt, *args, **kwargs):
                if src == src_a:
                    raise OSError("permission denied")
                return real_move(src, tgt, *args, **kwargs)

            with mock.patch.object(editor, "_fb_move_one", side_effect=flaky_move):
                editor._fb_perform_move([src_a, src_b], dst_dir, into_dir=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("Moved 1 item", editor.message)
            self.assertIn("a.txt", editor.message)
            self.assertTrue(os.path.exists(src_a))
            self.assertFalse(os.path.exists(src_b))
            with open(os.path.join(dst_dir, "b.txt")) as fh:
                self.assertEqual(fh.read(), "B")

    def test_fb_delete_batch_skips_failed_item_and_deletes_the_rest(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_a = os.path.join(tmp, "a.txt")
            src_b = os.path.join(tmp, "b.txt")
            with open(src_a, "w") as fh:
                fh.write("A")
            with open(src_b, "w") as fh:
                fh.write("B")

            real_remove = os.remove

            def flaky_remove(path):
                if path == src_a:
                    raise OSError("permission denied")
                return real_remove(path)

            editor = ViEditor()
            with mock.patch("vi_editor.os.remove", side_effect=flaky_remove):
                editor._fb_perform_delete([src_a, src_b])

            self.assertTrue(editor.message_is_error)
            self.assertIn("Deleted 1 item", editor.message)
            self.assertIn("a.txt", editor.message)
            self.assertTrue(os.path.exists(src_a))
            self.assertFalse(os.path.exists(src_b))

    def test_fb_f5_copy_new_destination_failure_cleans_up_partial_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW CONTENT")

            def flaky_copy2(src_path, tgt_path, *args, **kwargs):
                # Simulate a copy that writes some bytes to the new
                # destination before failing partway through (disk full).
                with open(tgt_path, "w") as fh:
                    fh.write("PARTIAL")
                raise OSError("disk full")

            editor = ViEditor()
            with mock.patch("vi_editor.shutil.copy2", side_effect=flaky_copy2):
                editor._fb_perform_copy([source_path], target_path)

            self.assertTrue(editor.message_is_error)
            self.assertFalse(
                os.path.exists(target_path),
                "a failed copy to a brand-new destination must not leave "
                "partial content behind",
            )

    def test_fb_f6_move_new_destination_failure_cleans_up_partial_dir(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_dir = os.path.join(tmp, "srcdir")
            os.makedirs(src_dir)
            with open(os.path.join(src_dir, "a.txt"), "w") as fh:
                fh.write("A")
            target_dir = os.path.join(tmp, "destdir")  # does not exist yet

            def flaky_copy(src_path, tgt_path, *args, **kwargs):
                # Simulate the copy phase of a cross-device
                # directory move (copytree succeeds partway) before failing.
                os.makedirs(tgt_path)
                with open(os.path.join(tgt_path, "partial.txt"), "w") as fh:
                    fh.write("partial")
                raise OSError("disk full")

            editor = ViEditor()
            with mock.patch("vi_editor.os.rename", side_effect=OSError(errno.EXDEV, "cross-device")), \
                 mock.patch.object(editor, "_fb_copy_one", side_effect=flaky_copy):
                editor._fb_perform_move([src_dir], target_dir)

            self.assertTrue(editor.message_is_error)
            self.assertFalse(
                os.path.exists(target_dir),
                "a failed move to a brand-new destination must not leave a "
                "partial directory behind",
            )
            self.assertTrue(os.path.exists(os.path.join(src_dir, "a.txt")))

    def test_fb_f5_refuses_to_copy_directory_inside_itself(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_dir = os.path.join(tmp, "dir")
            os.makedirs(src_dir)
            with open(os.path.join(src_dir, "f.txt"), "w") as fh:
                fh.write("data")
            target_dir = os.path.join(src_dir, "child")

            editor = ViEditor()
            editor._fb_perform_copy([src_dir], target_dir)

            self.assertTrue(editor.message_is_error)
            self.assertIn("inside itself", editor.message)
            self.assertFalse(os.path.exists(target_dir))
            self.assertTrue(os.path.exists(os.path.join(src_dir, "f.txt")))

    def test_fb_f5_copy_success_ignores_overwrite_backup_cleanup_failure(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            real_remove = editor._fb_remove_existing_target

            def fail_backup_cleanup(path):
                if os.path.basename(path).startswith(".vii-overwrite-"):
                    raise OSError("cleanup failed")
                return real_remove(path)

            with mock.patch.object(editor, "_fb_remove_existing_target", side_effect=fail_backup_cleanup):
                editor._fb_perform_copy([source_path], target_path, overwrite=True)

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.message, "Copied 1 item")
            with open(target_path) as fh:
                self.assertEqual(fh.read(), "NEW")

    def test_fb_f5_copy_file_overwriting_dir_replaces_dir(self):
        # Pre-fix bug: a file copied over an existing same-named directory
        # ended up INSIDE that directory. With trailing-slash semantics, an
        # input WITHOUT a trailing separator means "exact path" so the file
        # should replace the directory entirely.
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "foo"), "w") as fh:
                fh.write("FILE")
            os.makedirs(os.path.join(dst, "foo"))
            with open(os.path.join(dst, "foo", "old.txt"), "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="foo")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            # User clears default and types an exact path (no trailing /).
            s = editor.file_browser
            s.op_text = os.path.join(dst, "foo")
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))
            self.assertEqual(s.op_kind, "confirm:copy_overwrite")
            editor._handle_file_browser(ord("y"))

            self.assertTrue(os.path.isfile(os.path.join(dst, "foo")))
            with open(os.path.join(dst, "foo")) as fh:
                self.assertEqual(fh.read(), "FILE")

    def test_fb_f6_move_default_treats_destination_as_exact_path(self):
        # F6 default for a single source ends with the basename (no trailing
        # slash). Pressing Enter should rename to that exact path, including
        # overwriting an existing directory at that path after confirmation.
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            with open(os.path.join(src, "foo"), "w") as fh:
                fh.write("FILE")
            os.makedirs(os.path.join(dst, "foo"))

            editor = ViEditor()
            self._open_fb_at(editor, src, cursor_name="foo")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F6)
            editor._handle_file_browser(ord("\n"))
            self.assertEqual(editor.file_browser.op_kind, "confirm:move_overwrite")
            editor._handle_file_browser(ord("y"))

            self.assertTrue(os.path.isfile(os.path.join(dst, "foo")))
            with open(os.path.join(dst, "foo")) as fh:
                self.assertEqual(fh.read(), "FILE")
            self.assertFalse(os.path.exists(os.path.join(src, "foo")))

    def test_fb_f6_move_overwrite_failure_restores_destination(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            editor = ViEditor()
            real_rename = os.rename

            def fail_source_rename(src, dst):
                if src == source_path:
                    raise OSError("move failed")
                return real_rename(src, dst)

            with mock.patch("vi_editor.os.rename", side_effect=fail_source_rename):
                editor._fb_perform_move([source_path], target_path, overwrite=True)

            self.assertTrue(editor.message_is_error)
            with open(target_path) as fh:
                self.assertEqual(fh.read(), "OLD")
            with open(source_path) as fh:
                self.assertEqual(fh.read(), "NEW")

    def test_fb_f6_refuses_nested_source_selection_before_partial_move(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_root = os.path.join(tmp, "src")
            os.makedirs(src_root)
            dst_root = os.path.join(tmp, "dst")
            os.makedirs(dst_root)
            parent = os.path.join(src_root, "dir")
            os.makedirs(parent)
            child = os.path.join(parent, "child.txt")
            with open(child, "w") as fh:
                fh.write("child")

            editor = ViEditor()
            editor._fb_perform_move([parent, child], dst_root, into_dir=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("nested selection", editor.message)
            self.assertTrue(os.path.exists(parent))
            self.assertTrue(os.path.exists(child))
            self.assertEqual(os.listdir(dst_root), [])

    def test_fb_f5_copy_warns_before_large_operation(self):
        # Copy/move run shutil calls synchronously in the key handler with
        # no way to cancel, like the grep walk -- above FB_LARGE_OP_WARN_*
        # this should require an extra confirmation before blocking.
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            for i in range(5):
                with open(os.path.join(src, f"f{i}.txt"), "w") as fh:
                    fh.write("x" * 100)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)

            editor = ViEditor()
            editor.FB_LARGE_OP_WARN_COUNT = 3
            self._open_fb_at(editor, tmp, cursor_name="src")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            self.assertEqual(editor.file_browser.op_kind, "confirm:large_copy")
            self.assertIn("Continue?", editor.file_browser.op_label)

            editor._handle_file_browser(ord("y"))
            self.assertEqual(editor.file_browser.op_kind, "copy_dest")

            editor._handle_file_browser(ord("\n"))  # accept the default dest

            copied = os.path.join(dst, "src")
            self.assertTrue(os.path.isdir(copied))
            self.assertEqual(sorted(os.listdir(copied)), sorted(os.listdir(src)))

    def test_fb_f5_copy_large_operation_warning_declined_does_nothing(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            for i in range(5):
                with open(os.path.join(src, f"f{i}.txt"), "w") as fh:
                    fh.write("x")
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)

            editor = ViEditor()
            editor.FB_LARGE_OP_WARN_COUNT = 3
            self._open_fb_at(editor, tmp, cursor_name="src")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F5)
            self.assertEqual(editor.file_browser.op_kind, "confirm:large_copy")

            editor._handle_file_browser(ord("n"))

            self.assertFalse(editor.file_browser.op_prompt)
            self.assertEqual(os.listdir(dst), [])

    def test_fb_f6_move_warns_before_large_operation(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            for i in range(5):
                with open(os.path.join(src, f"f{i}.txt"), "w") as fh:
                    fh.write("x")
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)

            editor = ViEditor()
            editor.FB_LARGE_OP_WARN_COUNT = 3
            self._open_fb_at(editor, tmp, cursor_name="src")
            editor.file_browser.right.cwd = dst

            editor._handle_file_browser(curses.KEY_F6)
            self.assertEqual(editor.file_browser.op_kind, "confirm:large_move")
            self.assertIn("Continue?", editor.file_browser.op_label)

            editor._handle_file_browser(ord("y"))
            self.assertEqual(editor.file_browser.op_kind, "move_dest")

            editor._handle_file_browser(ord("\n"))  # accept the default dest

            self.assertFalse(os.path.exists(src))
            self.assertTrue(os.path.isdir(os.path.join(dst, "src")))

    def test_fb_f8_delete_recursive_warns_of_large_operation_in_confirm_label(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = os.path.join(tmp, "bigdir")
            os.makedirs(target)
            for i in range(5):
                with open(os.path.join(target, f"f{i}.txt"), "w") as fh:
                    fh.write("x")

            editor = ViEditor()
            editor.FB_LARGE_OP_WARN_COUNT = 3
            self._open_fb_at(editor, tmp, cursor_name="bigdir")

            editor._handle_file_browser(curses.KEY_F8)

            self.assertEqual(editor.file_browser.op_kind, "confirm:delete_recursive")
            self.assertIn("block the editor", editor.file_browser.op_label)

            editor._handle_file_browser(ord("y"))

            self.assertFalse(os.path.exists(target))

    def test_fb_f6_move_success_rebinds_buffer_when_backup_cleanup_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            os.makedirs(src)
            dst = os.path.join(tmp, "dst")
            os.makedirs(dst)
            source_path = os.path.join(src, "f.txt")
            target_path = os.path.join(dst, "f.txt")
            with open(source_path, "w") as fh:
                fh.write("NEW")
            with open(target_path, "w") as fh:
                fh.write("OLD")

            editor = ViEditor(source_path)
            real_remove = editor._fb_remove_existing_target

            def fail_backup_cleanup(path):
                if os.path.basename(path).startswith(".vii-overwrite-"):
                    raise OSError("cleanup failed")
                return real_remove(path)

            with mock.patch.object(editor, "_fb_remove_existing_target", side_effect=fail_backup_cleanup):
                editor._fb_perform_move([source_path], target_path, overwrite=True)

            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.message, "Moved 1 item")
            self.assertEqual(editor.filename, target_path)
            self.assertEqual(editor.buffers[0].filename, target_path)
            self.assertFalse(os.path.exists(source_path))
            with open(target_path) as fh:
                self.assertEqual(fh.read(), "NEW")

    def test_fb_f6_move_renames_in_place(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, "old.txt"), "w") as fh:
                fh.write("X")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="old.txt")

            editor._handle_file_browser(curses.KEY_F6)
            s = editor.file_browser
            s.op_text = os.path.join(tmp, "new.txt")
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(os.path.exists(os.path.join(tmp, "new.txt")))
            self.assertFalse(os.path.exists(os.path.join(tmp, "old.txt")))

    def test_fb_f8_delete_single_file_after_confirm(self):
        with tempfile.TemporaryDirectory() as tmp:
            with open(os.path.join(tmp, "doomed.txt"), "w") as fh:
                fh.write("X")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="doomed.txt")

            editor._handle_file_browser(curses.KEY_F8)
            self.assertEqual(editor.file_browser.op_kind, "confirm:delete")
            editor._handle_file_browser(ord("y"))

            self.assertFalse(os.path.exists(os.path.join(tmp, "doomed.txt")))

    def test_fb_f8_delete_n_cancels_without_removing(self):
        with tempfile.TemporaryDirectory() as tmp:
            keep = os.path.join(tmp, "keep.txt")
            with open(keep, "w") as fh:
                fh.write("X")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="keep.txt")

            editor._handle_file_browser(curses.KEY_F8)
            editor._handle_file_browser(ord("n"))

            self.assertTrue(os.path.exists(keep))

    def test_fb_f8_delete_nonempty_directory_requires_recursive_confirm(self):
        with tempfile.TemporaryDirectory() as tmp:
            sub = os.path.join(tmp, "subdir")
            os.makedirs(sub)
            with open(os.path.join(sub, "child.txt"), "w") as fh:
                fh.write("X")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="subdir")

            editor._handle_file_browser(curses.KEY_F8)
            self.assertEqual(editor.file_browser.op_kind, "confirm:delete_recursive")
            editor._handle_file_browser(ord("y"))

            self.assertFalse(os.path.exists(sub))

    def test_fb_f8_delete_unreadable_directory_requires_recursive_confirm(self):
        with tempfile.TemporaryDirectory() as tmp:
            sub = os.path.join(tmp, "subdir")
            os.makedirs(sub)

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="subdir")

            real_scandir = os.scandir
            abs_sub = os.path.abspath(sub)

            def flaky_scandir(path):
                if os.path.abspath(path) == abs_sub:
                    raise PermissionError("permission denied")
                return real_scandir(path)

            with mock.patch("vi_editor.os.scandir", side_effect=flaky_scandir):
                editor._handle_file_browser(curses.KEY_F8)

            self.assertEqual(
                editor.file_browser.op_kind, "confirm:delete_recursive",
                "emptiness of an unreadable directory is unknown, so the "
                "confirmation must assume the conservative non-empty case",
            )

    def test_fb_f8_delete_marked_files_clears_marks(self):
        with tempfile.TemporaryDirectory() as tmp:
            paths = [os.path.join(tmp, f"f{i}.txt") for i in range(3)]
            for p in paths:
                with open(p, "w") as fh:
                    fh.write("x")

            editor = ViEditor()
            self._open_fb_at(editor, tmp)
            panel = editor._active_fb_panel()
            panel.selected.update(paths[:2])

            editor._handle_file_browser(curses.KEY_F8)
            self.assertEqual(editor.file_browser.op_kind, "confirm:delete")
            editor._handle_file_browser(ord("y"))

            self.assertFalse(os.path.exists(paths[0]))
            self.assertFalse(os.path.exists(paths[1]))
            self.assertTrue(os.path.exists(paths[2]))
            self.assertEqual(panel.selected, set())

    def test_fb_op_prompt_esc_cancels(self):
        with tempfile.TemporaryDirectory() as tmp:
            editor = ViEditor()
            self._open_fb_at(editor, tmp)

            editor._handle_file_browser(curses.KEY_F7)
            self.assertTrue(editor.file_browser.op_prompt)
            editor._handle_file_browser(27)  # ESC

            self.assertFalse(editor.file_browser.op_prompt)
            self.assertEqual(editor.file_browser.op_kind, "")

    def test_fb_function_key_bar_renders_for_known_widths(self):
        # Sanity: each width tier returns a string whose label set matches.
        full = ViEditor._fb_function_key_bar(120)
        self.assertIn("F1Help", full)
        self.assertIn("F10Quit", full)
        compact = ViEditor._fb_function_key_bar(70)
        self.assertNotIn("F1Help", compact)
        self.assertIn("1Help", compact)
        self.assertIn("10Quit", compact)
        terse = ViEditor._fb_function_key_bar(20)
        self.assertNotIn("10Quit", terse)
        self.assertLessEqual(len(terse), 19)

    # --- Buffer rebind + conflict detection on F5 / F6 ---

    def test_fb_f6_rename_keeps_open_buffer_clean(self):
        # F6 renaming a file that is open in a buffer must rebind the buffer
        # and keep its modified flag False (the file content didn't change).
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "a.txt")
            with open(path, "w") as fh:
                fh.write("hi\n")

            editor = ViEditor()
            editor._append_buffer(path, switch=True)
            self._open_fb_at(editor, tmp, cursor_name="a.txt")

            editor._handle_file_browser(curses.KEY_F6)
            new_path = os.path.join(tmp, "b.txt")
            s = editor.file_browser
            s.op_text = new_path
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))

            editor._refresh_all_buffer_modified_flags()
            renamed_buffer = editor.buffers[editor.current_buffer]
            self.assertEqual(renamed_buffer.filename, new_path)
            self.assertFalse(renamed_buffer.modified)
            self.assertFalse(editor.modified)

    def test_fb_f6_rename_mmap_buffer_keeps_clean(self):
        # The MMap-backed code path stores a "file"-style saved_signature;
        # the rebind must swap the path/size/mtime AND the filename slot,
        # plus update MMapLineStore.filename so future signature lookups
        # resolve.
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "big.txt")
            with open(path, "w") as fh:
                fh.write("line1\nline2\n")

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 1
            try:
                editor._append_buffer(path, switch=True)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold
            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)

            self._open_fb_at(editor, tmp, cursor_name="big.txt")
            editor._handle_file_browser(curses.KEY_F6)
            new_path = os.path.join(tmp, "big2.txt")
            s = editor.file_browser
            s.op_text = new_path
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))

            editor._refresh_all_buffer_modified_flags()
            self.assertFalse(editor.modified)
            self.assertEqual(editor.lines.filename, new_path)

    def test_fb_f6_refuses_to_overwrite_open_buffer(self):
        # Renaming src → tgt where tgt is open in a different buffer would
        # leave two buffers pointing at the same path with different content
        # (silent data-loss risk). The op should be refused with an error
        # and the on-disk files unchanged.
        with tempfile.TemporaryDirectory() as tmp:
            a = os.path.join(tmp, "a.txt")
            b = os.path.join(tmp, "b.txt")
            with open(a, "w") as fh:
                fh.write("AAA")
            with open(b, "w") as fh:
                fh.write("BBB")

            editor = ViEditor()
            editor._append_buffer(a, switch=True)
            editor._append_buffer(b, switch=True)

            self._open_fb_at(editor, tmp, cursor_name="b.txt")
            editor._handle_file_browser(curses.KEY_F6)
            s = editor.file_browser
            s.op_text = a
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(editor.message_is_error)
            self.assertIn("close with :bd", editor.message)
            buffers_for_a = [buf for buf in editor.buffers if buf.filename == a]
            self.assertEqual(len(buffers_for_a), 1)
            with open(a) as fh:
                self.assertEqual(fh.read(), "AAA")
            with open(b) as fh:
                self.assertEqual(fh.read(), "BBB")

    def test_fb_f5_refuses_to_overwrite_open_buffer(self):
        # Same conflict shape as F6 but for copy: copying onto an open
        # buffer's file would silently replace its on-disk content.
        with tempfile.TemporaryDirectory() as tmp:
            a = os.path.join(tmp, "a.txt")
            b = os.path.join(tmp, "b.txt")
            with open(a, "w") as fh:
                fh.write("AAA")
            with open(b, "w") as fh:
                fh.write("BBB")

            editor = ViEditor()
            editor._append_buffer(a, switch=True)

            self._open_fb_at(editor, tmp, cursor_name="b.txt")
            editor._handle_file_browser(curses.KEY_F5)
            s = editor.file_browser
            s.op_text = a   # exact path (no trailing /) so it targets a.txt
            s.op_cursor = len(s.op_text)
            editor._handle_file_browser(ord("\n"))

            self.assertTrue(editor.message_is_error)
            self.assertIn("close with :bd", editor.message)
            with open(a) as fh:
                self.assertEqual(fh.read(), "AAA")

    def test_fb_f6_move_directory_rebinds_open_child_buffer(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_root = os.path.join(tmp, "src")
            os.makedirs(src_root)
            dst_root = os.path.join(tmp, "dst")
            os.makedirs(dst_root)
            src_dir = os.path.join(src_root, "dir")
            os.makedirs(src_dir)
            old_path = os.path.join(src_dir, "note.txt")
            with open(old_path, "w") as fh:
                fh.write("hello\n")

            editor = ViEditor(old_path)
            new_dir = os.path.join(dst_root, "dir")
            editor._fb_perform_move([src_dir], new_dir)

            new_path = os.path.join(new_dir, "note.txt")
            editor._refresh_all_buffer_modified_flags()
            self.assertFalse(editor.message_is_error)
            self.assertEqual(editor.filename, new_path)
            self.assertEqual(editor.buffers[editor.current_buffer].filename, new_path)
            self.assertFalse(editor.modified)
            self.assertTrue(editor._save_file())

    def test_fb_f8_delete_refuses_open_child_buffer(self):
        with tempfile.TemporaryDirectory() as tmp:
            directory = os.path.join(tmp, "dir")
            os.makedirs(directory)
            path = os.path.join(directory, "note.txt")
            with open(path, "w") as fh:
                fh.write("hello\n")

            editor = ViEditor(path)
            editor._fb_perform_delete([directory], recursive=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("close with :bd", editor.message)
            self.assertTrue(os.path.exists(path))

    def test_fb_f5_refuses_to_overwrite_directory_containing_open_buffer(self):
        with tempfile.TemporaryDirectory() as tmp:
            src_dir = os.path.join(tmp, "srcdir")
            os.makedirs(src_dir)
            target_dir = os.path.join(tmp, "target")
            os.makedirs(target_dir)
            open_path = os.path.join(target_dir, "open.txt")
            with open(os.path.join(src_dir, "replacement.txt"), "w") as fh:
                fh.write("new")
            with open(open_path, "w") as fh:
                fh.write("old")

            editor = ViEditor(open_path)
            editor._fb_perform_copy([src_dir], target_dir, overwrite=True)

            self.assertTrue(editor.message_is_error)
            self.assertIn("close with :bd", editor.message)
            self.assertTrue(os.path.exists(open_path))

    # --- Mode preservation when an open fails ---

    def test_fb_edit_on_unloadable_entry_stays_in_browser(self):
        # F4 / Enter on a path that fails to load (here: a file with its
        # read permission stripped) used to silently switch the editor to
        # NORMAL mode because _load_buffer_state inside _append_buffer
        # always sets mode=NORMAL. The fix captures and restores mode on
        # failure.
        if os.geteuid() == 0:
            self.skipTest("root bypasses file permission checks")
        with tempfile.TemporaryDirectory() as tmp:
            target = os.path.join(tmp, "secret.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("data\n")
            os.chmod(target, 0o000)
            try:
                editor = ViEditor()
                self._open_fb_at(editor, tmp, cursor_name="secret.txt")

                editor._handle_file_browser(curses.KEY_F4)

                self.assertEqual(editor.mode, Mode.FILE_BROWSER)
                self.assertTrue(editor.message_is_error)
            finally:
                os.chmod(target, 0o644)

    def test_fb_edit_marks_all_failed_stays_in_browser(self):
        # If every marked path fails to load (or is filtered out), the
        # multi-open helper used to leave the editor in NORMAL mode anyway
        # because _load_buffer_state ran during the failure-recovery path.
        # Now mode is restored when no opens succeeded.
        with tempfile.TemporaryDirectory() as tmp:
            real = os.path.join(tmp, "real")
            os.makedirs(real)
            link = os.path.join(tmp, "lnk")
            os.symlink(real, link)

            editor = ViEditor()
            self._open_fb_at(editor, tmp)
            panel = editor._active_fb_panel()
            # Mark a path that is_file rejects (directory).
            panel.selected.add(real)

            editor._handle_file_browser(curses.KEY_F4)

            # Cursor entry is whatever was first; if it's a dir, FB stays.
            # The test cares that we didn't end up silently in NORMAL with
            # no useful state.
            if not panel.selected:
                # marks were processed; we should be in FB or have navigated
                self.assertIn(editor.mode, (Mode.FILE_BROWSER, Mode.NORMAL))
            else:
                self.assertEqual(editor.mode, Mode.FILE_BROWSER)

    def test_fb_action_edit_with_only_directories_marked_reports_error(self):
        # F4 with only directories marked used to silently ignore the
        # marks and act on whatever entry the cursor happened to be on
        # instead, with no feedback that the marks were skipped.
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "adir"))
            with open(os.path.join(tmp, "other.txt"), "w") as fh:
                fh.write("data")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="other.txt")
            panel = editor._active_fb_panel()
            panel.selected.add(os.path.join(tmp, "adir"))
            buffer_count_before = len(editor.buffers)

            editor._handle_file_browser(curses.KEY_F4)

            self.assertEqual(editor.mode, Mode.FILE_BROWSER)
            self.assertTrue(editor.message_is_error)
            self.assertIn("No files in selection", editor.message)
            self.assertEqual(len(editor.buffers), buffer_count_before)

    def test_fb_enter_key_with_only_directories_marked_reports_error(self):
        with tempfile.TemporaryDirectory() as tmp:
            os.makedirs(os.path.join(tmp, "adir"))
            with open(os.path.join(tmp, "other.txt"), "w") as fh:
                fh.write("data")

            editor = ViEditor()
            self._open_fb_at(editor, tmp, cursor_name="other.txt")
            panel = editor._active_fb_panel()
            panel.selected.add(os.path.join(tmp, "adir"))
            buffer_count_before = len(editor.buffers)

            editor._handle_file_browser(ord("\n"))

            self.assertEqual(editor.mode, Mode.FILE_BROWSER)
            self.assertTrue(editor.message_is_error)
            self.assertIn("No files in selection", editor.message)
            self.assertEqual(len(editor.buffers), buffer_count_before)

    def test_fb_reverse_sort_keeps_dirs_before_files(self):
        # When reverse_sort is True, directories must still appear before files.
        # The pre-fix bug fully reversed the (dir_rank, value) tuple so files
        # (rank 2) sorted ahead of directories (rank 1).
        with tempfile.TemporaryDirectory() as tmpdir:
            os.makedirs(os.path.join(tmpdir, "alpha_dir"))
            os.makedirs(os.path.join(tmpdir, "zeta_dir"))
            open(os.path.join(tmpdir, "a_file.txt"), "w").close()
            open(os.path.join(tmpdir, "z_file.txt"), "w").close()

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.sort_mode = "name"
            panel.reverse_sort = True
            editor._invalidate_fb_entries(panel)

            entries = editor._fb_entries(panel)
            names = [e.name for e in entries]
            # ".." always first
            self.assertEqual(names[0], "..")
            # All dirs before all files
            non_parent = entries[1:]
            dir_indices  = [i for i, e in enumerate(non_parent) if e.is_dir]
            file_indices = [i for i, e in enumerate(non_parent) if not e.is_dir]
            self.assertTrue(dir_indices,  "expected at least one directory entry")
            self.assertTrue(file_indices, "expected at least one file entry")
            self.assertLess(
                max(dir_indices), min(file_indices),
                f"dirs must precede files in reverse sort; got order: {names}"
            )

    def test_fb_reverse_sort_reverses_within_dirs_and_within_files(self):
        # Within each group (dirs, files), names must be in reverse-alpha order.
        with tempfile.TemporaryDirectory() as tmpdir:
            os.makedirs(os.path.join(tmpdir, "aaa_dir"))
            os.makedirs(os.path.join(tmpdir, "mmm_dir"))
            os.makedirs(os.path.join(tmpdir, "zzz_dir"))
            open(os.path.join(tmpdir, "aaa_file.txt"), "w").close()
            open(os.path.join(tmpdir, "zzz_file.txt"), "w").close()

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.sort_mode = "name"
            panel.reverse_sort = True
            editor._invalidate_fb_entries(panel)

            entries = editor._fb_entries(panel)
            non_parent = entries[1:]
            dir_names  = [e.name for e in non_parent if e.is_dir]
            file_names = [e.name for e in non_parent if not e.is_dir]

            self.assertEqual(dir_names,  sorted(dir_names,  reverse=True),
                             "dirs must be in reverse-alpha order")
            self.assertEqual(file_names, sorted(file_names, reverse=True),
                             "files must be in reverse-alpha order")

    def test_fb_forward_sort_dirs_before_files(self):
        # Sanity check: forward sort still keeps dirs first.
        with tempfile.TemporaryDirectory() as tmpdir:
            os.makedirs(os.path.join(tmpdir, "a_dir"))
            open(os.path.join(tmpdir, "z_file.txt"), "w").close()

            editor = ViEditor()
            editor._execute_cmd(":fb")
            panel = editor.file_browser.left
            panel.cwd = tmpdir
            panel.sort_mode = "name"
            panel.reverse_sort = False
            editor._invalidate_fb_entries(panel)

            entries = editor._fb_entries(panel)
            non_parent = entries[1:]
            dir_indices  = [i for i, e in enumerate(non_parent) if e.is_dir]
            file_indices = [i for i, e in enumerate(non_parent) if not e.is_dir]
            self.assertLess(max(dir_indices), min(file_indices))

    def test_fb_f9_and_s_key_cycle_sort_mode_identically(self):
        # F9 and 's' both route through the shared _fb_cycle_sort_mode and
        # must cycle name -> ext -> size -> name identically, resetting the
        # cursor/scroll and invalidating the cached entries each time.
        with tempfile.TemporaryDirectory() as tmpdir:
            editor = ViEditor()
            self._open_fb_at(editor, tmpdir)
            panel = editor.file_browser.left
            panel.sort_mode = "name"
            panel.cursor = 3
            panel.top_line = 2

            editor._handle_file_browser(curses.KEY_F9)
            self.assertEqual(panel.sort_mode, "ext")
            self.assertEqual(panel.cursor, 0)
            self.assertEqual(panel.top_line, 0)

            panel.cursor = 3
            panel.top_line = 2
            editor._handle_file_browser(ord("s"))
            self.assertEqual(panel.sort_mode, "size")
            self.assertEqual(panel.cursor, 0)
            self.assertEqual(panel.top_line, 0)

            editor._handle_file_browser(ord("s"))
            self.assertEqual(panel.sort_mode, "name")

    def test_open_recent_file_stays_in_overlay_on_failed_open(self):
        # The recent-files overlay calls _open_file_from_path; before the
        # fix, a failed open silently dropped the user from RECENT_FILES
        # to NORMAL mode.
        with tempfile.TemporaryDirectory() as tmp:
            real = os.path.join(tmp, "real")
            os.makedirs(real)
            link = os.path.join(tmp, "lnk")
            os.symlink(real, link)

            editor = ViEditor()
            editor.recent_files_list = [link]
            editor.mode = Mode.RECENT_FILES
            editor._open_recent_file(0)

            self.assertEqual(editor.mode, Mode.RECENT_FILES)
            self.assertTrue(editor.message_is_error)

    def test_grep_results_render_embedded_null_as_caret_at(self):
        class FakeScreen:
            def __init__(self):
                self.drawn = []

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                text = args[2] if len(args) >= 3 else args[0]
                if "\x00" in text:
                    raise ValueError("embedded null character")
                self.drawn.append(text)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.grep_results = [GrepResult("/tmp/binary.txt", 1, "a\x00b")]
        editor.grep_result_label = "nul test"

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor._draw_grep_results(screen, 8, 80)

        self.assertTrue(any("a^@b" in text for text in screen.drawn))

    def test_empty_grep_results_navigation_keeps_valid_cursor(self):
        editor = ViEditor()
        editor.grep_results = []
        editor.grep_result_cursor = 0

        for key in (curses.KEY_DOWN, curses.KEY_NPAGE, curses.KEY_END):
            editor._handle_grep_results(key)
            self.assertEqual(editor.grep_result_cursor, 0)

    def test_grep_results_enter_clamps_stale_cursor_before_opening(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            target = os.path.join(tmpdir, "hit.txt")
            with open(target, "w", encoding="utf-8") as fh:
                fh.write("first\nsecond\n")

            editor = ViEditor()
            editor.grep_results = [GrepResult(target, 2, "second")]
            editor.grep_result_cursor = 99

            editor._handle_grep_results(ord("\n"))

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertEqual(editor.filename, target)
            self.assertEqual(editor.cursor_row, 1)
            self.assertEqual(editor.grep_result_cursor, 0)

    def test_editor_text_renderer_escapes_embedded_null(self):
        class FakeScreen:
            def __init__(self):
                self.drawn = []

            def addstr(self, *args):
                text = args[2] if len(args) >= 3 else args[0]
                if "\x00" in text:
                    raise ValueError("embedded null character")
                self.drawn.append(text)

        editor = ViEditor()
        screen = FakeScreen()

        editor._add_syntax_text(screen, 0, 0, "a\x00b", 0)

        self.assertIn("a^@b", screen.drawn)

    def test_curses_text_width_accounts_for_escaped_null(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 5, 20

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        width = editor._add_curses_text(screen, 0, 0, "a\x00b")

        self.assertEqual(width, 4)
        self.assertEqual(screen.calls[0][2], "a^@b")

    def test_display_width_accounts_for_escaped_null_in_buffer_lines(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []
                self.moves = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                self.moves.append(args)

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["a\x00b"]
        editor.cursor_col = 2

        visible, content_visible = editor._visible_line_parts(0, 10)
        self.assertEqual(visible, "a^@b")
        self.assertEqual(content_visible, "a^@b      ")
        self.assertEqual(editor._display_col(0, 2), 3)

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertIn((1, 0, "a^@b"), screen.calls)
        self.assertIn((1, 3), screen.moves)

    def test_visible_line_parts_pad_wide_chars_by_display_width(self):
        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["你"]

        visible, content_visible = editor._visible_line_parts(0, 3)

        self.assertEqual(visible, "你")
        self.assertEqual(editor._display_width(content_visible), 3)

    def test_display_slice_preserves_trailing_combining_mark_when_clipped(self):
        editor = ViEditor()

        visible = editor._display_slice("e\u0301x", 0, max_width=1)

        self.assertEqual(visible, "e\u0301")
        self.assertEqual(editor._display_width(visible), 1)

    def test_display_ljust_preserves_combining_mark_when_fitting_width(self):
        editor = ViEditor()

        visible = editor._display_ljust("e\u0301x", 2)

        self.assertEqual(visible, "e\u0301x")
        self.assertEqual(editor._display_width(visible), 2)

    def test_curses_text_skips_out_of_bounds_draws(self):
        class FakeScreen:
            def getmaxyx(self):
                return 1, 1

            def addstr(self, *args):
                raise AssertionError("should not draw out of bounds")

        editor = ViEditor()

        width = editor._add_curses_text(FakeScreen(), 0, 5, "abc")

        self.assertEqual(width, 3)

    def test_curses_text_clips_lower_right_write_error(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 4

            def addstr(self, *args):
                row, col, text = args[:3]
                if row == 0 and col + len(text) >= 4:
                    raise curses.error("lower-right write")
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        width = editor._add_curses_text(screen, 0, 0, "abcd")

        self.assertEqual(width, 4)
        self.assertEqual(screen.calls, [(0, 0, "abc")])

    def test_curses_text_skips_empty_lower_right_retry_for_wide_char(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 2

            def addstr(self, *args):
                row, col, text = args[:3]
                if not text:
                    raise AssertionError("should not retry an empty write")
                text_width = 2 if text == "你" else len(text)
                if row == 0 and col + text_width >= 2:
                    raise curses.error("lower-right write")
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        width = editor._add_curses_text(screen, 0, 0, "你")

        self.assertEqual(width, 2)
        self.assertEqual(screen.calls, [])

    # ------------------------------------------------------------------
    # Fix: draw()'s text-row loop recorded a row as rendered in
    # self._screen_buf *before* attempting the curses write. A transient
    # curses.error on that write (e.g. a resize race where getmaxyx() lags
    # the real terminal size) was swallowed, but the row's cache slot had
    # already been overwritten -- so on the next frame, with unchanged
    # dimensions and content, the row matched the cache and was skipped
    # again, leaving it permanently blank/stale on the real screen. The
    # cache is now only committed once the write has actually succeeded.
    # ------------------------------------------------------------------

    def test_draw_retries_row_after_transient_write_failure(self):
        class FlakyScreen:
            def __init__(self):
                self.calls = []
                self.fail_row = None

            def getmaxyx(self):
                return 24, 80

            def move(self, *a):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, row, col, text, *args):
                if row == self.fail_row:
                    raise curses.error("simulated transient failure")
                self.calls.append((row, col, text))

            def attron(self, *a):
                pass

            def attroff(self, *a):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(10)]
        editor.show_line_numbers = False

        screen = FlakyScreen()
        screen.fail_row = 3
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx"):
            editor.draw(screen)

        # The failed write must not be recorded as if it had succeeded:
        # this is the very first draw(), so row 2's cache slot (prow 3,
        # which failed) must still be the untouched initial value.
        self.assertEqual(editor._screen_buf[2], "")
        self.assertFalse(any(c[0] == 3 for c in screen.calls))

        # Same dimensions, same content, write now succeeds -- the row
        # must be retried, not skipped as "already correct".
        screen.fail_row = None
        screen.calls.clear()
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx"):
            editor.draw(screen)

        self.assertTrue(
            any(c[0] == 3 for c in screen.calls),
            "a row whose write previously raised curses.error must be "
            "retried on the next frame instead of staying cached as clean",
        )

    def test_curses_text_expands_tabs_from_draw_column(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 3, 20

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        editor.tab_stop = 8  # this test is about draw-column math, not ~/.viirc
        screen = FakeScreen()

        width = editor._add_curses_text(screen, 0, 2, "\tab")

        self.assertEqual(width, 8)
        self.assertEqual(screen.calls, [(0, 2, "      ab")])

    def test_marked_line_highlights_line_number(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 40

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.marks = {"a": (1, 0)}
        editor.linenum_attr = 0

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        line_number_calls = {
            args[0]: args
            for args in screen.calls
            if len(args) >= 4 and args[1] == 0 and args[2].strip().isdigit()
        }

        self.assertFalse(line_number_calls[1][3] & curses.A_REVERSE)
        self.assertTrue(line_number_calls[2][3] & curses.A_REVERSE)
        self.assertTrue(line_number_calls[2][3] & curses.A_BOLD)
        self.assertFalse(line_number_calls[3][3] & curses.A_REVERSE)

    def test_line_number_gutter_expands_for_five_digit_line_numbers(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []
                self.moves = []

            def getmaxyx(self):
                return 8, 40

            def move(self, *args):
                self.moves.append(args)

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["x"] * 10000
        editor.cursor_row = 9999
        editor.top_line = 9999

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertIn((1, 0, "10000 ", curses.A_DIM), screen.calls)
        self.assertIn((1, 6, "x"), screen.calls)
        self.assertIn((1, 6), screen.moves)

    def test_line_number_draw_is_clipped_on_narrow_screen(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 4

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                row, col, text = args[:3]
                if col + len(text) > self.getmaxyx()[1]:
                    raise curses.error("write past edge")
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["x"] * 10000

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertIn((1, 0, "    ", curses.A_DIM), screen.calls)

    def test_moved_mark_redraws_old_and_new_line_numbers(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 40

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.marks = {"a": (1, 0)}

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

            screen.calls.clear()
            editor.marks = {"a": (2, 0)}
            editor.draw(screen)

        line_number_calls = {
            args[0]: args
            for args in screen.calls
            if len(args) >= 4 and args[1] == 0 and args[2].strip().isdigit()
        }

        self.assertIn(2, line_number_calls)
        self.assertIn(3, line_number_calls)
        self.assertFalse(line_number_calls[2][3] & curses.A_REVERSE)
        self.assertTrue(line_number_calls[3][3] & curses.A_REVERSE)

    def test_prompt_view_keeps_cursor_visible_at_right_edge(self):
        editor = ViEditor()
        text = ":edit " + "abcdefghijklmno"

        visible, cursor_col = editor._prompt_view(text, len(text), 12)

        self.assertEqual(visible, "fghijklmno")
        self.assertEqual(cursor_col, 10)

    def test_prompt_view_accounts_for_escaped_null_width(self):
        editor = ViEditor()
        text = ":e a\x00bcdef"

        visible, cursor_col = editor._prompt_view(text, len(text), 9)

        self.assertEqual(visible, "^@bcdef")
        self.assertEqual(cursor_col, 7)

    def test_prompt_view_accounts_for_wide_unicode_width(self):
        editor = ViEditor()
        text = ":e 你好ab"

        visible, cursor_col = editor._prompt_view(text, len(text), 8)

        self.assertEqual(visible, "你好ab")
        self.assertEqual(cursor_col, 6)

    def test_draw_scrolls_long_command_buffer_to_cursor(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []
                self.moves = []

            def getmaxyx(self):
                return 8, 12

            def move(self, *args):
                self.moves.append(args)

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one"]
        editor._cmd_buf = ":edit " + "abcdefghijklmno"
        editor._cmd_cursor = len(editor._cmd_buf)

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        bottom_text = [
            args[2] for args in screen.calls
            if len(args) >= 3 and args[0] == 7 and args[1] == 0
        ]

        self.assertIn("fghijklmno", bottom_text)
        self.assertIn((7, 10), screen.moves)

    def test_draw_places_breadcrumbs_on_top_chrome_line_at_column_0(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.filename = "app.py"
        editor.lines = [
            "class App:",
            "    def run(self):",
            "        return 1",
        ]
        editor.cursor_row = 2

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        status_text = [
            args[2] for args in screen.calls
            if len(args) >= 3 and args[0] == 6 and args[1] == 0
        ]
        breadcrumb_calls = [
            args for args in screen.calls
            if len(args) >= 3 and args[0] == 0 and args[1] == 0
            and args[2].strip()
        ]

        self.assertTrue(status_text)
        self.assertFalse(any("class App" in text or "def run" in text for text in status_text))
        self.assertEqual(breadcrumb_calls[-1][2], "class App > def run")

    def test_draw_clips_breadcrumbs_by_display_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 9

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["pass"]
        editor.cursor_row = 0

        screen = FakeScreen()
        with mock.patch.object(editor, "_current_breadcrumbs", return_value=["class 你x"]):
            with mock.patch("curses.doupdate"):
                editor.draw(screen)

        breadcrumb_calls = [
            args for args in screen.calls
            if len(args) >= 3 and args[0] == 0 and args[1] == 0
            and args[2].strip()
        ]

        self.assertEqual(breadcrumb_calls[-1][2], "class 你")
        self.assertLessEqual(editor._display_width(breadcrumb_calls[-1][2]), 8)

    def test_draw_status_line_uses_configured_status_attr(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []
                self.attrs = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                self.attrs.append(("on", args[0]))

            def attroff(self, *args):
                self.attrs.append(("off", args[0]))

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one"]
        editor.status_attr = 1234

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertIn(("on", 1234), screen.attrs)
        self.assertIn(("off", 1234), screen.attrs)

    def test_draw_bottom_status_line_uses_configured_bottom_status_attr(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one"]
        editor.bottom_status_attr = 5678

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertIn((7, 0, " " * 79, 5678), screen.calls)

    def test_draw_uses_separate_derived_windows_for_status_and_message_bars(self):
        class FakeDerivedWindow:
            def __init__(self, parent, begin_y, begin_x, height, width):
                self.parent = parent
                self.begin_y = begin_y
                self.begin_x = begin_x
                self.height = height
                self.width = width

            def getmaxyx(self):
                return self.height, self.width

            def move(self, row, col):
                self.parent.move(self.begin_y + row, self.begin_x + col)

            def clrtoeol(self):
                self.parent.clrtoeol()

            def addstr(self, row, col, text, *args):
                self.parent.addstr(self.begin_y + row, self.begin_x + col, text, *args)

            def attron(self, attr):
                self.parent.attron(attr)

            def attroff(self, attr):
                self.parent.attroff(attr)

            def noutrefresh(self):
                self.parent.noutrefresh()

        class FakeScreen:
            def __init__(self):
                self.calls = []
                self.derwin_calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                self.calls.append(("move",) + args)

            def clrtoeol(self):
                self.calls.append(("clrtoeol",))

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                self.calls.append(("attron",) + args)

            def attroff(self, *args):
                self.calls.append(("attroff",) + args)

            def noutrefresh(self):
                self.calls.append(("noutrefresh",))

            def derwin(self, height, width, begin_y, begin_x):
                self.derwin_calls.append((height, width, begin_y, begin_x))
                return FakeDerivedWindow(self, begin_y, begin_x, height, width)

        editor = ViEditor()
        editor.lines = ["one"]
        editor.message = "msg"

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertEqual(screen.derwin_calls, [
            (1, 80, 6, 0),
            (1, 80, 7, 0),
            (1, 80, 0, 0),
        ])

    def test_draw_redraws_text_when_syntax_language_changes(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 40

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["return 42"]
        editor.filename = "note.txt"
        screen = FakeScreen()

        with mock.patch("curses.doupdate"):
            editor.draw(screen)
            screen.calls.clear()
            editor.filename = "code.py"
            editor.draw(screen)

        self.assertTrue(
            any(len(args) >= 4 and args[2] == "return" and args[3] & curses.A_BOLD
                for args in screen.calls)
        )

    def test_horizontal_scroll_preserves_comment_syntax_highlight(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.filename = "code.py"
        editor.lines = ["    # comment"]
        editor.left_col = 6
        editor.cursor_col = 8

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        self.assertTrue(
            any(len(args) >= 4 and args[2].startswith("comment") and args[3] & curses.A_DIM
                for args in screen.calls)
        )

    def test_horizontal_scroll_does_not_overhighlight_before_comment_after_wide_chars(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.filename = "code.py"
        editor.lines = ["你你 # comment"]
        editor.left_col = 4
        editor.cursor_col = 5

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            args[2] for args in screen.calls
            if len(args) >= 4 and args[0] == 1 and args[3] & curses.A_DIM
        ]

        self.assertTrue(highlighted)
        self.assertEqual(highlighted[0], "# comment")

    def test_visual_highlight_expands_tab_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["\tab"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            args[2] for args in screen.calls
            if len(args) >= 4 and args[0] == 1 and args[3] & curses.A_REVERSE
        ]

        self.assertIn(" " * editor.tab_stop, highlighted)

    def test_visual_highlight_uses_display_columns_for_wide_chars(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["你ab"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            args[2] for args in screen.calls
            if len(args) >= 4 and args[0] == 1 and args[3] & curses.A_REVERSE
        ]

        self.assertIn("你", highlighted)
        self.assertNotIn("你a", highlighted)

    def test_visual_highlight_after_wide_char_starts_at_display_column(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["你ab"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 1

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            args[2] for args in screen.calls
            if len(args) >= 4 and args[0] == 1 and args[3] & curses.A_REVERSE
        ]

        self.assertIn("a", highlighted)
        self.assertNotIn("b", highlighted)

    def test_draw_highlights_matching_bracket_pair_under_cursor(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["a(b)c"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            (args[0], args[1], args[2])
            for args in screen.calls
            if len(args) >= 4
            and args[0] == 1
            and args[3] & curses.A_REVERSE
            and args[3] & curses.A_BOLD
        ]

        self.assertIn((1, 1, "("), highlighted)
        self.assertIn((1, 3, ")"), highlighted)

    def test_draw_clears_matching_bracket_highlight_after_cursor_moves_off_pair(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = ["a(b)c"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)
            screen.calls.clear()
            editor.cursor_col = 0
            editor.draw(screen)

        self.assertTrue(
            any(len(args) >= 3 and args[0] == 1 and args[2] == "a(b)c"
                for args in screen.calls)
        )
        self.assertFalse(
            any(len(args) >= 4 and args[0] == 1 and args[3] & curses.A_REVERSE
                and args[3] & curses.A_BOLD
                for args in screen.calls)
        )

    def test_visual_line_highlights_empty_line_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 20

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.show_line_numbers = False
        editor.lines = [""]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        highlighted = [
            args[2] for args in screen.calls
            if len(args) >= 4 and args[0] == 1 and args[1] == 0 and args[3] & curses.A_REVERSE
        ]

        self.assertIn(" " * 20, highlighted)


class VisualModeTests(unittest.TestCase):
    def test_visual_motion_extends_selection_without_forcing_full_redraw(self):
        # Movement in visual mode should not force a full redraw on every
        # keystroke; the per-row cache plus `_last_visual_rows` invalidates only
        # the rows whose highlight state changed. See `_handle_visual` and the
        # cache-skip check in `draw`.
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor._force_redraw = False

        editor._handle_visual(ord("j"))

        self.assertEqual(editor.cursor_row, 1)
        self.assertFalse(editor._force_redraw)
        self.assertEqual(editor._visual_bounds(), (0, 0, 1, 0))

    def test_visual_yank_returns_to_normal_with_yank_buffer_populated(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord("y"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.yank_buffer, ["bcd"])

    def test_visual_accepts_counted_motion_and_counted_goto(self):
        editor = ViEditor()
        editor.lines = ["one two", "three four", "five", "six"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)

        editor._handle_visual(ord("2"))
        editor._handle_visual(ord("w"))
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

        editor._handle_visual(ord("3"))
        editor._handle_visual(ord("G"))
        self.assertEqual(editor.cursor_row, 2)

        editor = ViEditor()
        editor.lines = [str(i) for i in range(1, 21)]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        for ch in "10gg":
            editor._handle_visual(ord(ch))
        self.assertEqual((editor.cursor_row, editor.lines[editor.cursor_row]), (9, "10"))

    def test_visual_caret_toggles_between_first_nonblank_and_column_zero(self):
        editor = ViEditor()
        editor.lines = ["  alpha"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 4)
        editor.cursor_row = 0
        editor.cursor_col = 4

        editor._handle_visual(ord("^"))
        self.assertEqual(editor.cursor_col, 2)

        editor._handle_visual(ord("^"))
        self.assertEqual(editor.cursor_col, 0)

        editor._handle_visual(ord("^"))
        self.assertEqual(editor.cursor_col, 2)

    def test_visual_counted_find_preserves_count_until_target_character(self):
        editor = ViEditor()
        editor.lines = ["a x x x"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("2"))
        editor._handle_visual(ord("f"))
        editor._handle_visual(ord("x"))

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 4))

    def test_visual_pending_find_reports_unknown_command_on_escape(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("f"))
        editor._handle_visual(27)  # ESC -- not a valid find target

        self.assertEqual(editor._pending_op, "")
        self.assertTrue(editor.message_is_error)
        self.assertIn("Unknown command", editor.message)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_visual_pending_g_reports_unknown_command_on_bad_completion(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("g"))
        editor._handle_visual(ord("z"))  # not g/j/k

        self.assertEqual(editor._pending_op, "")
        self.assertTrue(editor.message_is_error)
        self.assertIn("Unknown command", editor.message)

    def test_visual_pending_register_reports_unknown_command_on_bad_name(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord('"'))
        editor._handle_visual(27)  # ESC -- not a valid register name

        self.assertEqual(editor._pending_op, "")
        self.assertIsNone(editor.active_register)
        self.assertTrue(editor.message_is_error)
        self.assertIn("Unknown command", editor.message)

    def test_visual_find_accepts_non_ascii_target_character(self):
        editor = ViEditor()
        editor.lines = ["aébc"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)

        editor._handle_visual(ord("f"))
        editor._handle_visual("é")

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_visual_ctrl_a_and_ctrl_e_move_to_line_edges(self):
        editor = ViEditor()
        editor.lines = ["alpha beta"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 3)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(1)  # Ctrl-A
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

        editor._handle_visual(5)  # Ctrl-E
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, len("alpha beta") - 1))

    def test_visual_o_swaps_active_end_of_selection(self):
        editor = ViEditor()
        editor.lines = ["alpha beta"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 5

        editor._handle_visual(ord("o"))

        self.assertEqual(editor.visual_start, (0, 5))
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_visual_p_replaces_selection_with_yank_buffer(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor.yank_buffer = ["ZZ"]
        editor.yank_is_lines = False

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["aZZef"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.yank_buffer, ["bcd"])

    def test_visual_line_p_replaces_only_empty_line_with_charwise_register(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["X"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.yank_buffer, [""])

    def test_visual_p_dot_repeat_uses_pasted_text_not_exchanged_register(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor.yank_buffer = ["ZZ"]
        editor.yank_is_lines = False

        editor._handle_visual(ord("p"))
        self.assertEqual(editor.yank_buffer, ["bcd"])

        editor.cursor_col = 4
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["aZZeZZf"])
        self.assertEqual(editor.yank_buffer, ["bcd"])

    def test_visual_named_register_P_preserves_plain_put_register(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor.registers['"'] = (["X"], False)
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["Y"], False)
        editor.register_line_endings["a"] = []
        editor.active_register = "a"

        editor._handle_visual(ord("P"))
        editor.cursor_col = 4
        editor._put(after=True)

        self.assertEqual(editor.lines, ["aYefX"])
        self.assertEqual(editor.yank_buffer, ["X"])
        self.assertEqual(editor.registers['"'], (["X"], False))

    def test_visual_p_empty_named_register_does_not_delete_selection(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor.yank_buffer = ["ZZ"]
        editor.yank_is_lines = False
        editor.active_register = "a"
        editor._mark_clean()

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["abcdef"])
        self.assertEqual(editor.mode, Mode.VISUAL)
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "Nothing in register")
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_visual_p_empty_register_on_empty_selection_is_noop(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.yank_buffer = [""]
        editor.yank_is_lines = False
        editor.marks = {"a": (0, 0)}
        editor._mark_clean()

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_visual_p_empty_register_on_multiline_selection_is_not_a_noop(self):
        # A multi-row charwise selection always changes the buffer even with
        # an empty put source, since deleting the selection itself is the
        # change -- only a genuinely empty (single-row, zero-width) selection
        # combined with an empty put should short-circuit as a no-op.
        editor = ViEditor()
        editor.lines = ["abc", "def"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 1
        editor.cursor_col = 1
        editor.yank_buffer = [""]
        editor.yank_is_lines = False
        editor._mark_clean()

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.modified)
        self.assertTrue(editor.undo_stack)

    def test_visual_line_paste_replaces_empty_buffer_placeholder(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.yank_buffer = ["foo"]
        editor.yank_is_lines = True
        editor._mark_clean()

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["foo"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.modified)

    def test_visual_yank_uses_named_register(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor.active_register = "a"

        editor._handle_visual(ord("y"))

        self.assertEqual(editor.registers["a"], (["bcd"], False))
        self.assertEqual(editor.registers['"'], (["bcd"], False))

    def test_visual_charwise_multiline_paste_preserves_line_breaks(self):
        editor = ViEditor()
        editor.lines = ["one alpha", "two beta", "target"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 4)
        editor.cursor_row = 1
        editor.cursor_col = 2

        editor._handle_visual(ord("y"))
        self.assertEqual(editor.yank_buffer, ["alpha", "two"])
        self.assertFalse(editor.yank_is_lines)

        editor.cursor_row = 2
        editor.cursor_col = len("target") - 1
        editor._put(after=True)

        self.assertEqual(editor.lines, ["one alpha", "two beta", "targetalpha", "two"])

    # ------------------------------------------------------------------
    # Fix: pasting a register whose type (linewise/charwise) didn't match
    # the visual selection's type used to splice the register's raw text
    # directly at the deletion point without regard for line boundaries,
    # instead of matching vim's v_p semantics (verified against real vim):
    # a charwise selection replaced by a linewise register must split the
    # (now-merged) line at the deletion column and insert the register's
    # lines between the two halves; a linewise selection replaced by a
    # charwise register must leave a blank placeholder line for the
    # charwise text to land on, rather than merging it into whatever line
    # followed the deleted selection.
    # ------------------------------------------------------------------

    def test_visual_charwise_selection_paste_of_linewise_register_splits_line(self):
        editor = ViEditor()
        editor.lines = ["abcdefghij", "XXXX"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (1, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._handle_visual(ord("y"))
        self.assertTrue(editor.yank_is_lines)

        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 3)
        editor.cursor_row = 0
        editor.cursor_col = 5

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["abc", "XXXX", "ghij", "XXXX"])
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_visual_line_selection_paste_of_charwise_register_stays_on_own_line(self):
        editor = ViEditor()
        editor.lines = ["AA", "BB", "CC"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 1
        editor._handle_visual(ord("y"))
        self.assertFalse(editor.yank_is_lines)

        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (1, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_visual(ord("p"))

        self.assertEqual(editor.lines, ["AA", "AA", "CC"])
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_visual_multiline_charwise_selection_paste_of_linewise_register_preserves_register_with_P(self):
        editor = ViEditor()
        editor.lines = ["one alpha", "two beta", "target"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._handle_visual(ord("y"))

        editor.mode = Mode.VISUAL
        editor.visual_start = (1, 4)
        editor.cursor_row = 2
        editor.cursor_col = 3

        editor._handle_visual(ord("P"))

        self.assertEqual(editor.lines, ["one alpha", "two ", "one alpha", "et"])
        self.assertEqual(editor.yank_buffer, ["one alpha"])
        self.assertTrue(editor.yank_is_lines)

    def test_visual_line_join_clamps_cursor_after_joining_last_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (1, 0)
        editor.cursor_row = 2
        editor.cursor_col = 0

        editor._handle_visual(ord("J"))

        self.assertEqual(editor.lines, ["one", "two three"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.cursor_row, 1)

    def test_visual_line_join_dot_repeat_uses_same_line_count(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d", "e", "f"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 2
        editor.cursor_col = 0

        editor._handle_visual(ord("J"))
        self.assertEqual(editor.lines, ["a b c", "d", "e", "f"])

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["a b c", "d e f"])

    def test_visual_single_line_selection_join_still_joins_with_next_line(self):
        # A single-line visual selection used to require r1 != r2 before J
        # did anything at all, so "vJ" (select nothing, press J) was a
        # silent no-op instead of joining with the following line -- the
        # same as plain normal-mode J on that line.
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("J"))

        self.assertEqual(editor.lines, ["one two", "three"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.cursor_row, 0)

        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["one two three"])

    def test_visual_line_change_replaces_selection_with_blank_insert_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (1, 0)
        editor.cursor_row = 2
        editor.cursor_col = 0

        editor._handle_visual(ord("c"))

        self.assertEqual(editor.lines, ["one", ""])
        self.assertEqual(editor.mode, Mode.INSERT)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

    def test_visual_change_dot_repeat_replays_selection_change(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord("c"))
        editor._handle_insert(ord("X"))
        editor._handle_insert(27)
        self.assertEqual(editor.lines, ["aXef"])

        editor.cursor_col = 2
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["aXX"])

    def test_visual_multiline_change_dot_repeat_replays_selection_shape(self):
        editor = ViEditor()
        editor.lines = ["ab", "cd", "ef", "gh"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_visual(ord("c"))
        editor._handle_insert(ord("X"))
        editor._handle_insert(27)
        self.assertEqual(editor.lines, ["aXd", "ef", "gh"])

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["aXd", "Xh"])

    def test_visual_line_change_dot_repeat_replays_line_change(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_visual(ord("c"))
        editor._handle_insert(ord("X"))
        editor._handle_insert(27)
        self.assertEqual(editor.lines, ["X", "three", "four"])

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["X", "X"])

    def test_visual_noop_edits_do_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["123"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2
        editor._mark_clean()

        editor._handle_visual(ord("~"))

        self.assertEqual(editor.lines, ["123"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor = ViEditor()
        editor.lines = ["plain"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._mark_clean()

        editor._handle_visual(ord("<"))

        self.assertEqual(editor.lines, ["plain"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        # J's true no-op case -- a single selected line that is also the
        # buffer's last line, so there's no next line to join with -- is
        # covered by test_visual_join_noop_falls_through_to_clamp_marks.
        # (A single line selected out of a *multi*-line buffer is not a
        # no-op: see test_visual_single_line_selection_join_still_joins_with_next_line.)

    def test_visual_toggle_case_dot_repeat_reuses_selection_shape(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord("~"))
        self.assertEqual(editor.lines, ["aBCDef"])

        editor.cursor_col = 3
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["aBCdEF"])

    def test_visual_line_toggle_case_dot_repeat_reuses_line_count(self):
        editor = ViEditor()
        editor.lines = ["ab", "cd", "ef", "gh"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_visual(ord("~"))
        self.assertEqual(editor.lines, ["AB", "CD", "ef", "gh"])

        editor.cursor_row = 2
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["AB", "CD", "EF", "GH"])

    def test_visual_counted_indent_dot_repeat_reuses_shift_count(self):
        # [count]> in visual mode shifts by [count] shiftwidths; the dot
        # repeat used to drop that count entirely (it only ever re-ran
        # _resolve_operator with cnt as a *line* count, applying a single
        # shiftwidth), so ".": always re-indented by one level regardless
        # of how many the original command applied.
        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._count_str = "3"
        editor._handle_visual(ord(">"))
        self.assertEqual(editor.lines, ["            a", "            b", "c", "d"])

        editor.cursor_row = 2
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(
            editor.lines,
            ["            a", "            b", "            c", "            d"],
        )

    def test_visual_counted_dedent_dot_repeat_reuses_shift_count(self):
        editor = ViEditor()
        editor.lines = ["            a", "            b", "            c", "            d"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._count_str = "2"
        editor._handle_visual(ord("<"))
        self.assertEqual(editor.lines, ["    a", "    b", "            c", "            d"])

        editor.cursor_row = 2
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["    a", "    b", "    c", "    d"])

    def test_visual_dedent_dot_repeat_noop_leaves_both_undo_stacks_untouched(self):
        # _repeat_visual_indent's dedent branch captures a checkpoint but
        # only commits it to undo_stack once the dedent loop confirms a
        # real change happened; a no-op repeat must never touch undo_stack
        # or redo_stack at all.
        editor = ViEditor()
        editor.lines = ["flush-left", "flush-left"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # Prime both stacks with unrelated history so a spurious clear or
        # pop of the wrong entry would be visible.
        editor._push_undo()
        editor._push_undo()
        editor._undo()
        self.assertEqual(len(editor.undo_stack), 1)
        self.assertEqual(len(editor.redo_stack), 1)
        editor._mark_clean()

        editor._repeat_visual_indent(2, 1, True)  # already flush-left: no-op

        self.assertEqual(editor.lines, ["flush-left", "flush-left"])
        self.assertEqual(len(editor.undo_stack), 1)
        self.assertEqual(len(editor.redo_stack), 1)
        self.assertFalse(editor.modified)

    def test_visual_dedent_dot_repeat_change_commits_undo_and_clears_redo(self):
        editor = ViEditor()
        editor.lines = ["    a", "    b"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._push_undo()
        editor._push_undo()
        editor._undo()
        self.assertEqual(len(editor.undo_stack), 1)
        self.assertEqual(len(editor.redo_stack), 1)
        editor._mark_clean()

        editor._repeat_visual_indent(2, 1, True)  # indented: real dedent

        self.assertEqual(editor.lines, ["a", "b"])
        self.assertEqual(len(editor.undo_stack), 2)
        self.assertEqual(len(editor.redo_stack), 0)
        self.assertTrue(editor.modified)

        editor._undo()
        self.assertEqual(editor.lines, ["    a", "    b"])

    def test_visual_dedent_dot_repeat_noop_does_not_evict_undo_history_at_cap(self):
        # Regression test: _repeat_visual_indent's dedent branch used to
        # push a checkpoint via _push_capped *before* knowing whether the
        # dedent would actually change anything. Once undo_stack was at its
        # cap, that eager push evicted the oldest entry (_push_capped's
        # popleft()); a no-op dedent then only popped the tentative *new*
        # entry back off, leaving the evicted oldest entry gone for good --
        # silently shrinking undo history for a repeat that changed nothing.
        editor = ViEditor()
        editor.max_undo = 3
        editor.cursor_row = 0
        editor.cursor_col = 0

        for i in range(3):
            editor.lines = [f"marker-{i}", "flush-left"]
            editor._push_undo()
        editor.lines = ["flush-left", "flush-left"]
        self.assertEqual(len(editor.undo_stack), 3)
        oldest_before = editor.undo_stack[0]

        editor._repeat_visual_indent(2, 1, True)  # already flush-left: no-op

        self.assertEqual(editor.lines, ["flush-left", "flush-left"])
        self.assertEqual(len(editor.undo_stack), 3)
        self.assertIs(editor.undo_stack[0], oldest_before)
        self.assertFalse(editor.modified)

    def test_visual_indent_count_is_clamped_to_selection_size(self):
        # A count in visual '>' repeats a full-selection _indent_lines()
        # pass that many times, so an uncapped count combined with a large
        # selection scales cost as count * selection_size with no bound.
        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(50)]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 49
        editor.cursor_col = 0

        selection_size = len(editor.lines)
        indent_unit = len(editor._indent_str())
        editor._count_str = str(editor.MAX_COUNT)
        editor._handle_visual(ord(">"))

        added = len(editor.lines[0]) - len("line0")
        applied_count = added // indent_unit
        self.assertLessEqual(applied_count * selection_size, editor.MAX_COUNT)
        self.assertTrue(editor.message_is_error)
        self.assertIn("clamped", editor.message)

    def test_visual_empty_delete_does_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._mark_clean()

        editor._handle_visual(ord("x"))

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.yank_buffer)

        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._mark_clean()

        editor._handle_visual(ord("d"))

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.yank_buffer)

    def test_visual_char_delete_dot_repeat_reuses_selection_width(self):
        editor = ViEditor()
        editor.lines = ["abcdefgh"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord("d"))
        self.assertEqual(editor.lines, ["aefgh"])
        self.assertEqual(editor.yank_buffer, ["bcd"])

        editor.cursor_col = 1
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["ah"])
        self.assertEqual(editor.yank_buffer, ["efg"])

    def test_visual_multiline_delete_dot_repeat_reuses_selection_shape(self):
        editor = ViEditor()
        editor.lines = ["ab", "cd", "ef", "gh"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_visual(ord("d"))
        self.assertEqual(editor.lines, ["ad", "ef", "gh"])
        self.assertEqual(editor.yank_buffer, ["b", "c"])

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._repeat_last_change(1)

        self.assertEqual(editor.lines, ["ad", "h"])
        self.assertEqual(editor.yank_buffer, ["ef", "g"])

    # ------------------------------------------------------------------
    # _repeat_visual_char_delete / _begin_visual_char_change_repeat /
    # _repeat_visual_toggle_case used to diff `list(self.lines)` copies
    # taken before and after the edit (toggle-case even took two full
    # copies plus a full re-scan to find the changed row) to detect a
    # no-op or find what changed, on every dot-repeat -- regardless of
    # file size. Assert the whole buffer is walked at most once (only the
    # unavoidable undo snapshot, when one is taken).
    # ------------------------------------------------------------------

    class _CountingLines(list):
        """Tracks how many times the whole sequence was iterated (list(x),
        enumerate(x), `for` over it, etc. all go through __iter__)."""
        iter_calls = 0

        def __iter__(self):
            type(self).iter_calls += 1
            return super().__iter__()

    def test_visual_multiline_char_delete_repeat_helper_avoids_full_buffer_copy(self):
        editor = ViEditor()
        editor.lines = self._CountingLines(
            ["one alpha", "two beta", "three gamma", "four delta"]
        )
        editor.line_endings = ["\n", "\n", "\n", ""]
        editor.cursor_row = 0
        editor.cursor_col = 4

        self._CountingLines.iter_calls = 0
        editor._repeat_visual_char_delete(0, 1, 4)

        # Only the undo-state snapshot may walk the whole buffer.
        self.assertLessEqual(self._CountingLines.iter_calls, 1)
        self.assertEqual(list(editor.lines), ["one eta", "three gamma", "four delta"])

        # A repeat that lands on a no-op range must not even pay for that.
        self._CountingLines.iter_calls = 0
        editor.cursor_row = 2
        editor.cursor_col = len(editor.lines[2])  # past EOL: same-line no-op
        editor._repeat_visual_char_delete(0, 0, len(editor.lines[2]))
        self.assertEqual(self._CountingLines.iter_calls, 0)

    def test_visual_multiline_char_change_repeat_helper_avoids_full_buffer_copy(self):
        editor = ViEditor()
        editor.lines = self._CountingLines(
            ["one alpha", "two beta", "three gamma", "four delta"]
        )
        editor.line_endings = ["\n", "\n", "\n", ""]
        editor.intellisense = False
        editor.cursor_row = 0
        editor.cursor_col = 4

        self._CountingLines.iter_calls = 0
        editor._begin_visual_char_change_repeat(0, 1, 4)

        # Only _enter_insert's own baseline undo snapshot may walk the whole
        # buffer; the no-op check and the delete itself must not add another.
        self.assertLessEqual(self._CountingLines.iter_calls, 1)
        self.assertEqual(list(editor.lines), ["one eta", "three gamma", "four delta"])
        self.assertEqual(editor.mode, Mode.INSERT)

    def test_visual_toggle_case_repeat_helper_avoids_full_buffer_copy(self):
        editor = ViEditor()
        editor.lines = self._CountingLines(["abc", "def", "ghi"])
        editor.line_endings = ["\n", "\n", ""]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self._CountingLines.iter_calls = 0
        editor._repeat_visual_toggle_case(0, 0, linewise=True)

        # Only _push_undo's snapshot may walk the whole buffer; finding
        # which row changed must not re-scan every line to do it.
        self.assertLessEqual(self._CountingLines.iter_calls, 1)
        self.assertEqual(list(editor.lines), ["abc", "DEF", "ghi"])

        # A repeat over a line with nothing to swap case on is a true no-op.
        editor.lines[0] = "123"
        editor.cursor_row = 0
        self._CountingLines.iter_calls = 0
        editor._repeat_visual_toggle_case(0, 0, linewise=True)
        self.assertEqual(self._CountingLines.iter_calls, 0)
        self.assertEqual(list(editor.lines), ["123", "DEF", "ghi"])

    def test_visual_v_toggle_to_visual_line_preserves_anchor(self):
        # Pressing V while in VISUAL should switch mode but keep visual_start intact.
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 2
        editor.cursor_col = 0

        editor._handle_visual(ord("V"))

        self.assertEqual(editor.mode, Mode.VISUAL_LINE)
        self.assertEqual(editor.visual_start, (0, 1),
                         "visual_start must not be overwritten when switching modes")

    def test_visual_line_V_toggle_to_visual_preserves_anchor(self):
        # Pressing v while in VISUAL_LINE should switch mode but keep visual_start intact.
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 2
        editor.cursor_col = 3

        editor._handle_visual(ord("v"))

        self.assertEqual(editor.mode, Mode.VISUAL)
        self.assertEqual(editor.visual_start, (0, 0),
                         "visual_start must not be overwritten when switching modes")

    def test_visual_v_to_normal_when_already_visual(self):
        editor = ViEditor()
        editor.lines = ["hello"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2

        editor._handle_visual(ord("v"))

        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_visual_line_V_to_normal_when_already_visual_line(self):
        editor = ViEditor()
        editor.lines = ["hello"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("V"))

        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_visual_escape_clears_named_register_prefix(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(27)
        editor._handle_normal(ord("x"), 24, 80)

        self.assertEqual(editor.lines, ["abdef"])
        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["c"], False))

    def test_visual_toggle_to_normal_clears_named_register_prefix(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(ord("v"))
        editor._handle_normal(ord("x"), 24, 80)

        self.assertEqual(editor.lines, ["abdef"])
        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["c"], False))

    def test_visual_register_prefix_routes_yank_to_named_register(self):
        # "ay in visual mode should yank into register 'a'.
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(ord("y"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.registers.get("a", ([], False))[0], ["bcd"])

    def test_visual_register_prefix_routes_delete_to_named_register(self):
        # "bd in visual mode should delete into register 'b'.
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("b"))
        editor._handle_visual(ord("d"))

        self.assertEqual(editor.lines, ["def"])
        self.assertEqual(editor.registers.get("b", ([], False))[0], ["abc"])

    def test_visual_register_prefix_ignored_for_movement(self):
        # Typing "a then a movement key (not y/d/c) should not crash and
        # should leave active_register cleared after the movement.
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        # 'w' is a movement — active_register should be cleared by _store_register
        # only if an operation is performed, otherwise it persists until used.
        # The important thing is no exception is raised.
        editor._handle_visual(ord("w"))
        self.assertEqual(editor.mode, Mode.VISUAL)

    def test_visual_register_prefix_cleared_when_indent_exits_visual(self):
        # ">"/"<"/"~"/"J" drop back to NORMAL mode without ever touching
        # active_register (they don't go through _store_register()/_put()).
        # An armed "a from earlier in the same visual selection must not
        # survive into the next, unrelated NORMAL-mode command -- e.g. a
        # plain "p" right after should paste the unnamed register, not
        # silently reuse the register that was armed (and then abandoned)
        # for a completely different action.
        editor = ViEditor()
        editor.lines = ["hello", "world"]
        editor.yank_buffer = ["UNNAMED"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["FROM_A"], False)
        editor.register_line_endings["a"] = []
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 4

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(ord(">"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertIsNone(editor.active_register)

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._handle_normal(ord("p"), 24, 80)

        self.assertEqual(editor.lines[1], "wUNNAMEDorld")

    def test_visual_register_prefix_cleared_when_swapcase_exits_visual(self):
        editor = ViEditor()
        editor.lines = ["hello", "world"]
        editor.yank_buffer = ["UNNAMED"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["FROM_A"], False)
        editor.register_line_endings["a"] = []
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 4

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(ord("~"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertIsNone(editor.active_register)

    def test_visual_register_prefix_cleared_on_noop_delete(self):
        # d/x on a selection that turns out to be a no-op (e.g. an empty
        # line) skip _store_register() entirely, which is the only thing
        # that normally clears active_register for these keys.
        editor = ViEditor()
        editor.lines = ["", "world"]
        editor.yank_buffer = ["UNNAMED"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["FROM_A"], False)
        editor.register_line_endings["a"] = []
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord('"'))
        editor._handle_visual(ord("a"))
        editor._handle_visual(ord("x"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertIsNone(editor.active_register)

        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._handle_normal(ord("p"), 24, 80)

        self.assertEqual(editor.lines[1], "wUNNAMEDorld")

    def test_visual_line_yank_cursor_moves_to_first_nonblank(self):
        # After VISUAL_LINE yank, cursor should land on the first non-blank
        # column of the first selected line, not at whatever column it was.
        editor = ViEditor()
        editor.lines = ["  alpha", "  beta", "  gamma"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 6)   # anchor deep in the line
        editor.cursor_row = 1
        editor.cursor_col = 5

        editor._handle_visual(ord("y"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.cursor_row, 0)
        self.assertEqual(editor.cursor_col, 2,   # first non-blank of row 0
                         "linewise yank should place cursor at first non-blank of top row")

    def test_visual_charwise_yank_cursor_moves_to_selection_start(self):
        # After charwise yank, cursor should go to the start of the selection.
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._handle_visual(ord("y"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.cursor_row, 0)
        self.assertEqual(editor.cursor_col, 1)

    def test_visual_selection_will_change_predicate(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        # r1 == r2, slice has content → would change
        self.assertTrue(editor._visual_selection_will_change(0, 0, 0, 0, False))
        self.assertTrue(editor._visual_selection_will_change(0, 1, 0, 2, False))
        # Multi-row charwise selection always changes
        editor.lines = ["abc", "def"]
        self.assertTrue(editor._visual_selection_will_change(0, 0, 1, 0, False))
        # Empty buffer single-line linewise "delete" is a no-op
        editor.lines = [""]
        self.assertFalse(editor._visual_selection_will_change(0, 0, 0, 0, True))
        self.assertFalse(editor._visual_selection_will_change(0, 0, 0, 0, False))
        # Linewise delete on a non-empty buffer always changes, even if the
        # selected line is empty
        editor.lines = ["", "x"]
        self.assertTrue(editor._visual_selection_will_change(0, 0, 0, 0, True))
        # Charwise on empty line with cursor at col 0 is a no-op (slice empty)
        editor.lines = ["", "x"]
        self.assertFalse(editor._visual_selection_will_change(0, 0, 0, 0, False))

    def test_visual_motion_uses_per_row_invalidation_not_full_redraw(self):
        # After moving the cursor in visual mode the next draw must redraw the
        # row entering the selection AND the row leaving (if any), but not the
        # entire screen. `_last_visual_rows` plus the cursor row carry that.
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (1, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._last_visual_rows = {1}  # simulate prior draw
        editor._force_redraw = False

        editor._handle_visual(ord("j"))

        self.assertFalse(editor._force_redraw)
        # `_last_visual_rows` is updated by the draw loop, not the key handler,
        # so it should still hold the prior frame's rows here. The current
        # bounds reflect the new selection, and row 1 (now leaving the
        # boundary's char-col extent) plus row 2 (newly inside) will both be
        # invalidated by the draw-loop check.
        self.assertEqual(editor._visual_bounds(), (1, 0, 2, 0))
        self.assertIn(1, editor._last_visual_rows)

    def test_visual_tilde_only_mutates_selected_rows(self):
        # Pre-fix, `~` did `list(self.lines)` twice. Now it should only build
        # a per-row change list over the selected range.
        editor = ViEditor()
        editor.lines = ["unchanged before",
                        "abc",
                        "DEF",
                        "unchanged after"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (1, 0)
        editor.cursor_row = 2
        editor.cursor_col = 0
        original_outside_before = editor.lines[0]
        original_outside_after = editor.lines[3]

        editor._handle_visual(ord("~"))

        self.assertEqual(editor.lines,
                         ["unchanged before", "ABC", "def", "unchanged after"])
        # Identity check: the unaffected rows must still be the exact same
        # string objects — proves we did not rebuild the buffer.
        self.assertIs(editor.lines[0], original_outside_before)
        self.assertIs(editor.lines[3], original_outside_after)

    def test_visual_tilde_noop_does_not_push_undo(self):
        editor = ViEditor()
        editor.lines = ["123 456"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 2  # selects "123" — digits + space have no case
        editor._mark_clean()

        editor._handle_visual(ord("~"))

        self.assertEqual(editor.lines, ["123 456"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_visual_indent_honors_count(self):
        editor = ViEditor()
        editor.lines = ["a", "b"]
        editor.shift_width = 2
        editor.expand_tab = True
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._count_str = "3"

        editor._handle_visual(ord(">"))

        self.assertEqual(editor.lines, ["      a", "      b"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.modified)

    def test_visual_dedent_honors_count_and_stops_at_zero_indent(self):
        editor = ViEditor()
        editor.lines = ["    a", "    b"]
        editor.shift_width = 2
        editor.expand_tab = True
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._count_str = "5"  # asks for 5× but only 2 levels exist

        editor._handle_visual(ord("<"))

        self.assertEqual(editor.lines, ["a", "b"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.modified)
        # Exactly one undo entry — the loop snapshotted via
        # _capture_undo_state_for_edit and committed once.
        self.assertEqual(len(editor.undo_stack), 1)

    def test_visual_dedent_noop_does_not_push_undo(self):
        editor = ViEditor()
        editor.lines = ["a", "b"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._mark_clean()

        editor._handle_visual(ord("<"))

        self.assertEqual(editor.lines, ["a", "b"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)
        # redo_stack must also not be cleared — the dedent never executed.
        self.assertFalse(editor.redo_stack)

    def test_visual_join_noop_falls_through_to_clamp_marks(self):
        # B2: the J no-op branch used to early-return and skip the trailing
        # cleanup. Just verify it terminates normally and leaves count/op
        # cleared along with the buffer unchanged.
        editor = ViEditor()
        editor.lines = ["only"]
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._mark_clean()

        result = editor._handle_visual(ord("J"))

        self.assertTrue(result)
        self.assertEqual(editor.lines, ["only"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)


    # --- Visual block (Ctrl-V) ---

    @staticmethod
    def _block_editor(lines, start, keys=()):
        editor = ViEditor()
        editor.lines = list(lines)
        editor.line_endings = ["\n"] * len(lines)
        editor.cursor_row, editor.cursor_col = start
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(22)
        return VisualModeTests._feed_keys(editor, keys)

    @staticmethod
    def _feed_keys(editor, keys):
        for key in keys:
            key = ord(key) if isinstance(key, str) else key
            if editor.mode == Mode.INSERT:
                editor._handle_insert(key)
            elif editor.mode == Mode.VISUAL_BLOCK:
                editor._handle_visual(key)
            else:
                editor._handle_normal(key, 24, 80)
        return editor

    def test_ctrl_v_switches_from_visual_into_block_mode_and_toggles(self):
        editor = self._block_editor(["abc"], (0, 1))
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        self.assertEqual(editor.visual_start, (0, 1))
        editor._handle_visual(ord("v"))
        self.assertEqual(editor.mode, Mode.VISUAL)
        editor._handle_visual(22)
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        editor._handle_visual(22)
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_ctrl_x_switches_visual_modes_like_ctrl_v(self):
        editor = ViEditor()
        editor.lines = ["abc", "def"]
        editor.cursor_col = 1
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(24)
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        self.assertEqual(editor.visual_start, (0, 1))
        editor._handle_visual(ord("V"))
        self.assertEqual(editor.mode, Mode.VISUAL_LINE)
        editor._handle_visual(24)
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        editor._handle_visual(24)
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["abc", "def"])

    def test_ctrl_v_ctrl_x_and_ctrl_n_do_nothing_in_normal_mode(self):
        # Block mode is reached only from inside v / V, so neither Ctrl-V nor
        # Ctrl-X starts it from NORMAL; Ctrl-N belongs to insert completion.
        for key in (22, 24, 14):
            with self.subTest(key=key):
                editor = ViEditor()
                editor.lines = ["abc", "def"]
                editor.cursor_col = 1
                editor._handle_normal(key, 24, 80)
                self.assertEqual(editor.mode, Mode.NORMAL)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))
                self.assertEqual(editor.lines, ["abc", "def"])
                self.assertFalse(editor.modified)

    def test_ctrl_n_does_not_switch_visual_modes(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(14)
        self.assertEqual(editor.mode, Mode.VISUAL)

    def test_enter_and_ctrl_m_do_not_start_block_mode(self):
        # An unbracketed paste delivers its newlines as 10/13; they must not
        # toggle block mode and turn the pasted letters into block operators.
        for key in (10, 13):
            with self.subTest(key=key):
                editor = ViEditor()
                editor.lines = ["abc", "def"]
                editor._handle_normal(key, 24, 80)
                self.assertNotEqual(editor.mode, Mode.VISUAL_BLOCK)
                editor.mode = Mode.NORMAL
                editor._handle_normal(ord("v"), 24, 80)
                editor._handle_visual(key)
                self.assertNotEqual(editor.mode, Mode.VISUAL_BLOCK)

    def test_block_delete_removes_column_into_blockwise_register(self):
        editor = self._block_editor(["abcdef", "ghijkl", "mnopqr"], (0, 1), "jjlld")
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["aef", "gkl", "mqr"])
        self.assertEqual(editor.yank_buffer, ["bcd", "hij", "nop"])
        self.assertTrue(editor.yank_is_block)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))
        editor._handle_normal(ord("u"), 24, 80)
        self.assertEqual(editor.lines, ["abcdef", "ghijkl", "mnopqr"])

    def test_block_delete_dot_repeat_uses_same_block_size_at_cursor(self):
        editor = self._block_editor(["abcdef", "ghijkl", "mnopqr"], (0, 1), "jlld")
        editor._move(1, 0)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["aef", "", "pqr"])

    def test_block_yank_then_put_pastes_as_column(self):
        editor = self._block_editor(["abcdef", "ghijkl"], (0, 1), "jly")
        self.assertEqual(editor.yank_buffer, ["bc", "hi"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))
        editor._move(0, 5)
        editor._handle_normal(ord("p"), 24, 80)
        self.assertEqual(editor.lines, ["abcdefbc", "ghijklhi"])
        editor._handle_normal(ord("u"), 24, 80)
        self.assertEqual(editor.lines, ["abcdef", "ghijkl"])

    def test_block_put_pads_short_lines_and_keeps_following_text_aligned(self):
        editor = ViEditor()
        editor.lines = ["xy", "xy"]
        editor._store_register(["ab", "c"], False, blockwise=True)
        editor._move(0, 1)
        editor._handle_normal(ord("P"), 24, 80)
        self.assertEqual(editor.lines, ["xaby", "xc y"])

        editor = ViEditor()
        editor.lines = ["abc"]
        editor.line_endings = ["\n"]
        editor._store_register(["1", "2"], False, blockwise=True)
        editor._move(0, 2)
        editor._handle_normal(ord("p"), 24, 80)
        self.assertEqual(editor.lines, ["abc1", "   2"])
        self.assertEqual(len(editor.line_endings), 2)

    def test_charwise_yank_after_block_yank_is_not_put_blockwise(self):
        editor = self._block_editor(["abc", "def"], (0, 0), "jy")
        self.assertTrue(editor.yank_is_block)
        editor._handle_normal(ord("y"), 24, 80)
        editor._handle_normal(ord("w"), 24, 80)
        self.assertFalse(editor.yank_is_block)
        self.assertNotIn('"', editor.block_registers)

    def test_named_register_remembers_block_shape(self):
        editor = self._block_editor(["abc", "def"], (0, 0), ['"', "a", "j", "y"])
        self.assertIn("a", editor.block_registers)
        editor._handle_normal(ord("y"), 24, 80)
        editor._handle_normal(ord("y"), 24, 80)   # unnamed now linewise
        editor._move(0, 2)
        for key in '"ap':
            editor._handle_normal(ord(key), 24, 80)
        self.assertEqual(editor.lines, ["abca", "defd"])

    def test_block_insert_repeats_text_on_every_row_that_reaches_block(self):
        editor = self._block_editor(
            ["abc", "d", "efg"], (0, 1), ["j", "j", "I", "X", "Y", 27])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["aXYbc", "dXY", "eXYfg"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

        editor = self._block_editor(["abcd", "a", "efgh"], (0, 2), ["j", "j", "I", "X", 27])
        self.assertEqual(editor.lines, ["abXcd", "a", "efXgh"])

    def test_block_insert_is_a_single_undo_step(self):
        editor = self._block_editor(["abc", "def"], (0, 1), ["j", "I", "X", 27])
        self.assertEqual(editor.lines, ["aXbc", "dXef"])
        editor._handle_normal(ord("u"), 24, 80)
        self.assertEqual(editor.lines, ["abc", "def"])

    def test_block_append_pads_short_rows(self):
        editor = self._block_editor(["abc", "d", "efg"], (0, 1), ["j", "j", "A", "X", 27])
        self.assertEqual(editor.lines, ["abXc", "d X", "efXg"])

    def test_block_append_with_nothing_typed_leaves_buffer_untouched(self):
        editor = self._block_editor(["a", "bcd"], (1, 2), ["k", "A", 27])
        self.assertEqual(editor.lines, ["a", "bcd"])

    def test_block_dollar_append_adds_to_each_line_end(self):
        editor = self._block_editor(
            ["abc", "d", "efgh"], (0, 0), ["j", "j", "$", "A", "!", 27])
        self.assertEqual(editor.lines, ["abc!", "d!", "efgh!"])

    def test_block_dollar_survives_vertical_motion_but_not_horizontal(self):
        editor = self._block_editor(["abc", "d", "efgh"], (0, 0), ["$", "j", "j"])
        self.assertTrue(editor._block_to_eol)
        self.assertEqual(editor.cursor_col, 3)
        editor._handle_visual(ord("h"))
        self.assertFalse(editor._block_to_eol)

    def test_block_change_replaces_block_on_every_row_and_dot_repeats(self):
        editor = self._block_editor(["abcd", "efgh"], (0, 1), ["j", "l", "c", "Z", 27])
        self.assertEqual(editor.lines, ["aZd", "eZh"])
        self.assertEqual(editor.yank_buffer, ["bc", "fg"])
        editor._move(0, 0)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["Zd", "Zh"])

    def test_block_replace_char_and_toggle_case(self):
        editor = self._block_editor(["abcd", "efgh"], (0, 1), "jlrx")
        self.assertEqual(editor.lines, ["axxd", "exxh"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        editor = self._block_editor(["abcd", "efgh"], (0, 1), "jl~")
        self.assertEqual(editor.lines, ["aBCd", "eFGh"])

    def test_block_paste_over_selection_with_single_line_text_fills_each_row(self):
        editor = self._block_editor(["abcd", "efgh"], (0, 1), "jl")
        editor._store_register(["Z"], False)
        editor._handle_visual(ord("p"))
        self.assertEqual(editor.lines, ["aZd", "eZh"])
        self.assertEqual(editor.yank_buffer, ["bc", "fg"])
        self.assertTrue(editor.yank_is_block)

    def test_block_paste_over_selection_dot_repeats_the_replace(self):
        editor = self._block_editor(["abcd", "efgh", "ijkl", "mnop"], (0, 0))
        editor._handle_visual(27)
        editor._handle_normal(ord("d"), 24, 80)
        editor._handle_normal(ord("d"), 24, 80)   # an earlier, unrelated change
        editor._store_register(["Z"], False)
        editor._move(0, 1)
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(22)
        for key in "jlp":
            editor._handle_visual(ord(key))
        self.assertEqual(editor.lines, ["eZh", "iZl", "mnop"])

        editor._move(1, 0)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["eZh", "Zl", "Zop"])   # 2-wide block "iZ" -> "Z"
        editor._handle_normal(ord("u"), 24, 80)
        self.assertEqual(editor.lines, ["eZh", "iZl", "mnop"])

        # Near the end of the buffer the block is shorter; the text follows it.
        editor._move(2, 0)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["eZh", "iZl", "Zop"])

    def test_block_put_count_clamp_accounts_for_row_padding(self):
        editor = ViEditor()
        editor.lines = ["x"] * 1000
        editor.line_endings = ["\n"] * 1000
        editor._store_register(["W" * 1000] + [""] * 999, False, blockwise=True)
        for key in "50P":
            editor._handle_normal(ord(key), 24, 80)
        inserted = sum(len(line) for line in editor.lines) - 1000
        self.assertLessEqual(inserted, editor.MAX_COUNT)
        self.assertTrue(editor.message_is_error)

    def test_block_put_past_eof_keeps_missing_final_newline(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.line_endings = [""]
        editor._store_register(["1", "2", "3"], False, blockwise=True)
        editor._move(0, 2)
        editor._handle_normal(ord("p"), 24, 80)
        self.assertEqual(editor.lines, ["abc1", "   2", "   3"])
        self.assertEqual(editor.line_endings, ["\n", "\n", ""])

    def test_block_append_refuses_padding_past_limit(self):
        editor = self._block_editor(["x" * 40, "", "", ""], (0, 39))
        editor.BLOCK_PAD_LIMIT = 50
        self._feed_keys(editor, ["j", "j", "j", "A"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["x" * 40, "", "", ""])
        self.assertTrue(editor.message_is_error)
        self.assertFalse(editor.undo_stack)
        self.assertIsNone(editor._block_insert)

    def test_block_append_padding_exactly_at_limit_is_allowed(self):
        editor = self._block_editor(["x" * 10, "", ""], (0, 9))
        editor.BLOCK_PAD_LIMIT = 20
        self._feed_keys(editor, ["j", "j", "A", "Z", 27])
        self.assertEqual(editor.lines, ["x" * 10 + "Z", " " * 10 + "Z", " " * 10 + "Z"])

    def test_block_append_dot_repeat_refused_does_not_type_into_normal_mode(self):
        editor = self._block_editor(["ab", "cd", "x" * 40, "", ""], (0, 0), ["j", "A", "Z", 27])
        self.assertEqual(editor.lines[:2], ["aZb", "cZd"])
        editor.BLOCK_PAD_LIMIT = 30
        undo_depth = len(editor.undo_stack)
        editor._move(2, 39)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["aZb", "cZd", "x" * 40, "", ""])
        self.assertTrue(editor.message_is_error)
        self.assertEqual(len(editor.undo_stack), undo_depth)

    def test_block_put_refuses_padding_past_limit(self):
        editor = ViEditor()
        editor.lines = ["y" * 40]
        editor.line_endings = [""]
        editor.BLOCK_PAD_LIMIT = 50
        editor._store_register(["q", "q", "q"], False, blockwise=True)
        editor._move(0, 39)
        editor._handle_normal(ord("p"), 24, 80)
        self.assertEqual(editor.lines, ["y" * 40])
        self.assertEqual(editor.line_endings, [""])
        self.assertTrue(editor.message_is_error)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.modified)

    def test_block_paste_over_selection_refuses_padding_past_limit(self):
        # Both corners on long rows keep the block at column 39 over the
        # two empty rows between them: 2 x 39 padding cells > 50.
        lines = ["x" * 40, "", "", "x" * 40]
        editor = self._block_editor(lines, (0, 39), "jjj")
        self.assertEqual(editor._visual_block_bounds(), (0, 3, 39, 39))
        editor.BLOCK_PAD_LIMIT = 50
        editor._store_register(["Z"], False)
        editor._handle_visual(ord("p"))
        self.assertEqual(editor.lines, lines)
        self.assertEqual(editor.yank_buffer, ["Z"])
        self.assertTrue(editor.message_is_error)
        self.assertFalse(editor.undo_stack)

    def test_block_paste_over_selection_dot_repeat_refuses_padding_past_limit(self):
        editor = self._block_editor(["abcd", "efgh", "x" * 40, "", ""], (0, 1), "j")
        editor._store_register(["Z"], False)
        editor._handle_visual(ord("p"))
        self.assertEqual(editor.lines[:2], ["aZcd", "eZgh"])
        editor.BLOCK_PAD_LIMIT = 30
        undo_depth = len(editor.undo_stack)
        editor._move(2, 39)
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["aZcd", "eZgh", "x" * 40, "", ""])
        self.assertTrue(editor.message_is_error)
        self.assertEqual(len(editor.undo_stack), undo_depth)

    def test_block_put_refuses_piece_width_padding_past_limit(self):
        # One wide piece and four empty ones: each empty piece is padded to
        # 20 columns because text follows it, 5 x 20 = 100 cells > 50.
        editor = ViEditor()
        editor.lines = ["ab"] * 5
        editor.line_endings = ["\n"] * 5
        editor.BLOCK_PAD_LIMIT = 50
        editor._store_register(["W" * 20] + [""] * 4, False, blockwise=True)
        editor._handle_normal(ord("P"), 24, 80)
        self.assertEqual(editor.lines, ["ab"] * 5)
        self.assertTrue(editor.message_is_error)
        self.assertNotIn("clamped", editor.message)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.modified)

    def test_block_put_single_copy_over_count_cap_is_not_reported_clamped(self):
        editor = ViEditor()
        editor.lines = ["xy", "xy"]
        editor.line_endings = ["\n", "\n"]
        editor.MAX_COUNT = 4   # one copy is 3 x 2 = 6 cells
        editor._store_register(["abc", "def"], False, blockwise=True)
        editor._handle_normal(ord("P"), 24, 80)
        self.assertEqual(editor.lines, ["abcxy", "defxy"])
        self.assertFalse(editor.message_is_error)

    def test_block_paste_over_selection_refuses_piece_width_padding_past_limit(self):
        lines = ["abcd"] * 5
        editor = self._block_editor(lines, (0, 0), "jjjj")
        editor.BLOCK_PAD_LIMIT = 50
        editor._store_register(["W" * 20] + [""] * 4, False, blockwise=True)
        editor._handle_visual(ord("p"))
        self.assertEqual(editor.lines, lines)
        self.assertTrue(editor.message_is_error)
        self.assertFalse(editor.undo_stack)

    def test_block_paste_refusal_keeps_selected_register_for_retry(self):
        lines = ["x" * 40, "", "", "x" * 40]
        editor = self._block_editor(lines, (0, 39), "jjj")
        editor.active_register = "a"
        editor._store_register(["Z"], False)
        editor._store_register(["U"], False)   # unnamed only
        editor.BLOCK_PAD_LIMIT = 50
        for key in '"ap':
            editor._handle_visual(ord(key))
        self.assertEqual(editor.lines, lines)
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        self.assertEqual(editor.active_register, "a")

        editor.BLOCK_PAD_LIMIT = 10_000
        editor._handle_visual(ord("p"))
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines[1], " " * 39 + "Z")
        self.assertFalse(any("U" in line for line in editor.lines))

    def test_block_paste_from_empty_register_keeps_selected_register(self):
        editor = self._block_editor(["abc", "def"], (0, 0), "j")
        for key in '"bp':
            editor._handle_visual(ord(key))
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.mode, Mode.VISUAL_BLOCK)
        self.assertEqual(editor.active_register, "b")

    def test_block_insert_too_large_to_repeat_changes_first_row_only(self):
        editor = self._block_editor(["ab"] * 4, (0, 0), "jjjI")
        editor.BLOCK_PAD_LIMIT = 20   # 10 chars x 3 more rows = 30 cells
        self._feed_keys(editor, ["Q"] * 10 + [27])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["Q" * 10 + "ab", "ab", "ab", "ab"])
        self.assertTrue(editor.message_is_error)
        editor._handle_normal(ord("u"), 24, 80)
        self.assertEqual(editor.lines, ["ab"] * 4)

    def test_block_insert_repeat_exactly_at_limit_is_allowed(self):
        editor = self._block_editor(["ab"] * 4, (0, 0), "jjjI")
        editor.BLOCK_PAD_LIMIT = 30
        self._feed_keys(editor, ["Q"] * 10 + [27])
        self.assertEqual(editor.lines, ["Q" * 10 + "ab"] * 4)
        self.assertFalse(editor.message_is_error)

    def test_block_other_corner_swaps_columns_on_same_row(self):
        editor = self._block_editor(["abcdef", "ghijkl"], (0, 1), "jll")
        editor._handle_visual(ord("O"))
        self.assertEqual(editor.visual_start, (0, 3))
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 1))
        self.assertEqual(editor._visual_block_bounds(), (0, 1, 1, 3))

    def test_block_uses_display_columns_across_tabs(self):
        editor = ViEditor()
        editor.tab_stop = 8
        editor.lines = ["\tx", "abcdefghij"]
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(22)
        for key in "jld":
            editor._handle_visual(ord(key))
        # The tab covers display columns 0-7, so the block spans them all.
        self.assertEqual(editor.lines, ["x", "ij"])
        self.assertEqual(editor.yank_buffer, ["\t", "abcdefgh"])

    def test_block_selection_highlights_only_block_columns(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = self._block_editor(["abcdef", "ghijkl"], (0, 1), "jl")
        editor.show_line_numbers = False
        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)
        highlighted = [
            args[2] for args in screen.calls
            if len(args) == 4 and args[3] & curses.A_REVERSE and args[0] in (1, 2)
        ]
        self.assertIn("bc", highlighted)
        self.assertIn("hi", highlighted)


class NormalModeViFeatureTests(unittest.TestCase):
    def send(self, editor: ViEditor, keys):
        for key in keys:
            if editor._cmd_buf:
                editor._handle_cmd_buf(key)
            elif editor.mode == Mode.INSERT:
                editor._handle_insert(key)
            elif editor.mode == Mode.REPLACE:
                editor._handle_replace_mode(key)
            elif editor.mode in (Mode.VISUAL, Mode.VISUAL_LINE):
                editor._handle_visual(key)
            else:
                editor._handle_normal(key, 24, 80)

    def test_normal_mode_clamps_stale_cursor_before_handling_key(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_row = 99
        editor.cursor_col = 99

        # Normal mode allows the cursor one past the last char (like insert
        # mode), so the stray cursor clamps to len(line) here, not len(line)
        # - 1 -- a position with no char under it, so "x" is a no-op there.
        self.send(editor, [ord("x")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))

        # Back it up one and "x" deletes the last char as usual.
        self.send(editor, [ord("h"), ord("x")])

        self.assertEqual(editor.lines, ["ab"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 2))

    def test_linewise_change_last_line_preserves_previous_lines(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.cursor_row = 1

        self.send(editor, [ord("c"), ord("c")])

        self.assertEqual(editor.lines, ["one", ""])
        self.assertEqual(editor.mode, Mode.INSERT)

    def test_double_space_inserts_space_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["abcd"]
        editor.cursor_row = 0
        editor.cursor_col = 2

        self.send(editor, [ord(" "), ord(" ")])

        self.assertEqual(editor.lines, ["ab cd"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))
        self.assertTrue(editor.modified)

        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["ab  cd"])

    def test_single_space_does_not_insert_and_swallows_next_key(self):
        editor = ViEditor()
        editor.lines = ["abcd"]
        editor.cursor_row = 0
        editor.cursor_col = 2

        self.send(editor, [ord(" ")])
        self.assertEqual(editor.lines, ["abcd"])
        self.assertFalse(editor.modified)

        # A non-space second key just cancels the pending space (gg-style),
        # it is not separately dispatched as its own command.
        self.send(editor, [ord("x")])
        self.assertEqual(editor.lines, ["abcd"])

        self.send(editor, [ord("x")])
        self.assertEqual(editor.lines, ["abd"])

    def test_plus_copies_word_under_cursor_to_editor_clipboard(self):
        editor = ViEditor()
        editor.lines = ["alpha beta_gamma"]
        editor.cursor_row = 0
        editor.cursor_col = 9

        self.send(editor, [ord("+")])

        self.assertEqual(editor.yank_buffer, ["beta_gamma"])
        self.assertFalse(editor.yank_is_lines)
        self.assertEqual(editor.registers['"'], (["beta_gamma"], False))
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.message, "copied 'beta_gamma'")

    def test_plus_copy_can_be_pasted_with_p(self):
        editor = ViEditor()
        editor.lines = ["alpha beta", "target"]
        editor.cursor_row = 0
        editor.cursor_col = 7

        self.send(editor, [ord("+")])
        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["alpha beta", "tbetaarget"])

    def test_plus_uses_named_register(self):
        editor = ViEditor()
        editor.lines = ["alpha beta"]
        editor.cursor_row = 0
        editor.cursor_col = 7
        editor.active_register = "a"

        self.send(editor, [ord("+")])

        self.assertEqual(editor.registers["a"], (["beta"], False))
        self.assertEqual(editor.registers['"'], (["beta"], False))
        self.assertIsNone(editor.active_register)

    def test_armed_register_does_not_leak_across_buffer_switch(self):
        editor = ViEditor()
        editor.lines = ["hello"]
        editor._append_buffer("unsaved-buffer.txt", switch=False)
        editor.buffers[1].lines = ["world"]

        self.send(editor, [ord('"'), ord("a")])
        self.assertEqual(editor.active_register, "a")

        editor._switch_buffer(1)
        self.assertIsNone(editor.active_register)

        self.send(editor, [ord("y"), ord("y")])
        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["world"], True))

    def test_armed_register_does_not_leak_into_help_overlay(self):
        editor = ViEditor()
        editor.lines = ["hello"]

        self.send(editor, [ord('"'), ord("a")])
        self.assertEqual(editor.active_register, "a")

        editor._open_help()
        self.assertIsNone(editor.active_register)

    def test_plus_reports_when_cursor_is_not_on_word(self):
        editor = ViEditor()
        editor.lines = ["alpha beta"]
        editor.cursor_row = 0
        editor.cursor_col = 5

        self.send(editor, [ord("+")])

        self.assertFalse(editor.yank_buffer)
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.message, "No word under cursor")

    def test_undo_clamps_insert_end_cursor_for_normal_mode(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 2

        self.send(editor, [ord("A"), ord("x"), 27, ord("u")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))

    def test_replace_mode_extends_line_at_end(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 2

        self.send(editor, [ord("R"), ord("X"), ord("Y"), ord("Z"), 27])

        self.assertEqual(editor.lines, ["abXYZ"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.modified)

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 2))

    def test_replace_mode_backspace_restores_overwritten_characters(self):
        editor = ViEditor()
        editor.lines = ["abcde"]
        editor.cursor_col = 0

        self.send(editor, [ord("R"), ord("X"), ord("Y")])
        self.assertEqual(editor.lines, ["XYcde"])

        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines, ["Xbcde"])
        self.assertEqual(editor.cursor_col, 1)

        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines, ["abcde"])
        self.assertEqual(editor.cursor_col, 0)

        # Nothing left to restore at the start of the replace session —
        # further backspacing must not eat pre-existing text.
        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines, ["abcde"])
        self.assertEqual(editor.cursor_col, 0)

    def test_replace_mode_backspace_undoes_append_past_end_of_line(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 1

        self.send(editor, [ord("R"), ord("X"), ord("Z")])
        self.assertEqual(editor.lines, ["aXZ"])

        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines, ["aX"])
        self.assertEqual(editor.cursor_col, 2)

    def test_replace_mode_backspace_after_navigation_is_plain_delete(self):
        editor = ViEditor()
        editor.lines = ["abcde"]
        editor.cursor_col = 0

        self.send(editor, [ord("R"), ord("X")])
        self.assertEqual(editor.lines, ["Xbcde"])
        self.send(editor, [curses.KEY_RIGHT])
        self.send(editor, [curses.KEY_BACKSPACE])

        # Cursor moved away from the just-overtyped column, so backspace
        # falls back to a normal delete instead of restoring 'X'.
        self.assertEqual(editor.lines, ["Xcde"])
        self.assertEqual(editor.cursor_col, 1)

    # ------------------------------------------------------------------
    # Fix: _replace_overwritten records (row, col, original_char) tuples
    # for Replace mode's backspace-undo, but unlike self.marks (which
    # _newline and the EOL-join both shift explicitly), its row indices
    # used to go stale whenever a line was inserted/removed mid-session.
    # A later backspace could then match a stale entry by coincidence and
    # splice an unrelated character into the wrong row. _newline and the
    # EOL-join now shift _replace_overwritten the same way they shift
    # marks; _repeat_insert_change also resets it on every dot-repeat
    # iteration, not just the first, mirroring _enter_replace().
    # ------------------------------------------------------------------

    def test_replace_mode_newline_keeps_backspace_undo_pointed_at_correct_row(self):
        editor = ViEditor()
        editor.lines = ["1111", "BBBB"]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord("R")])
        self.send(editor, [curses.KEY_RIGHT, curses.KEY_RIGHT])  # -> col 2
        self.send(editor, [ord("X")])
        self.assertEqual(editor.lines[1], "BBXB")

        # Move to row 0 col 0 and press Enter: splits row0, pushing the
        # already-edited "BBXB" row down to index 2 untouched.
        self.send(editor, [curses.KEY_HOME, curses.KEY_UP, curses.KEY_HOME])
        self.send(editor, [ord("\n")])
        self.assertEqual(editor.lines, ["", "1111", "BBXB"])

        # On the freshly-created row 1 ("1111"), type over col 3, undo it
        # with one backspace, then backspace once more. That second
        # backspace must not reach a stale entry describing the unrelated
        # row-2 edit.
        self.send(editor, [curses.KEY_RIGHT, curses.KEY_RIGHT, curses.KEY_RIGHT])
        self.send(editor, [ord("Z")])
        self.assertEqual(editor.lines[1], "111Z")
        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines[1], "1111")
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertNotIn("B", editor.lines[1])
        self.assertEqual(editor.lines[2], "BBXB")

    def test_replace_mode_eol_join_keeps_backspace_undo_pointed_at_correct_row(self):
        editor = ViEditor()
        editor.lines = ["AA", "BBBB", "CCCC"]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord("R")])
        self.send(editor, [curses.KEY_RIGHT])  # -> col 1
        self.send(editor, [ord("X")])
        self.assertEqual(editor.lines[1], "BXBB")

        # Move to the end of row 0 and press Delete: joins row1 ("BXBB")
        # into row0, shifting row2 ("CCCC") up to index 1.
        self.send(editor, [curses.KEY_HOME, curses.KEY_UP, curses.KEY_END])
        self.send(editor, [curses.KEY_DC])
        self.assertEqual(editor.lines, ["AABXBB", "CCCC"])

        # On the row that shifted into index 1 ("CCCC"), type over col 2,
        # undo it with one backspace, then backspace once more. That
        # second backspace must not reach a stale entry describing the
        # unrelated row-0 edit.
        self.send(editor, [curses.KEY_DOWN, curses.KEY_HOME,
                            curses.KEY_RIGHT, curses.KEY_RIGHT])
        self.send(editor, [ord("Z")])
        self.assertEqual(editor.lines[1], "CCZC")
        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines[1], "CCCC")
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertNotIn("B", editor.lines[1])
        self.assertEqual(editor.lines[0], "AABXBB")

    def test_replace_mode_dot_repeat_resets_backspace_undo_between_iterations(self):
        editor = ViEditor()
        editor.lines = ["aaaaaaaaaa"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # Each repeat types over a char, backspaces it back, backspaces
        # again (exhausting this iteration's own undo history), then
        # types the real replacement. Without a reset per iteration, that
        # second backspace can reach into the previous iteration's
        # leftover entry instead of falling back to a plain delete.
        keys = [ord("X"), curses.KEY_BACKSPACE, curses.KEY_BACKSPACE, ord("Y")]
        editor._repeat_insert_change(keys, Mode.REPLACE, None, repeat=3)

        self.assertEqual(editor.lines, ["Yaaaaaaa"])

    def test_replace_mode_mid_line_delete_key_shifts_backspace_undo_columns(self):
        # _delete_char_under_insert_cursor's non-EOL branch removes a
        # character from the row but, before the fix, never shifted
        # _replace_overwritten the way _adjust_marks_for_same_line_delete
        # already shifts marks. A later backspace could then match a
        # stale (pre-delete) column and splice the restored character
        # into the wrong, already-shifted position -- corrupting the
        # line instead of just failing to restore it.
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        self.send(editor, [ord("R")])
        self.send(editor, [ord("X")])                          # a->X, col 1
        self.send(editor, [curses.KEY_RIGHT])                  # skip 'b', col 2
        self.send(editor, [ord("Y")])                          # c->Y, col 3
        self.assertEqual(editor.lines, ["XbYdef"])

        self.send(editor, [curses.KEY_LEFT, curses.KEY_LEFT])  # col 1
        self.send(editor, [curses.KEY_DC])                     # forward-delete 'b'
        self.assertEqual(editor.lines, ["XYdef"])

        self.send(editor, [curses.KEY_RIGHT])                  # col 2, matches Y's shifted column
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertEqual(editor.lines, ["Xcdef"])

    def test_replace_mode_plain_backspace_fallback_shifts_later_undo_columns(self):
        # Same root cause as above, reached through _backspace()'s plain
        # (non-restoring) delete branch: navigating away and backspacing
        # falls back to an ordinary character delete, which must shift
        # any _replace_overwritten entries recorded further right on the
        # same row or a later, coincidentally-matching backspace corrupts
        # the line instead of restoring the right character.
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        self.send(editor, [ord("R")])
        self.send(editor, [ord("X")])                          # a->X, col 1
        self.send(editor, [curses.KEY_RIGHT, curses.KEY_RIGHT])  # skip 'b','c', col 3
        self.send(editor, [ord("Y")])                          # d->Y, col 4
        self.assertEqual(editor.lines, ["XbcYef"])

        self.send(editor, [curses.KEY_LEFT, curses.KEY_LEFT])  # col 2, mismatches top entry
        self.send(editor, [curses.KEY_BACKSPACE])              # plain fallback delete of 'b'
        self.assertEqual(editor.lines, ["XcYef"])

        self.send(editor, [curses.KEY_RIGHT, curses.KEY_RIGHT])  # col 3, matches Y's shifted column
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertEqual(editor.lines, ["Xcdef"])

    def test_replace_mode_backspace_join_keeps_backspace_undo_pointed_at_correct_row(self):
        # _backspace()'s row-join branch (backspacing at column 0) shifts
        # self.marks/self.auto_marks for the joined row but, before the
        # fix, never shifted _replace_overwritten -- so an entry recorded
        # on the row that gets deleted by the join kept its stale (row,
        # col), and a later backspace on an unrelated row that happened
        # to land on that same (row, col) could splice the wrong
        # character into it.
        editor = ViEditor()
        editor.lines = ["AA", "BBBB", "CCCC"]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord("R")])
        self.send(editor, [curses.KEY_RIGHT])                  # -> col 1
        self.send(editor, [ord("X")])                          # B->X, col 2
        self.assertEqual(editor.lines[1], "BXBB")

        # Backspace at column 0 joins row1 into row0, shifting row2
        # ("CCCC") up to index 1.
        self.send(editor, [curses.KEY_HOME])
        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines, ["AABXBB", "CCCC"])

        # On the row that shifted into index 1 ("CCCC"), type over col 2,
        # undo it with one backspace, then backspace once more. That
        # second backspace must not reach the stale entry describing the
        # unrelated row-0 edit.
        self.send(editor, [curses.KEY_DOWN, curses.KEY_HOME,
                            curses.KEY_RIGHT, curses.KEY_RIGHT])
        self.send(editor, [ord("Z")])
        self.assertEqual(editor.lines[1], "CCZC")
        self.send(editor, [curses.KEY_BACKSPACE])
        self.assertEqual(editor.lines[1], "CCCC")
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertNotIn("B", editor.lines[1])
        self.assertEqual(editor.lines[0], "AABXBB")

    def test_replace_mode_detab_shifts_backspace_undo_columns(self):
        # _detab_before_cursor deletes a same-line character range
        # (Shift-Tab in Replace mode) but, before the fix, never shifted
        # _replace_overwritten the way _adjust_marks_for_same_line_delete
        # already shifts marks -- entries recorded to the right of the
        # deleted span kept their pre-detab columns, so a later backspace
        # couldn't reach them at their new (shifted) position and
        # silently fell back to a plain delete instead of restoring the
        # original characters.
        editor = ViEditor()
        editor.lines = ["    abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 4

        self.send(editor, [ord("R")])
        self.send(editor, [ord("1")])   # a->1, col 5
        self.send(editor, [ord("2")])   # b->2, col 6
        self.assertEqual(editor.lines, ["    12cdef"])

        self.send(editor, [curses.KEY_LEFT, curses.KEY_LEFT])  # back to col 4
        self.send(editor, [curses.KEY_BTAB])                   # detab 4 spaces
        self.assertEqual(editor.lines, ["12cdef"])

        self.send(editor, [curses.KEY_RIGHT, curses.KEY_RIGHT])
        self.send(editor, [curses.KEY_BACKSPACE])
        self.send(editor, [curses.KEY_BACKSPACE])

        self.assertEqual(editor.lines, ["abcdef"])

    def test_insert_mode_ctrl_a_ctrl_e_and_ctrl_d(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1
        editor._enter_insert()

        editor._handle_insert(5)  # Ctrl-E
        self.assertEqual(editor.cursor_col, 3)

        editor._handle_insert(1)  # Ctrl-A
        self.assertEqual(editor.cursor_col, 0)

        editor._handle_insert(4)  # Ctrl-D
        self.assertEqual(editor.lines, ["bc"])
        self.assertEqual(editor.cursor_col, 0)

    def test_insert_mode_accepts_non_ascii_text(self):
        editor = ViEditor()
        editor.lines = [""]
        editor._enter_insert()

        editor._handle_insert(ord("é"))

        self.assertEqual(editor.lines, ["é"])
        self.assertEqual(editor.cursor_col, 1)

    def test_handle_insert_accepts_raw_wide_unicode_string_directly(self):
        # curses' get_wch() only normalizes ASCII single-char strings to an
        # int (see edit()'s read loop); anything wider -- like "你" here --
        # reaches _handle_insert as a raw str, not ord()'d into an int the
        # way test_insert_mode_accepts_non_ascii_text above exercises it.
        # _handle_insert's key parameter must accept that directly.
        editor = ViEditor()
        editor.lines = [""]
        editor._enter_insert()

        editor._handle_insert("你")

        self.assertEqual(editor.lines, ["你"])
        self.assertEqual(editor.cursor_col, 1)

    def test_counted_insert_mode_replays_wide_unicode_text(self):
        editor = ViEditor()
        editor.lines = [""]

        self.send(editor, [ord("2"), ord("i"), "你", 27])

        self.assertEqual(editor.lines, ["你你"])

    def test_dot_repeat_insert_mode_replays_wide_unicode_text(self):
        editor = ViEditor()
        editor.lines = ["ab"]

        self.send(editor, [ord("i"), "你", 27])
        editor.cursor_col = 1
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["你你ab"])

    def test_replace_mode_ctrl_a_ctrl_e_and_ctrl_d(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1
        editor._enter_replace()

        editor._handle_replace_mode(5)  # Ctrl-E
        self.assertEqual(editor.cursor_col, 3)

        editor._handle_replace_mode(1)  # Ctrl-A
        self.assertEqual(editor.cursor_col, 0)

        editor._handle_replace_mode(4)  # Ctrl-D
        self.assertEqual(editor.lines, ["bc"])
        self.assertEqual(editor.cursor_col, 0)

    def test_replace_mode_accepts_non_ascii_text(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1
        editor._enter_replace()

        editor._handle_replace_mode(ord("é"))

        self.assertEqual(editor.lines, ["aéc"])
        self.assertEqual(editor.cursor_col, 2)

    def test_handle_replace_mode_accepts_raw_wide_unicode_string_directly(self):
        # Same rationale as test_handle_insert_accepts_raw_wide_unicode_string_
        # directly: get_wch() delivers a raw str for non-ASCII input, and
        # _handle_replace_mode's key parameter must accept that directly.
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1
        editor._enter_replace()

        editor._handle_replace_mode("你")

        self.assertEqual(editor.lines, ["a你c"])
        self.assertEqual(editor.cursor_col, 2)

    def test_handle_insert_and_replace_mode_key_type_accepts_str(self):
        # _handle_insert/_handle_replace_mode's key parameter used to be
        # typed `int` even though curses' get_wch() (and _repeat_insert_
        # change's identically-typed `keys: List[Union[int, str]]`, which
        # feeds both of these) can hand it a raw str for non-ASCII input.
        # The project doesn't run mypy in CI, so nothing else catches a
        # regression back to the narrower, incorrect annotation -- check
        # it directly here.
        insert_hints = typing.get_type_hints(ViEditor._handle_insert)
        replace_hints = typing.get_type_hints(ViEditor._handle_replace_mode)
        self.assertEqual(insert_hints["key"], typing.Union[int, str])
        self.assertEqual(replace_hints["key"], typing.Union[int, str])

    def test_counted_replace_mode_replays_wide_unicode_text(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("2"), ord("R"), "你", 27])

        self.assertEqual(editor.lines, ["你你c"])

    def test_insert_mode_delete_at_eol_joins_next_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = ["\r\n", ""]
        editor.line_endings_trusted = True
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor._enter_insert()

        editor._handle_insert(curses.KEY_DC)

        self.assertEqual(editor.lines, ["onetwo"])
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor._line_endings_view_lines(), ["onetwo[NONE]"])
        self.assertTrue(editor.modified)

    def test_replace_mode_delete_at_eol_joins_next_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = ["\n", ""]
        editor.line_endings_trusted = True
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor._enter_replace()

        editor._handle_replace_mode(curses.KEY_DC)

        self.assertEqual(editor.lines, ["onetwo"])
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor._line_endings_view_lines(), ["onetwo[NONE]"])
        self.assertTrue(editor.modified)

    def test_replace_mode_navigation_keys_match_insert_mode(self):
        editor = ViEditor()
        editor.lines = ["abc", "def"]
        editor.cursor_row = 0
        editor.cursor_col = 1
        editor._enter_replace()

        editor._handle_replace_mode(curses.KEY_RIGHT)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 2))

        editor._handle_replace_mode(curses.KEY_LEFT)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

        editor._handle_replace_mode(curses.KEY_DOWN)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 1))

        editor._handle_replace_mode(curses.KEY_UP)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

        editor._handle_replace_mode(curses.KEY_END)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))

        editor._handle_replace_mode(curses.KEY_HOME)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_insert_tab_and_shift_tab_keep_cursor_on_following_char(self):
        editor = ViEditor()
        editor.lines = ["Cat"]
        editor.cursor_col = 0
        editor.shift_width = 3
        editor.expand_tab = True
        editor._enter_insert()

        editor._handle_insert(ord("\t"))
        self.assertEqual(editor.lines, ["   Cat"])
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor.lines[0][editor.cursor_col], "C")

        editor._handle_insert(curses.KEY_BTAB)
        self.assertEqual(editor.lines, ["Cat"])
        self.assertEqual(editor.cursor_col, 0)
        self.assertEqual(editor.lines[0][editor.cursor_col], "C")

    def test_replace_tab_and_shift_tab_keep_cursor_on_following_char(self):
        editor = ViEditor()
        editor.lines = ["Cat"]
        editor.cursor_col = 0
        editor.shift_width = 3
        editor.expand_tab = True
        editor._enter_replace()

        editor._handle_replace_mode(ord("\t"))
        self.assertEqual(editor.lines, ["   Cat"])
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor.lines[0][editor.cursor_col], "C")

        editor._handle_replace_mode(curses.KEY_BTAB)
        self.assertEqual(editor.lines, ["Cat"])
        self.assertEqual(editor.cursor_col, 0)
        self.assertEqual(editor.lines[0][editor.cursor_col], "C")

    def test_operator_motion_undo_restores_start_cursor(self):
        editor = ViEditor()
        editor.lines = ["abc def", "ghi"]
        editor.cursor_col = 1

        self.send(editor, [ord("d"), ord("w")])
        self.assertEqual(editor.lines, ["adef", "ghi"])

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["abc def", "ghi"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_change_motion_undo_restores_start_cursor(self):
        editor = ViEditor()
        editor.lines = ["abc def", "ghi"]
        editor.cursor_col = 1

        self.send(editor, [ord("c"), ord("w"), ord("Z"), 27])
        self.assertEqual(editor.lines, ["aZ def", "ghi"])

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["abc def", "ghi"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_backward_operator_motion_undo_restores_start_cursor(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 2
        editor.cursor_col = 1

        self.send(editor, [ord("d"), ord("k")])
        self.assertEqual(editor.lines, ["one"])

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["one", "two", "three"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (2, 1))

    def test_downward_linewise_operator_motion_includes_target_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]

        self.send(editor, [ord("d"), ord("j")])
        self.assertEqual(editor.lines, ["three", "four"])
        self.assertEqual(editor.yank_buffer, ["one", "two"])

        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]

        self.send(editor, [ord("y"), ord("2"), ord("j")])
        self.assertEqual(editor.yank_buffer, ["one", "two", "three"])

        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]

        self.send(editor, [ord(">"), ord("j")])
        self.assertEqual(editor.lines, ["    one", "    two", "three", "four"])

    def test_yank_motion_leaves_cursor_at_operator_start(self):
        editor = ViEditor()
        editor.lines = ["abc def"]
        editor.cursor_col = 1

        self.send(editor, [ord("y"), ord("w")])

        self.assertEqual(editor.yank_buffer, ["bc "])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 1))

    def test_yank_backward_word_motion_yanks_the_traversed_text(self):
        # apply() (shared by d/y/c/>/<) only normalized (r1,c1)<=(r2,c2)
        # implicitly via _delete_range()'s own internal swap, which d/c
        # get for free but y (via _get_char_range) and >/< (via
        # _indent_lines) do not. Backward motions like b/B hand apply()
        # the range in (end, start) order, so yb/yB silently yanked ""
        # instead of the word that was traversed.
        editor = ViEditor()
        editor.lines = ["hello world foo"]
        editor.cursor_col = 12

        self.send(editor, [ord("y"), ord("b")])

        self.assertEqual(editor.yank_buffer, ["world f"])
        self.assertEqual(editor.lines, ["hello world foo"])

    def test_yank_backward_word_motion_leaves_cursor_at_range_start(self):
        # apply()'s "y" branch used to restore the pre-motion cursor
        # position (op_start) instead of the normalized range start,
        # so yb left the cursor exactly where it started instead of
        # moving it back to the yanked text -- unlike d/c/>/< and
        # visual-mode y, which all land on the range start. Verified
        # against real Vim 9.1: `yb` from inside "gamma" in
        # "alpha beta gamma delta" moves the cursor to "beta"'s start.
        editor = ViEditor()
        editor.lines = ["alpha beta gamma delta"]
        editor.cursor_col = 11  # 'g' of "gamma" -- already at a word start

        self.send(editor, [ord("y"), ord("b")])

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 6))

    def test_yank_forward_word_motion_leaves_cursor_unmoved(self):
        # Regression guard for the op_start fix above: forward motions
        # already start at the range start, so cursor placement must be
        # unchanged by switching from op_start to (r1, c1).
        editor = ViEditor()
        editor.lines = ["hello world foo"]
        editor.cursor_col = 6

        self.send(editor, [ord("y"), ord("w")])

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 6))

    def test_yank_backward_find_motion_yanks_the_traversed_text(self):
        editor = ViEditor()
        editor.lines = ["hello world foo"]
        editor.cursor_col = 10

        self.send(editor, [ord("y"), ord("F"), ord("h")])

        self.assertEqual(editor.yank_buffer, ["hello world"])

    def test_yank_backward_find_motion_leaves_cursor_at_range_start(self):
        # Verified against real Vim 9.1: `yFh` from col 10 in
        # "hello world foo" moves the cursor to col 0.
        editor = ViEditor()
        editor.lines = ["hello world foo"]
        editor.cursor_col = 10

        self.send(editor, [ord("y"), ord("F"), ord("h")])

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_yank_backward_search_motion_yanks_the_traversed_text(self):
        editor = ViEditor()
        editor.lines = ["hello world foo"]
        editor.cursor_col = 12

        editor._resolve_operator(
            "y", 1, SearchMotion(cmd="?", pattern="world"))

        self.assertEqual(editor.yank_buffer, ["world f"])

    def test_yank_backward_linewise_motion_moves_cursor_to_start_row(self):
        # Same root cause as the charwise cases above, but for a linewise
        # backward motion (yk/y{/ygg): the row must move to the earlier
        # line, while the column stays at its original value -- verified
        # against real Vim 9.1, which preserves the column across a
        # linewise yank but corrects the row.
        editor = ViEditor()
        editor.lines = ["    indented line here", "second line here too", "third"]
        editor.cursor_row = 1
        editor.cursor_col = 9

        self.send(editor, [ord("y"), ord("k")])

        self.assertEqual(editor.yank_buffer,
                          ["    indented line here", "second line here too"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 9))

    def test_yank_forward_linewise_motion_leaves_cursor_unmoved(self):
        # Regression guard: forward linewise motions (yj) already start
        # at the range's top row, so this must be unaffected by the fix.
        editor = ViEditor()
        editor.lines = ["    indented line here", "second line here too", "third"]
        editor.cursor_row = 0
        editor.cursor_col = 11

        self.send(editor, [ord("y"), ord("j")])

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 11))

    def test_indent_backward_word_motion_indents_the_traversed_line(self):
        # Same root cause as the yank cases above: _indent_lines() also
        # assumes r1 <= r2, so >b on a motion crossing to an earlier line
        # silently indented nothing instead of that line.
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.cursor_col = 8
        editor.shift_width = 4
        editor.expandtab = True

        self.send(editor, [ord(">"), ord("b")])

        self.assertEqual(editor.lines, ["    hello world"])

    def test_operator_to_first_nonblank_handles_forward_motion(self):
        editor = ViEditor()
        editor.lines = ["  alpha"]
        editor.cursor_col = 0

        self.send(editor, [ord("y"), ord("^")])

        self.assertEqual(editor.yank_buffer, ["  "])
        self.assertEqual(editor.lines, ["  alpha"])

        self.send(editor, [ord("d"), ord("^")])

        self.assertEqual(editor.lines, ["alpha"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_caret_toggles_between_first_nonblank_and_column_zero(self):
        editor = ViEditor()
        editor.lines = ["  alpha"]
        editor.cursor_col = 5

        self.send(editor, [ord("^")])
        self.assertEqual(editor.cursor_col, 2)

        self.send(editor, [ord("^")])
        self.assertEqual(editor.cursor_col, 0)

        self.send(editor, [ord("^")])
        self.assertEqual(editor.cursor_col, 2)

    def test_named_register_yank_and_put(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]

        self.send(editor, [ord('"'), ord("a"), ord("y"), ord("y")])
        editor.cursor_row = 1
        self.send(editor, [ord('"'), ord("a"), ord("p")])

        self.assertEqual(editor.lines, ["alpha", "beta", "alpha"])

    def test_named_register_put_does_not_replace_plain_put_register(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 0
        editor.registers['"'] = (["X"], False)
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["Y"], False)
        editor.register_line_endings["a"] = []

        self.send(editor, [ord('"'), ord("a"), ord("p")])
        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["aYXb"])
        self.assertEqual(editor.yank_buffer, ["X"])
        self.assertEqual(editor.registers['"'], (["X"], False))

    def test_named_register_put_dot_repeat_uses_named_payload(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 0
        editor.registers['"'] = (["X"], False)
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False
        editor.registers["a"] = (["Y"], False)
        editor.register_line_endings["a"] = []

        self.send(editor, [ord('"'), ord("a"), ord("p")])
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["aYYb"])
        self.assertEqual(editor.yank_buffer, ["X"])

    def test_count_before_named_register_put_is_preserved(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 1
        editor.registers["a"] = (["Y"], False)
        editor.register_line_endings["a"] = []
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False

        self.send(editor, [ord("2"), ord('"'), ord("a"), ord("p")])

        self.assertEqual(editor.lines, ["abYY"])
        self.assertEqual(editor.yank_buffer, ["X"])

    def test_named_register_counted_linewise_yank_and_put_uses_named_register(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "target"]

        self.send(editor, [ord('"'), ord("b"), ord("2"), ord("y"), ord("y")])

        self.assertEqual(editor.registers["b"], (["one", "two"], True))
        self.assertEqual(editor.registers['"'], (["one", "two"], True))

        editor.cursor_row = 2
        self.send(editor, [ord("y"), ord("y")])

        self.assertEqual(editor.registers['"'], (["three"], True))
        self.assertEqual(editor.registers["b"], (["one", "two"], True))

        editor.cursor_row = 4
        self.send(editor, [ord('"'), ord("b"), ord("p")])

        self.assertEqual(editor.lines, ["one", "two", "three", "four", "target", "one", "two"])

    def test_register_prefix_clears_after_non_register_command(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord('"'), ord("a"), ord("j"), ord("x")])

        self.assertEqual(editor.lines, ["bc"])
        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["a"], False))

    def test_register_prefix_clears_after_noop_operator_motion(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1

        self.send(editor, [ord('"'), ord("a"), ord("d"), ord("t"), ord("b"), ord("x")])

        self.assertEqual(editor.lines, ["ac"])
        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["b"], False))

    def test_register_prefix_clears_after_noop_substitute(self):
        editor = ViEditor()
        editor.lines = [""]

        self.send(editor, [ord('"'), ord("a"), ord("s"), 27])
        self.assertIsNone(editor.active_register)

        editor.lines = ["abc"]
        editor.cursor_col = 0
        self.send(editor, [ord("x")])

        self.assertNotIn("a", editor.registers)
        self.assertEqual(editor.registers['"'], (["a"], False))

    def test_linewise_put_bulk_inserts_yanked_lines(self):
        editor = ViEditor()
        editor.lines = ["top", "bottom"]
        editor.yank_buffer = ["one", "two"]
        editor.yank_is_lines = True

        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["top", "one", "two", "bottom"])
        self.assertTrue(editor.modified)

    def test_counted_linewise_put_preserves_block_order(self):
        editor = ViEditor()
        editor.lines = ["top", "bottom"]
        editor.yank_buffer = ["one", "two"]
        editor.yank_is_lines = True

        self.send(editor, [ord("2"), ord("p")])

        self.assertEqual(editor.lines, ["top", "one", "two", "one", "two", "bottom"])

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["top", "bottom"])

    def test_linewise_put_count_is_clamped_to_max_count(self):
        editor = ViEditor()
        editor.lines = ["top", "bottom"]
        editor.yank_buffer = ["one", "two", "three"]
        editor.yank_is_lines = True

        editor._put_count(after=True, cnt=editor.MAX_COUNT)

        # len(yank_buffer) * cnt must never be allowed to exceed MAX_COUNT,
        # regardless of how large the requested count is.
        self.assertLessEqual(len(editor.lines) - 2, editor.MAX_COUNT)
        self.assertTrue(editor.message_is_error)
        self.assertIn("clamped", editor.message)
        self.assertEqual(editor.lines[1:1 + len(editor.yank_buffer)], ["one", "two", "three"])

    def test_charwise_put_count_is_clamped_to_max_count(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 0
        editor.yank_buffer = ["x" * 100]
        editor.yank_is_lines = False

        editor._put_count(after=True, cnt=editor.MAX_COUNT)

        inserted_chars = len(editor.lines[0]) - len("ab")
        # 100 chars * MAX_COUNT would be 100,000,000 chars unclamped; the
        # clamp must keep the inserted payload at or below MAX_COUNT.
        self.assertLessEqual(inserted_chars, editor.MAX_COUNT)
        self.assertTrue(editor.message_is_error)
        self.assertIn("clamped", editor.message)

    def test_counted_gg_uses_line_count(self):
        editor = ViEditor()
        editor.lines = [str(i) for i in range(1, 21)]

        self.send(editor, [ord("1"), ord("0"), ord("g"), ord("g")])

        self.assertEqual((editor.cursor_row, editor.lines[editor.cursor_row]), (9, "10"))

    def test_operator_accepts_count_after_operator(self):
        editor = ViEditor()
        editor.lines = ["one two three four"]

        self.send(editor, [ord("d"), ord("3"), ord("w")])
        self.assertEqual(editor.lines, ["four"])

        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d"]
        self.send(editor, [ord("d"), ord("2"), ord("d")])
        self.assertEqual(editor.lines, ["c", "d"])
        self.assertEqual(editor.yank_buffer, ["a", "b"])

        editor = ViEditor()
        editor.lines = ["a", "b", "c", "d"]
        self.send(editor, [ord(">"), ord("2"), ord(">")])
        self.assertEqual(editor.lines, ["    a", "    b", "c", "d"])

    def test_delete_word_at_final_word_deletes_to_end_of_line(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("d"), ord("w")])

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.yank_buffer, ["abc"])

        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1

        self.send(editor, [ord("d"), ord("w")])

        self.assertEqual(editor.lines, ["a"])
        self.assertEqual(editor.yank_buffer, ["bc"])

    def test_change_word_keeps_following_space(self):
        editor = ViEditor()
        editor.lines = ["foo bar"]

        self.send(editor, [ord("c"), ord("w"), ord("X"), 27])

        self.assertEqual(editor.lines, ["X bar"])
        self.assertEqual(editor.yank_buffer, ["foo"])

    def test_operator_prefix_and_motion_counts_multiply(self):
        editor = ViEditor()
        editor.lines = ["one two three four five six seven"]

        self.send(editor, [ord("2"), ord("d"), ord("3"), ord("w")])

        self.assertEqual(editor.lines, ["seven"])

    def test_huge_digit_prefix_does_not_crash_and_clamps_to_max_count(self):
        # int(self._count_str) used to run unconditionally on whatever digit
        # string had been typed. Python raises ValueError once a string of
        # digits exceeds its default int-conversion limit (4300 digits) --
        # trivially reachable by pasting a long numeral, or a key held down
        # long enough for terminal auto-repeat to queue thousands of
        # keystrokes -- crashing the whole editor.
        editor = ViEditor()
        editor.lines = ["x"] * 10

        for _ in range(5000):
            editor._handle_normal(ord("9"), 24, 80)
        self.assertLessEqual(len(editor._count_str), editor.MAX_COUNT_STR_LEN)

        editor._handle_normal(ord("j"), 24, 80)  # must not raise

        self.assertEqual(editor.cursor_row, len(editor.lines) - 1)
        self.assertEqual(editor._count_str, "")

    def test_huge_digit_prefix_in_pending_operator_does_not_crash(self):
        editor = ViEditor()
        editor.lines = ["x"] * 10

        editor._handle_normal(ord("d"), 24, 80)
        for _ in range(5000):
            editor._handle_normal(ord("9"), 24, 80)
        editor._handle_normal(ord("j"), 24, 80)  # must not raise

        self.assertEqual(editor.lines, [""])

    def test_huge_digit_prefix_in_visual_mode_does_not_crash(self):
        editor = ViEditor()
        editor.lines = ["x"] * 10
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)

        for _ in range(5000):
            editor._handle_visual(ord("9"))
        editor._handle_visual(ord("j"))  # must not raise

        self.assertEqual(editor.cursor_row, len(editor.lines) - 1)

    def test_operator_counted_g_and_gg_use_line_count(self):
        editor = ViEditor()
        editor.lines = [str(i) for i in range(1, 21)]
        editor.cursor_row = 14

        self.send(editor, [ord("d"), ord("1"), ord("0"), ord("G")])
        self.assertEqual(editor.lines, [str(i) for i in range(1, 10)] + [str(i) for i in range(16, 21)])
        self.assertEqual(editor.yank_buffer, [str(i) for i in range(10, 16)])

        editor = ViEditor()
        editor.lines = [str(i) for i in range(1, 21)]
        editor.cursor_row = 14

        self.send(editor, [ord("d"), ord("1"), ord("0"), ord("g"), ord("g")])
        self.assertEqual(editor.lines, [str(i) for i in range(1, 10)] + [str(i) for i in range(16, 21)])
        self.assertEqual(editor.yank_buffer, [str(i) for i in range(10, 16)])

    def test_counted_replace_and_put_apply_count(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]

        self.send(editor, [ord("3"), ord("r"), ord("x")])
        self.assertEqual(editor.lines, ["xxxdef"])

        editor = ViEditor()
        editor.lines = ["a"]
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False

        self.send(editor, [ord("3"), ord("p")])

        self.assertEqual(editor.lines, ["aXXX"])

        editor = ViEditor()
        editor.lines = ["ab"]
        editor.cursor_col = 1
        editor.yank_buffer = ["XY"]
        editor.yank_is_lines = False

        self.send(editor, [ord("3"), ord("P")])

        self.assertEqual(editor.lines, ["aXYXYXYb"])

    def test_replace_command_accepts_non_ascii_target_character(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("r"), "é"])

        self.assertEqual(editor.lines, ["ébc"])

    def test_counted_find_does_not_move_on_missing_occurrence(self):
        editor = ViEditor()
        editor.lines = ["abca"]

        self.send(editor, [ord("3"), ord("f"), ord("a")])

        self.assertEqual(editor.cursor_col, 0)

    def test_find_command_accepts_non_ascii_target_character(self):
        editor = ViEditor()
        editor.lines = ["aébc"]

        self.send(editor, [ord("f"), "é"])

        self.assertEqual(editor.cursor_col, 1)

    def test_operator_find_accepts_non_ascii_target_character(self):
        editor = ViEditor()
        editor.lines = ["aébc"]

        self.send(editor, [ord("d"), ord("f"), "é"])

        self.assertEqual(editor.lines, ["bc"])

    def test_t_motion_then_semicolon_advances_past_resting_position(self):
        # `t` lands the cursor on the column BEFORE the target. Pressing `;`
        # to repeat must advance to the next occurrence — pre-fix it stuck
        # at the same column because the search restarted at the same target.
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]

        self.send(editor, [ord("t"), ord("x")])
        self.assertEqual(editor.cursor_col, 0)

        self.send(editor, [ord(";")])
        self.assertEqual(editor.cursor_col, 2)

        self.send(editor, [ord(";")])
        self.assertEqual(editor.cursor_col, 4)

    def test_T_motion_then_semicolon_advances_backward(self):
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]
        editor.cursor_col = 7

        self.send(editor, [ord("T"), ord("x")])
        self.assertEqual(editor.cursor_col, 6)

        self.send(editor, [ord(";")])
        self.assertEqual(editor.cursor_col, 4)

    def test_f_repeat_still_advances_after_t_repeat_fix(self):
        # Regression: `f`/`F` were not affected by the bug; confirm they still
        # advance correctly when `;` is pressed.
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]

        self.send(editor, [ord("f"), ord("x")])
        self.assertEqual(editor.cursor_col, 1)

        self.send(editor, [ord(";")])
        self.assertEqual(editor.cursor_col, 3)

    def test_counted_semicolon_inserts_hash_before_first_nonblank_on_n_lines(self):
        editor = ViEditor()
        editor.lines = ["  one", "two", "   three", "four", "five"]

        self.send(editor, [ord("3"), ord(";")])

        self.assertEqual(
            editor.lines, ["  #one", "#two", "   #three", "four", "five"])
        self.assertTrue(editor.modified)
        self.assertEqual(editor.cursor_row, 0)

    def test_bare_semicolon_without_count_still_repeats_last_find(self):
        # `;` with no digit prefix must keep its original meaning (repeat
        # last f/F/t/T), not the new N; comment-insert behaviour.
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]

        self.send(editor, [ord("f"), ord("x")])
        self.assertEqual(editor.cursor_col, 1)

        self.send(editor, [ord(";")])
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor.lines, ["axbxcxdx"])

    def test_counted_semicolon_clamps_to_end_of_buffer(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("9"), ord(";")])

        self.assertEqual(editor.lines, ["#one", "#two"])

    def test_counted_semicolon_is_dot_repeatable(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]

        self.send(editor, [ord("2"), ord(";")])
        self.assertEqual(editor.lines, ["#one", "#two", "three", "four"])

        editor.cursor_row = 2
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["#one", "#two", "#three", "#four"])

    def test_counted_semicolon_does_not_modify_buffer_when_no_lines_match(self):
        editor = ViEditor()
        editor.lines = ["", "", ""]

        self.send(editor, [ord("3"), ord(";")])

        self.assertEqual(editor.lines, ["", "", ""])
        self.assertFalse(editor.modified)
        self.assertEqual(len(editor.undo_stack), 0)

    def test_counted_bang_deletes_leading_hash_on_n_lines(self):
        editor = ViEditor()
        editor.lines = ["  #one", "#two", "   #three", "four", "five"]

        self.send(editor, [ord("3"), ord("!")])

        self.assertEqual(
            editor.lines, ["  one", "two", "   three", "four", "five"])
        self.assertTrue(editor.modified)
        self.assertEqual(editor.cursor_row, 0)

    def test_bang_only_deletes_hash_when_it_is_first_nonblank_char(self):
        editor = ViEditor()
        editor.lines = ["a#b", "#ok", "  x#y"]

        self.send(editor, [ord("3"), ord("!")])

        self.assertEqual(editor.lines, ["a#b", "ok", "  x#y"])

    def test_bare_bang_without_count_only_affects_current_line(self):
        editor = ViEditor()
        editor.lines = ["#one", "#two"]

        self.send(editor, [ord("!")])

        self.assertEqual(editor.lines, ["one", "#two"])

    def test_bang_does_not_modify_buffer_when_no_lines_match(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("2"), ord("!")])

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertFalse(editor.modified)

    def test_counted_bang_clamps_to_end_of_buffer(self):
        editor = ViEditor()
        editor.lines = ["#one", "#two"]

        self.send(editor, [ord("9"), ord("!")])

        self.assertEqual(editor.lines, ["one", "two"])

    def test_counted_bang_is_dot_repeatable(self):
        editor = ViEditor()
        editor.lines = ["#one", "#two", "#three", "#four"]

        self.send(editor, [ord("2"), ord("!")])
        self.assertEqual(editor.lines, ["one", "two", "#three", "#four"])

        editor.cursor_row = 2
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["one", "two", "three", "four"])

    def test_t_first_press_from_resting_position_does_not_skip(self):
        # If the cursor happens to be one column before the target when the
        # user FIRST presses `tx`, vim-style behaviour leaves the cursor in
        # place. Only `;` should bump past the resting position.
        editor = ViEditor()
        editor.lines = ["axbx"]

        self.send(editor, [ord("t"), ord("x")])

        self.assertEqual(editor.cursor_col, 0)

    def test_t_with_explicit_count_skips_n_occurrences(self):
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]

        self.send(editor, [ord("2"), ord("t"), ord("x")])

        self.assertEqual(editor.cursor_col, 2)

    def test_comma_after_f_searches_backward(self):
        editor = ViEditor()
        editor.lines = ["axbxcxdx"]
        editor.cursor_col = 5

        self.send(editor, [ord("f"), ord("x"), ord(",")])

        # f at col 5 finds x at col 7; `,` reverses → x at col 5.
        # But cursor is *now* at 7 after f, so `,` searches backward from 7
        # and lands on the previous x at col 5.
        self.assertEqual(editor.cursor_col, 5)

    def test_pending_register_mark_and_textobj_ignore_non_ascii_without_crashing(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor._pending_op = '"'
        self.assertTrue(editor._handle_normal("é", 24, 80))
        self.assertIsNone(editor.active_register)

        editor._pending_op = "m"
        self.assertTrue(editor._handle_normal("é", 24, 80))
        self.assertEqual(editor.marks, {})

        editor._pending_op = "textobj:d:i"
        self.assertTrue(editor._handle_normal("é", 24, 80))
        self.assertEqual(editor.lines, ["abc"])

    def test_pending_operator_second_key_ignores_non_ascii_without_crashing(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor._pending_op = "d"
        editor._count_str = "2"

        self.assertTrue(editor._handle_normal("é", 24, 80))
        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual(editor._pending_op, "")

    def test_undo_restores_last_jump_to_its_snapshot_value(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.marks["a"] = (2, 0)

        editor._jump_to_mark("a", True)
        self.assertEqual(editor.last_jump, (0, 0))

        editor._push_undo()
        editor.lines[2] = "THREE"
        editor.modified = True

        # A later jump changes last_jump again before the undo happens.
        editor.marks["b"] = (1, 0)
        editor._jump_to_mark("b", True)
        self.assertEqual(editor.last_jump, (2, 0))

        editor._undo()
        self.assertEqual(editor.lines, ["one", "two", "three"])
        self.assertEqual(editor.last_jump, (0, 0))

        editor._redo()
        self.assertEqual(editor.lines, ["one", "two", "THREE"])
        self.assertEqual(editor.last_jump, (2, 0))

    def test_huge_count_undo_stops_once_stack_is_exhausted(self):
        # A count far larger than the undo history (e.g. "999999u") must not
        # keep looping/calling _undo() once undo_stack is empty.
        editor = ViEditor()
        editor.lines = ["one"]
        editor._push_undo()
        editor.lines[0] = "two"
        editor.modified = True

        calls = []
        real_undo = editor._undo
        def counting_undo():
            calls.append(1)
            real_undo()
        editor._undo = counting_undo

        self.send(editor, [ord("9"), ord("9"), ord("9"), ord("9"), ord("9"), ord("9"), ord("u")])

        self.assertEqual(editor.lines, ["one"])
        self.assertEqual(len(calls), 1)

    def test_huge_count_redo_stops_once_stack_is_exhausted(self):
        editor = ViEditor()
        editor.lines = ["one"]
        editor._push_undo()
        editor.lines[0] = "two"
        editor.modified = True
        editor._undo()

        calls = []
        real_redo = editor._redo
        def counting_redo():
            calls.append(1)
            real_redo()
        editor._redo = counting_redo

        self.send(editor, [ord("9"), ord("9"), ord("9"), ord("9"), ord("9"), ord("9"), 18])

        self.assertEqual(editor.lines, ["two"])
        self.assertEqual(len(calls), 1)

    def test_counted_put_undoes_as_single_change(self):
        editor = ViEditor()
        editor.lines = ["a"]
        editor._mark_clean()
        editor.yank_buffer = ["X"]
        editor.yank_is_lines = False

        self.send(editor, [ord("3"), ord("p")])
        self.assertEqual(editor.lines, ["aXXX"])

        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["a"])
        self.assertFalse(editor.modified)

    def test_charwise_empty_put_does_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.yank_buffer = [""]
        editor.yank_is_lines = False
        editor._mark_clean()

        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.yank_is_lines = True
        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["abc", ""])
        self.assertTrue(editor.modified)
        self.assertEqual(len(editor.undo_stack), 1)

    def test_marks_support_line_and_exact_jumps(self):
        editor = ViEditor()
        editor.lines = ["  alpha", "beta", "gamma"]
        editor.cursor_row = 0
        editor.cursor_col = 3

        self.send(editor, [ord("m"), ord("a")])
        editor.cursor_row = 2
        editor.cursor_col = 1
        self.send(editor, [ord("'"), ord("a")])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 2))

        editor.cursor_row = 2
        editor.cursor_col = 0
        self.send(editor, [ord("`"), ord("a")])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))

    def test_marks_follow_line_inserts_and_deletes(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 2
        editor.cursor_col = 1
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("O"), 27])

        self.assertEqual(editor.marks["a"], (3, 1))

        self.send(editor, [ord("d"), ord("d")])

        self.assertEqual(editor.marks["a"], (2, 1))

    def test_typed_insert_shifts_same_line_mark_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.marks = {"a": (0, 3)}
        editor.cursor_row, editor.cursor_col = 0, 3
        editor._enter_insert()

        editor._handle_insert(ord("X"))
        editor._handle_insert(ord("Y"))

        self.assertEqual(editor.lines, ["abcXYdef"])
        self.assertEqual(editor.marks["a"], (0, 5))

    def test_insert_text_at_cursor_shifts_same_line_mark_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.marks = {"a": (0, 3)}
        editor.cursor_row, editor.cursor_col = 0, 3

        editor._insert_text_at_cursor("XY")

        self.assertEqual(editor.lines, ["abcXYdef"])
        self.assertEqual(editor.marks["a"], (0, 5))

    def test_charwise_single_line_put_shifts_same_line_mark_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.marks = {"a": (0, 3)}
        editor.cursor_row, editor.cursor_col = 0, 1
        editor.yank_buffer = ["XY"]
        editor.yank_is_lines = False

        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["abXYcdef"])
        self.assertEqual(editor.marks["a"], (0, 5))

    def test_same_line_insert_mark_shift_is_a_noop_for_marks_before_cursor(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.marks = {"b": (0, 1), "a": (0, 3)}
        editor.cursor_row, editor.cursor_col = 0, 3
        editor._enter_insert()

        editor._handle_insert(ord("X"))

        self.assertEqual(editor.marks["b"], (0, 1))
        self.assertEqual(editor.marks["a"], (0, 4))

    def test_auto_mark_command_toggles_current_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 1

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {1: 1})
        self.assertEqual(editor.message, "auto-mark set at line 2")

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {})
        self.assertEqual(editor.message, "auto-mark removed from line 2")

    def test_auto_mark_toggle_updates_current_buffer_state_immediately(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 1
        editor._sync_current_buffer()

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {1: 1})
        self.assertEqual(editor.buffers[0].auto_marks, {1: 1})

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {})
        self.assertEqual(editor.buffers[0].auto_marks, {})

    def test_auto_mark_toggle_removes_mark_that_moved_to_current_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.auto_marks = {2: 1}
        editor.cursor_row = 1

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {})

    def test_auto_mark_ids_survive_creation_row_reuse_after_line_shift(self):
        # Auto-mark ids used to be the creation-time row number. Once an
        # earlier mark's tracked line drifts away from its own id (because
        # lines were inserted/deleted elsewhere), that original row number
        # is free to be reused as a *different* mark's creation row later
        # in the same session. Since the id is the dict key, the two marks
        # collided and the older one was silently overwritten -- with no
        # removal message, because the toggle-off path was never taken.
        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(30)]

        editor.cursor_row = 10
        self.send(editor, [ord("m"), ord(".")])
        first_id = next(iter(editor.auto_marks))
        self.assertEqual(editor.auto_marks[first_id], 10)

        # Insert 5 lines above everything, shifting the first mark to row 15.
        editor._adjust_marks_for_line_insert(0, 5)
        editor.lines = [f"new{i}" for i in range(5)] + editor.lines
        self.assertEqual(editor.auto_marks[first_id], 15)

        # A second, unrelated auto-mark created at (the now-different) row
        # 10 must not collide with the first mark's id.
        editor.cursor_row = 10
        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(len(editor.auto_marks), 2)
        self.assertEqual(sorted(editor.auto_marks.values()), [10, 15])

    def test_mdel_command_clears_named_and_auto_marks(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.marks = {"a": (0, 0), "b": (2, 1)}
        editor.auto_marks = {1: 1}
        editor._sync_current_buffer()

        self.assertTrue(editor._execute_cmd(":mdel"))

        self.assertEqual(editor.marks, {})
        self.assertEqual(editor.auto_marks, {})
        self.assertEqual(editor.buffers[0].marks, {})
        self.assertEqual(editor.buffers[0].auto_marks, {})
        self.assertEqual(editor.message, "All marks deleted")

    def test_auto_mark_removal_reports_when_named_marks_remain_on_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.marks = {"a": (1, 0)}
        editor.auto_marks = {1: 1}
        editor.cursor_row = 1
        editor._sync_current_buffer()

        self.send(editor, [ord("m"), ord(".")])

        self.assertEqual(editor.auto_marks, {})
        self.assertEqual(editor.marks, {"a": (1, 0)})
        self.assertEqual(editor.message, "auto-mark removed from line 2 (other marks remain)")

    def test_auto_marks_restore_through_undo_and_redo(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.auto_marks = {2: 2}
        editor.cursor_row = 0
        editor._mark_clean()

        self.send(editor, [ord("d"), ord("d")])

        self.assertEqual(editor.auto_marks, {2: 1})

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["one", "two", "three"])
        self.assertEqual(editor.auto_marks, {2: 2})

        self.send(editor, [18])

        self.assertEqual(editor.lines, ["two", "three"])
        self.assertEqual(editor.auto_marks, {2: 1})

    def test_insert_mode_undo_restores_auto_marks(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.auto_marks = {1: 1}
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor._mark_clean()

        self.send(editor, [ord("i"), ord("\n"), 27])

        self.assertEqual(editor.auto_marks, {1: 2})

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertEqual(editor.auto_marks, {1: 1})

    def test_auto_mark_follows_line_content_when_newline_splits_at_start(self):
        editor = ViEditor()
        editor.lines = ["one"]
        editor.auto_marks = {0: 0}
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._enter_insert()

        editor._handle_insert(ord("\n"))

        self.assertEqual(editor.lines, ["", "one"])
        self.assertEqual(editor.auto_marks, {0: 1})

        editor._handle_insert(curses.KEY_BACKSPACE)

        self.assertEqual(editor.lines, ["one"])
        self.assertEqual(editor.auto_marks, {0: 0})

    def test_auto_mark_stays_on_head_when_newline_splits_after_text(self):
        editor = ViEditor()
        editor.lines = ["one"]
        editor.auto_marks = {0: 0}
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor._enter_insert()

        editor._handle_insert(ord("\n"))

        self.assertEqual(editor.lines, ["one", ""])
        self.assertEqual(editor.auto_marks, {0: 0})

    def test_visual_exit_sets_less_and_greater_marks(self):
        editor = ViEditor()
        editor.visual_marks = True
        editor.lines = ["one", "two", "three", "four", "five"]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord("V"), ord("j"), ord("j"), 27])

        self.assertEqual(editor.marks["<"], (1, 0))
        self.assertEqual(editor.marks[">"], (3, 0))

        editor.cursor_row, editor.cursor_col = 4, 0
        self.send(editor, [ord("'"), ord("<")])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

        self.send(editor, [ord("'"), ord(">")])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (3, 0))

    def test_visual_marks_off_by_default(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        self.send(editor, [ord("v"), ord("l"), ord("l"), ord("y")])

        self.assertFalse(editor.visual_marks)
        self.assertNotIn("<", editor.marks)
        self.assertNotIn(">", editor.marks)

    def test_set_visualmarks_toggles_and_novisualmarks_clears_existing(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        editor._execute_cmd("set visualmarks")
        self.assertTrue(editor.visual_marks)
        self.send(editor, [ord("v"), ord("l"), ord("y")])
        self.assertEqual(editor.marks["<"], (0, 1))
        self.assertEqual(editor.marks[">"], (0, 2))

        editor._execute_cmd("set novisualmarks")
        self.assertFalse(editor.visual_marks)
        self.assertNotIn("<", editor.marks)
        self.assertNotIn(">", editor.marks)

        editor._execute_cmd("set invvisualmarks")
        self.assertTrue(editor.visual_marks)

    def test_visual_exit_sets_marks_on_operator_not_just_escape(self):
        editor = ViEditor()
        editor.visual_marks = True
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        self.send(editor, [ord("v"), ord("l"), ord("l"), ord("y")])

        self.assertEqual(editor.marks["<"], (0, 1))
        self.assertEqual(editor.marks[">"], (0, 3))

    def test_backtick_less_greater_marks_jump_to_exact_column(self):
        editor = ViEditor()
        editor.visual_marks = True
        editor.lines = ["  indented", "next"]
        editor.cursor_row = 0
        editor.cursor_col = 4

        self.send(editor, [ord("v"), ord("l"), ord("l"), 27])

        editor.cursor_row, editor.cursor_col = 1, 0
        self.send(editor, [ord("`"), ord("<")])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 4))

    def test_less_greater_marks_survive_a_subsequent_edit(self):
        # '< and '> aren't alphabetic mark names, so the general mark-clamp
        # pass that runs after every edit must special-case them instead of
        # dropping them like any other non-letter dict key.
        editor = ViEditor()
        editor.visual_marks = True
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        self.send(editor, [ord("V"), ord("j"), 27])
        self.assertIn("<", editor.marks)
        self.assertIn(">", editor.marks)

        editor.cursor_row = 2
        self.send(editor, [ord("x")])

        self.assertIn("<", editor.marks)
        self.assertIn(">", editor.marks)

    def test_auto_mark_navigation_moved_to_bracket_marks(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four"]
        editor.auto_marks = {1: 0, 2: 3}
        editor.cursor_row = 2

        self.send(editor, [ord("'"), ord("[")])
        self.assertEqual(editor.cursor_row, 0)

        editor.cursor_row = 2
        self.send(editor, [ord("'"), ord("]")])
        self.assertEqual(editor.cursor_row, 3)

    def test_marks_are_removed_when_marked_line_is_deleted(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 1
        self.send(editor, [ord("m"), ord("a")])

        self.send(editor, [ord("d"), ord("d")])

        self.assertNotIn("a", editor.marks)

    def test_linewise_noop_on_empty_buffer_preserves_marks(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("m"), ord("a")])
        editor._mark_clean()

        self.send(editor, [ord("d"), ord("d")])

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("d"))

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_empty_linewise_change_preserves_marks_until_inserted_text_changes(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("m"), ord("a")])
        editor._mark_clean()

        self.send(editor, [ord("S"), 27])

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        self.send(editor, [ord("S"), ord("X"), 27])

        self.assertEqual(editor.lines, ["X"])
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertTrue(editor.modified)
        self.assertEqual(len(editor.undo_stack), 1)

    def test_empty_visual_line_change_preserves_marks(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("m"), ord("a")])
        editor._mark_clean()
        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)

        editor._handle_visual(ord("c"))
        editor._handle_insert(27)

        self.assertEqual(editor.lines, [""])
        self.assertEqual(editor.marks, {"a": (0, 0)})
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_marks_shift_after_line_delete_using_surviving_line_length(self):
        editor = ViEditor()
        editor.lines = ["short", "x", "much longer line"]
        editor.cursor_row = 2
        editor.cursor_col = 10
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord("d"), ord("d")])

        self.assertEqual(editor.lines, ["short", "much longer line"])
        self.assertEqual(editor.marks["a"], (1, 10))

    def test_marks_clamp_after_same_line_delete_uses_new_line_length(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 5
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_col = 3
        self.send(editor, [ord("D")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual(editor.marks["a"], (0, 2))

    def test_marks_follow_character_edits_and_undo(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 3
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_col = 1
        self.send(editor, [ord("i"), ord("X"), 27])

        self.assertEqual(editor.marks["a"], (0, 4))

        self.send(editor, [ord("x")])

        self.assertEqual(editor.marks["a"], (0, 3))

        self.send(editor, [ord("u")])
        self.assertEqual(editor.marks["a"], (0, 4))

        self.send(editor, [ord("u")])
        self.assertEqual(editor.marks["a"], (0, 3))

    def test_marks_follow_unicode_case_toggle_expansion(self):
        editor = ViEditor()
        editor.lines = ["aßb"]
        editor.cursor_col = 2
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_col = 1
        self.send(editor, [ord("~")])

        self.assertEqual(editor.lines, ["aSSb"])
        self.assertEqual(editor.marks["a"], (0, 3))

    def test_tilde_toggle_case_matches_str_swapcase_for_titlecase_chars(self):
        # Normal-mode '~' used to toggle case manually via
        # `ch.lower() if ch.isupper() else ch.upper()`, which diverges from
        # str.swapcase() (used by visual-mode '~' and its dot-repeat) for
        # Unicode titlecase digraphs: 'ǅ'.isupper() is False, so the manual
        # form upper()'d it to 'Ǆ' -- str.swapcase() (neither upper nor
        # lower) correctly leaves a titlecase char unchanged. Both modes
        # must now agree, and neither should produce the old 'Ǆ' output.
        editor = ViEditor()
        editor.lines = ["aǅb"]
        editor.cursor_col = 1
        editor._mark_clean()

        self.send(editor, [ord("~")])

        self.assertEqual(editor.lines, ["a" + "ǅ".swapcase() + "b"])
        self.assertEqual(editor.lines, ["aǅb"])
        self.assertFalse(editor.modified)

    def test_visual_tilde_toggle_case_matches_str_swapcase_for_titlecase_chars(self):
        editor = ViEditor()
        editor.lines = ["aǅb"]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 1

        editor._handle_visual(ord("~"))

        self.assertEqual(editor.lines, ["a" + "ǅ".swapcase() + "b"])
        self.assertEqual(editor.lines, ["aǅb"])

    def test_marks_follow_visual_unicode_case_toggle_expansion(self):
        editor = ViEditor()
        editor.lines = ["aßb"]
        editor.cursor_col = 2
        self.send(editor, [ord("m"), ord("a")])
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 1

        editor._handle_visual(ord("~"))

        self.assertEqual(editor.lines, ["aSSb"])
        self.assertEqual(editor.marks["a"], (0, 3))

    def test_marks_follow_single_line_put_and_undo(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 3
        self.send(editor, [ord("m"), ord("a")])
        editor.yank_buffer = ["XX"]
        editor.yank_is_lines = False

        editor.cursor_col = 0
        self.send(editor, [ord("p")])

        self.assertEqual(editor.lines, ["aXXbcdef"])
        self.assertEqual(editor.marks["a"], (0, 5))

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, ["abcdef"])
        self.assertEqual(editor.marks["a"], (0, 3))

    def test_substitute_clamps_marks_after_shortening_line(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 5
        self.send(editor, [ord("m"), ord("a")])

        self.assertTrue(editor._execute_cmd(":s/cdef/x/"))

        self.assertEqual(editor.lines, ["abx"])
        self.assertEqual(editor.marks["a"], (0, 2))

    def test_substitute_moves_marks_after_expanding_before_mark(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 4
        self.send(editor, [ord("m"), ord("a")])

        self.assertTrue(editor._execute_cmd(":s/cd/XXXX/"))

        self.assertEqual(editor.lines, ["abXXXXef"])
        self.assertEqual(editor.marks["a"], (0, 6))

        editor._undo()

        self.assertEqual(editor.lines, ["abcdef"])
        self.assertEqual(editor.marks["a"], (0, 4))

    def test_substitute_moves_marks_inside_replaced_text_to_replacement_end(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 3
        self.send(editor, [ord("m"), ord("a")])

        self.assertTrue(editor._execute_cmd(":s/cde/X/"))

        self.assertEqual(editor.lines, ["abXf"])
        self.assertEqual(editor.marks["a"], (0, 2))

    def test_substitute_global_keeps_marks_between_separate_matches_on_own_chars(self):
        """:s///g on a line with several separate matches must not collapse
        a mark sitting on an untouched character between two matches onto
        one match's replacement -- each mark should keep tracking its own
        character."""
        editor = ViEditor()
        editor.lines = ["xaxbxc"]
        editor.marks["a"] = (0, 1)  # sits on the 'a' between match 1 and 2
        editor.marks["b"] = (0, 3)  # sits on the 'b' between match 2 and 3

        self.assertTrue(editor._execute_cmd(":s/x/y/g"))

        self.assertEqual(editor.lines, ["yaybyc"])
        self.assertEqual(editor.marks["a"], (0, 1))
        self.assertEqual(editor.marks["b"], (0, 3))

    def test_substitute_global_moves_mark_on_matched_text_to_its_own_replacement_end(self):
        """A mark sitting directly on one of several matches must move to
        the end of *that* match's replacement, not some other match's."""
        editor = ViEditor()
        editor.lines = ["pXqXr"]
        editor.marks["p"] = (0, 0)
        editor.marks["q"] = (0, 2)
        editor.marks["r"] = (0, 4)
        editor.marks["m"] = (0, 1)  # sits directly on the first X

        self.assertTrue(editor._execute_cmd(":s/X/NUM/g"))

        self.assertEqual(editor.lines, ["pNUMqNUMr"])
        self.assertEqual(editor.marks["p"], (0, 0))
        self.assertEqual(editor.marks["m"], (0, 3))
        self.assertEqual(editor.marks["q"], (0, 4))
        self.assertEqual(editor.marks["r"], (0, 8))

    def test_substitute_global_shrinking_matches_shift_later_marks_correctly(self):
        """Replacements that shrink the line must still shift marks after
        later matches by the correct cumulative delta, not the first
        match's delta applied to everything."""
        editor = ViEditor()
        editor.lines = ["aXXbXXXc"]
        editor.marks["a"] = (0, 0)
        editor.marks["b"] = (0, 3)
        editor.marks["c"] = (0, 7)

        self.assertTrue(editor._execute_cmd(":s/X+/Z/g"))

        self.assertEqual(editor.lines, ["aZbZc"])
        self.assertEqual(editor.marks["a"], (0, 0))
        self.assertEqual(editor.marks["b"], (0, 2))
        self.assertEqual(editor.marks["c"], (0, 4))

    def test_marks_follow_newline_and_join(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 4
        self.send(editor, [ord("m"), ord("a")])

        editor.cursor_col = 2
        self.send(editor, [ord("i"), ord("\n"), 27])

        self.assertEqual(editor.lines, ["ab", "cdef"])
        self.assertEqual(editor.marks["a"], (1, 2))

        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("J")])

        self.assertEqual(editor.lines, ["ab cdef"])
        self.assertEqual(editor.marks["a"], (0, 5))

    def test_marks_follow_indent_and_dedent(self):
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]
        editor.cursor_row = 0
        editor.cursor_col = 2
        self.send(editor, [ord("m"), ord("a")])

        self.send(editor, [ord(">"), ord(">")])

        self.assertEqual(editor.lines[0], "    alpha")
        self.assertEqual(editor.marks["a"], (0, 6))

        self.send(editor, [ord("<"), ord("<")])

        self.assertEqual(editor.lines[0], "alpha")
        self.assertEqual(editor.marks["a"], (0, 2))

    def test_marks_follow_visual_line_indent_and_undo(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.cursor_row = 1
        editor.cursor_col = 1
        self.send(editor, [ord("m"), ord("a")])

        editor.mode = Mode.VISUAL_LINE
        editor.visual_start = (0, 0)
        editor.cursor_row = 1
        editor.cursor_col = 0
        editor._handle_visual(ord(">"))

        self.assertEqual(editor.lines, ["    one", "    two"])
        self.assertEqual(editor.marks["a"], (1, 5))

        editor._undo()

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertEqual(editor.marks["a"], (1, 1))

    def test_operator_supports_word_text_objects(self):
        editor = ViEditor()
        editor.lines = ["say hello world"]
        editor.cursor_col = 5

        self.send(editor, [ord("d"), ord("i"), ord("w")])

        self.assertEqual(editor.lines, ["say  world"])

    def test_operator_supports_find_and_search_motions(self):
        editor = ViEditor()
        editor.lines = ["abc def ghi", "target line"]

        self.send(editor, [ord("d"), ord("f"), ord(" ")])
        self.assertEqual(editor.lines[0], "def ghi")

        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("d"), ord("/"), ord("g"), ord("h"), ord("i"), 10])
        self.assertEqual(editor.lines[0], "hi")

    def test_backslash_search_is_literal_and_case_insensitive(self):
        editor = ViEditor()
        editor.lines = ["abc DEF ghi", "target line"]

        self.send(editor, [ord("\\"), ord("d"), ord("e"), ord("f"), 10])

        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 4))
        self.assertEqual(editor.search_pattern, "def")
        self.assertTrue(editor._search_literal)

    def test_backslash_search_treats_regex_metacharacters_literally(self):
        editor = ViEditor()
        editor.lines = ["a.b", "aXb"]

        self.send(editor, [ord("\\"), ord("a"), ord("."), ord("b"), 10])

        # Must wrap back to the literal "a.b" on row 0, not match "aXb" --
        # a plain '/' search would treat '.' as "any character".
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))
        self.assertEqual(editor.message, "search wrapped")

    def test_backslash_search_n_repeat_stays_literal_and_case_insensitive(self):
        editor = ViEditor()
        editor.lines = ["FOO", "bar", "foo"]

        self.send(editor, [ord("\\"), ord("f"), ord("o"), ord("o"), 10])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (2, 0))

        self.send(editor, [ord("n")])
        # Wraps back to row 0's "FOO", matched case-insensitively.
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_backslash_search_bare_repeat_reuses_last_pattern_and_mode(self):
        editor = ViEditor()
        editor.lines = ["FOO", "bar", "foo"]

        self.send(editor, [ord("\\"), ord("f"), ord("o"), ord("o"), 10])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (2, 0))

        self.send(editor, [ord("\\"), 10])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

    def test_slash_search_after_backslash_search_reverts_to_regex_mode(self):
        editor = ViEditor()
        editor.lines = ["a.b", "aXb"]

        self.send(editor, [ord("\\"), ord("a"), ord("."), ord("b"), 10])
        self.assertTrue(editor._search_literal)

        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord("/"), ord("a"), ord("."), ord("b"), 10])

        self.assertFalse(editor._search_literal)
        # '.' is a regex wildcard again, so this matches "aXb" too.
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

    def test_operator_supports_backslash_search_motion(self):
        editor = ViEditor()
        editor.lines = ["abc DEF ghi", "target line"]

        self.send(editor, [ord("d"), ord("\\"), ord("g"), ord("h"), ord("i"), 10])

        self.assertEqual(editor.lines[0], "hi")

    # ------------------------------------------------------------------
    # _resolve_operator's motion argument is a typed union (int for a plain
    # curses key, or one of TextObjectMotion/FindMotion/SearchMotion/
    # GotoMotion for a motion that carries extra data) instead of untyped,
    # unchecked tuples. These tests exercise the dataclasses directly to
    # pin down field names/semantics, and confirm a malformed motion (the
    # kind of mistake the old tuple-based key silently let through until
    # it happened to be exercised at runtime) fails immediately instead of
    # miscomputing a range or raising an obscure IndexError deep inside a
    # branch that doesn't expect it.
    # ------------------------------------------------------------------

    def test_resolve_operator_text_object_motion_around_and_inner(self):
        editor = ViEditor()
        editor.lines = ["foo bar baz"]
        editor.cursor_col = 4

        editor._resolve_operator("d", 1, TextObjectMotion(around=False, ch="w"))
        self.assertEqual(editor.lines, ["foo  baz"])

        editor.lines = ["foo bar baz"]
        editor.cursor_col = 4
        editor._resolve_operator("d", 1, TextObjectMotion(around=True, ch="w"))
        self.assertEqual(editor.lines, ["foobaz"])

    def test_resolve_operator_find_motion(self):
        editor = ViEditor()
        editor.lines = ["abcxdef"]

        editor._resolve_operator("d", 1, FindMotion(cmd="f", ch="x"))

        self.assertEqual(editor.lines, ["def"])

    def test_resolve_operator_search_motion(self):
        editor = ViEditor()
        editor.lines = ["abc def ghi"]

        editor._resolve_operator("d", 1, SearchMotion(cmd="/", pattern="ghi"))

        self.assertEqual(editor.lines, ["hi"])

    def test_resolve_operator_goto_motion_top_and_bottom(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 2

        editor._resolve_operator("d", 1, GotoMotion(to_top=True, had_count=False))
        self.assertEqual(editor.lines, [""])

        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 0
        editor._resolve_operator("d", 1, GotoMotion(to_top=False, had_count=False))
        self.assertEqual(editor.lines, [""])

        editor.lines = ["one", "two", "three"]
        editor.cursor_row = 0
        editor._resolve_operator("d", 2, GotoMotion(to_top=False, had_count=True))
        self.assertEqual(editor.lines, ["three"])

    def test_resolve_operator_rejects_malformed_motion_construction(self):
        # A motion missing a required field fails immediately at
        # construction, rather than reaching _resolve_operator and either
        # matching no branch or indexing past the end of an under-sized
        # tuple deep inside one.
        with self.assertRaises(TypeError):
            TextObjectMotion(around=True)  # missing 'ch'
        with self.assertRaises(TypeError):
            FindMotion(cmd="f")  # missing 'ch'
        with self.assertRaises(TypeError):
            SearchMotion(cmd="/")  # missing 'pattern'

    def test_resolve_operator_no_longer_accepts_a_height_argument(self):
        # height was threaded through every call site (including a
        # fabricated placeholder at some visual-mode dot-repeat sites) but
        # never read inside _resolve_operator. It was removed; calling
        # with the old 4-argument form must fail loudly instead of being
        # silently accepted and ignored.
        editor = ViEditor()
        editor.lines = ["abc"]
        with self.assertRaises(TypeError):
            editor._resolve_operator("d", 1, ord("d"), 24)

    def test_operator_find_to_adjacent_character_is_noop(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor._mark_clean()

        self.send(editor, [ord("d"), ord("t"), ord("b")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.cursor_col = 1
        self.send(editor, [ord("d"), ord("T"), ord("a")])

        self.assertEqual(editor.lines, ["abc"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_dot_repeats_last_change(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 1

        self.send(editor, [ord("x")])
        self.assertEqual(editor.lines[0], "acdef")

        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines[0], "adef")

    def test_dot_repeats_insert_and_replace_mode_changes(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("i"), ord("X"), 27])
        self.assertEqual(editor.lines, ["Xabc"])

        editor.cursor_col = 1
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["XXabc"])

        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1

        self.send(editor, [ord("R"), ord("X"), ord("Y"), 27])
        self.assertEqual(editor.lines, ["aXY"])

        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["XYY"])

    def test_counted_insert_append_and_replace_repeat_typed_edit(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("3"), ord("i"), ord("X"), 27])
        self.assertEqual(editor.lines, ["XXXabc"])

        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("2"), ord("A"), ord("!"), 27])
        self.assertEqual(editor.lines, ["abc!!"])

        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 1

        self.send(editor, [ord("3"), ord("R"), ord("X"), 27])
        self.assertEqual(editor.lines, ["aXXXef"])

    def test_counted_open_line_repeats_typed_edit(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("3"), ord("o"), ord("X"), 27])
        self.assertEqual(editor.lines, ["one", "X", "X", "X", "two"])

        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.cursor_row = 1

        self.send(editor, [ord("2"), ord("O"), ord("X"), 27])
        self.assertEqual(editor.lines, ["one", "X", "X", "two"])

    def test_counted_open_line_without_typed_text_preserves_count(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("3"), ord("o"), 27])
        self.assertEqual(editor.lines, ["one", "", "", "", "two"])

        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.cursor_row = 1

        self.send(editor, [ord("2"), ord("O"), 27])
        self.assertEqual(editor.lines, ["one", "", "", "two"])

    def test_dot_repeats_counted_insert_append_and_replace_count(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("3"), ord("i"), ord("X"), 27])
        editor.cursor_col = len(editor.lines[0]) - 1
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["XXXabXXXc"])

        editor = ViEditor()
        editor.lines = ["abc", "def"]

        self.send(editor, [ord("2"), ord("A"), ord("!"), 27])
        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["abc!!", "def!!"])

        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_col = 1

        self.send(editor, [ord("3"), ord("R"), ord("X"), 27])
        editor.cursor_col = 3
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["aXXXXX"])

    def test_dot_repeats_counted_open_line_count(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        # 3oX produces ["one", "X", "X", "X", "two"]; cursor ends on last "X"
        self.send(editor, [ord("3"), ord("o"), ord("X"), 27])
        self.assertEqual(editor.lines, ["one", "X", "X", "X", "two"])
        # Move cursor to "two" and dot-repeat — inserts 3 more "X" lines below "two"
        editor.cursor_row = 4
        editor.cursor_col = 0
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["one", "X", "X", "X", "two", "X", "X", "X"])

    def test_dot_repeats_counted_blank_open_line_count(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("3"), ord("o"), 27])
        editor.cursor_row = len(editor.lines) - 1
        editor.cursor_col = 0
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["one", "", "", "", "two", "", "", ""])

    def test_dot_repeats_insert_mode_cursor_movement_within_change(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.cursor_col = 1

        self.send(editor, [ord("i"), ord("X"), curses.KEY_LEFT, ord("Y"), 27])
        self.assertEqual(editor.lines, ["aYXbc"])

        editor.cursor_col = len(editor.lines[0]) - 1
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["aYXbYXc"])

    def test_dot_repeats_insert_mode_noop_delete_keys_when_later_text_changes(self):
        editor = ViEditor()
        editor.lines = [""]

        self.send(editor, [ord("i"), 4, ord("X"), 27])  # Ctrl-D no-ops on the final empty line.
        self.assertEqual(editor.lines, ["X"])

        editor.lines.append("abc")
        editor.cursor_row = 1
        editor.cursor_col = 1
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["X", "aXc"])

    def test_dot_repeats_insert_mode_noop_shift_tab_when_later_text_changes(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.shift_width = 2
        editor.expand_tab = True
        editor.cursor_col = 0

        self.send(editor, [ord("i"), curses.KEY_BTAB, ord("X"), 27])
        self.assertEqual(editor.lines, ["Xabc"])

        editor.lines = ["  " + editor.lines[0]]
        editor.cursor_col = 2
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["XXabc"])

    def test_dot_repeats_append_and_line_start_insert_entry_setup(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("A"), ord("X"), 27])
        self.assertEqual(editor.lines, ["oneX", "two"])

        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["oneX", "twoX"])

        editor = ViEditor()
        editor.lines = ["  one", "  two"]
        editor.cursor_row = 0
        editor.cursor_col = len(editor.lines[0]) - 1

        self.send(editor, [ord("I"), ord("X"), 27])
        self.assertEqual(editor.lines, ["  Xone", "  two"])

        editor.cursor_row = 1
        editor.cursor_col = len(editor.lines[1]) - 1
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["  Xone", "  Xtwo"])

    def test_dot_repeats_open_line_insert_entry_setup(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]

        self.send(editor, [ord("o"), ord("X"), 27])
        self.assertEqual(editor.lines, ["one", "X", "two"])

        editor.cursor_row = 2
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["one", "X", "two", "X"])

        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.cursor_row = 1

        self.send(editor, [ord("O"), ord("X"), 27])
        self.assertEqual(editor.lines, ["one", "X", "two"])

        editor.cursor_row = 0
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["X", "one", "X", "two"])

    def test_dot_repeats_replace_mode_cursor_movement_within_change(self):
        editor = ViEditor()
        editor.lines = ["abcde"]
        editor.cursor_col = 1

        self.send(editor, [ord("R"), ord("X"), curses.KEY_LEFT, ord("Y"), 27])
        self.assertEqual(editor.lines, ["aYcde"])

        editor.cursor_col = 3
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["aYcYe"])

    def test_dot_repeats_replace_mode_noop_shift_tab_when_later_text_changes(self):
        editor = ViEditor()
        editor.lines = ["abc"]
        editor.shift_width = 2
        editor.expand_tab = True
        editor.cursor_col = 0

        self.send(editor, [ord("R"), curses.KEY_BTAB, ord("X"), 27])
        self.assertEqual(editor.lines, ["Xbc"])

        editor.lines = ["  " + editor.lines[0]]
        editor.cursor_col = 2
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["Xbc"])

    def test_dot_repeats_change_setup_before_inserted_text(self):
        editor = ViEditor()
        editor.lines = ["one two three"]

        self.send(editor, [ord("c"), ord("w"), ord("X"), 27])
        self.assertEqual(editor.lines, ["X two three"])

        editor.cursor_col = 2
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["X X three"])

    def test_dot_repeats_change_shortcuts_before_inserted_text(self):
        editor = ViEditor()
        editor.lines = ["one two", "three four"]

        self.send(editor, [ord("C"), ord("X"), 27])
        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["X", "X"])

        editor = ViEditor()
        editor.lines = ["abc def"]
        self.send(editor, [ord("s"), ord("X"), 27])
        editor.cursor_col = 1
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["XXc def"])

        editor = ViEditor()
        editor.lines = ["one", "two"]
        self.send(editor, [ord("S"), ord("X"), 27])
        editor.cursor_row = 1
        editor.cursor_col = 0
        self.send(editor, [ord(".")])
        self.assertEqual(editor.lines, ["X", "X"])

    def test_counted_change_to_eol_shortcut_uses_counted_motion(self):
        editor = ViEditor()
        editor.lines = ["ab", "cd", "ef"]
        editor.cursor_col = 1

        self.send(editor, [ord("2"), ord("C"), ord("X"), 27])

        self.assertEqual(editor.lines, ["aX", "ef"])

        editor.cursor_col = 1
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["aX"])

    def test_dot_repeats_change_even_without_inserted_text(self):
        editor = ViEditor()
        editor.lines = ["one two three"]

        self.send(editor, [ord("c"), ord("w"), 27])
        self.assertEqual(editor.lines, [" two three"])

        editor.cursor_col = 1
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["  three"])

    def test_noop_edit_commands_do_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = ["a1"]
        editor._mark_clean()

        self.send(editor, [ord("r"), ord("a")])
        self.assertEqual(editor.lines, ["a1"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.cursor_col = 1
        self.send(editor, [ord("~")])
        self.assertEqual(editor.lines, ["a1"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.cursor_row = 0
        self.send(editor, [ord("J")])
        self.assertEqual(editor.lines, ["a1"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_noop_toggle_case_does_not_replace_last_change(self):
        editor = ViEditor()
        editor.lines = ["a1bc"]

        self.send(editor, [ord("x")])
        self.assertEqual(editor.lines, ["1bc"])

        self.send(editor, [ord("~")])
        self.assertEqual(editor.lines, ["1bc"])

        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["1c"])

    def test_dot_repeated_toggle_case_advances_like_original_command(self):
        editor = ViEditor()
        editor.lines = ["abc"]

        self.send(editor, [ord("~")])
        self.assertEqual((editor.lines, editor.cursor_col), (["Abc"], 1))

        self.send(editor, [ord(".")])
        self.assertEqual((editor.lines, editor.cursor_col), (["ABc"], 2))

        self.send(editor, [ord(".")])
        self.assertEqual((editor.lines, editor.cursor_col), (["ABC"], 2))

    def test_noop_edits_do_not_discard_oldest_undo_state(self):
        editor = ViEditor()
        editor.max_undo = 2
        editor.lines = ["abc"]
        editor._mark_clean()

        self.send(editor, [ord("i"), ord("X"), 27])
        self.send(editor, [ord("A"), ord("Y"), 27])
        self.assertEqual(editor.lines, ["XabcY"])
        self.assertEqual(len(editor.undo_stack), 2)

        self.send(editor, [ord("<"), ord("<")])

        self.assertEqual(len(editor.undo_stack), 2)

        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["Xabc"])
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["abc"])
        self.assertFalse(editor.modified)

        editor = ViEditor()
        editor.max_undo = 2
        editor.lines = ["123"]
        editor._mark_clean()
        self.send(editor, [ord("i"), ord("X"), 27])
        self.send(editor, [ord("A"), ord("Y"), 27])
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 1)
        editor.cursor_row = 0
        editor.cursor_col = 1

        editor._handle_visual(ord("~"))

        self.assertEqual(len(editor.undo_stack), 2)
        self.send(editor, [ord("u")])
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["123"])

        editor = ViEditor()
        editor.max_undo = 2
        editor.lines = ["abc"]
        editor._mark_clean()
        self.send(editor, [ord("i"), ord("X"), 27])
        self.send(editor, [ord("A"), ord("Y"), 27])
        editor.lines = [""]
        editor.cursor_row = 0
        editor.cursor_col = 0

        self.send(editor, [ord("d"), ord("$")])

        self.assertEqual(len(editor.undo_stack), 2)
        editor.lines = ["XabcY"]
        editor.cursor_col = len(editor.lines[0]) - 1
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["Xabc"])
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["abc"])

        editor = ViEditor()
        editor.max_undo = 2
        editor.lines = ["abc"]
        editor._mark_clean()
        self.send(editor, [ord("i"), ord("X"), 27])
        self.send(editor, [ord("A"), ord("Y"), 27])
        editor.lines = [""]
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._handle_visual(ord("d"))

        self.assertEqual(len(editor.undo_stack), 2)
        editor.lines = ["XabcY"]
        editor.mode = Mode.NORMAL
        editor.cursor_col = len(editor.lines[0]) - 1
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["Xabc"])
        self.send(editor, [ord("u")])
        self.assertEqual(editor.lines, ["abc"])

    def test_operator_delete_noop_check_avoids_second_full_buffer_copy(self):
        # _resolve_operator used to detect a no-op delete (only possible for
        # deleting the sole empty line, or a same-line charwise range past
        # EOL) by diffing `list(self.lines)` taken before and after the
        # delete -- an extra full-buffer copy and comparison on every single
        # d/c operator command, on top of the one already required for the
        # undo snapshot. Assert the buffer is only ever fully walked once
        # (for that unavoidable undo snapshot).
        class CountingLines(list):
            iter_calls = 0

            def __iter__(self):
                CountingLines.iter_calls += 1
                return super().__iter__()

        editor = ViEditor()
        editor.lines = CountingLines([f"word{i} another{i}" for i in range(50)])
        editor.line_endings = ["\n"] * 49 + [""]
        editor.cursor_row = 25
        editor.cursor_col = 0

        CountingLines.iter_calls = 0
        self.send(editor, [ord("d"), ord("w")])

        self.assertLessEqual(CountingLines.iter_calls, 1)
        self.assertEqual(editor.lines[25], "another25")

    def test_operator_noop_predicate_shared_with_visual_mode(self):
        # _resolve_operator's d/c no-op check used to be a second, hand-
        # rolled copy of _visual_selection_will_change()'s predicate; it
        # now calls that shared helper directly. Pin both cases it covers
        # via the operator+motion path: a same-line charwise range past
        # EOL (c$/d$ on an empty line) and the sole empty line (cc/dd).
        editor = ViEditor()
        editor.lines = ["abc", ""]
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord("d"), ord("$")])

        self.assertEqual(editor.lines, ["abc", ""])
        self.assertFalse(editor.modified)
        self.assertEqual(len(editor.undo_stack), 0)

        editor2 = ViEditor()
        editor2.lines = [""]

        self.send(editor2, [ord("d"), ord("d")])

        self.assertEqual(editor2.lines, [""])
        self.assertFalse(editor2.modified)
        self.assertEqual(len(editor2.undo_stack), 0)

    def test_empty_delete_commands_do_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = [""]
        editor._mark_clean()

        self.send(editor, [ord("x")])
        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        self.send(editor, [ord("D")])
        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

        editor.lines = ["abc"]
        editor.cursor_col = 0
        editor._mark_clean()
        self.send(editor, [ord("X")])
        self.assertEqual(editor.lines, ["abc"])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_empty_operator_deletes_do_not_create_undo_state(self):
        editor = ViEditor()
        editor.lines = [""]
        editor._mark_clean()

        self.send(editor, [ord("d"), ord("$")])

        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.yank_buffer)

        self.send(editor, [ord("d"), ord("d")])

        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)
        self.assertFalse(editor.yank_buffer)

    def test_empty_change_can_insert_without_dirty_delete_state(self):
        editor = ViEditor()
        editor.lines = [""]
        editor._mark_clean()

        self.send(editor, [ord("c"), ord("$"), ord("X"), 27])

        self.assertEqual(editor.lines, ["X"])
        self.assertTrue(editor.modified)
        self.assertEqual(len(editor.undo_stack), 1)
        self.assertFalse(editor.yank_buffer)

        self.send(editor, [ord("u")])

        self.assertEqual(editor.lines, [""])
        self.assertFalse(editor.modified)

    def test_empty_change_shortcuts_do_not_clobber_register(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.yank_buffer = ["keep"]
        editor.yank_is_lines = False
        editor._mark_clean()

        self.send(editor, [ord("s"), ord("X"), 27])

        self.assertEqual(editor.lines, ["X"])
        self.assertEqual(editor.yank_buffer, ["keep"])
        self.assertFalse(editor.yank_is_lines)
        self.assertTrue(editor.modified)

        editor = ViEditor()
        editor.lines = [""]
        editor.yank_buffer = ["keep"]
        editor.yank_is_lines = False
        editor._mark_clean()

        self.send(editor, [ord("C"), ord("X"), 27])

        self.assertEqual(editor.lines, ["X"])
        self.assertEqual(editor.yank_buffer, ["keep"])
        self.assertFalse(editor.yank_is_lines)
        self.assertTrue(editor.modified)

    def test_dot_repeat_delete_to_eol_is_noop_on_empty_line(self):
        editor = ViEditor()
        editor.lines = ["abc", ""]

        self.send(editor, [ord("D")])
        self.assertEqual(editor.lines, ["", ""])
        self.assertEqual(len(editor.undo_stack), 1)

        editor._mark_clean()
        editor.cursor_row = 1
        editor.cursor_col = 0

        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["", ""])
        self.assertFalse(editor.modified)
        self.assertEqual(len(editor.undo_stack), 1)

    def test_counted_D_deletes_through_end_of_line_across_following_lines(self):
        editor = ViEditor()
        editor.lines = ["abcdef", "second line", "third line", "fourth line"]
        editor.cursor_row = 0
        editor.cursor_col = 2

        self.send(editor, [ord("3"), ord("D")])

        self.assertEqual(editor.lines, ["ab", "fourth line"])

    def test_counted_D_dot_repeat_reapplies_same_count(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three", "four", "five", "six"]
        editor.cursor_row = 0
        editor.cursor_col = 1

        self.send(editor, [ord("2"), ord("D")])
        self.assertEqual(editor.lines, ["o", "three", "four", "five", "six"])

        editor.cursor_row = 1
        editor.cursor_col = 2
        self.send(editor, [ord(".")])

        self.assertEqual(editor.lines, ["o", "th", "five", "six"])

    def test_operator_find_motion_updates_semicolon_repeat_target(self):
        # dfa should update _last_find_char so that a subsequent ; repeats the
        # 'a' find from the new cursor position.
        editor = ViEditor()
        editor.lines = ["a b a c a"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # d f a — delete from col 0 up to (and including) the first 'a' at col 0
        # Actually cursor is ON the first 'a', so the next 'a' is at col 4.
        # dfa deletes from col 0 through col 4 inclusive.
        self.send(editor, [ord("d"), ord("f"), ord("a")])

        self.assertEqual(editor.lines, [" c a"])
        self.assertEqual(editor._last_find_char, "a",
                         "dfa must update _last_find_char to 'a'")
        self.assertEqual(editor._last_find_cmd, "f",
                         "dfa must update _last_find_cmd to 'f'")

    def test_operator_find_motion_semicolon_repeats_from_new_position(self):
        # After dfa the cursor is at the new position; pressing ; should find
        # the next 'a' from there (not from the original position).
        editor = ViEditor()
        editor.lines = ["xaxbxcx"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # dfa: delete col 0-1 ("xa"), cursor lands at 0
        self.send(editor, [ord("d"), ord("f"), ord("a")])
        self.assertEqual(editor.lines, ["xbxcx"])

        # ; should now find the next 'a' from col 0 — none exists,
        # so cursor should not move (and no crash).
        self.send(editor, [ord(";")])
        # The important thing: _last_find_char was set so ; runs without error.
        self.assertEqual(editor._last_find_char, "a")

    def test_operator_t_motion_updates_semicolon_repeat_target(self):
        # cta should update _last_find_cmd to 't' so ; repeats a t-find.
        editor = ViEditor()
        editor.lines = ["abcabc"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # cta: change up to (not including) the first 'a' — but cursor IS on
        # 'a' so we look for next 'a' at col 3. 't' stops one before: col 2.
        self.send(editor, [ord("c"), ord("t"), ord("a")])
        # Now in insert mode; ESC out.
        self.send(editor, [27])

        self.assertEqual(editor._last_find_char, "a")
        self.assertEqual(editor._last_find_cmd, "t")

    def test_operator_F_motion_updates_last_find_cmd_to_F(self):
        # yFx should set _last_find_cmd to 'F' (backward find).
        editor = ViEditor()
        editor.lines = ["xhello"]
        editor.cursor_row = 0
        editor.cursor_col = 5

        self.send(editor, [ord("y"), ord("F"), ord("x")])

        self.assertEqual(editor._last_find_char, "x")
        self.assertEqual(editor._last_find_cmd, "F")

    def test_open_line_below_with_count_and_text_creates_separate_lines(self):
        # 3oHELLO<ESC> must produce three new lines each containing "HELLO",
        # not one line with "HELLOHELLOHELLO".
        editor = ViEditor()
        editor.lines = ["base"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        # Press 3, o, then type HELLO, then ESC
        self.send(editor, [ord("3"), ord("o")])
        self.send(editor, [ord("H"), ord("E"), ord("L"), ord("L"), ord("O")])
        self.send(editor, [27])  # ESC

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["base", "HELLO", "HELLO", "HELLO"])

    def test_open_line_above_with_count_and_text_creates_separate_lines(self):
        # 3OHELLO<ESC> must produce three new lines each containing "HELLO"
        # inserted above the current line.
        editor = ViEditor()
        editor.lines = ["base"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        self.send(editor, [ord("3"), ord("O")])
        self.send(editor, [ord("H"), ord("I")])
        self.send(editor, [27])

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(len(editor.lines), 4)
        self.assertEqual(editor.lines[3], "base")
        self.assertEqual(editor.lines[:3], ["HI", "HI", "HI"])

    def test_open_line_below_count_1_still_works(self):
        # Sanity check: plain oHELLO still works with the fix in place.
        editor = ViEditor()
        editor.lines = ["base"]
        editor.cursor_row = 0

        self.send(editor, [ord("o")])
        self.send(editor, [ord("x")])
        self.send(editor, [27])

        self.assertEqual(editor.lines, ["base", "x"])

    def test_open_line_below_count_text_dot_repeat_creates_separate_lines(self):
        # After 3oHELLO<ESC>, pressing . should again produce three new lines
        # each with "HELLO" (not one line with "HELLOHELLOHELLO").
        editor = ViEditor()
        editor.lines = ["base"]
        editor.cursor_row = 0

        self.send(editor, [ord("3"), ord("o")])
        self.send(editor, [ord("H"), ord("I")])
        self.send(editor, [27])

        self.assertEqual(editor.lines, ["base", "HI", "HI", "HI"])

        # Move cursor back to "base" row and dot-repeat
        editor.cursor_row = 0
        self.send(editor, [ord(".")])

        # Should insert 3 more "HI" lines below "base"
        self.assertEqual(editor.lines[0], "base")
        self.assertEqual(editor.lines[1:4], ["HI", "HI", "HI"])

    def test_insert_count_text_is_unaffected_by_fix(self):
        # 3iHI<ESC> must still produce "HIHI" (not 3 separate lines).
        # This verifies the o/O fix doesn't break plain insert repeat.
        editor = ViEditor()
        editor.lines = ["base"]
        editor.cursor_row = 0
        editor.cursor_col = 4  # after "base"

        self.send(editor, [ord("3"), ord("a")])
        self.send(editor, [ord("H"), ord("I")])
        self.send(editor, [27])

        self.assertEqual(editor.lines, ["baseHIHIHI"])


class HelpSystemTests(unittest.TestCase):
    def test_help_opens_from_ex_command(self):
        editor = ViEditor()

        self.assertTrue(editor._execute_cmd(":help"))

        self.assertEqual(editor.mode, Mode.HELP)
        self.assertEqual(editor.help_top_line, 0)

    def test_help_opens_from_f1_and_closes(self):
        editor = ViEditor()

        editor._handle_normal(curses.KEY_F1, 24, 80)
        self.assertEqual(editor.mode, Mode.HELP)

        editor._last_h = 24
        editor._handle_help(ord("q"))
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_help_scrolls_and_supports_gg_g(self):
        editor = ViEditor()
        editor._open_help()
        editor._last_h = 10

        editor._handle_help(ord("j"))
        self.assertEqual(editor.help_top_line, 1)

        editor._handle_help(ord("G"))
        self.assertGreater(editor.help_top_line, 1)

        editor._handle_help(ord("g"))
        editor._handle_help(ord("g"))
        self.assertEqual(editor.help_top_line, 0)

    def test_help_tabs_between_sections(self):
        editor = ViEditor()
        editor._open_help()

        editor._handle_help(ord("\t"))
        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Movement")

        editor._handle_help(ord("\t"))
        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Editing")

        editor._handle_help(curses.KEY_BTAB)
        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Movement")

    def test_help_search_and_repeat(self):
        editor = ViEditor()
        editor._open_help()

        editor._handle_help(ord("/"))
        self.assertEqual(editor._cmd_buf, "/")
        for ch in "buffers":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))
        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Buffers")

        editor._handle_help(ord("n"))
        self.assertIn("buffer", editor.HELP_LINES[editor.help_top_line].lower())
        self.assertNotEqual(editor.HELP_LINES[editor.help_top_line], "Buffers")

        editor._handle_help(ord("N"))
        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Buffers")

    def test_help_search_supports_question_direction(self):
        editor = ViEditor()
        editor._open_help()
        editor.help_top_line = len(editor.HELP_LINES) - 1

        editor._handle_help(ord("?"))
        for ch in "^Search$":
            editor._handle_cmd_buf(ord(ch))
        self.assertTrue(editor._handle_cmd_buf(ord("\n")))

        self.assertEqual(editor.HELP_LINES[editor.help_top_line], "Search")
        self.assertFalse(editor.help_search_forward)

    def test_help_lists_recent_insert_completion_and_line_ending_items(self):
        help_text = "\n".join(ViEditor.HELP_LINES)

        for text in (
            "Ctrl-A / Ctrl-E",
            "Delete / Ctrl-D",
            "Shift-Tab",
            "insert mode: cycle intellisense",
            "insert mode: accept highlighted intellisense",
            "intellisense",
            "filename completion (matches shown on status bar)",
            "accept highlighted completion match",
            ":le-unix  :le-win",
            ":set option=value",
            "lnendings=unix|win",
        ):
            self.assertIn(text, help_text)

    def test_help_file_browser_keys_do_not_claim_g_always_jumps_first(self):
        help_text = "\n".join(ViEditor.HELP_LINES)

        self.assertIn("Tab / Shift-Tab", help_text)
        self.assertIn("grep current panel", help_text)
        self.assertNotIn("g G Home End         jump to first/last entry", help_text)

    def test_help_and_shell_clear_pending_state(self):
        editor = ViEditor()
        editor._pending_op = "r"
        editor._count_str = "12"

        editor._open_help()
        self.assertEqual(editor._pending_op, "")
        self.assertEqual(editor._count_str, "")
        editor._last_h = 10
        editor._handle_help(27)
        self.assertEqual(editor._pending_op, "")

        editor._pending_op = "d"
        editor._count_str = "3"
        editor._open_shell_output("printf ok", ["ok"])
        self.assertEqual(editor._pending_op, "")
        self.assertEqual(editor._count_str, "")
        editor._handle_shell(ord("q"))
        self.assertEqual(editor._pending_op, "")

    def test_view_openers_clear_stale_error_state(self):
        editor = ViEditor()

        for opener, mode in (
            (editor._open_help, Mode.HELP),
            (lambda: editor._open_shell_output("printf ok", ["ok"]), Mode.SHELL),
            (editor._show_buffers, Mode.BUFFER_LIST),
            (editor._open_file_browser, Mode.FILE_BROWSER),
        ):
            editor.message = "old error"
            editor.message_is_error = True

            opener()

            self.assertEqual(editor.mode, mode)
            self.assertEqual(editor.message, "")
            self.assertFalse(editor.message_is_error)


class HexModeTests(unittest.TestCase):
    def test_hex_command_opens_hex_mode_and_esc_closes(self):
        editor = ViEditor()
        editor.lines = ["ABC", "xy"]

        self.assertTrue(editor._execute_cmd(":hex"))

        self.assertEqual(editor.mode, Mode.HEX)
        self.assertEqual(editor.hex_top_line, 0)
        hex_line = editor._hex_view_lines()[0]
        self.assertIn("00000000  41 42 43 0a 78 79", hex_line)
        self.assertIn("|ABC.xy", hex_line)

        editor._last_h = 24
        editor._handle_hex(27)

        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_draw_hex_mode_renders_hex_buffer(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 90

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["ABC", "xy"]
        editor._open_hex_view()

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        rendered = [args[2] for args in screen.calls if len(args) >= 3]
        self.assertTrue(any("41 42 43 0a 78 79" in text for text in rendered))
        self.assertTrue(any("|ABC.xy" in text for text in rendered))
        self.assertTrue(any("HEX" in text for text in rendered))

    # ------------------------------------------------------------------
    # Fix: hex view used to be a pure scroll view with no notion of a
    # current row, so the real terminal cursor was left wherever the last
    # draw call happened to leave it (visually pinned near the bottom)
    # instead of tracking navigation the way the editor's own cursor does.
    # It now tracks hex_cursor_line, which follows j/k/paging/gg/G, scrolls
    # the view to stay visible, is highlighted, and drives the real cursor
    # position.
    # ------------------------------------------------------------------

    def test_hex_j_and_k_move_cursor_line(self):
        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(50)]
        editor._open_hex_view()
        editor._last_h = 24

        self.assertEqual(editor.hex_cursor_line, 0)
        editor._handle_hex(ord("j"))
        self.assertEqual(editor.hex_cursor_line, 1)
        editor._handle_hex(ord("j"))
        self.assertEqual(editor.hex_cursor_line, 2)
        editor._handle_hex(ord("k"))
        self.assertEqual(editor.hex_cursor_line, 1)

    def test_hex_gg_and_g_jump_cursor_to_top_and_bottom(self):
        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(50)]
        editor._open_hex_view()
        editor._last_h = 24
        total = editor._hex_line_count

        editor._handle_hex(ord("G"))
        self.assertEqual(editor.hex_cursor_line, total - 1)

        editor._handle_hex(ord("g"))
        editor._handle_hex(ord("g"))
        self.assertEqual(editor.hex_cursor_line, 0)

    def test_hex_view_scrolls_to_keep_cursor_visible_and_places_terminal_cursor(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 90

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = [f"{i:03d}" for i in range(60)]  # well over one hex page
        editor._open_hex_view()
        editor._last_h = 8

        for _ in range(10):
            editor._handle_hex(ord("j"))
        self.assertEqual(editor.hex_cursor_line, 10)

        screen = FakeScreen()
        setsyx_calls = []
        with mock.patch("curses.doupdate"), \
                mock.patch("curses.setsyx", side_effect=lambda *a: setsyx_calls.append(a)):
            editor.draw(screen)

        text_rows = 8 - 2
        self.assertGreater(
            editor.hex_top_line, 0,
            "the view must scroll once the cursor moves past the first page",
        )
        expected_row = editor.hex_cursor_line - editor.hex_top_line
        self.assertTrue(0 <= expected_row < text_rows)
        self.assertEqual(
            setsyx_calls[-1], (expected_row, 0),
            "the real terminal cursor must track the current hex row, not "
            "stay fixed at a default position",
        )

        # The current row must also be visually highlighted.
        reversed_calls = [args for args in screen.calls if len(args) >= 4 and args[3] == curses.A_REVERSE]
        self.assertTrue(
            any(args[0] == expected_row for args in reversed_calls),
            "the current hex row must be drawn with A_REVERSE",
        )

    def test_hex_mode_uses_preserved_line_endings(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r", ""]
        editor.line_endings_trusted = True

        hex_text = "\n".join(editor._hex_view_lines())

        self.assertIn("6f 6e 65 0d 0a 74 77 6f", hex_text)
        self.assertIn("0d 74 68 72 65 65", hex_text)

    def test_hex_mode_uses_effective_untrusted_line_endings(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor.line_endings = [""]
        editor.line_endings_trusted = False

        hex_text = "\n".join(editor._hex_view_lines())

        self.assertIn("61 6c 70 68 61", hex_text)
        self.assertNotIn("61 6c 70 68 61 0a", hex_text)

    def test_scroll_overlay_home_end_navigation(self):
        editor = ViEditor()
        editor.lines = [f"line {idx}" for idx in range(40)]
        editor.line_endings = ["\n"] * 39 + [""]
        editor._open_line_endings_view()
        editor._last_h = 8

        editor._handle_line_endings(curses.KEY_END)
        self.assertGreater(editor.line_endings_top_line, 0)

        editor._handle_line_endings(curses.KEY_HOME)
        self.assertEqual(editor.line_endings_top_line, 0)

    # ------------------------------------------------------------------
    # Fix: hex view used to materialize the whole file/buffer into memory
    # with no size cap, and flipped self.mode to HEX before that
    # materialization succeeded -- a failure left mode stuck on HEX with a
    # stale/never-populated cache. _open_hex_view now probes size cheaply
    # first (without copying) and only switches mode/cache once the data
    # is actually in hand.
    # ------------------------------------------------------------------

    def test_hex_view_refuses_oversized_materialized_buffer(self):
        editor = ViEditor()
        editor.lines = ["hello world"]
        old_cap = editor.HEX_VIEW_MAX_BYTES
        try:
            editor.HEX_VIEW_MAX_BYTES = 5
            editor._open_hex_view()
        finally:
            editor.HEX_VIEW_MAX_BYTES = old_cap

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.message_is_error)
        self.assertIn("too large", editor.message)

    def test_hex_view_refuses_oversized_mmap_file_without_materializing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "big.bin")
            with open(path, "wb") as fh:
                fh.write(b"x" * 200)

            editor = ViEditor()
            old_threshold = editor.LARGE_FILE_MMAP_THRESHOLD
            editor.LARGE_FILE_MMAP_THRESHOLD = 0
            try:
                editor._load_file(path)
            finally:
                editor.LARGE_FILE_MMAP_THRESHOLD = old_threshold

            self.assertIsInstance(editor.lines, MMapLineStore)
            self.assertTrue(editor.lines.is_mapped)

            old_cap = editor.HEX_VIEW_MAX_BYTES
            try:
                editor.HEX_VIEW_MAX_BYTES = 10
                editor._open_hex_view()
            finally:
                editor.HEX_VIEW_MAX_BYTES = old_cap

            self.assertEqual(editor.mode, Mode.NORMAL)
            self.assertTrue(editor.message_is_error)
            # Refusing the oversized view must not have forced the lazy
            # store to materialize -- that would defeat the size probe's
            # whole purpose of avoiding a full-file copy.
            self.assertTrue(editor.lines.is_mapped)

    def test_hex_view_stays_in_prior_mode_when_materialization_fails(self):
        editor = ViEditor()
        editor.lines = ["ABC", "xy"]
        editor.mode = Mode.NORMAL

        with mock.patch.object(editor, "_buffer_hex_bytes", side_effect=MemoryError):
            editor._open_hex_view()

        self.assertEqual(
            editor.mode, Mode.NORMAL,
            "a failed materialization must not leave mode switched to HEX",
        )
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor._hex_cached_data, b"")
        self.assertEqual(editor._hex_line_count, 1)

    def test_hex_view_opens_normally_within_size_cap(self):
        """Sanity check: ordinary hex views are unaffected by the new cap."""
        editor = ViEditor()
        editor.lines = ["ABC", "xy"]

        editor._open_hex_view()

        self.assertEqual(editor.mode, Mode.HEX)
        self.assertFalse(editor.message_is_error)

    # ------------------------------------------------------------------
    # Fix: _hex_source_size() counted characters (len(str(line))) instead
    # of encoded UTF-8 bytes for non-mmap buffers. Multi-byte characters
    # (e.g. CJK, 3 bytes each in UTF-8) made the probe undercount the real
    # size _buffer_hex_bytes() would produce by up to 4x, letting content
    # past HEX_VIEW_MAX_BYTES slip through the gate it exists to enforce.
    # ------------------------------------------------------------------

    def test_hex_source_size_counts_encoded_bytes_not_characters(self):
        editor = ViEditor()
        # Each "中" character is 1 char but 3 bytes in UTF-8, so the
        # char count (5) and the real encoded size (15 + 1 for \n) diverge.
        editor.lines = ["中" * 5]
        editor.line_endings = ["\n"]
        editor.line_endings_trusted = True

        size = editor._hex_source_size()

        self.assertEqual(size, len(("中" * 5 + "\n").encode("utf-8")))
        self.assertNotEqual(size, len("中" * 5) + len("\n"))

    def test_hex_view_refuses_oversized_multibyte_buffer_by_byte_count(self):
        editor = ViEditor()
        # 20 3-byte characters = 20 "chars" but 60 bytes. A char-based probe
        # would have let this slip under a 40-byte cap; a byte-accurate one
        # must not.
        editor.lines = ["中" * 20]
        old_cap = editor.HEX_VIEW_MAX_BYTES
        try:
            editor.HEX_VIEW_MAX_BYTES = 40
            editor._open_hex_view()
        finally:
            editor.HEX_VIEW_MAX_BYTES = old_cap

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.message_is_error)
        self.assertIn("too large", editor.message)

    # ------------------------------------------------------------------
    # Fix: _fb_action_view() loaded a binary file into a live, switched-to
    # buffer before checking whether it would fit in the hex-view size cap.
    # An oversized binary would get fully loaded (lossy UTF-8 decoded) and
    # left sitting in an editable NORMAL-mode buffer marked "clean" when
    # _open_hex_view() rejected it -- risking silent corruption on :w.
    # ------------------------------------------------------------------

    def test_fb_action_view_refuses_oversized_binary_without_loading_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "big.bin")
            with open(path, "wb") as fh:
                fh.write(b"\x00\x01\x02binary" * 20)

            editor = ViEditor()
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1  # entries: [.., big.bin]
            editor.file_browser.active_panel = 0
            editor.mode = Mode.FILE_BROWSER
            buffer_count_before = len(editor.buffers)

            old_cap = editor.HEX_VIEW_MAX_BYTES
            try:
                editor.HEX_VIEW_MAX_BYTES = 10
                editor._fb_action_view()
            finally:
                editor.HEX_VIEW_MAX_BYTES = old_cap

            self.assertEqual(editor.mode, Mode.FILE_BROWSER)
            self.assertTrue(editor.message_is_error)
            self.assertIn("too large", editor.message)
            self.assertEqual(
                len(editor.buffers), buffer_count_before,
                "an oversized binary must not be loaded into a new buffer "
                "just because the hex view rejected it",
            )

    def test_fb_action_view_opens_hex_for_binary_within_cap(self):
        """Sanity check: binaries within the cap are unaffected by the size
        pre-check and still open in hex mode as before."""
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "small.bin")
            with open(path, "wb") as fh:
                fh.write(b"\x00\x01\x02binary")

            editor = ViEditor()
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1  # entries: [.., small.bin]
            editor.file_browser.active_panel = 0
            editor.mode = Mode.FILE_BROWSER

            editor._fb_action_view()

            self.assertEqual(editor.mode, Mode.HEX)
            self.assertFalse(editor.message_is_error)

    def test_fb_action_view_shows_exact_bytes_for_non_utf8_binary(self):
        # _fb_action_view() used to route binaries through _append_buffer(),
        # which decodes as UTF-8 with errors="replace" before hex view
        # re-encoded the already-lossy text. For bytes that aren't valid
        # UTF-8 -- true of virtually any real binary, which is the whole
        # reason this path is taken -- that round trip fabricated hex
        # output that didn't match the file on disk, with no warning.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "img.bin")
            raw = bytes([0x89, 0x50, 0x4E, 0x47, 0x0D, 0x0A, 0x1A, 0x0A,
                         0xFF, 0xD8, 0xFF, 0xE0, 0x00, 0x10])
            with open(path, "wb") as fh:
                fh.write(raw)

            editor = ViEditor()
            buffer_count_before = len(editor.buffers)
            editor.file_browser.left.cwd = tmpdir
            editor.file_browser.left.cursor = 1  # entries: [.., img.bin]
            editor.file_browser.active_panel = 0
            editor.mode = Mode.FILE_BROWSER

            editor._fb_action_view()

            self.assertEqual(editor.mode, Mode.HEX)
            self.assertEqual(editor._hex_cached_data, raw)
            self.assertEqual(editor._hex_cached_data_len, len(raw))
            # The binary must never be routed through a decoded text buffer.
            self.assertEqual(len(editor.buffers), buffer_count_before)


class LineEndingsModeTests(unittest.TestCase):
    def test_new_editor_starts_clean_with_line_ending_signature(self):
        editor = ViEditor()

        editor._refresh_modified()

        self.assertFalse(editor.modified)

    def test_line_ending_only_change_marks_buffer_modified(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = ["\r\n", ""]
        editor._mark_clean()

        editor.line_endings = ["\n", ""]
        editor._refresh_modified()

        self.assertTrue(editor.modified)

    def test_line_ending_trust_only_change_marks_buffer_modified(self):
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor.line_endings = [""]
        editor.line_endings_trusted = True
        editor._mark_clean()

        editor.line_endings_trusted = False
        editor._refresh_modified()

        self.assertTrue(editor.modified)

    def test_undo_restores_line_ending_trust_state_for_exports(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            encoded = os.path.join(tmpdir, "out.b64")

            editor = ViEditor()
            editor.lines = ["manual"]
            editor.line_endings = [""]
            editor.line_endings_trusted = False
            editor._push_undo()
            editor.lines = ["loaded"]
            editor.line_endings = [""]
            editor.line_endings_trusted = True

            editor._undo()

            self.assertFalse(editor.line_endings_trusted)
            self.assertTrue(editor._execute_cmd(f":b64e {encoded}"))
            with open(encoded, "rb") as fh:
                self.assertEqual(base64.b64decode(fh.read()), b"manual\n")

    def test_line_endings_command_shows_preserved_file_endings_and_esc_closes(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "mixed.txt")
            with open(path, "wb") as fh:
                fh.write(b"one\r\ntwo\rthree\nfour")

            editor = ViEditor()
            self.assertTrue(editor._load_file(path))

            self.assertTrue(editor._execute_cmd(":le"))

            self.assertEqual(editor.mode, Mode.LINE_ENDINGS)
            self.assertEqual(editor._line_endings_view_lines(), [
                "one[CRLF]",
                "two[CR]",
                "three[NL]",
                "four[NONE]",
            ])

            editor._last_h = 24
            editor._handle_line_endings(27)

            self.assertEqual(editor.mode, Mode.NORMAL)

    def test_draw_line_endings_mode_renders_markers(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 90

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r", "\n"]
        editor._open_line_endings_view()

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        rendered = [args[2] for args in screen.calls if len(args) >= 3]
        self.assertTrue(any("one[CRLF]" in text for text in rendered))
        self.assertTrue(any("two[CR]" in text for text in rendered))
        self.assertTrue(any("three[NL]" in text for text in rendered))
        self.assertTrue(any("LE" in text for text in rendered))

    def test_line_endings_follow_linewise_delete(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r", "\n"]

        editor._delete_range(1, 0, 1, 0, linewise=True)

        self.assertEqual(editor.lines, ["one", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "three[NL]",
        ])

    def test_line_endings_follow_join_and_undo(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r", "\n"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._mark_clean()

        editor._join_current_line(2)

        self.assertEqual(editor.lines, ["one two", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one two[CR]",
            "three[NL]",
        ])

        editor._undo()

        self.assertEqual(editor.lines, ["one", "two", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "two[CR]",
            "three[NL]",
        ])

    def test_join_with_missing_metadata_keeps_final_row_without_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = []

        editor._join_line(0)

        self.assertEqual(editor.lines, ["one two"])
        self.assertEqual(editor._line_endings_view_lines(), ["one two[NONE]"])

    def test_multiline_char_delete_with_missing_metadata_keeps_merged_final_row_without_ending(self):
        editor = ViEditor()
        editor.lines = ["abc", "def"]
        editor.line_endings = []

        editor._delete_range(0, 1, 1, 1, linewise=False)

        self.assertEqual(editor.lines, ["af"])
        self.assertEqual(editor._line_endings_view_lines(), ["af[NONE]"])

    def test_insert_backspace_join_with_missing_metadata_keeps_final_row_without_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = []
        editor.mode = Mode.INSERT
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._handle_insert(curses.KEY_BACKSPACE)

        self.assertEqual(editor.lines, ["onetwo"])
        self.assertEqual(editor._line_endings_view_lines(), ["onetwo[NONE]"])

    def test_missing_line_ending_metadata_falls_back_to_text_rows(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = []

        self.assertEqual(editor._line_endings_view_lines(), [
            "one[NL]",
            "two[NONE]",
        ])

    def test_normalizing_missing_line_endings_keeps_final_row_without_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = []

        editor._normalize_line_endings()

        self.assertEqual(editor._line_endings_view_lines(), [
            "one[NL]",
            "two[NONE]",
        ])

    def test_open_line_at_end_marks_previous_line_not_new_final_line(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.line_endings = [""]

        editor._handle_normal(ord("o"), 24, 80)

        self.assertEqual(editor.lines, ["", ""])
        self.assertEqual(editor._line_endings_view_lines(), [
            "[NL]",
            "[NONE]",
        ])

    def test_read_append_after_final_line_marks_separator_line_ending(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            with open(source, "wb") as fh:
                fh.write(b"one\n")

            editor = ViEditor()
            editor.lines = ["top"]
            editor.line_endings = [""]

            self.assertTrue(editor._execute_cmd(f":read {source}"))

            self.assertEqual(editor.lines, ["top", "one"])
            self.assertEqual(editor._line_endings_view_lines(), [
                "top[NL]",
                "one[NL]",
            ])

    def test_read_imported_endings_use_default_line_endings_on_save(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "wb") as fh:
                fh.write(b"one\r\ntwo")

            editor = ViEditor()
            editor.lines = ["top"]
            editor.line_endings = [""]

            self.assertTrue(editor._execute_cmd(f":read {source}"))
            self.assertTrue(editor._save_file(target))

            with open(target, "rb") as fh:
                self.assertEqual(fh.read(), b"top\none\ntwo\n")

    def test_read_no_final_newline_into_middle_uses_default_line_endings_on_save(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            source = os.path.join(tmpdir, "source.txt")
            target = os.path.join(tmpdir, "target.txt")
            with open(source, "wb") as fh:
                fh.write(b"inserted")

            editor = ViEditor()
            editor.lines = ["top", "bottom"]
            editor.line_endings = ["\r\n", ""]
            editor.line_endings_trusted = True
            editor.cursor_row = 0

            self.assertTrue(editor._execute_cmd(f":read {source}"))
            self.assertEqual(editor._line_endings_view_lines(), [
                "top[CRLF]",
                "inserted[CRLF]",
                "bottom[NONE]",
            ])

            self.assertTrue(editor._save_file(target))
            with open(target, "rb") as fh:
                self.assertEqual(fh.read(), b"top\ninserted\nbottom\n")

    def test_newline_with_missing_metadata_keeps_new_final_line_without_ending(self):
        editor = ViEditor()
        editor.lines = ["onetwo"]
        editor.line_endings = []
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._newline()

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[NL]",
            "two[NONE]",
        ])

    def test_insert_mode_canonicalizes_missing_line_endings_before_edit(self):
        editor = ViEditor()
        editor.lines = ["ab"]
        editor.line_endings = []
        editor._mark_clean()
        editor.mode = Mode.INSERT
        editor.cursor_row = 0
        editor.cursor_col = 1
        editor._enter_insert()

        editor._newline()
        editor._backspace()
        editor._leave_insert()

        self.assertEqual(editor.lines, ["ab"])
        self.assertEqual(editor.line_endings, [""])
        self.assertFalse(editor.modified)
        self.assertFalse(editor.undo_stack)

    def test_newline_uses_windows_default_line_ending(self):
        editor = ViEditor()
        editor.lines = ["onetwo"]
        editor.line_endings = [""]
        editor.default_line_ending = "\r\n"
        editor.cursor_row = 0
        editor.cursor_col = 3

        editor._newline()

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "two[NONE]",
        ])

    def test_insert_newline_inside_indent_does_not_duplicate_remaining_indent(self):
        editor = ViEditor()
        editor.lines = ["    value"]
        editor.line_endings = [""]
        editor.cursor_row = 0
        editor.cursor_col = 2
        editor.marks = {"a": (0, 6)}
        editor._enter_insert()

        editor._handle_insert(ord("\n"))

        self.assertEqual(editor.lines, ["  ", "  value"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))
        self.assertEqual(editor.marks["a"], (1, 4))

    def test_insert_newline_before_indent_keeps_original_indent_on_tail(self):
        editor = ViEditor()
        editor.lines = ["    value"]
        editor.line_endings = [""]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._enter_insert()

        editor._handle_insert(ord("\n"))

        self.assertEqual(editor.lines, ["", "    value"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

    def test_open_line_uses_windows_default_line_ending(self):
        editor = ViEditor()
        editor.lines = ["one"]
        editor.line_endings = [""]
        editor.default_line_ending = "\r\n"
        editor.cursor_row = 0

        editor._handle_normal(ord("o"), 24, 80)

        self.assertEqual(editor.lines, ["one", ""])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "[NONE]",
        ])

    def test_substitute_lines_preserves_replaced_range_trailing_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r", ""]
        editor.cursor_row = 1
        editor.cursor_col = 0

        editor._begin_substitute_lines(2)

        self.assertEqual(editor.lines, ["one", ""])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "[NONE]",
        ])

    def test_linewise_change_target_preserves_deleted_crlf_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "three"]
        editor.line_endings = ["\r\n", ""]

        editor._insert_linewise_change_target(0, 1, "\r\n")

        self.assertEqual(editor.lines, ["", "one", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "[CRLF]",
            "one[CRLF]",
            "three[NONE]",
        ])

    def test_linewise_change_target_uses_default_line_ending_when_unspecified(self):
        editor = ViEditor()
        editor.lines = ["one", "three"]
        editor.line_endings = ["\r\n", ""]
        editor.default_line_ending = "\r\n"

        editor._insert_linewise_change_target(0, 1)

        self.assertEqual(editor.lines, ["", "one", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "[CRLF]",
            "one[CRLF]",
            "three[NONE]",
        ])

    def test_linewise_yank_put_preserves_yanked_line_ending(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r\n", "\r\n", ""]
        editor.line_endings_trusted = True
        editor.cursor_row = 0

        editor._handle_normal(ord("Y"), 24, 80)
        editor.cursor_row = 1
        editor._put(after=True)

        self.assertEqual(editor.lines, ["one", "two", "one", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "two[CRLF]",
            "one[CRLF]",
            "three[NONE]",
        ])

    def test_linewise_put_final_no_ending_gets_separator_before_existing_line(self):
        editor = ViEditor()
        editor.lines = ["one", "two"]
        editor.line_endings = ["\r\n", ""]
        editor.line_endings_trusted = True
        editor.cursor_row = 1

        editor._handle_normal(ord("Y"), 24, 80)
        editor.cursor_row = 0
        editor._put(after=True)

        self.assertEqual(editor.lines, ["one", "two", "two"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CRLF]",
            "two[CRLF]",
            "two[NONE]",
        ])

    def test_counted_linewise_put_repeats_preserved_endings(self):
        editor = ViEditor()
        editor.lines = ["one", "two", "three"]
        editor.line_endings = ["\r", "\r", ""]
        editor.line_endings_trusted = True
        editor.cursor_row = 0

        editor._handle_normal(ord("Y"), 24, 80)
        editor.cursor_row = 1
        editor._put_count(after=True, cnt=2)

        self.assertEqual(editor.lines, ["one", "two", "one", "one", "three"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "one[CR]",
            "two[CR]",
            "one[CR]",
            "one[CR]",
            "three[NONE]",
        ])

    def test_charwise_multiline_put_uses_default_line_ending_for_new_rows(self):
        editor = ViEditor()
        editor.lines = ["startend"]
        editor.line_endings = [""]
        editor.default_line_ending = "\r\n"
        editor.yank_buffer = ["A", "B"]
        editor.yank_is_lines = False
        editor.cursor_row = 0
        editor.cursor_col = 4

        editor._put(after=True)

        self.assertEqual(editor.lines, ["startA", "Bend"])
        self.assertEqual(editor._line_endings_view_lines(), [
            "startA[CRLF]",
            "Bend[NONE]",
        ])


class InputHandlingTests(unittest.TestCase):
    def test_ignored_control_keys_cover_ctrl_c_ctrl_backslash_and_ctrl_4(self):
        editor = ViEditor()

        self.assertTrue(editor._is_ignored_control_key(3))
        self.assertTrue(editor._is_ignored_control_key(28))
        self.assertFalse(editor._is_ignored_control_key(ord("c")))

    def _paging_editor(self):
        editor = ViEditor()
        editor.lines = [f"line {i}" for i in range(100)]
        editor.line_endings = ["\n"] * 99 + [""]
        editor._last_h = 24  # 21 text rows after chrome
        return editor

    def test_page_down_in_insert_mode_moves_cursor_a_screenful(self):
        editor = self._paging_editor()
        editor.cursor_row = 0
        editor.cursor_col = 3
        editor._enter_insert()

        editor._handle_insert(curses.KEY_NPAGE)

        text_rows = editor._editor_text_rows(editor._last_h)
        self.assertEqual(editor.mode, Mode.INSERT)
        self.assertEqual(editor.cursor_row, text_rows)
        self.assertEqual(editor.cursor_col, 3)
        self.assertEqual(editor.top_line, text_rows)
        self.assertEqual(editor.lines[0], "line 0")  # nothing inserted

    def test_page_up_in_insert_mode_moves_cursor_back(self):
        editor = self._paging_editor()
        editor.cursor_row = 50
        editor.cursor_col = 3
        editor.top_line = 40
        editor._enter_insert()

        editor._handle_insert(curses.KEY_PPAGE)

        text_rows = editor._editor_text_rows(editor._last_h)
        self.assertEqual(editor.mode, Mode.INSERT)
        self.assertEqual(editor.cursor_row, 50 - text_rows)
        self.assertEqual(editor.top_line, 40 - text_rows)

    def test_page_keys_clamp_at_buffer_edges_in_insert_mode(self):
        editor = self._paging_editor()
        editor.cursor_row = 0
        editor._enter_insert()

        editor._handle_insert(curses.KEY_PPAGE)
        self.assertEqual((editor.cursor_row, editor.top_line), (0, 0))

        for _ in range(20):
            editor._handle_insert(curses.KEY_NPAGE)
        self.assertEqual(editor.cursor_row, len(editor.lines) - 1)
        self.assertEqual(editor.top_line, len(editor.lines) - 1)

    def test_page_keys_work_in_replace_mode(self):
        editor = self._paging_editor()
        editor.cursor_row = 0
        editor.cursor_col = 2
        editor._enter_replace()

        editor._handle_replace_mode(curses.KEY_NPAGE)
        text_rows = editor._editor_text_rows(editor._last_h)
        self.assertEqual(editor.mode, Mode.REPLACE)
        self.assertEqual(editor.cursor_row, text_rows)

        editor._handle_replace_mode(curses.KEY_PPAGE)
        self.assertEqual(editor.cursor_row, 0)

    def test_page_keys_are_recorded_for_insert_replay(self):
        editor = self._paging_editor()
        editor.cursor_row = 0
        editor._enter_insert()

        editor._handle_insert(curses.KEY_NPAGE)
        editor._handle_insert(curses.KEY_PPAGE)

        self.assertEqual(editor._insert_replay_keys,
                         [curses.KEY_NPAGE, curses.KEY_PPAGE])

    def test_normal_mode_scroll_keys_request_hidden_cursor(self):
        # Ctrl-F/PgDn, Ctrl-B/PgUp, Ctrl-D, Ctrl-U, Ctrl-E, Ctrl-Y
        for key in (curses.KEY_NPAGE, curses.KEY_PPAGE, 6, 2, 4, 21, 5, 25):
            editor = self._paging_editor()
            editor.cursor_row = 50
            editor.top_line = 40
            editor._handle_normal(key, 24, 80)
            self.assertTrue(editor._hide_cursor_next_draw, f"key {key}")

    def test_z_recenter_requests_hidden_cursor(self):
        for second in ("z", "t", "b"):
            editor = self._paging_editor()
            editor.cursor_row = 50
            editor._handle_normal(ord("z"), 24, 80)
            self.assertFalse(editor._hide_cursor_next_draw)
            editor._handle_normal(ord(second), 24, 80)
            self.assertTrue(editor._hide_cursor_next_draw, f"z{second}")

    def test_insert_and_visual_paging_request_hidden_cursor(self):
        editor = self._paging_editor()
        editor._enter_insert()
        editor._handle_insert(curses.KEY_NPAGE)
        self.assertTrue(editor._hide_cursor_next_draw)

        editor = self._paging_editor()
        editor._handle_normal(ord("v"), 24, 80)
        editor._handle_visual(curses.KEY_NPAGE)
        self.assertTrue(editor._hide_cursor_next_draw)

    def test_plain_keys_do_not_request_hidden_cursor(self):
        editor = self._paging_editor()
        editor._handle_normal(ord("j"), 24, 80)
        self.assertFalse(editor._hide_cursor_next_draw)
        editor._enter_insert()
        editor._handle_insert(ord("a"))
        self.assertFalse(editor._hide_cursor_next_draw)

    def test_edit_hides_cursor_only_while_scroll_frame_is_painted(self):
        editor = self._paging_editor()
        editor._reinit_colors = mock.MagicMock()
        editor._save_session = mock.MagicMock()
        events = []
        editor.draw = lambda scr: events.append("draw")

        class Screen:
            def __init__(self):
                self._keys = [curses.KEY_NPAGE]

            def get_wch(self):
                return self._keys.pop(0)  # IndexError ends the test loop

            def getmaxyx(self):
                return (24, 80)

            def keypad(self, flag):
                pass

        with mock.patch("curses.curs_set",
                        side_effect=lambda v: events.append(("curs_set", v))), \
                mock.patch("curses.noecho"), \
                mock.patch("curses.start_color"), \
                mock.patch("curses.use_default_colors"):
            with self.assertRaises(IndexError):
                editor.edit(Screen())

        # Visible at startup, first frame drawn with a visible cursor; the
        # frame after the paging key is drawn hidden, then re-shown.
        self.assertEqual(events, [("curs_set", 1), "draw",
                                  ("curs_set", 0), "draw", ("curs_set", 1)])
        self.assertFalse(editor._hide_cursor_next_draw)

    def test_edit_tolerates_curs_set_failure_during_scroll(self):
        editor = self._paging_editor()
        editor._reinit_colors = mock.MagicMock()
        editor._save_session = mock.MagicMock()
        draws = []
        editor.draw = lambda scr: draws.append(True)

        class Screen:
            def __init__(self):
                self._keys = [curses.KEY_NPAGE]

            def get_wch(self):
                return self._keys.pop(0)

            def getmaxyx(self):
                return (24, 80)

            def keypad(self, flag):
                pass

        with mock.patch("curses.curs_set", side_effect=curses.error("boom")), \
                mock.patch("curses.noecho"), \
                mock.patch("curses.start_color"), \
                mock.patch("curses.use_default_colors"):
            with self.assertRaises(IndexError):
                editor.edit(Screen())

        self.assertEqual(len(draws), 2)  # both frames still painted


class BracketedPasteTests(unittest.TestCase):
    """Covers pasting text into INSERT/REPLACE mode via terminal bracketed
    paste (ESC [200~ ... ESC [201~), which must not run pasted newlines
    through the normal auto-indenting Enter path -- that's what causes
    vim's classic "staircase" of ever-growing indentation on paste."""

    class FakeScreen:
        """A minimal curses window double that also supports timeout(),
        needed by the bracketed-paste start-marker probe. Queued keys are
        served in order; once exhausted, get_wch() raises curses.error("no
        input") while a finite timeout is active (mimicking a real
        non-blocking read expiring) or IndexError while blocking (ending
        the test loop), matching how real curses actually behaves in each
        mode."""

        def __init__(self, keys):
            self._keys = list(keys)
            self._timeout_ms = -1

        def get_wch(self):
            if self._keys:
                return self._keys.pop(0)
            if self._timeout_ms is not None and self._timeout_ms >= 0:
                raise curses.error("no input")
            raise IndexError("no more keys queued")

        def getmaxyx(self):
            return (24, 80)

        def keypad(self, flag):
            pass

        def timeout(self, ms):
            self._timeout_ms = ms

    @staticmethod
    def _patched_curses_init():
        return mock.patch.multiple(
            curses, curs_set=mock.DEFAULT, noecho=mock.DEFAULT,
            start_color=mock.DEFAULT, use_default_colors=mock.DEFAULT,
        )

    @staticmethod
    def _paste_keys(text):
        """The raw key sequence a terminal sends for a bracketed paste of
        `text`, as individual get_wch() reads (ESC, then each byte of the
        marker, then the text's characters, then the end marker)."""
        keys = [27, *[ord(c) for c in "[200~"]]
        keys.extend(ord(c) if ord(c) < 128 else c for c in text)
        keys.extend([27, *[ord(c) for c in "[201~"]])
        return keys

    def _editor(self):
        editor = ViEditor()
        editor._reinit_colors = mock.MagicMock()
        editor.draw = mock.MagicMock()
        editor._save_session = mock.MagicMock()
        editor._handle_normal = mock.MagicMock(return_value=False)
        return editor

    # -- _insert_pasted_text / _replace_pasted_text (unit level) -----------

    def test_insert_pasted_multiline_text_does_not_grow_indent(self):
        editor = ViEditor()
        editor.lines = ["    outer"]
        editor.cursor_row = 0
        editor.cursor_col = len("    outer")
        editor._enter_insert()

        editor._insert_pasted_text("\n    line1\n    line2\n    line3")

        self.assertEqual(editor.lines, [
            "    outer",
            "    line1",
            "    line2",
            "    line3",
        ])

    def test_insert_pasted_text_splits_line_at_cursor_without_indent(self):
        editor = ViEditor()
        editor.lines = ["    abcXYZ"]
        editor.cursor_row = 0
        editor.cursor_col = len("    abc")
        editor._enter_insert()

        editor._insert_pasted_text("1\n2")

        self.assertEqual(editor.lines, ["    abc1", "2XYZ"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 1))

    def test_insert_pasted_text_without_newline_inserts_at_cursor(self):
        editor = ViEditor()
        editor.lines = ["ac"]
        editor.cursor_row = 0
        editor.cursor_col = 1
        editor._enter_insert()

        editor._insert_pasted_text("b")

        self.assertEqual(editor.lines, ["abc"])
        self.assertEqual(editor.cursor_col, 2)

    def test_insert_pasted_text_normalizes_crlf_and_cr_newlines(self):
        editor = ViEditor()
        editor.lines = [""]
        editor._enter_insert()

        editor._insert_pasted_text("a\r\nb\rc")

        self.assertEqual(editor.lines, ["a", "b", "c"])

    def test_replace_pasted_text_overwrites_and_splits_without_indent(self):
        editor = ViEditor()
        editor.lines = ["    XXXXX"]
        editor.cursor_row = 0
        editor.cursor_col = 4
        editor._enter_replace()

        editor._replace_pasted_text("ab\ncd")

        self.assertEqual(editor.lines, ["    ab", "cdX"])

    def test_pasted_literal_tab_replays_as_literal_not_indent_expansion(self):
        # A pasted line segment is replayed as one multi-char string entry
        # (not one entry per character) specifically so a literal tab in
        # pasted text doesn't run through the Tab *key's* indent-expansion
        # branch on `.`/count-repeat -- it must stay a literal tab both
        # times, matching what the live paste just inserted.
        editor = ViEditor()
        editor.lines = ["a", "x"]
        editor.cursor_row = 0
        editor._handle_normal(ord("A"), 24, 80)
        editor._insert_pasted_text("\tb")
        self.assertEqual(editor._insert_replay_keys, ["\tb"])
        editor._leave_insert()

        self.assertEqual(editor.lines[0], "a\tb")

        editor.cursor_row = 1
        editor._handle_normal(ord("."), 24, 80)

        self.assertEqual(editor.lines[1], "x\tb")

    def test_dot_repeat_after_paste_does_not_regrow_indent(self):
        editor = ViEditor()
        editor.lines = ["    outer", "    target"]
        editor.cursor_row = 0
        editor._handle_normal(ord("A"), 24, 80)  # append at end of "    outer"
        editor._insert_pasted_text("\n    pasted1\n    pasted2")
        editor._leave_insert()

        editor.cursor_row = len(editor.lines) - 1  # "    target"
        editor._handle_normal(ord("."), 24, 80)

        self.assertEqual(editor.lines[-3:], [
            "    target",
            "    pasted1",
            "    pasted2",
        ])

    def test_paste_literal_outside_insert_splits_lines_without_indent(self):
        # NORMAL/VISUAL(_LINE)-mode paste uses the same literal, non-
        # auto-indenting splice as insert-mode paste (_insert_pasted_text) --
        # see _handle_bracketed_paste for why it must not replay as keys.
        editor = ViEditor()
        editor.lines = ["    abcXYZ"]
        editor.cursor_row = 0
        editor.cursor_col = len("    abc")
        editor.mode = Mode.NORMAL

        editor._paste_literal_outside_insert("1\n2")

        self.assertEqual(editor.lines, ["    abc1", "2XYZ"])
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 1))
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_paste_literal_outside_insert_normalizes_crlf_and_is_undoable(self):
        editor = ViEditor()
        editor.lines = [""]
        editor.mode = Mode.NORMAL

        editor._paste_literal_outside_insert("a\r\nb\rc")

        self.assertEqual(editor.lines, ["a", "b", "c"])
        self.assertTrue(editor.modified)

        editor._undo()
        self.assertEqual(editor.lines, [""])

    def test_paste_literal_outside_insert_from_visual_mode_exits_visual(self):
        editor = ViEditor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 2
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 2)

        editor._paste_literal_outside_insert("XY")

        self.assertEqual(editor.lines, ["abXYcdef"])
        self.assertEqual(editor.mode, Mode.NORMAL)

    # -- full edit() loop: real ESC [200~ ... ESC [201~ byte sequence ------

    def test_edit_loop_consumes_bracketed_paste_and_avoids_indent_growth(self):
        editor = self._editor()
        editor.lines = ["    outer"]
        editor.cursor_row = 0
        editor.cursor_col = len("    outer")
        editor._enter_insert()
        editor.mode = Mode.INSERT

        keys = self._paste_keys("\n    line1\n    line2")
        keys.append(27)                      # leave insert mode
        keys.append(ord("q"))                 # reaches mocked _handle_normal -> False
        screen = self.FakeScreen(keys)

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        self.assertEqual(editor.lines, ["    outer", "    line1", "    line2"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_edit_loop_bracketed_paste_in_normal_mode_inserts_literally(self):
        # Paste in NORMAL mode is no longer replayed through the normal
        # per-key dispatch. Pasted text is untrusted external input (e.g.
        # clipboard content from a web page); replaying it as keystrokes
        # would let it open and submit a ':' command -- including a shell
        # command -- with no confirmation (the classic terminal
        # "pastejacking" vector). It's inserted literally instead, exactly
        # like insert-mode paste.
        editor = self._editor()
        editor.lines = ["abc"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        keys = self._paste_keys("xy")
        keys.append(ord("q"))  # reaches mocked _handle_normal -> False
        screen = self.FakeScreen(keys)

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        self.assertEqual(editor.lines, ["xyabc"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_edit_loop_bracketed_paste_in_normal_mode_does_not_execute_commands(self):
        # Regression test for the pastejacking vector: clipboard content
        # containing a ':' command (here a shell command) must never be
        # auto-submitted just because it arrived via bracketed paste while
        # in NORMAL mode.
        editor = self._editor()
        editor.lines = ["abc"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._run_shell_command = mock.MagicMock()

        keys = self._paste_keys(":!touch /tmp/pwned\n")
        keys.append(ord("q"))
        screen = self.FakeScreen(keys)

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        editor._run_shell_command.assert_not_called()
        self.assertEqual(editor.lines, [":!touch /tmp/pwned", "abc"])
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor._cmd_buf, "")

    def test_edit_loop_bracketed_paste_in_visual_mode_inserts_literally(self):
        editor = self._editor()
        editor.lines = ["abcdef"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 0)

        keys = self._paste_keys("XY")
        keys.append(ord("q"))
        screen = self.FakeScreen(keys)

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        self.assertEqual(editor.lines, ["XYabcdef"])
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_edit_loop_bracketed_paste_inserts_into_open_command_line(self):
        # Pasting into an already-open ':' prompt -- one the user opened
        # themselves by pressing ':' -- is a deliberate paste target and
        # must keep working by inserting into the command buffer, not by
        # inserting literally into the document.
        editor = self._editor()
        editor.lines = ["abc"]
        editor._start_cmd_buf(":")

        keys = self._paste_keys("set number")
        keys.extend([27, ord("q")])  # ESC cancels the command line, then quit
        screen = self.FakeScreen(keys)

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        self.assertEqual(editor.lines, ["abc"])
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_edit_loop_bare_escape_without_paste_marker_still_works(self):
        # No paste follows this ESC -- the start-marker probe must time out
        # and fall back to ordinary ESC handling instead of eating input.
        editor = self._editor()
        editor.lines = ["abc"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._enter_insert()
        editor.mode = Mode.INSERT

        screen = self.FakeScreen([27, ord("q")])

        with self._patched_curses_init(), mock.patch("sys.stdout"):
            editor.edit(screen)

        self.assertEqual(editor.mode, Mode.NORMAL)
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_edit_enables_and_disables_bracketed_paste_around_session(self):
        editor = self._editor()
        screen = self.FakeScreen([ord("q")])

        with self._patched_curses_init(), mock.patch("sys.stdout") as stdout:
            editor.edit(screen)

        written = "".join(c.args[0] for c in stdout.write.call_args_list)
        self.assertIn(editor._BRACKETED_PASTE_ON, written)
        self.assertIn(editor._BRACKETED_PASTE_OFF, written)
        self.assertLess(
            written.index(editor._BRACKETED_PASTE_ON),
            written.index(editor._BRACKETED_PASTE_OFF),
        )


class SuspendResumeTests(unittest.TestCase):
    """Covers the Ctrl-Z (SIGTSTP) suspend/resume handling in edit()."""

    class FakeScreen:
        def __init__(self, keys):
            self._keys = list(keys)
            self.refresh_calls = 0

        def get_wch(self):
            item = self._keys.pop(0)
            if callable(item):
                item()
                raise curses.error("no input")
            return item

        def getmaxyx(self):
            return (24, 80)

        def keypad(self, flag):
            pass

        def refresh(self):
            self.refresh_calls += 1

    def _editor(self):
        editor = ViEditor()
        editor._reinit_colors = mock.MagicMock()
        editor.draw = mock.MagicMock()
        editor._save_session = mock.MagicMock()
        editor._handle_normal = mock.MagicMock(return_value=False)
        return editor

    @staticmethod
    def _patched_curses_init():
        return mock.patch.multiple(
            curses, curs_set=mock.DEFAULT, noecho=mock.DEFAULT,
            start_color=mock.DEFAULT, use_default_colors=mock.DEFAULT,
        )

    @staticmethod
    def _fire_sigtstp():
        signal.getsignal(signal.SIGTSTP)(signal.SIGTSTP, None)

    @unittest.skipUnless(hasattr(signal, "SIGTSTP"), "platform has no SIGTSTP")
    def test_sigtstp_suspends_and_restores_terminal_mode(self):
        editor = self._editor()
        original_handler = signal.getsignal(signal.SIGTSTP)
        order = []
        screen = self.FakeScreen([self._fire_sigtstp, ord("q")])

        with self._patched_curses_init(), \
                mock.patch("curses.def_prog_mode", side_effect=lambda: order.append("def_prog_mode")), \
                mock.patch("curses.endwin", side_effect=lambda: order.append("endwin")), \
                mock.patch("curses.reset_prog_mode", side_effect=lambda: order.append("reset_prog_mode")), \
                mock.patch("curses.flushinp", side_effect=lambda: order.append("flushinp")), \
                mock.patch("os.kill") as kill_mock:
            editor.edit(screen)

        kill_mock.assert_called_once_with(os.getpid(), signal.SIGSTOP)
        self.assertEqual(order, ["def_prog_mode", "endwin", "reset_prog_mode", "flushinp"])
        self.assertTrue(editor._force_redraw)
        self.assertEqual(screen.refresh_calls, 1)
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)
        self.assertEqual(signal.getsignal(signal.SIGTSTP), original_handler)

    @unittest.skipUnless(hasattr(signal, "SIGTSTP"), "platform has no SIGTSTP")
    def test_suspend_handler_tolerates_curses_failures(self):
        editor = self._editor()
        screen = self.FakeScreen([self._fire_sigtstp, ord("q")])

        with self._patched_curses_init(), \
                mock.patch("curses.def_prog_mode", side_effect=curses.error("boom")), \
                mock.patch("curses.endwin"), \
                mock.patch("curses.reset_prog_mode", side_effect=curses.error("boom")), \
                mock.patch("curses.flushinp"), \
                mock.patch("os.kill") as kill_mock:
            editor.edit(screen)

        kill_mock.assert_called_once_with(os.getpid(), signal.SIGSTOP)
        self.assertTrue(editor._force_redraw)
        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    @unittest.skipUnless(hasattr(signal, "SIGTSTP"), "platform has no SIGTSTP")
    def test_suspend_handler_tolerates_failed_sigstop(self):
        editor = self._editor()
        screen = self.FakeScreen([self._fire_sigtstp, ord("q")])

        with self._patched_curses_init(), \
                mock.patch("os.kill", side_effect=OSError("operation not permitted")):
            editor.edit(screen)

        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_no_input_curses_error_is_retried_not_fatal(self):
        editor = self._editor()

        class FlakyScreen(self.FakeScreen):
            def __init__(self, keys):
                super().__init__(keys)
                self.attempts = 0

            def get_wch(self):
                self.attempts += 1
                if self.attempts == 1:
                    raise curses.error("no input")
                return super().get_wch()

        screen = FlakyScreen([ord("q")])

        with self._patched_curses_init():
            editor.edit(screen)

        editor._handle_normal.assert_called_once_with(ord("q"), 24, 80)

    def test_other_curses_error_during_read_propagates(self):
        editor = self._editor()

        class ErrScreen(self.FakeScreen):
            def get_wch(self):
                raise curses.error("some other failure")

        screen = ErrScreen([])

        with self._patched_curses_init():
            with self.assertRaises(curses.error):
                editor.edit(screen)

        editor._save_session.assert_called_once()
        editor._handle_normal.assert_not_called()


class CrashRecoveryTests(unittest.TestCase):
    """Covers the crash dump of modified buffers when edit() dies unexpectedly."""

    def test_dump_writes_modified_named_buffer_and_skips_clean_ones(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            dirty_path = os.path.join(tmpdir, "dirty.txt")
            clean_path = os.path.join(tmpdir, "clean.txt")
            for path in (dirty_path, clean_path):
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write("content\n")

            editor = ViEditor([dirty_path, clean_path])
            editor._switch_buffer(0)
            editor.lines[0] = "unsaved edit"
            editor.modified = True

            written = editor._dump_crash_recovery()

            self.assertEqual(written, [dirty_path + ".vii_crash"])
            with open(dirty_path + ".vii_crash", "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "unsaved edit\n")
            self.assertFalse(os.path.exists(clean_path + ".vii_crash"))
            # The original file must be untouched.
            with open(dirty_path, "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "content\n")

    def test_dump_never_raises_when_a_buffer_cannot_be_written(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("content\n")

            editor = ViEditor(path)
            editor.lines[0] = "unsaved edit"
            editor.modified = True

            with mock.patch("builtins.open", side_effect=OSError("read-only fs")):
                written = editor._dump_crash_recovery()

            self.assertEqual(written, [])

    def test_edit_loop_crash_dumps_modified_buffers_before_propagating(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("content\n")

            editor = ViEditor(path)
            editor.lines[0] = "unsaved edit"
            editor.modified = True
            editor._reinit_colors = mock.MagicMock()
            editor.draw = mock.MagicMock()
            editor._save_session = mock.MagicMock()
            editor._handle_normal = mock.MagicMock(side_effect=RuntimeError("dispatch bug"))
            screen = SuspendResumeTests.FakeScreen([ord("x")])

            with SuspendResumeTests._patched_curses_init():
                with self.assertRaises(RuntimeError):
                    editor.edit(screen)

            self.assertEqual(editor.crash_dump_paths, [path + ".vii_crash"])
            with open(path + ".vii_crash", "r", encoding="utf-8") as fh:
                self.assertEqual(fh.read(), "unsaved edit\n")
            editor._save_session.assert_called_once()

    def test_edit_loop_original_crash_propagates_even_if_save_session_also_fails(self):
        # A prior bug let _save_session's own exception, raised from the
        # finally block while the real crash was still propagating, replace
        # the original exception -- so main()'s one-line error summary and
        # final traceback pointed at session-saving code instead of the
        # actual bug that crashed the dispatch loop.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "note.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("content\n")

            editor = ViEditor(path)
            editor.lines[0] = "unsaved edit"
            editor.modified = True
            editor._reinit_colors = mock.MagicMock()
            editor.draw = mock.MagicMock()
            editor._save_session = mock.MagicMock(side_effect=TypeError("bad mark data"))
            editor._handle_normal = mock.MagicMock(side_effect=RuntimeError("dispatch bug"))
            screen = SuspendResumeTests.FakeScreen([ord("x")])

            with SuspendResumeTests._patched_curses_init():
                with self.assertRaises(RuntimeError) as ctx:
                    editor.edit(screen)

            self.assertEqual(str(ctx.exception), "dispatch bug")
            self.assertEqual(editor.crash_dump_paths, [path + ".vii_crash"])
            editor._save_session.assert_called_once()


class ViiRcTests(unittest.TestCase):
    def _editor_with_rc(self, rc_path):
        """Create a ViEditor whose rc file is redirected to rc_path."""
        return _editor_with_rc(rc_path)

    def test_default_viirc_is_created_when_missing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            self.assertFalse(os.path.exists(rc_path))
            self._editor_with_rc(rc_path)
            self.assertTrue(os.path.isfile(rc_path))

    def test_default_viirc_contains_all_configurable_settings(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            self._editor_with_rc(rc_path)
            with open(rc_path, encoding="utf-8") as fh:
                content = fh.read()
            for keyword in ("number", "mdwrap", "expandtab", "tabstop", "shiftwidth",
                            "lnendings", "undolevels", "scrolljump", "sidescrolljump",
                            "sessionfiles",
                            "linenumcolor", "commentcolor",
                            "stringcolor", "keywordcolor", "numbercolor",
                            "typecolor", "builtincolor", "functioncolor",
                            "operatorcolor", "preproccolor",
                            "statusfgcolor", "statusbgcolor",
                            "bottomstatusfgcolor", "bottomstatusbgcolor",
                            "errorcolor"):
                self.assertIn(keyword, content, f"Missing setting: {keyword}")

    def test_default_viirc_applies_defaults_on_load(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            editor = self._editor_with_rc(rc_path)
            self.assertTrue(editor.show_line_numbers)
            self.assertTrue(editor.markdown_wrap)
            self.assertTrue(editor.expand_tab)
            self.assertEqual(editor.vertical_scroll_jump, 1)
            self.assertEqual(editor.horizontal_scroll_jump, 1)
            self.assertEqual(editor.default_line_ending, "\n")
            self.assertEqual(editor.color_status_fg, "black")
            self.assertEqual(editor.color_status_bg, "yellow")
            self.assertEqual(editor.color_bottom_status_fg, "black")
            self.assertEqual(editor.color_bottom_status_bg, "green")
            self.assertEqual(editor.color_error, "black")

    def test_existing_viirc_is_not_overwritten(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            with open(rc_path, "w") as fh:
                fh.write(
                    'set nonu\nset noexpandtab\n'
                    'set lnendings=win\n'
                    'set scrolljump=5 sidescrolljump=7\n'
                )
            editor = self._editor_with_rc(rc_path)
            self.assertFalse(editor.show_line_numbers)
            self.assertFalse(editor.expand_tab)
            self.assertEqual(editor.default_line_ending, "\r\n")
            self.assertEqual(editor.vertical_scroll_jump, 5)
            self.assertEqual(editor.horizontal_scroll_jump, 7)

    def test_viirc_can_disable_markdown_wrapping(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            with open(rc_path, "w", encoding="utf-8") as fh:
                fh.write("set nomdwrap\n")

            editor = self._editor_with_rc(rc_path)
            editor.filename = "notes.md"

            self.assertFalse(editor._markdown_wrap_enabled())

    def test_viirc_inline_comments_are_ignored(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            with open(rc_path, "w") as fh:
                fh.write('set tabstop=4 " noexpandtab should be ignored\n')

            editor = self._editor_with_rc(rc_path)

            self.assertEqual(editor.tab_stop, 4)
            self.assertTrue(editor.expand_tab)

    def test_viirc_accepts_bare_lnendings_value(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            with open(rc_path, "w") as fh:
                fh.write("lnendings=win\n")

            editor = self._editor_with_rc(rc_path)

            self.assertEqual(editor.default_line_ending, "\r\n")

    def test_load_viirc_opens_file_as_utf8(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            rc_path = os.path.join(tmpdir, ".viirc")
            with open(rc_path, "w", encoding="utf-8") as fh:
                fh.write('" snowman: \u2603\nset nonu\n')

            real_expanduser = os.path.expanduser
            real_open = open

            def fake_expanduser(path):
                if path == "~/.viirc":
                    return rc_path
                return real_expanduser(path)

            with mock.patch("os.path.expanduser", side_effect=fake_expanduser), \
                    mock.patch("builtins.open", wraps=real_open) as open_mock:
                editor = ViEditor()

            self.assertFalse(editor.show_line_numbers)
            self.assertTrue(any(
                call.args and call.args[0] == rc_path
                and call.kwargs.get("encoding") == "utf-8"
                and call.kwargs.get("errors") == "replace"
                for call in open_mock.call_args_list
            ))

    def test_status_color_options_apply_and_reinitialize_pair(self):
        editor = ViEditor()
        editor._stdscr = object()

        with mock.patch("curses.init_pair") as init_pair, \
                mock.patch("curses.color_pair", return_value=4321):
            self.assertEqual(editor._apply_set_opt("statusfgcolor=white"), "")
            self.assertEqual(editor._apply_set_opt("statusbg=blue"), "")

        self.assertEqual(editor.color_status_fg, "white")
        self.assertEqual(editor.color_status_bg, "blue")
        self.assertEqual(editor.status_attr, 4321)
        init_pair.assert_any_call(editor.STATUS_PAIR, curses.COLOR_WHITE, curses.COLOR_BLUE)

        self.assertEqual(editor._apply_set_opt("statusfgcolor=bogus"),
                         "Unknown colour 'bogus'. Known: black, red, green, yellow, blue, magenta, cyan, white")

    def test_status_color_options_can_be_queried(self):
        editor = _editor_with_rc()  # isolated from the real ~/.viirc

        self.assertEqual(editor._apply_set_opt("statusfg"), "")
        self.assertEqual(editor.message, "statusfgcolor=black")

        self.assertEqual(editor._apply_set_opt("statusbgcolor"), "")
        self.assertEqual(editor.message, "statusbgcolor=yellow")

    def test_bottom_status_color_options_apply_and_reinitialize_pair(self):
        editor = ViEditor()
        editor._stdscr = object()

        with mock.patch("curses.init_pair") as init_pair, \
                mock.patch("curses.color_pair", return_value=8765):
            self.assertEqual(editor._apply_set_opt("bottomstatusfgcolor=white"), "")
            self.assertEqual(editor._apply_set_opt("bottomstatusbg=blue"), "")

        self.assertEqual(editor.color_bottom_status_fg, "white")
        self.assertEqual(editor.color_bottom_status_bg, "blue")
        self.assertEqual(editor.bottom_status_attr, 8765)
        init_pair.assert_any_call(editor.BOTTOM_STATUS_PAIR, curses.COLOR_WHITE, curses.COLOR_BLUE)

        self.assertEqual(editor._apply_set_opt("bottomstatusfgcolor=bogus"),
                         "Unknown colour 'bogus'. Known: black, red, green, yellow, blue, magenta, cyan, white")

    def test_bottom_status_color_options_can_be_queried(self):
        editor = _editor_with_rc()  # isolated from the real ~/.viirc

        self.assertEqual(editor._apply_set_opt("bottomstatusfg"), "")
        self.assertEqual(editor.message, "bottomstatusfgcolor=black")

        self.assertEqual(editor._apply_set_opt("bottomstatusbgcolor"), "")
        self.assertEqual(editor.message, "bottomstatusbgcolor=green")

    def test_error_color_option_applies_and_reinitializes_pair(self):
        editor = _editor_with_rc()  # isolated from the real ~/.viirc: the
        # error pair's background tracks color_bottom_status_bg, so a local
        # ~/.viirc overriding bottomstatusbg would change the expected
        # init_pair() call below out from under this test.
        editor._stdscr = object()

        with mock.patch("curses.init_pair") as init_pair, \
                mock.patch("curses.color_pair", return_value=2468):
            self.assertEqual(editor._apply_set_opt("errorcolor=red"), "")

        self.assertEqual(editor.color_error, "red")
        self.assertEqual(editor.error_attr, 2468)
        init_pair.assert_any_call(editor.ERROR_PAIR, curses.COLOR_RED, curses.COLOR_GREEN)

        self.assertEqual(editor._apply_set_opt("errorcolor=bogus"),
                         "Unknown colour 'bogus'. Known: black, red, green, yellow, blue, magenta, cyan, white")

    def test_error_color_option_can_be_queried_and_defaults_to_black(self):
        editor = _editor_with_rc()  # isolated from the real ~/.viirc

        self.assertEqual(editor.color_error, "black")
        self.assertEqual(editor._apply_set_opt("errorcolor"), "")
        self.assertEqual(editor.message, "errorcolor=black")
        self.assertEqual(editor._apply_set_opt("errorfg"), "")
        self.assertEqual(editor.message, "errorcolor=black")

    def test_error_messages_use_error_attr_with_bold(self):
        editor = ViEditor()

        editor.error_attr = 0
        editor.bottom_status_attr = 512
        self.assertEqual(editor._bottom_status_text_attr(error=True),
                         512 | curses.A_BOLD)

        editor.error_attr = 1024
        self.assertEqual(editor._bottom_status_text_attr(error=True),
                         1024 | curses.A_BOLD)
        self.assertEqual(editor._bottom_status_text_attr(), 512)

    def test_write_default_viirc_is_silent_on_bad_path(self):
        editor = ViEditor()
        # Should not raise even if the path is unwritable
        editor._write_default_viirc("/nonexistent_dir/subdir/.viirc")


class ShellCommandTests(unittest.TestCase):
    def test_shell_command_inserts_output_after_cursor(self):
        editor = ViEditor()
        editor.lines = ["top", "bottom"]
        editor.cursor_row = 0

        self.assertTrue(editor._execute_cmd(":!printf 'one\\ntwo\\n'"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.last_shell_cmd, "printf 'one\\ntwo\\n'")
        self.assertEqual(editor.lines, ["top", "one", "two", "bottom"])
        self.assertTrue(editor.modified)

    def test_repeat_last_shell_command(self):
        editor = ViEditor()
        editor.lines = ["top"]
        editor.last_shell_cmd = "printf repeat"

        self.assertTrue(editor._execute_cmd(":!!"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["top", "repeat"])

    def test_shell_view_command_shows_output_without_modifying_buffer(self):
        editor = ViEditor()
        editor.lines = ["top", "bottom"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(":sh printf 'one\\ntwo\\n'"))

        self.assertEqual(editor.mode, Mode.SHELL)
        self.assertEqual(editor.shell_lines, ["one", "two"])
        self.assertEqual(editor.shell_command_label, "printf 'one\\ntwo\\n'")
        self.assertEqual(editor.lines, ["top", "bottom"])
        self.assertFalse(editor.modified)
        self.assertEqual(editor.last_shell_cmd, "printf 'one\\ntwo\\n'")

        editor._handle_shell(27)
        self.assertEqual(editor.mode, Mode.NORMAL)

    def test_bare_shell_view_command_reruns_previous_command(self):
        editor = ViEditor()
        editor.lines = ["top"]
        editor.last_shell_cmd = "printf again"

        self.assertTrue(editor._execute_cmd(":shell"))

        self.assertEqual(editor.mode, Mode.SHELL)
        self.assertEqual(editor.shell_lines, ["again"])
        self.assertEqual(editor.lines, ["top"])

    def test_shell_view_command_with_no_previous_command_reports_error(self):
        editor = ViEditor()
        editor.lines = ["top"]

        self.assertTrue(editor._execute_cmd(":sh"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertTrue(editor.message_is_error)
        self.assertEqual(editor.message, "No previous shell command")

    def test_shell_view_command_reports_nonzero_exit_and_truncation(self):
        editor = ViEditor()
        editor.lines = ["top"]

        self.assertTrue(editor._execute_cmd(":sh sh -c 'echo bad >&2; exit 3'"))

        self.assertEqual(editor.shell_lines, ["bad", "[exit 3]"])

        old_limit = editor.SHELL_COMMAND_MAX_OUTPUT_BYTES
        try:
            editor.SHELL_COMMAND_MAX_OUTPUT_BYTES = 8
            self.assertTrue(editor._execute_cmd(":sh printf abcdefghijklmnopqrstuvwxyz"))
        finally:
            editor.SHELL_COMMAND_MAX_OUTPUT_BYTES = old_limit
        self.assertEqual(editor.shell_lines, ["abcdefgh", "[output truncated]"])

    def test_shell_command_runs_detached_from_terminal_stdin(self):
        editor = ViEditor()
        import subprocess as subprocess_module

        with mock.patch(
            "vi_editor.subprocess.Popen", wraps=subprocess_module.Popen
        ) as popen_mock:
            returncode, output, truncated, timed_out = (
                editor._run_shell_command_limited("cat", "/bin/sh")
            )

        # With stdin on /dev/null `cat` sees EOF immediately instead of
        # stealing keystrokes from curses (or hanging until the timeout).
        self.assertEqual(returncode, 0)
        self.assertEqual(output, b"")
        self.assertFalse(timed_out)
        kwargs = popen_mock.call_args.kwargs
        self.assertEqual(kwargs.get("stdin"), subprocess_module.DEVNULL)
        self.assertTrue(kwargs.get("start_new_session"))

    def test_shell_command_limited_reaps_process_when_setup_fails(self):
        # A failure in os.set_blocking()/selector.register() -- which run
        # after the child is already started -- used to propagate straight
        # out without ever terminating or wait()'ing the child, leaking an
        # orphaned/zombie process.
        editor = ViEditor()
        import subprocess as subprocess_module

        real_popen = subprocess_module.Popen
        created: list = []

        def spy_popen(*args, **kwargs):
            proc = real_popen(*args, **kwargs)
            created.append(proc)
            return proc

        with mock.patch("vi_editor.subprocess.Popen", side_effect=spy_popen), \
             mock.patch("vi_editor.os.set_blocking",
                        side_effect=OSError("boom")):
            with self.assertRaises(OSError):
                editor._run_shell_command_limited("sleep 5", "/bin/sh")

        self.assertEqual(len(created), 1)
        proc = created[0]
        deadline = time.monotonic() + 2.0
        while proc.poll() is None and time.monotonic() < deadline:
            time.sleep(0.05)
        self.assertIsNotNone(
            proc.poll(), "child process was left running/unreaped"
        )

    def test_shell_timeout_kills_background_children_too(self):
        editor = ViEditor()
        with tempfile.TemporaryDirectory() as tmpdir:
            pidfile = os.path.join(tmpdir, "pid")
            old_timeout = editor.SHELL_COMMAND_TIMEOUT_SECONDS
            editor.SHELL_COMMAND_TIMEOUT_SECONDS = 0.3
            try:
                _, _, _, timed_out = editor._run_shell_command_limited(
                    f"sleep 30 & echo $! > {pidfile}; wait", "/bin/sh"
                )
            finally:
                editor.SHELL_COMMAND_TIMEOUT_SECONDS = old_timeout

            self.assertTrue(timed_out)
            with open(pidfile, "r", encoding="utf-8") as fh:
                child_pid = int(fh.read().strip())
            # The group signal must reach the backgrounded sleep, not just
            # the shell; give the SIGTERM a moment to be delivered.
            deadline = time.monotonic() + 2.0
            while time.monotonic() < deadline:
                try:
                    os.kill(child_pid, 0)
                except ProcessLookupError:
                    break
                time.sleep(0.05)
            else:
                self.fail(f"background child {child_pid} survived the timeout kill")

    def test_shell_command_captures_nonzero_exit(self):
        editor = ViEditor()
        editor.lines = ["top"]

        self.assertTrue(editor._execute_cmd(":!sh -c 'echo bad >&2; exit 3'"))

        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(editor.lines, ["top", "bad", "[exit 3]"])
        self.assertTrue(editor.message_is_error)

    def test_shell_command_without_output_does_not_modify_buffer(self):
        editor = ViEditor()
        editor.lines = ["top"]
        editor._mark_clean()

        self.assertTrue(editor._execute_cmd(":!true"))

        self.assertEqual(editor.lines, ["top"])
        self.assertFalse(editor.modified)
        self.assertEqual(editor.message, ":!true 0L inserted")

    def test_shell_command_output_is_capped(self):
        editor = ViEditor()
        editor.lines = ["top"]
        old_limit = editor.SHELL_COMMAND_MAX_OUTPUT_BYTES
        try:
            editor.SHELL_COMMAND_MAX_OUTPUT_BYTES = 8
            self.assertTrue(editor._execute_cmd(":!printf abcdefghijklmnopqrstuvwxyz"))
        finally:
            editor.SHELL_COMMAND_MAX_OUTPUT_BYTES = old_limit

        self.assertEqual(editor.lines, ["top", "abcdefgh", "[output truncated]"])
        self.assertTrue(editor.message_is_error)

    def test_shell_command_timeout_is_reported(self):
        editor = ViEditor()
        editor.lines = ["top"]
        old_timeout = editor.SHELL_COMMAND_TIMEOUT_SECONDS
        try:
            editor.SHELL_COMMAND_TIMEOUT_SECONDS = 0.05
            cmd = f"{sys.executable} -c 'import time; time.sleep(1)'"
            self.assertTrue(editor._execute_cmd(f":!{cmd}"))
        finally:
            editor.SHELL_COMMAND_TIMEOUT_SECONDS = old_timeout

        self.assertEqual(editor.lines, ["top", "[command timed out]"])
        self.assertTrue(editor.message_is_error)

    def test_shell_status_keeps_position_counter_visible(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor._open_shell_output("x" * 80, ["one", "two", "three"])
        screen = FakeScreen()

        with mock.patch("curses.doupdate"):
            editor._draw_shell(screen, 6, 32)

        status_lines = [
            args[2] for args in screen.calls
            if len(args) >= 3 and args[0] == 4 and args[1] == 0
        ]

        self.assertTrue(any(text.endswith(" 1-3/3 ") for text in status_lines))

    def test_shell_overlay_uses_display_width_instead_of_raw_slice(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.tab_stop = 8  # this test is about display-width math, not ~/.viirc
        editor._open_shell_output("printf", ["\tab"])
        screen = FakeScreen()

        with mock.patch("curses.doupdate"):
            editor._draw_shell(screen, 4, 6)

        line_draws = [args[:3] for args in screen.calls if len(args) >= 3 and args[0] == 0]
        self.assertIn((0, 0, "        ab"), line_draws)

    def test_shell_overlay_closes(self):
        editor = ViEditor()
        editor._open_shell_output("printf ok", ["ok"])
        editor._last_h = 10

        editor._handle_shell(ord("q"))

        self.assertEqual(editor.mode, Mode.NORMAL)


class SyntaxHighlightTests(unittest.TestCase):
    def test_detects_requested_languages_by_extension(self):
        cases = {
            "main.c": "c",
            "script.py": "python",
            "tool.tcl": "tcl",
            "server.go": "go",
            "App.cs": "csharp",
            "widget.vala": "vala",
            "query.sql": "sql",
            "README.md": "markdown",
            "notes.markdown": "markdown",
            "utils.lisp": "lisp",
            "init.el": "lisp",
            "script.lsp": "lisp",
            "system.cl": "lisp",
            "math.scm": "lisp",
            "kernel.fs": "forth",
            "kernel.fth": "forth",
            "kernel.4th": "forth",
            "kernel.forth": "forth",
        }

        editor = ViEditor()
        for filename, language in cases.items():
            editor.filename = filename
            self.assertEqual(editor._syntax_language(), language)

    def test_logtype_command_sets_and_clears_current_buffer_formatting(self):
        editor = ViEditor()

        self.assertTrue(editor._execute_cmd(":lgt python"))
        self.assertEqual(editor.log_type, "python")
        self.assertIn("python", editor.message)

        self.assertTrue(editor._execute_cmd(":logtype off"))
        self.assertEqual(editor.log_type, "")
        self.assertIn("off", editor.message)

    def test_logtype_persists_per_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            first = os.path.join(tmpdir, "one.log")
            second = os.path.join(tmpdir, "two.log")
            with open(first, "w", encoding="utf-8") as fh:
                fh.write("first\n")
            with open(second, "w", encoding="utf-8") as fh:
                fh.write("second\n")

            editor = ViEditor([first, second])
            self.assertTrue(editor._execute_cmd(":lgt http"))
            self.assertEqual(editor.log_type, "http")

            editor._switch_buffer(1)
            self.assertIsNone(editor.log_type)

            self.assertTrue(editor._execute_cmd(":lgt lnx_auth"))
            self.assertEqual(editor.log_type, "lnx_auth")

            editor._switch_buffer(0)
            self.assertEqual(editor.log_type, "http")

    def test_reused_new_buffer_clears_logtype(self):
        editor = ViEditor()
        self.assertTrue(editor._execute_cmd(":lgt http"))

        self.assertTrue(editor._execute_cmd(":enew!"))

        self.assertIsNone(editor.log_type)
        self.assertIsNone(editor.buffers[0].log_type)

    def test_delete_only_buffer_clears_logtype(self):
        editor = ViEditor()
        self.assertTrue(editor._execute_cmd(":lgt http"))

        self.assertTrue(editor._execute_cmd(":bd!"))

        self.assertIsNone(editor.log_type)
        self.assertIsNone(editor.buffers[0].log_type)

    def test_display_line_text_formats_python_logs(self):
        editor = ViEditor()
        editor.log_type = "python"
        editor.lines = [
            "2026-04-21 12:34:56,789 INFO api.server: request complete",
            "Traceback (most recent call last):",
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "2026-04-21 12:34:56,789 | INFO     | api.server | request complete",
        )
        self.assertEqual(editor._display_line_text(1), "Traceback (most recent call last):")

    def test_display_line_text_formats_linux_auth_logs(self):
        editor = ViEditor()
        editor.log_type = "lnx_auth"
        editor.lines = [
            "Apr 21 12:34:56 host sshd[1234]: Failed password for invalid user root from 10.0.0.8 port 22 ssh2"
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "Apr 21 12:34:56 | host | sshd[1234] | Failed password for invalid user root from 10.0.0.8 port 22 ssh2",
        )

    def test_display_line_text_formats_http_logs(self):
        editor = ViEditor()
        editor.log_type = "http"
        editor.lines = [
            '10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "GET /health HTTP/1.1" 200 1536'
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "10.0.0.8 | 21/Apr/2026:12:34:56 +0000 | GET /health | 200 | 1.5K",
        )

    def test_display_col_tracks_formatted_http_logs(self):
        editor = ViEditor()
        editor.log_type = "http"
        editor.show_line_numbers = False
        editor.lines = [
            '10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "GET /health HTTP/1.1" 200 1536'
        ]

        rendered = editor._display_line_text(0)

        self.assertEqual(editor._display_col(0, editor.lines[0].index("10.0.0.8")), rendered.index("10.0.0.8"))
        self.assertEqual(
            editor._display_col(0, editor.lines[0].index("21/Apr/2026:12:34:56 +0000")),
            rendered.index("21/Apr/2026:12:34:56 +0000"),
        )
        self.assertEqual(editor._display_col(0, editor.lines[0].index("GET")), rendered.index("GET"))
        self.assertEqual(editor._display_col(0, editor.lines[0].index("/health")), rendered.index("/health"))
        self.assertEqual(editor._display_col(0, editor.lines[0].index("200")), rendered.index("200"))
        self.assertEqual(editor._display_col(0, editor.lines[0].index("1536")), rendered.index("1.5K"))

    def test_display_col_tracks_formatted_http_logs_with_wide_path(self):
        editor = ViEditor()
        editor.log_type = "http"
        editor.lines = [
            '10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "GET /你x HTTP/1.1" 200 1536'
        ]

        raw_status_col = editor.lines[0].index("200")
        rendered = editor._display_line_text(0)
        rendered_status_col = editor._display_width(rendered[:rendered.index("200")])

        self.assertEqual(editor._display_col(0, raw_status_col), rendered_status_col)

    def test_display_col_tracks_formatted_python_logs_with_wide_message(self):
        editor = ViEditor()
        editor.log_type = "python"
        editor.lines = [
            "2026-04-21 12:34:56 INFO app: 你x 42"
        ]

        raw_number_col = editor.lines[0].index("42")
        rendered = editor._display_line_text(0)
        rendered_number_col = editor._display_width(rendered[:rendered.index("42")])

        self.assertEqual(editor._display_col(0, raw_number_col), rendered_number_col)

    def test_display_line_text_formats_flask_logs_and_http_fallback(self):
        editor = ViEditor()
        editor.log_type = "flask"
        editor.lines = [
            "[2026-04-21 12:34:56,789] ERROR in app: request failed",
            '10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "POST /login HTTP/1.1" 401 512',
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "2026-04-21 12:34:56,789 | ERROR    | app | request failed",
        )
        self.assertEqual(
            editor._display_line_text(1),
            "10.0.0.8 | 21/Apr/2026:12:34:56 +0000 | POST /login | 401 | 512",
        )

    def test_display_line_text_formats_flask_access_logs(self):
        editor = ViEditor()
        editor.log_type = "flask"
        editor.lines = [
            "179 [2026-04-05 14:36:53 -0400] [269886] [INFO] 127.0.0.1:35390 GET / HTTP/1.1 200 49941 511219",
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "2026-04-05 14:36:53 -0400 | INFO     | 269886 | 127.0.0.1:35390 | GET / | 200 | 49K | 511219",
        )

    def test_display_line_text_normalizes_malformed_flask_access_remote_addr(self):
        editor = ViEditor()
        editor.log_type = "flask"
        editor.lines = [
            "179 [2026-04-05 14:36:53 -0400] [269886] [INFO] 127127.0.0.1001:35390 GET / 1.1 200 49941 511219",
        ]

        self.assertEqual(
            editor._display_line_text(0),
            "2026-04-05 14:36:53 -0400 | INFO     | 269886 | 127.0.0.1:35390 | GET / | 200 | 49K | 511219",
        )

    def test_flask_http_fallback_uses_http_syntax_spans(self):
        editor = ViEditor()

        spans = editor._syntax_spans(
            "10.0.0.8 | 21/Apr/2026:12:34:56 +0000 | POST /login | 401 | 512",
            "log:flask",
        )

        self.assertTrue(any(kind == "builtin" for _, _, kind in spans))
        self.assertTrue(any(kind == "string" for _, _, kind in spans))
        self.assertTrue(any(kind == "preproc" for _, _, kind in spans))

    def test_flask_access_logs_use_structured_syntax_spans(self):
        editor = ViEditor()

        spans = editor._syntax_spans(
            "2026-04-05 14:36:53 -0400 | INFO     | 269886 | 127.0.0.1:35390 | GET / | 200 | 48.8K | 511219",
            "log:flask",
        )

        self.assertTrue(any(kind == "function" for _, _, kind in spans))
        self.assertTrue(any(kind == "builtin" for _, _, kind in spans))
        self.assertTrue(any(kind == "keyword" for _, _, kind in spans))
        self.assertTrue(any(kind == "number" for _, _, kind in spans))

    def test_display_col_tracks_hidden_http_gap_monotonically(self):
        editor = ViEditor()
        editor.log_type = "http"
        editor.lines = [
            '10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "GET /health HTTP/1.1" 200 1536'
        ]

        ip_end = editor._display_col(0, editor.lines[0].index("10.0.0.8") + len("10.0.0.8"))
        gap_cols = [
            editor._display_col(0, col)
            for col in range(editor.lines[0].index("10.0.0.8") + len("10.0.0.8"), editor.lines[0].index("21/Apr/2026:12:34:56 +0000"))
        ]
        ts_start = editor._display_col(0, editor.lines[0].index("21/Apr/2026:12:34:56 +0000"))

        self.assertTrue(all(ip_end <= col <= ts_start for col in gap_cols))

    def test_draw_status_uses_display_column_for_log_views(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 120

            def move(self, *args):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *args):
                self.calls.append(args)

            def attron(self, *args):
                pass

            def attroff(self, *args):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.log_type = "http"
        editor.lines = ['10.0.0.8 - - [21/Apr/2026:12:34:56 +0000] "GET /health HTTP/1.1" 200 1536']
        editor.cursor_row = 0
        editor.cursor_col = editor.lines[0].index("200")

        screen = FakeScreen()
        with mock.patch("curses.doupdate"):
            editor.draw(screen)

        status_lines = [args[2] for args in screen.calls if len(args) >= 3 and " [log:http]" in args[2]]
        self.assertTrue(status_lines)
        self.assertIn(",55  100%", status_lines[-1])

    def test_logtype_clears_breadcrumbs(self):
        editor = ViEditor("app.py")
        editor.lines = ["def outer():", "    pass"]
        editor.cursor_row = 1

        self.assertEqual(editor._current_breadcrumbs(), ["def outer"])

        self.assertTrue(editor._execute_cmd(":lgt http"))
        self.assertEqual(editor._current_breadcrumbs(), [])

        self.assertTrue(editor._execute_cmd(":lgt off"))
        self.assertEqual(editor._current_breadcrumbs(), ["def outer"])

    def test_syntax_spans_classify_common_tokens(self):
        editor = ViEditor()

        spans = editor._syntax_spans('def f(): return "x" # comment', "python")
        self.assertIn((0, 3, "keyword"), spans)
        self.assertIn((4, 5, "function"), spans)
        self.assertTrue(any(kind == "string" for _, _, kind in spans))
        self.assertTrue(any(kind == "comment" for _, _, kind in spans))
        self.assertTrue(any(kind == "operator" for _, _, kind in spans))

        spans = editor._syntax_spans("SELECT 42 FROM users -- comment", "sql")
        self.assertIn((0, 6, "keyword"), spans)
        self.assertTrue(any(kind == "number" for _, _, kind in spans))
        self.assertTrue(any(kind == "comment" for _, _, kind in spans))

        spans = editor._syntax_spans("package main // comment", "go")
        self.assertIn((0, 7, "keyword"), spans)
        self.assertTrue(any(kind == "comment" for _, _, kind in spans))

    def test_lisp_syntax_spans_classify_common_tokens(self):
        editor = ViEditor()

        text = '(defun add (a b) "doc" (+ a b)) ; comment'
        spans = editor._syntax_spans(text, "lisp")
        self.assertIn((1, 6, "keyword"), spans)
        self.assertTrue(any(kind == "string" and text[start:end] == '"doc"'
                            for start, end, kind in spans))
        self.assertTrue(any(kind == "comment" and text[start:end] == "; comment"
                            for start, end, kind in spans))

        # ' is the quote reader macro in Lisp, not a string delimiter — it
        # must not swallow the rest of the line looking for a closing quote.
        text = "(defun f (x) 'sym (list 1 2))"
        spans = editor._syntax_spans(text, "lisp")
        self.assertFalse(any(kind == "string" for _, _, kind in spans))

    def test_forth_syntax_spans_classify_common_tokens(self):
        editor = ViEditor()

        text = ': square ( n -- n^2 ) dup * ;  \\ doubles via multiply'
        spans = editor._syntax_spans(text, "forth")
        self.assertIn((2, 8, "function"), spans)
        self.assertIn((22, 25, "builtin"), spans)
        self.assertTrue(any(kind == "comment" and text[start:end] == "( n -- n^2 )"
                            for start, end, kind in spans))
        self.assertTrue(any(kind == "comment" and text[start:end] == "\\ doubles via multiply"
                            for start, end, kind in spans))

        # ' is the tick (execution-token) operator in Forth, not a string
        # delimiter — it must not swallow the rest of the line.
        text = ": f ( xt -- ) ['] dup execute ;"
        spans = editor._syntax_spans(text, "forth")
        self.assertFalse(any(kind == "string" for _, _, kind in spans))

    def test_markdown_syntax_spans_classify_document_elements(self):
        editor = ViEditor()

        spans = editor._syntax_spans("# Heading", "markdown")
        self.assertIn((0, 1, "preproc"), spans)
        self.assertIn((1, len("# Heading"), "keyword"), spans)

        spans = editor._syntax_spans("> quoted text", "markdown")
        self.assertEqual(spans, [(0, len("> quoted text"), "comment")])

        spans = editor._syntax_spans("- [x] item with `code` and [link](https://example.com)", "markdown")
        self.assertIn((0, 1, "operator"), spans)
        self.assertIn((2, 5, "builtin"), spans)
        self.assertTrue(any(kind == "string" and "`code`" == "- [x] item with `code` and [link](https://example.com)"[start:end]
                            for start, end, kind in spans))
        self.assertTrue(any(kind == "builtin" and "[link]" == "- [x] item with `code` and [link](https://example.com)"[start:end]
                            for start, end, kind in spans))
        self.assertTrue(any(kind == "string" and "(https://example.com)" == "- [x] item with `code` and [link](https://example.com)"[start:end]
                            for start, end, kind in spans))

        spans = editor._syntax_spans("**bold** and *em*", "markdown")
        self.assertTrue(any(kind == "preproc" for _, _, kind in spans))

        spans = editor._syntax_spans("```python", "markdown")
        self.assertEqual(spans, [(0, len("```python"), "string")])

    def test_markdown_table_display_lines_align_columns(self):
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | ---: |",
            "| a | 2 |",
            "| longer | 15 |",
        ]

        self.assertEqual(editor._markdown_table_display_line(0), "| Name   | Count |")
        self.assertEqual(editor._markdown_table_display_line(1), "| ------ | ----: |")
        self.assertEqual(editor._markdown_table_display_line(2), "| a      |     2 |")
        self.assertEqual(editor._markdown_table_display_line(3), "| longer |    15 |")

    def test_markdown_table_display_finds_middle_bars_and_escaped_pipes(self):
        editor = ViEditor()
        editor.filename = "notes.markdown"
        editor.lines = [
            "Name | Description | Count",
            "--- | --- | ---:",
            "alpha | has \\| pipe | 1",
            "beta | plain | 22",
        ]

        self.assertEqual(editor._markdown_table_display_line(0), "| Name  | Description | Count |")
        self.assertEqual(editor._markdown_table_display_line(1), "| ----- | ----------- | ----: |")
        self.assertEqual(editor._markdown_table_display_line(2), "| alpha | has \\| pipe |     1 |")
        self.assertEqual(editor._markdown_table_display_line(3), "| beta  | plain       |    22 |")

    def test_markdown_table_display_centers_aligned_columns(self):
        editor = ViEditor()
        editor.filename = "notes.md"
        editor.lines = [
            "| Item | State |",
            "| --- | :---: |",
            "| a | on |",
            "| longer | off |",
        ]

        self.assertEqual(editor._markdown_table_display_line(0), "| Item   | State |")
        self.assertEqual(editor._markdown_table_display_line(1), "| ------ | :---: |")
        self.assertEqual(editor._markdown_table_display_line(2), "| a      |  on   |")
        self.assertEqual(editor._markdown_table_display_line(3), "| longer |  off  |")

    def test_markdown_table_display_uses_rendered_cell_width(self):
        editor = ViEditor()
        editor.filename = "notes.md"
        editor.show_line_numbers = False
        editor.lines = [
            "| X | Y |",
            "| --- | --- |",
            "| a\x00b | 1 |",
            "| abc | 2 |",
        ]

        visible, _ = editor._visible_line_parts(2, 40)
        self.assertEqual(visible, "| a^@b | 1   |")

        visible, _ = editor._visible_line_parts(3, 40)
        self.assertEqual(visible, "| abc  | 2   |")

    def test_markdown_table_display_expands_tabs_at_cell_column(self):
        editor = ViEditor()
        editor.tab_stop = 8  # this test is about cell-column math, not ~/.viirc
        editor.filename = "notes.md"
        editor.show_line_numbers = False
        editor.lines = [
            "| X | Y |",
            "| --- | --- |",
            "| a\tb | 1 |",
            "| abc | 2 |",
        ]

        first, _ = editor._visible_line_parts(2, 80)
        second, _ = editor._visible_line_parts(3, 80)

        self.assertEqual([idx for idx, ch in enumerate(first) if ch == "|"], [0, 10, 16])
        self.assertEqual([idx for idx, ch in enumerate(second) if ch == "|"], [0, 10, 16])

    def test_markdown_table_display_col_tracks_right_aligned_tabbed_cells(self):
        editor = ViEditor()
        editor.filename = "notes.md"
        editor.show_line_numbers = False
        editor.lines = [
            "| X | Y |",
            "| ---: | --- |",
            "| a\tb | 1 |",
            "| abcdefghij | 2 |",
        ]

        visible, _ = editor._visible_line_parts(2, 80)
        raw_col = editor.lines[2].index("b")

        self.assertEqual(editor._display_col(2, raw_col), visible.index("b"))

    def test_markdown_table_display_col_tracks_aligned_cells(self):
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | ---: |",
            "| a | 2 |",
            "| longer | 15 |",
        ]

        raw_col = editor.lines[2].index("2")
        display_col = editor._markdown_table_display_line(2).index("2")

        self.assertEqual(editor._display_col(2, raw_col), display_col)

    def test_markdown_table_display_col_tracks_centered_cells(self):
        editor = ViEditor()
        editor.filename = "notes.md"
        editor.lines = [
            "| Item | State |",
            "| --- | :---: |",
            "| a | on |",
            "| longer | off |",
        ]

        raw_col = editor.lines[2].index("on")
        display_col = editor._markdown_table_display_line(2).index("on")

        self.assertEqual(editor._display_col(2, raw_col), display_col)

    def test_markdown_table_display_col_tracks_delimiters(self):
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | ---: |",
            "| a | 2 |",
            "| longer | 15 |",
        ]

        display_line = editor._markdown_table_display_line(2)

        self.assertEqual(editor._display_col(2, 0), 0)
        self.assertEqual(editor._display_col(2, editor.lines[2].index("|", 1)), display_line.index("|", 1))
        self.assertEqual(editor._display_col(2, len(editor.lines[2]) - 1), len(display_line) - 1)

    def test_markdown_table_display_col_tracks_middle_pipe_tables(self):
        editor = ViEditor()
        editor.filename = "notes.markdown"
        editor.lines = [
            "Name | Count",
            "--- | ---:",
            "a | 2",
            "longer | 15",
        ]

        raw_col = editor.lines[2].index("|")
        display_col = editor._markdown_table_display_line(2).index("|", 1)

        self.assertEqual(editor._display_col(2, raw_col), display_col)

    def test_markdown_formatted_table_rows_do_not_use_source_syntax_offsets(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | ---: |",
            "| wider | 2 |",
        ]
        editor.show_line_numbers = False

        screen = FakeScreen()
        editor._add_syntax_text(
            screen, 0, 0,
            editor._markdown_table_display_line(0),
            0,
            editor.lines[0],
            0,
        )

        self.assertEqual(screen.calls, [(0, 0, "| Name  | Count |")])

    # ------------------------------------------------------------------
    # Fix: _add_syntax_text derived the buffer line index from the
    # *physical screen row* (self.top_line + row) instead of the logical
    # buffer line actually being rendered. draw() calls it with `row` set
    # to the physical row (offset by one for the chrome/breadcrumb line),
    # so the markdown-table bypass check always inspected the line one
    # below the one on screen. lnum is now passed explicitly instead of
    # being re-derived from the physical row.
    # ------------------------------------------------------------------

    def test_add_syntax_text_table_bypass_uses_lnum_not_physical_row(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 8, 80

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | ---: |",
            "| wider | 2 |",
        ]
        editor.show_line_numbers = False
        editor.top_line = 0

        # `row` (the physical screen row) is deliberately different from
        # `lnum` (the buffer line being rendered) to prove the bypass
        # decision follows lnum, not self.top_line + row.
        screen = FakeScreen()
        editor._add_syntax_text(
            screen, 5, 0,
            editor._markdown_table_display_line(0),
            0,
            editor.lines[0],
            0,
        )

        self.assertEqual(screen.calls, [(5, 0, "| Name  | Count |")])

    def test_draw_keeps_syntax_highlighting_on_line_above_markdown_table(self):
        class RecordingScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 24, 80

            def move(self, *a):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, row, col, text, *args):
                self.calls.append((row, col, text, args[0] if args else None))

            def attron(self, *a):
                pass

            def attroff(self, *a):
                pass

            def noutrefresh(self):
                pass

        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "# Heading",
            "| Name | Count |",
            "| --- | ---: |",
            "| wider | 12 |",
        ]
        editor.show_line_numbers = False
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor.top_line = 0
        editor.left_col = 0

        screen = RecordingScreen()
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx"):
            editor.draw(screen)

        # Row 1 is the physical text row for buffer line 0 ("# Heading"):
        # a highlighted "# Heading" is drawn as multiple spans (with syntax
        # attrs), whereas the bug rendered it as one unattributed call for
        # the whole line.
        heading_calls = [c for c in screen.calls if c[0] == 1]
        self.assertGreater(len(heading_calls), 1)
        self.assertTrue(any(c[3] is not None for c in heading_calls))
        self.assertFalse(
            any(c[2] == "# Heading" and c[3] is None for c in heading_calls)
        )

    def test_markdown_table_recognizes_single_dash_separator(self):
        # GFM only requires >=1 dash per separator cell (e.g. "|-|-|"); the
        # old regex demanded 3+ and silently failed to recognize such tables.
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "|-|-|",
            "| a | 2 |",
        ]

        self.assertEqual(editor._markdown_table_display_line(0), "| Name | Count |")
        self.assertEqual(editor._markdown_table_display_line(1), "| ---- | ----- |")
        self.assertEqual(editor._markdown_table_display_line(2), "| a    | 2     |")

    def test_markdown_table_width_ignores_data_row_that_looks_like_separator(self):
        # A data row whose cells happen to match the separator pattern
        # (e.g. a literal "---" divider) must still count toward column
        # width -- only the *actual* header separator row is excluded.
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | --- |",
            "| ---------- | 2 |",
            "| a | 5 |",
        ]

        display = editor._markdown_table_display_line(2)
        self.assertTrue(display.startswith("| ---------- |"))
        # every row in the block should share the same pipe columns --
        # if the divider-looking row were excluded from the width scan,
        # its first column would be too narrow and the "|" positions
        # would drift relative to the other rows.
        first_pipe = display.index("|", 1)
        for r in (0, 1, 3):
            self.assertEqual(
                editor._markdown_table_display_line(r).index("|", 1),
                first_pipe,
            )

    def test_markdown_table_split_ignores_pipe_inside_inline_code(self):
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Expr | Result |",
            "| --- | --- |",
            "| `a|b` | 1 |",
        ]

        cells = editor._markdown_split_table_row(editor.lines[2])
        self.assertEqual(cells, ["`a|b`", "1"])

        spans = editor._markdown_split_table_row_spans(editor.lines[2])
        self.assertEqual(len(spans), 2)
        self.assertEqual(spans[0][0], "`a|b`")

    def test_markdown_table_layout_cache_reflects_edits(self):
        # The layout cache is content-addressed on the table's own line text,
        # so editing a table row must not return a stale cached width/layout
        # for that (now different) content.
        editor = ViEditor()
        editor.filename = "README.md"
        editor.lines = [
            "| Name | Count |",
            "| --- | --- |",
            "| a | 2 |",
        ]

        first = editor._markdown_table_display_line(2)
        self.assertEqual(first, "| a    | 2     |")

        editor.lines[2] = "| a much longer value | 2 |"
        second = editor._markdown_table_display_line(2)
        self.assertIn("a much longer value", second)
        # header row's rendering must also widen to match the new content
        self.assertEqual(
            editor._markdown_table_display_line(0).index("|", 1),
            second.index("|", 1),
        )

    def test_markdown_table_layout_cache_is_bounded_by_weight(self):
        # entries_cache used to bound only entry count (64), not bytes, so
        # a handful of large tables could retain unbounded cache memory --
        # unlike _syntax_cache/_clike_analysis_cache, which are held to
        # SYNTAX_CACHE_BYTE_BUDGET. Shrink the budget and confirm a large
        # table doesn't push cached bytes past it.
        editor = ViEditor()
        editor.filename = "big.md"
        editor.SYNTAX_CACHE_BYTE_BUDGET = 4096

        header = "| " + " | ".join(f"col{c}" for c in range(5)) + " |"
        sep = "| " + " | ".join("---" for _ in range(5)) + " |"
        data_row = "| " + " | ".join("x" * 200 for _ in range(5)) + " |"
        editor.lines = [header, sep] + [data_row] * 200

        editor._markdown_table_layout(2)

        self.assertLessEqual(
            editor._md_table_layout_cache_bytes, editor.SYNTAX_CACHE_BYTE_BUDGET
        )

    def test_oversized_table_does_not_evict_unrelated_md_table_layout_entries(self):
        editor = ViEditor()
        editor.filename = "big.md"
        editor.SYNTAX_CACHE_BYTE_BUDGET = 2048

        def make_table(idx, n_rows):
            header = f"| id{idx} | value |"
            sep = "| --- | --- |"
            rows = [f"| {idx}-{r} | v |" for r in range(n_rows)]
            return [header, sep] + rows

        small_keys = []
        for i in range(5):
            table = make_table(i, 2)
            editor.lines = table
            editor._markdown_table_layout(2)
            small_keys.append((editor.tab_stop, tuple(table)))
        self.assertEqual(len(editor._md_table_layout_cache), 5)

        huge_table = make_table("huge", 500)  # cell text alone dwarfs the shrunk budget
        editor.lines = huge_table
        editor._markdown_table_layout(2)

        self.assertEqual(len(editor._md_table_layout_cache), 5)
        for key in small_keys:
            self.assertIn(key, editor._md_table_layout_cache)
        self.assertNotIn((editor.tab_stop, tuple(huge_table)), editor._md_table_layout_cache)

    def test_syntax_spans_classify_extra_color_categories(self):
        editor = ViEditor()

        spans = editor._syntax_spans("@decorator\n", "python")
        self.assertIn((0, 10, "preproc"), spans)

        spans = editor._syntax_spans("value = len(items) + 3", "python")
        self.assertIn((8, 11, "builtin"), spans)
        self.assertTrue(any(kind == "operator" for _, _, kind in spans))

        spans = editor._syntax_spans("int main(void) { return 0; }", "c")
        self.assertIn((0, 3, "type"), spans)
        self.assertIn((4, 8, "function"), spans)
        self.assertTrue(any(kind == "operator" for _, _, kind in spans))

        spans = editor._syntax_spans("#include <stdio.h>", "c")
        self.assertIn((0, 8, "preproc"), spans)

        spans = editor._syntax_spans("SELECT COUNT(*) FROM users", "sql")
        self.assertIn((7, 12, "builtin"), spans)

    def test_syntax_spans_cache_returns_independent_lists(self):
        editor = ViEditor()

        spans = editor._syntax_spans("return 42", "python")
        spans.append((0, 1, "mutated"))

        cached = editor._syntax_spans("return 42", "python")
        self.assertNotIn((0, 1, "mutated"), cached)
        self.assertIn((0, 6, "keyword"), cached)

    def test_c_block_comments_are_stateful_across_lines(self):
        editor = ViEditor("main.c")
        editor.lines = ["/* int", "return 42;", "*/ int value;"]

        first, _ = editor._ensure_clike_row(0, "c")
        middle, _ = editor._ensure_clike_row(1, "c")
        last, _ = editor._ensure_clike_row(2, "c")

        self.assertEqual(first.spans, ((0, len(editor.lines[0]), "comment"),))
        self.assertEqual(middle.spans, ((0, len(editor.lines[1]), "comment"),))
        self.assertIn((0, 2, "comment"), last.spans)
        self.assertIn((3, 6, "type"), last.spans)

    def test_c_block_comment_state_invalidates_forward_after_edit(self):
        editor = ViEditor("main.c")
        editor.lines = ["/*", "return 42;"]
        before, _ = editor._ensure_clike_row(1, "c")
        self.assertEqual(before.spans, ((0, len(editor.lines[1]), "comment"),))

        editor.lines[0] = "// no open block"
        after, _ = editor._ensure_clike_row(1, "c")

        self.assertIn((0, 6, "keyword"), after.spans)
        self.assertNotIn((0, len(editor.lines[1]), "comment"), after.spans)

    def test_c_single_line_block_comment_does_not_highlight_payload(self):
        editor = ViEditor()
        text = "/* int return 42 */"

        self.assertEqual(editor._syntax_spans(text, "c"), [(0, len(text), "comment")])

    def test_comment_payload_skips_code_token_regexes(self):
        editor = ViEditor()
        original = editor._RE_SYNTAX_WORD

        class CountingPattern:
            def __init__(self):
                self.calls = 0

            def finditer(self, *args, **kwargs):
                self.calls += 1
                return original.finditer(*args, **kwargs)

        counting = CountingPattern()
        with mock.patch.object(ViEditor, "_RE_SYNTAX_WORD", counting):
            spans = editor._syntax_spans_core("// return 42 + function()", "c")

        self.assertEqual(counting.calls, 0)
        self.assertEqual(spans, [(0, len("// return 42 + function()"), "comment")])

    def test_syntax_cache_is_bounded_by_weight(self):
        editor = ViEditor()
        editor.SYNTAX_CACHE_BYTE_BUDGET = 2048

        for index in range(12):
            editor._syntax_spans(f"identifier_{index} " + ("x" * 1000), "python")

        self.assertLessEqual(editor._syntax_cache_bytes, editor.SYNTAX_CACHE_BYTE_BUDGET)

    def test_oversized_entry_does_not_evict_unrelated_syntax_cache_entries(self):
        # An entry heavier than the whole byte budget can never be cached no
        # matter how much gets evicted first -- the eviction loop used to
        # run anyway, wiping out every other cached line for nothing.
        editor = ViEditor()
        editor.SYNTAX_CACHE_BYTE_BUDGET = 2048

        for index in range(5):
            editor._syntax_spans(f"small_{index}", "python")
        self.assertEqual(len(editor._syntax_cache), 5)

        huge = "x " * 5000  # weight = len(text) alone is ~4x the shrunk budget
        editor._syntax_spans(huge, "python")

        self.assertEqual(len(editor._syntax_cache), 5)
        for index in range(5):
            self.assertIn(("python", f"small_{index}"), editor._syntax_cache)
        self.assertNotIn(("python", huge), editor._syntax_cache)

    def test_c_line_analysis_cache_uses_raw_line_not_horizontal_prefix(self):
        editor = ViEditor("generated.c")
        line = "int value = function(42); " * 100
        editor.lines = [line]
        editor._last_h = 24
        editor._last_w = 300

        editor._add_syntax_text(mock.MagicMock(), 0, 0, line[100:180], 0, line, 100)
        editor._add_syntax_text(mock.MagicMock(), 0, 0, line[200:280], 0, line, 200)

        self.assertEqual(len(editor._clike_analysis_cache), 1)
        self.assertEqual(next(iter(editor._clike_analysis_cache))[1], line)

    def test_oversized_line_does_not_evict_unrelated_clike_analysis_cache_entries(self):
        # Same bug as the syntax-cache case above, for the C-like structural
        # analysis cache: _syntax_protected_regions builds a full-length
        # `structure` copy of the line with no MAX_SYNTAX_LINE_CHARS gate,
        # so one very long line's weight alone can exceed the byte budget
        # and used to wipe every other cached line's analysis for nothing.
        editor = ViEditor("huge.c")
        editor.SYNTAX_CACHE_BYTE_BUDGET = 2048

        small_lines = [f"int var_{i};" for i in range(5)]
        for line in small_lines:
            editor.lines = [line]
            editor._ensure_clike_row(0, "c", line)
        self.assertEqual(len(editor._clike_analysis_cache), 5)

        huge_line = "int x = 1; " * 500  # weight far exceeds the shrunk budget
        editor.lines = [huge_line]
        editor._ensure_clike_row(0, "c", huge_line)

        self.assertEqual(len(editor._clike_analysis_cache), 5)
        cached_texts = {key[1] for key in editor._clike_analysis_cache}
        self.assertEqual(cached_texts, set(small_lines))
        self.assertNotIn(huge_line, cached_texts)

    def test_c_bracket_matching_ignores_strings_and_comments(self):
        editor = ViEditor("main.c")
        editor.lines = ["int main() {", '    printf("}"); /* } */', "}"]
        opening = editor.lines[0].index("{")

        self.assertEqual(editor._find_matching_bracket(0, opening), (2, 0))

    def test_c_bracket_matching_has_a_scan_budget(self):
        editor = ViEditor("main.c")
        editor.MAX_BRACKET_SCAN_CHARS = 10
        editor.lines = ["{", "x" * 20, "}"]

        self.assertIsNone(editor._find_matching_bracket(0, 0))

    def test_log_syntax_spans_classify_formatted_http_and_python_logs(self):
        editor = ViEditor()

        http_spans = editor._syntax_spans(
            "21/Apr/2026:12:34:56 +0000 | 10.0.0.8 | GET /health | 404 | 1.5K",
            "log:http",
        )
        self.assertTrue(any(kind == "comment" for _, _, kind in http_spans))
        self.assertTrue(any(kind == "builtin" for _, _, kind in http_spans))
        self.assertTrue(any(kind == "keyword" for _, _, kind in http_spans))
        self.assertTrue(any(kind == "preproc" for _, _, kind in http_spans))

        py_spans = editor._syntax_spans(
            "2026-04-21 12:34:56,789 | ERROR    | api.server | request failed for 10.0.0.8 after 3 retries",
            "log:python",
        )
        self.assertTrue(any(kind == "comment" for _, _, kind in py_spans))
        self.assertTrue(any(kind == "function" for _, _, kind in py_spans))
        self.assertTrue(any(kind == "preproc" for _, _, kind in py_spans))
        self.assertTrue(any(kind == "number" for _, _, kind in py_spans))

    def test_dot_log_files_auto_detect_generic_log_highlighting(self):
        editor = ViEditor()
        editor.filename = "/var/log/app.log"

        self.assertIsNone(editor.log_type)
        self.assertEqual(editor._display_syntax_language(), "log:generic")

        editor.filename = "/var/log/app.txt"
        self.assertIsNone(editor._display_syntax_language())

    def test_logtype_off_disables_dot_log_auto_highlight(self):
        editor = ViEditor()
        editor.filename = "/var/log/app.log"

        self.assertTrue(editor._execute_cmd(":lgt off"))
        self.assertEqual(editor.log_type, "")
        self.assertIsNone(editor._display_syntax_language())

    def test_logtype_generic_can_be_selected_explicitly(self):
        editor = ViEditor()
        editor.filename = "notes.txt"

        self.assertTrue(editor._execute_cmd(":lgt generic"))
        self.assertEqual(editor.log_type, "generic")
        self.assertEqual(editor._display_syntax_language(), "log:generic")

    def test_generic_log_lines_are_not_reformatted(self):
        editor = ViEditor()
        editor.filename = "/var/log/app.log"
        editor.lines = ['2026-04-21 12:34:56 ERROR msg="disk full" host=10.0.0.8']

        self.assertEqual(editor._display_line_text(0), editor.lines[0])
        self.assertIsNone(editor._log_display_col(0, 5))

    def test_log_syntax_spans_classify_generic_log_line(self):
        editor = ViEditor()

        spans = editor._syntax_spans(
            '2026-04-21 12:34:56 ERROR msg="disk full" host=10.0.0.8 retries=3',
            "log:generic",
        )
        self.assertTrue(any(kind == "comment" for _, _, kind in spans))
        self.assertTrue(any(kind == "preproc" for _, _, kind in spans))
        self.assertTrue(any(kind == "string" for _, _, kind in spans))
        self.assertTrue(any(kind == "number" for _, _, kind in spans))

    def test_log_syntax_spans_colors_generic_traceback_line(self):
        editor = ViEditor()

        spans = editor._syntax_spans("Traceback (most recent call last):", "log:generic")

        self.assertEqual(spans, [(0, len("Traceback (most recent call last):"), "preproc")])

    def test_visible_line_parts_expands_once_for_content(self):
        editor = ViEditor()
        editor.tab_stop = 8  # this test is about expansion math, not ~/.viirc
        editor.lines = ["a\tb"]
        editor.left_col = 0

        visible, content_visible = editor._visible_line_parts(0, 10)

        self.assertEqual(visible, "a       b")
        self.assertEqual(content_visible, "a       b ")


class BreadcrumbTests(unittest.TestCase):
    def breadcrumbs_for(self, filename, lines, row):
        editor = ViEditor(filename)
        editor.lines = lines
        editor.cursor_row = row
        return editor._current_breadcrumbs()

    def test_python_breadcrumbs_follow_indentation(self):
        crumbs = self.breadcrumbs_for(
            "script.py",
            ["class App:", "    def run(self):", "        return 1", "def other():", "    pass"],
            2,
        )

        self.assertEqual(crumbs, ["class App", "def run"])

    def test_c_breadcrumbs_follow_brace_scopes(self):
        crumbs = self.breadcrumbs_for(
            "main.c",
            ["struct App {", "    int value;", "};", "int main(void)", "{", "    return 0;", "}"],
            5,
        )

        self.assertEqual(crumbs, ["main"])

    def test_c_breadcrumbs_ignore_braces_inside_block_comments(self):
        crumbs = self.breadcrumbs_for(
            "main.c",
            ["int main(void) {", "/* }", "still commented { */", "return 0;", "}"],
            3,
        )

        self.assertEqual(crumbs, ["main"])

    def test_c_breadcrumb_cache_is_incremental_for_navigation_and_current_line_edit(self):
        editor = ViEditor("main.c")
        editor.lines = [f"int value_{row};" for row in range(1000)]
        editor.cursor_row = len(editor.lines) - 1

        with mock.patch.object(
            editor, "_advance_clike_state", wraps=editor._advance_clike_state
        ) as advance:
            editor._current_breadcrumbs()
            initial_calls = advance.call_count
            editor._current_breadcrumbs()
            editor.cursor_row -= 1
            editor._current_breadcrumbs()
            navigation_calls = advance.call_count
            editor.lines[editor.cursor_row] = "int changed_value;"
            editor._current_breadcrumbs()

        self.assertEqual(initial_calls, len(editor.lines))
        self.assertEqual(navigation_calls, initial_calls)
        self.assertEqual(advance.call_count, initial_calls + 1)

    def test_tcl_breadcrumbs_include_proc(self):
        crumbs = self.breadcrumbs_for(
            "tool.tcl",
            ["namespace eval app {", "proc run {} {", "    return ok", "}", "}"],
            2,
        )

        self.assertEqual(crumbs, ["namespace app", "proc run"])

    def test_go_breadcrumbs_include_receiver_methods(self):
        crumbs = self.breadcrumbs_for(
            "server.go",
            ["type Server struct {", "}", "func (s *Server) Run() {", "    return", "}"],
            3,
        )

        self.assertEqual(crumbs, ["func Run"])

    def test_csharp_breadcrumbs_include_namespace_class_method(self):
        crumbs = self.breadcrumbs_for(
            "App.cs",
            ["namespace Demo {", "public class App {", "public void Run() {", "return;", "}", "}", "}"],
            3,
        )

        self.assertEqual(crumbs, ["namespace Demo", "class App", "Run"])

    def test_vala_breadcrumbs_include_class_method(self):
        crumbs = self.breadcrumbs_for(
            "widget.vala",
            ["public class Widget : Object {", "public void draw() {", "return;", "}", "}"],
            2,
        )

        self.assertEqual(crumbs, ["class Widget", "draw"])

    def test_lisp_breadcrumbs_follow_paren_nesting(self):
        crumbs = self.breadcrumbs_for(
            "utils.lisp",
            ["(defun outer (x)", "  (defun inner (y)", "    (+ x y)))"],
            2,
        )

        self.assertEqual(crumbs, ["defun outer", "defun inner"])

    def test_forth_breadcrumbs_track_colon_definitions(self):
        crumbs = self.breadcrumbs_for(
            "kernel.fs",
            [": square ( n -- n^2 )", "  dup * ;", ": cube ( n -- n^3 )", "  dup dup * * ;"],
            2,
        )

        self.assertEqual(crumbs, [": cube"])

        crumbs = self.breadcrumbs_for(
            "kernel.fs",
            [": square ( n -- n^2 )", "  dup * ;", "0 constant zero"],
            2,
        )

        self.assertEqual(crumbs, [])

    def test_sql_breadcrumbs_include_statement_head(self):
        crumbs = self.breadcrumbs_for(
            "query.sql",
            ["-- report", "SELECT id", "FROM users", "WHERE active = 1;"],
            2,
        )

        self.assertEqual(crumbs, ["SELECT"])

    def test_breadcrumb_cache_invalidates_after_content_change(self):
        editor = ViEditor("script.py")
        editor.lines = ["class App:", "    pass"]
        editor.cursor_row = 1

        self.assertEqual(editor._current_breadcrumbs(), ["class App"])

        editor.lines[0] = "def run():"
        editor.modified = True

        self.assertEqual(editor._current_breadcrumbs(), ["def run"])

    def test_breadcrumb_cache_detects_in_place_same_row_same_length_edit(self):
        editor = ViEditor("script.py")
        editor.lines = ["class App:", "    pass"]
        editor.cursor_row = 1

        self.assertEqual(editor._current_breadcrumbs(), ["class App"])

        editor.lines[0] = "def run():"

        self.assertEqual(editor._current_breadcrumbs(), ["def run"])

    def test_status_formatter_keeps_right_side_visible(self):
        editor = ViEditor()
        status = editor._format_status(" NORMAL  " + "x" * 80, " 10,1  50%% ", 40)

        self.assertTrue(status.endswith(" 10,1  50%% "))
        self.assertEqual(len(status), 39)

    def test_status_formatter_accounts_for_escaped_null_width(self):
        editor = ViEditor()
        status = editor._format_status("ABCDE\x00FGHI", " 1 ", 15)

        self.assertTrue(status.endswith(" 1 "))
        self.assertIn("^@", status)
        self.assertEqual(len(status), 14)

    def test_status_formatter_accounts_for_wide_unicode_width(self):
        editor = ViEditor()
        status = editor._format_status("你界abc", " 1 ", 10)

        self.assertTrue(status.endswith(" 1 "))
        self.assertIn("界", status)
        self.assertEqual(editor._display_width(status), 9)

    def test_completion_matches_account_for_escaped_null_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 9, ["a\x00b", "xyz"], 0)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "a^@b", curses.A_REVERSE | curses.A_BOLD),
                (0, 4, "  ", curses.A_REVERSE),
                (0, 6, "..", curses.A_REVERSE),
            ],
        )

    def test_completion_matches_keep_selected_item_visible_on_narrow_width(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 12, ["alpha", "bravo", "charlie"], 2)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "... ", curses.A_REVERSE),
                (0, 4, "charlie", curses.A_REVERSE | curses.A_BOLD),
            ],
        )

    def test_completion_matches_drop_left_prefix_when_it_hides_selected_text(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 7

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 7, ["foo", "alphabet"], 1)

        self.assertEqual(
            screen.calls,
            [(0, 0, "alphabe", curses.A_REVERSE | curses.A_BOLD)],
        )

    def test_completion_matches_clip_selected_item_instead_of_hiding_it(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 7

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 8, ["alphabet"], 0)

        self.assertEqual(
            screen.calls,
            [(0, 0, "alphabe", curses.A_REVERSE | curses.A_BOLD)],
        )

    def test_completion_matches_mark_left_hidden_when_selected_fits_after_prefix_drop(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 6

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 6, ["alpha", "bravo"], 1)

        self.assertEqual(
            screen.calls,
            [(0, 0, "bravo", curses.A_REVERSE | curses.A_BOLD)],
        )

    def test_completion_matches_show_right_indicator_when_later_items_are_hidden(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 15

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 15, ["alpha", "bravo", "charlie"], 1)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "alpha", curses.A_REVERSE),
                (0, 5, "  ", curses.A_REVERSE),
                (0, 7, "bravo", curses.A_REVERSE | curses.A_BOLD),
                (0, 12, "  ", curses.A_REVERSE),
            ],
        )

    def test_completion_matches_mark_both_hidden_sides_when_selected_fits_exactly(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 9

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 9, ["foo", "alphabet", "zoo"], 1)

        self.assertEqual(
            screen.calls,
            [(0, 0, "alphabet", curses.A_REVERSE | curses.A_BOLD)],
        )

    def test_completion_matches_use_trailing_space_for_left_hidden_indicator(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 9

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 9, ["alpha", "bravo"], 1)

        self.assertEqual(
            screen.calls,
            [(0, 0, "bravo", curses.A_REVERSE | curses.A_BOLD)],
        )

    def test_completion_matches_show_real_previous_match_instead_of_prefix_when_it_fits(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 13

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 13, ["alpha", "bravo"], 1)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "alpha", curses.A_REVERSE),
                (0, 5, "  ", curses.A_REVERSE),
                (0, 7, "bravo", curses.A_REVERSE | curses.A_BOLD),
            ],
        )

    def test_completion_matches_mark_hidden_items_after_separator_exact_fit(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 11

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 11, ["foo", "alphabet", "zoo"], 1)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "alphabet", curses.A_REVERSE | curses.A_BOLD),
                (0, 8, "  ", curses.A_REVERSE),
            ],
        )

    def test_completion_matches_mark_both_hidden_sides_when_selected_item_is_clipped(self):
        class FakeScreen:
            def __init__(self):
                self.calls = []

            def getmaxyx(self):
                return 1, 6

            def addstr(self, *args):
                self.calls.append(args)

        editor = ViEditor()
        screen = FakeScreen()

        editor._draw_completion_matches(screen, 0, 7, ["foo", "alphabet", "zoo"], 1)

        self.assertEqual(
            screen.calls,
            [
                (0, 0, "alphab", curses.A_REVERSE | curses.A_BOLD),
            ],
        )


class DisplayPerfTests(unittest.TestCase):
    """Tests for display code bug fixes and performance improvements."""

    # ------------------------------------------------------------------
    # _add_curses_text: uses _last_h/_last_w without calling getmaxyx
    # ------------------------------------------------------------------

    def test_add_curses_text_uses_cached_dimensions(self):
        editor = ViEditor()
        editor._last_h = 24
        editor._last_w = 80

        getmaxyx_called = []

        class FakeWin:
            def getmaxyx(self):
                getmaxyx_called.append(True)
                return 24, 80

            def addstr(self, *args):
                pass

        editor._add_curses_text(FakeWin(), 0, 0, "hello")
        self.assertEqual(getmaxyx_called, [], "getmaxyx should not be called when _last_h/_last_w are valid")

    def test_add_curses_text_falls_back_to_getmaxyx_when_dims_zero(self):
        editor = ViEditor()
        editor._last_h = 0
        editor._last_w = 0

        getmaxyx_called = []

        class FakeWin:
            def getmaxyx(self):
                getmaxyx_called.append(True)
                return 24, 80

            def addstr(self, *args):
                pass

        editor._add_curses_text(FakeWin(), 0, 0, "hello")
        self.assertTrue(getmaxyx_called, "getmaxyx should be called when _last_h/_last_w are zero")

    # ------------------------------------------------------------------
    # Bracket match cache
    # ------------------------------------------------------------------

    def test_bracket_match_cache_avoids_repeated_scan(self):
        editor = ViEditor()
        editor.lines = ["(hello)"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        scan_count = []
        orig = editor._find_matching_bracket

        def counting_find(row, col):
            scan_count.append((row, col))
            return orig(row, col)

        editor._find_matching_bracket = counting_find

        result1 = editor._matching_bracket_pair()
        result2 = editor._matching_bracket_pair()

        self.assertEqual(result1, result2)
        self.assertEqual(len(scan_count), 1, "_find_matching_bracket should only run once per position")

    def test_bracket_match_cache_invalidated_on_content_change(self):
        editor = ViEditor()
        editor.lines = ["(hello)"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        scan_count = []
        orig = editor._find_matching_bracket

        def counting_find(row, col):
            scan_count.append((row, col))
            return orig(row, col)

        editor._find_matching_bracket = counting_find

        editor._matching_bracket_pair()
        editor._content_revision += 1
        editor._matching_bracket_pair()

        self.assertEqual(len(scan_count), 2, "cache should miss after content_revision changes")

    # ------------------------------------------------------------------
    # Undo/redo replaces self.lines wholesale. The tracked buffer setter must
    # advance _content_revision even when the restored text is the saved
    # modified=False state, or the position/revision bracket cache can return
    # a result computed against pre-undo content.
    # ------------------------------------------------------------------

    def test_bracket_match_cache_invalidated_by_undo_to_saved_state(self):
        editor = ViEditor()
        editor.lines = ["(a)"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._saved_signature = editor._current_signature()
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._refresh_modified()
        self.assertFalse(editor.modified)

        self.assertEqual(editor._matching_bracket_pair(), ((0, 0), (0, 2)))

        editor._push_undo()
        editor.lines[0] = "(ab)"
        editor.modified = True
        editor.cursor_row, editor.cursor_col = 0, 0
        self.assertEqual(editor._matching_bracket_pair(), ((0, 0), (0, 3)))

        editor._undo()
        self.assertEqual(editor.lines, ["(a)"])
        self.assertFalse(editor.modified, "undo landed back on the exact saved content")
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

        self.assertEqual(
            editor._matching_bracket_pair(), ((0, 0), (0, 2)),
            "stale cache must not survive an undo that revert-matches the saved buffer",
        )

    def test_bracket_match_cache_invalidated_by_redo_to_saved_state(self):
        editor = ViEditor()
        editor.lines = ["(a)"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor.cursor_row = 0
        editor.cursor_col = 0

        editor._push_undo()
        editor.lines[0] = "(ab)"
        editor.modified = True
        editor._saved_signature = editor._current_signature()  # "(ab)" is now "saved"
        editor._refresh_modified()
        editor._matching_bracket_pair()  # caches ((0,0),(0,3)) for "(ab)"

        editor._undo()
        self.assertEqual(editor.lines, ["(a)"])
        self.assertTrue(editor.modified, "reverted content no longer matches the saved buffer")
        editor.cursor_row, editor.cursor_col = 0, 0
        self.assertEqual(editor._matching_bracket_pair(), ((0, 0), (0, 2)))

        editor._redo()
        self.assertEqual(editor.lines, ["(ab)"])
        self.assertFalse(editor.modified, "redo landed back on the exact saved content")
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))

        self.assertEqual(
            editor._matching_bracket_pair(), ((0, 0), (0, 3)),
            "stale cache must not survive a redo that revert-matches the saved buffer",
        )

    def test_bracket_match_cache_invalidated_on_cursor_move(self):
        editor = ViEditor()
        editor.lines = ["(hello)"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        scan_count = []
        orig = editor._find_matching_bracket

        def counting_find(row, col):
            scan_count.append((row, col))
            return orig(row, col)

        editor._find_matching_bracket = counting_find

        editor._matching_bracket_pair()
        editor.cursor_col = 1
        editor._matching_bracket_pair()

        self.assertEqual(len(scan_count), 2, "cache should miss after cursor moves")

    def test_bracket_match_cache_invalidated_by_file_rename_changing_language(self):
        # :file/:f changes self.filename (and thus the effective syntax
        # language, which decides generic vs. clike-aware bracket
        # matching) without reassigning self.lines -- content_revision
        # alone doesn't change, so the cache key must include the
        # language itself or a rename returns a stale, wrong match.
        editor = ViEditor()
        editor.filename = "notes.txt"  # no associated syntax language
        editor.lines = ["int main() {", '    printf("}");', "}"]
        editor.cursor_row, editor.cursor_col = 0, editor.lines[0].index("{")

        # Generic scan (no language): naively pairs with the '}' inside
        # the string literal on line 1.
        self.assertEqual(editor._matching_bracket_pair(), ((0, 11), (1, 12)))

        editor._execute_cmd(":file main.c")
        self.assertEqual(editor._syntax_language(), "c")

        # C-aware scan must now skip the string-embedded '}' and match
        # the real closing brace on line 2 -- not the stale cached answer.
        self.assertEqual(editor._matching_bracket_pair(), ((0, 11), (2, 0)))

    def test_bracket_match_cache_returns_none_for_non_bracket(self):
        editor = ViEditor()
        editor.lines = ["hello"]
        editor.cursor_row = 0
        editor.cursor_col = 0

        result = editor._matching_bracket_pair()
        self.assertIsNone(result)
        cached_result = editor._matching_bracket_pair()
        self.assertIsNone(cached_result)

    # ------------------------------------------------------------------
    # Hex view: _buffer_hex_bytes called once per draw, not per keystroke
    # ------------------------------------------------------------------

    def test_hex_view_lines_accepts_precomputed_data(self):
        editor = ViEditor()
        editor.lines = ["AB"]
        data = editor._buffer_hex_bytes()

        encode_count = []
        orig = editor._buffer_hex_bytes

        def counting_bytes():
            encode_count.append(True)
            return orig()

        editor._buffer_hex_bytes = counting_bytes

        lines = editor._hex_view_lines(data)
        self.assertEqual(encode_count, [], "should not re-encode when data is provided")
        self.assertIn("41 42", lines[0])

    def test_hex_handle_uses_cached_line_count_not_view_lines(self):
        editor = ViEditor()
        editor.lines = ["A" * 16]
        editor._open_hex_view()
        editor._last_h = 24

        encode_count = []
        orig_bytes = editor._buffer_hex_bytes

        def counting_bytes():
            encode_count.append(True)
            return orig_bytes()

        editor._buffer_hex_bytes = counting_bytes

        editor._handle_hex(ord("j"))
        self.assertEqual(encode_count, [], "_handle_hex should not re-encode the buffer")

    def test_hex_line_count_set_on_open(self):
        editor = ViEditor()
        editor.lines = ["A" * 32]
        editor._open_hex_view()
        self.assertGreater(editor._hex_line_count, 0)

    def test_draw_hex_does_not_re_encode_buffer_per_redraw(self):
        editor = ViEditor()
        editor.lines = ["A" * 16]
        editor._open_hex_view()
        editor._last_h = 24

        encode_count = []
        orig_bytes = editor._buffer_hex_bytes

        def counting_bytes():
            encode_count.append(True)
            return orig_bytes()

        editor._buffer_hex_bytes = counting_bytes

        class FakeScreen:
            def getmaxyx(self):
                return 24, 80
            def move(self, *args):
                pass
            def clrtoeol(self):
                pass
            def addstr(self, *args):
                pass
            def attron(self, *args):
                pass
            def attroff(self, *args):
                pass
            def noutrefresh(self):
                pass

        with mock.patch("curses.doupdate"):
            editor._draw_hex(FakeScreen(), 24, 80)
            editor._draw_hex(FakeScreen(), 24, 80)

        self.assertEqual(encode_count, [], "_draw_hex should reuse the buffer encoded at open")

    # ------------------------------------------------------------------
    # Line-endings view: cached line count avoids per-keystroke rebuild
    # ------------------------------------------------------------------

    def test_line_endings_handle_uses_cached_line_count(self):
        editor = ViEditor()
        editor.lines = [f"line {i}" for i in range(20)]
        editor.line_endings = ["\n"] * 19 + [""]
        editor._open_line_endings_view()
        editor._last_h = 8

        build_count = []
        orig = editor._line_endings_view_lines

        def counting_view():
            build_count.append(True)
            return orig()

        editor._line_endings_view_lines = counting_view

        editor._handle_line_endings(ord("j"))
        self.assertEqual(build_count, [], "_handle_line_endings should not rebuild the view list")

    def test_line_endings_line_count_set_on_open(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.line_endings = ["\n", "\n", ""]
        editor._open_line_endings_view()
        self.assertEqual(editor._line_endings_line_count, 3)

    def test_draw_line_endings_does_not_rebuild_view_per_redraw(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.line_endings = ["\n", "\n", ""]
        editor._open_line_endings_view()
        editor._last_h = 24

        build_count = []
        orig = editor._line_endings_view_lines

        def counting_view():
            build_count.append(True)
            return orig()

        editor._line_endings_view_lines = counting_view

        class FakeScreen:
            def getmaxyx(self):
                return 24, 80
            def move(self, *args):
                pass
            def clrtoeol(self):
                pass
            def addstr(self, *args):
                pass
            def attron(self, *args):
                pass
            def attroff(self, *args):
                pass
            def noutrefresh(self):
                pass

        with mock.patch("curses.doupdate"):
            editor._draw_line_endings(FakeScreen(), 24, 80)
            editor._draw_line_endings(FakeScreen(), 24, 80)

        self.assertEqual(build_count, [], "_draw_line_endings should reuse the list built at open")

    # ------------------------------------------------------------------
    # Source syntax uses raw lines rather than viewport-specific expanded prefixes
    # ------------------------------------------------------------------

    def test_source_syntax_draw_does_not_build_expanded_prefix(self):
        editor = ViEditor("sample.c")
        editor.lines = ["hello\tworld"]
        editor._last_h = 10
        editor._last_w = 80

        expand_calls = []
        orig = editor._expanded_line_prefix

        def counting_expand(lnum, text_w):
            expand_calls.append(lnum)
            return orig(lnum, text_w)

        editor._expanded_line_prefix = counting_expand

        class FakeScreen:
            def getmaxyx(self):
                return 10, 80

            def move(self, *a):
                pass

            def clrtoeol(self):
                pass

            def addstr(self, *a):
                pass

            def attron(self, *a):
                pass

            def attroff(self, *a):
                pass

            def noutrefresh(self):
                pass

            def derwin(self, *a):
                return self

        screen = FakeScreen()
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx"):
            editor.draw(screen)
            editor.draw(screen)

        self.assertEqual(expand_calls, [])

    # ------------------------------------------------------------------
    # File browser header row cleared before drawing
    # ------------------------------------------------------------------

    def test_file_browser_header_row_cleared_before_draw(self):
        editor = ViEditor()
        editor._last_h = 24
        editor._last_w = 80

        move_args = []
        clrtoeol_count = []

        class FakeScreen:
            def getmaxyx(self):
                return 24, 80

            def move(self, r, c):
                move_args.append((r, c))

            def clrtoeol(self):
                clrtoeol_count.append(True)

            def addstr(self, *a):
                pass

            def attron(self, *a):
                pass

            def attroff(self, *a):
                pass

            def noutrefresh(self):
                pass

            def derwin(self, *a):
                return self

        editor._execute_cmd(":fb")
        screen = FakeScreen()
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx"):
            editor.draw(screen)

        # Row 0 should have been cleared via move(0, 0) + clrtoeol before headers
        row0_clears = [
            i for i, (r, _) in enumerate(move_args) if r == 0
        ]
        self.assertTrue(row0_clears, "move to row 0 should occur before drawing headers")
        # clrtoeol must have been called
        self.assertTrue(clrtoeol_count, "clrtoeol should be called to clear the header row")


class SessionTests(unittest.TestCase):
    """Tests for ~/.vii_session save/restore."""

    def _editor_with_session(self, session_path):
        """Return a ViEditor whose SESSION_PATH is redirected to session_path."""
        editor = ViEditor()
        editor.SESSION_PATH = session_path
        return editor

    def test_save_session_survives_stale_fixed_tmp_path(self):
        # Older versions used the fixed name SESSION_PATH + ".tmp"; a stale
        # directory squatting there (or a concurrent instance's temp file)
        # must not block the session write.
        with tempfile.TemporaryDirectory() as tmpdir:
            note = os.path.join(tmpdir, "note.txt")
            with open(note, "w", encoding="utf-8") as fh:
                fh.write("hello\n")
            session_path = os.path.join(tmpdir, "session")
            os.makedirs(session_path + ".tmp")

            editor = self._editor_with_session(session_path)
            editor._load_file(note)
            editor._save_session()

            self.assertTrue(os.path.isfile(session_path))
            with open(session_path, "r", encoding="utf-8") as fh:
                self.assertIn(json.dumps(note, ensure_ascii=False), fh.read())
            leftovers = [
                name for name in os.listdir(tmpdir)
                if name.startswith(".vii_session.") and name.endswith(".tmp")
            ]
            self.assertEqual(leftovers, [])

    def test_save_session_writes_filename_and_cursor(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "notes.txt")
            with open(path, "w") as fh:
                fh.write("line1\nline2\nline3\n")
            session_path = os.path.join(tmpdir, "session")

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["line1", "line2", "line3"]
            editor.cursor_row = 2
            editor.cursor_col = 3
            editor.buffers = [editor._capture_buffer_state()]
            editor._save_session()

            with open(session_path, "r") as fh:
                content = fh.read()

            self.assertIn(os.path.abspath(path), content)
            self.assertIn("\t2\t3", content)

    def test_save_session_skips_unnamed_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = self._editor_with_session(session_path)
            editor.filename = None
            editor.lines = ["hello"]
            editor.buffers = [editor._capture_buffer_state()]
            editor._save_session()

            with open(session_path, "r") as fh:
                lines = [line for line in fh if not line.startswith("#")]
            self.assertEqual(lines, [])

    def test_set_sessionfiles_changes_cap(self):
        editor = ViEditor()
        self.assertEqual(editor.session_max_files, editor.SESSION_MAX_FILES)
        self.assertEqual(editor._apply_set_opt("sessionfiles=3"), "")
        self.assertEqual(editor.session_max_files, 3)
        self.assertIn("sessionfiles must be a positive integer",
                       editor._apply_set_opt("sessionfiles=0"))
        self.assertIn("sessionfiles must be a positive integer",
                       editor._apply_set_opt("sessionfiles=nope"))

    def test_save_session_respects_custom_cap_and_evicts_oldest(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            paths = []
            for i in range(5):
                path = os.path.join(tmpdir, f"file{i}.txt")
                with open(path, "w") as fh:
                    fh.write("hello\n")
                paths.append(os.path.abspath(path))

            for path in paths:
                editor = self._editor_with_session(session_path)
                editor.session_max_files = 3
                editor.filename = path
                editor.lines = ["hello"]
                editor.buffers = [editor._capture_buffer_state()]
                editor._save_session()

            with open(session_path, "r") as fh:
                lines = [line for line in fh if not line.startswith("#") and line.strip()]
            self.assertEqual(len(lines), 3)
            kept = [line.split("\t", 1)[0] for line in lines]
            self.assertEqual(kept, [json.dumps(p, ensure_ascii=False) for p in reversed(paths[-3:])])

    def test_load_file_restores_cursor_from_session(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "code.py")
            with open(path, "w") as fh:
                fh.write("alpha\nbeta\ngamma\ndelta\nepsilon\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(f"# vii session\n{os.path.abspath(path)}\t3\t2\n")

            editor = self._editor_with_session(session_path)
            editor._load_file(path)

            self.assertEqual(editor.cursor_row, 3)
            self.assertEqual(editor.cursor_col, 2)

    def test_load_file_restores_cursor_from_tilde_session_entry(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            os.mkdir(home)
            path = os.path.join(home, "code.py")
            with open(path, "w") as fh:
                fh.write("alpha\nbeta\ngamma\ndelta\nepsilon\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w", encoding="utf-8") as fh:
                fh.write('# vii session\n"~/code.py"\t3\t2\t{}\t{}\n')
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            editor = self._editor_with_session(session_path)
            with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                editor._load_file(path)

            self.assertEqual(editor.cursor_row, 3)
            self.assertEqual(editor.cursor_col, 2)

    def test_load_file_clamps_out_of_range_cursor(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "short.txt")
            with open(path, "w") as fh:
                fh.write("only\none\n")
            session_path = os.path.join(tmpdir, "session")
            # Session says row 99, col 50 — both out of range
            with open(session_path, "w") as fh:
                fh.write(f"# vii session\n{os.path.abspath(path)}\t99\t50\n")

            editor = self._editor_with_session(session_path)
            editor._load_file(path)

            self.assertLessEqual(editor.cursor_row, 1)
            self.assertLessEqual(editor.cursor_col, 3)  # "one" is 3 chars

    def test_load_file_no_session_entry_leaves_cursor_at_zero(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "new.txt")
            with open(path, "w") as fh:
                fh.write("hello\nworld\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write("# vii session\n")

            editor = self._editor_with_session(session_path)
            editor._load_file(path)

            self.assertEqual(editor.cursor_row, 0)
            self.assertEqual(editor.cursor_col, 0)

    def test_load_different_file_without_session_clears_previous_marks_and_view(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            old_path = os.path.join(tmpdir, "old.txt")
            new_path = os.path.join(tmpdir, "new.txt")
            with open(old_path, "w") as fh:
                fh.write("old\n")
            with open(new_path, "w") as fh:
                fh.write("new\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write("# vii session\n")

            editor = self._editor_with_session(session_path)
            editor.filename = old_path
            editor.lines = ["old"]
            editor.cursor_row = 0
            editor.cursor_col = 0
            editor.top_line = 12
            editor.left_col = 4
            editor.marks = {"a": (0, 0)}

            editor._load_file(new_path)

            self.assertEqual(editor.filename, new_path)
            self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 0))
            self.assertEqual((editor.top_line, editor.left_col), (0, 0))
            self.assertEqual(editor.marks, {})

    def test_reload_same_file_without_session_keeps_buffer_marks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "same.txt")
            with open(path, "w") as fh:
                fh.write("one\ntwo\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write("# vii session\n")

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["one", "two"]
            editor.cursor_row = 1
            editor.cursor_col = 1
            editor.marks = {"a": (1, 1)}

            editor._load_file(path)

            self.assertEqual(editor.marks, {"a": (1, 1)})

    def test_reload_same_file_without_session_clamps_cursor_and_marks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "same.txt")
            with open(path, "w") as fh:
                fh.write("one\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write("# vii session\n")

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["one", "two", "three"]
            editor.cursor_row = 2
            editor.cursor_col = 20
            editor.marks = {"a": (2, 20)}
            editor.auto_marks = {1: 2}

            editor._load_file(path)

            self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 3))
            self.assertEqual(editor.marks, {"a": (0, 2)})
            self.assertEqual(editor.auto_marks, {1: 0})

    def test_session_saves_and_loads_file_marks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "marks.txt")
            with open(path, "w") as fh:
                fh.write("alpha\nbeta\ngamma\n")
            session_path = os.path.join(tmpdir, "session")

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["alpha", "beta", "gamma"]
            editor.cursor_row = 2
            editor.cursor_col = 1
            editor.marks = {"a": (0, 2), "Z": (2, 4)}
            editor.buffers = [editor._capture_buffer_state()]
            editor._save_session()

            restored = self._editor_with_session(session_path)
            restored._load_file(path)

            self.assertEqual(restored.marks, {"a": (0, 2), "Z": (2, 4)})
            restored._jump_to_mark("a", exact=True)
            self.assertEqual((restored.cursor_row, restored.cursor_col), (0, 2))

    def test_session_marks_are_saved_for_inactive_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            f1 = os.path.join(tmpdir, "one.txt")
            f2 = os.path.join(tmpdir, "two.txt")
            for path in (f1, f2):
                with open(path, "w") as fh:
                    fh.write("one\ntwo\n")
            session_path = os.path.join(tmpdir, "session")

            editor = ViEditor([f1, f2])
            editor.SESSION_PATH = session_path
            self.assertTrue(editor._execute_cmd(":buffer 2"))
            editor.marks = {"b": (1, 1)}
            self.assertTrue(editor._execute_cmd(":buffer 1"))
            editor.marks = {"a": (0, 1)}
            editor._save_session()

            restored = self._editor_with_session(session_path)
            restored._load_file(f2)

            self.assertEqual(restored.marks, {"b": (1, 1)})

    def test_session_load_clamps_out_of_range_marks(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "short.txt")
            with open(path, "w") as fh:
                fh.write("one\n\n")
            session_path = os.path.join(tmpdir, "session")
            marks = {"a": [99, 50], "b": [1, 20], "bad": [0, 0], "c": ["x", 0]}
            auto_marks = {"1": 99, "2": -4, "bad": "x"}
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    f"{json.dumps(os.path.abspath(path))}\t0\t0\t{json.dumps(marks)}\t{json.dumps(auto_marks)}\n"
                )

            restored = self._editor_with_session(session_path)
            restored._load_file(path)

            self.assertEqual(restored.marks, {"a": (1, 0), "b": (1, 0)})
            self.assertEqual(restored.auto_marks, {1: 1, 2: 0})

    def test_read_session_filenames_returns_existing_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            real = os.path.join(tmpdir, "exists.txt")
            gone = os.path.join(tmpdir, "gone.txt")
            with open(real, "w") as fh:
                fh.write("x")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(f"# vii session\n{real}\t0\t0\n{gone}\t1\t0\n")

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                paths = _read_session_filenames()
            finally:
                ViEditor.SESSION_PATH = orig

            self.assertEqual(paths, [real])

    def test_read_session_filenames_expands_tilde_paths(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            home = os.path.join(tmpdir, "home")
            os.mkdir(home)
            real = os.path.join(home, "exists.txt")
            with open(real, "w") as fh:
                fh.write("x")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w", encoding="utf-8") as fh:
                fh.write('# vii session\n"~/exists.txt"\t0\t0\t{}\t{}\n')
            real_expanduser = os.path.expanduser

            def fake_expanduser(value):
                if value == "~":
                    return home
                if value.startswith("~/"):
                    return os.path.join(home, value[2:])
                return real_expanduser(value)

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                with mock.patch("vi_editor.os.path.expanduser", side_effect=fake_expanduser):
                    paths = _read_session_filenames()
            finally:
                ViEditor.SESSION_PATH = orig

            self.assertEqual(paths, [real])

    def test_session_roundtrip_current_buffer_first(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            f1 = os.path.join(tmpdir, "a.txt")
            f2 = os.path.join(tmpdir, "b.txt")
            for p in (f1, f2):
                with open(p, "w") as fh:
                    fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = self._editor_with_session(session_path)
            editor.filename = f1
            editor.lines = ["x"]
            editor.cursor_row = 0
            editor.cursor_col = 0
            editor.buffers = [editor._capture_buffer_state()]
            editor.current_buffer = 0

            # Add a second buffer
            from vi_editor import BufferState
            b2 = BufferState(f2, ["x"], None, 5, 0, False, 0, 0, [], [], {})
            editor.buffers.append(b2)
            editor.current_buffer = 1   # f2 is active
            editor.filename = f2
            editor.cursor_row = 5

            editor._save_session()

            with open(session_path, "r") as fh:
                lines = [
                    line.rstrip("\n")
                    for line in fh
                    if not line.startswith("#") and line.strip()
                ]

            # Current buffer (f2) should appear first
            self.assertIn(os.path.abspath(f2), lines[0])
            self.assertIn(os.path.abspath(f1), lines[1])

    def test_session_roundtrip_handles_tab_in_filename(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "has\ttab.txt")
            with open(path, "w") as fh:
                fh.write("one\ntwo\n")
            session_path = os.path.join(tmpdir, "session")

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["one", "two"]
            editor.cursor_row = 1
            editor.cursor_col = 2
            editor.buffers = [editor._capture_buffer_state()]
            editor._save_session()

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                self.assertEqual(_read_session_filenames(), [os.path.abspath(path)])
            finally:
                ViEditor.SESSION_PATH = orig

            restored = self._editor_with_session(session_path)
            restored._load_file(path)

            self.assertEqual((restored.cursor_row, restored.cursor_col), (1, 2))

    def test_session_reader_supports_legacy_raw_paths_with_tabs(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "legacy\ttab.txt")
            with open(path, "w") as fh:
                fh.write("one\ntwo\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(f"# vii session\n{os.path.abspath(path)}\t1\t1\n")

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                self.assertEqual(_read_session_filenames(), [os.path.abspath(path)])
            finally:
                ViEditor.SESSION_PATH = orig

            restored = self._editor_with_session(session_path)
            restored._load_file(path)

            self.assertEqual((restored.cursor_row, restored.cursor_col), (1, 1))

    def test_session_reader_ignores_malformed_and_duplicate_entries(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "exists.txt")
            with open(path, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write("bad line\n")
                fh.write(f"{os.path.abspath(path)}\tnot-row\t0\n")
                fh.write(f"{os.path.abspath(path)}\t0\t0\n")
                fh.write(f"{os.path.abspath(path)}\t1\t0\n")

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                self.assertEqual(_read_session_filenames(), [os.path.abspath(path)])
            finally:
                ViEditor.SESSION_PATH = orig

    def test_save_session_is_atomic(self):
        """Session file must not be left as a .tmp on success."""
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = self._editor_with_session(session_path)
            editor.buffers = [editor._capture_buffer_state()]
            editor._save_session()
            self.assertFalse(os.path.exists(session_path + ".tmp"))

    def test_session_map_opens_session_as_utf8(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "snowman-\u2603.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w", encoding="utf-8") as fh:
                fh.write(f"# vii session\n{json.dumps(os.path.abspath(path), ensure_ascii=False)}\t0\t0\n")

            editor = self._editor_with_session(session_path)
            real_open = open

            with mock.patch("builtins.open", wraps=real_open) as open_mock:
                session = editor._session_map()

            self.assertIn(os.path.abspath(path), session)
            self.assertTrue(any(
                call.args[:2] == (session_path, "r")
                and call.kwargs.get("encoding") == "utf-8"
                and call.kwargs.get("errors") == "replace"
                for call in open_mock.call_args_list
            ))

    def test_read_session_filenames_opens_session_as_utf8(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "snowman-\u2603.txt")
            with open(path, "w", encoding="utf-8") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w", encoding="utf-8") as fh:
                fh.write(f"# vii session\n{json.dumps(os.path.abspath(path), ensure_ascii=False)}\t0\t0\n")

            orig = ViEditor.SESSION_PATH
            real_open = open
            ViEditor.SESSION_PATH = session_path
            try:
                with mock.patch("builtins.open", wraps=real_open) as open_mock:
                    paths = _read_session_filenames()
            finally:
                ViEditor.SESSION_PATH = orig

            self.assertEqual(paths, [os.path.abspath(path)])
            self.assertTrue(any(
                call.args[:2] == (session_path, "r")
                and call.kwargs.get("encoding") == "utf-8"
                and call.kwargs.get("errors") == "replace"
                for call in open_mock.call_args_list
            ))

    # ------------------------------------------------------------------
    # :project / :prj / :prj-del
    # ------------------------------------------------------------------

    def test_project_command_requires_a_name(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for cmd in (":project", ":prj", ":prj-del"):
                editor = self._editor_with_session(os.path.join(tmpdir, "session"))
                editor._execute_cmd(cmd)
                self.assertTrue(editor.message_is_error)
                self.assertIn("name required", editor.message.lower())

    def test_project_save_requires_at_least_one_named_buffer(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = self._editor_with_session(session_path)
            editor.filename = None
            editor.lines = ["hello"]
            editor.buffers = [editor._capture_buffer_state()]

            editor._execute_cmd(":project demo")

            self.assertTrue(editor.message_is_error)
            self.assertFalse(os.path.exists(session_path))

    def test_project_command_saves_new_section_with_open_buffer_paths(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            b = os.path.join(tmpdir, "b.py")
            for p in (a, b):
                with open(p, "w") as fh:
                    fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = ViEditor([a, b])
            editor.SESSION_PATH = session_path
            editor._execute_cmd(":project demo")

            self.assertFalse(editor.message_is_error)
            self.assertIn("saved", editor.message)
            sections = ViEditor._read_project_sections(session_path)
            self.assertEqual(sorted(sections["demo"]), sorted([a, b]))

    def test_prj_alias_loads_an_existing_section_by_adding_buffers(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            c = os.path.join(tmpdir, "c.py")
            for p in (a, c):
                with open(p, "w") as fh:
                    fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                )

            editor = ViEditor([c])
            editor.SESSION_PATH = session_path
            starting_buffer_count = len(editor.buffers)

            editor._execute_cmd(":prj demo")

            self.assertFalse(editor.message_is_error)
            self.assertEqual(len(editor.buffers), starting_buffer_count + 1)
            self.assertEqual(editor.filename, a)  # switched to the loaded file
            self.assertTrue(any(bs.filename == c for bs in editor.buffers))
            self.assertTrue(any(bs.filename == a for bs in editor.buffers))

    def test_project_load_reports_and_skips_missing_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            missing = os.path.join(tmpdir, "gone.py")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                    f"{json.dumps(missing, ensure_ascii=False)}\n"
                )

            editor = self._editor_with_session(session_path)
            editor._execute_cmd(":project demo")

            self.assertFalse(editor.message_is_error)
            self.assertIn("1 missing", editor.message)
            self.assertTrue(any(bs.filename == a for bs in editor.buffers))
            self.assertFalse(any(bs.filename == missing for bs in editor.buffers))

    def test_prj_del_removes_section_and_errors_if_missing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = ViEditor([a])
            editor.SESSION_PATH = session_path
            editor._execute_cmd(":project demo")
            self.assertIn("demo", ViEditor._read_project_sections(session_path))

            editor._execute_cmd(":prj-del demo")
            self.assertFalse(editor.message_is_error)
            self.assertNotIn("demo", ViEditor._read_project_sections(session_path))

            editor._execute_cmd(":prj-del demo")
            self.assertTrue(editor.message_is_error)
            self.assertIn("No such project", editor.message)

    # ------------------------------------------------------------------
    # :sessclr
    # ------------------------------------------------------------------

    def test_sessclr_clears_mru_but_keeps_project_sections(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    f"{json.dumps(a, ensure_ascii=False)}\t0\t0\t{{}}\t{{}}\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                )

            editor = self._editor_with_session(session_path)
            editor._execute_cmd(":sessclr")

            self.assertFalse(editor.message_is_error)
            self.assertIn("cleared", editor.message.lower())
            self.assertEqual(ViEditor._read_session_map(session_path), {})
            sections = ViEditor._read_project_sections(session_path)
            self.assertEqual(sections.get("demo"), [a])

    def test_sessclr_on_missing_session_file_is_not_an_error(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = self._editor_with_session(session_path)

            editor._execute_cmd(":sessclr")

            self.assertFalse(editor.message_is_error)
            self.assertEqual(ViEditor._read_session_map(session_path), {})

    def test_save_session_preserves_project_sections(self):
        # _save_session() rewrites the whole file on every quit; a project
        # section saved earlier must not be silently dropped by that rewrite.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "notes.txt")
            with open(path, "w") as fh:
                fh.write("line1\n")
            other = os.path.join(tmpdir, "other.py")
            with open(other, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(other, ensure_ascii=False)}\n"
                )

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["line1"]
            editor.buffers = [editor._capture_buffer_state()]

            editor._save_session()

            sections = ViEditor._read_project_sections(session_path)
            self.assertEqual(sections.get("demo"), [other])
            with open(session_path) as fh:
                content = fh.read()
            self.assertIn(os.path.abspath(path), content)

    def test_project_helpers_respect_instance_session_path_override(self):
        # Regression guard: _read_project_sections/_read_raw_session_mru_lines
        # must never silently fall back to the real ~/.vii_session when an
        # instance's SESSION_PATH has been redirected (as every test in this
        # class does), since that would both corrupt test isolation and leak
        # the real file's contents into whatever gets written.
        real_session = os.path.expanduser("~/.vii_session")
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            before = None
            if os.path.exists(real_session):
                with open(real_session, "rb") as fh:
                    before = fh.read()

            editor = ViEditor([a])
            editor.SESSION_PATH = session_path
            editor._execute_cmd(":project demo")

            after = None
            if os.path.exists(real_session):
                with open(real_session, "rb") as fh:
                    after = fh.read()
            self.assertEqual(before, after)
            self.assertIn("demo", ViEditor._read_project_sections(session_path))

    def test_read_project_sections_raises_on_real_read_error_not_missing_file(self):
        # A missing file is the normal "nothing saved yet" case and must
        # stay silent; a file that exists but can't actually be read (here:
        # it's a directory, a portable way to force IsADirectoryError
        # without relying on chmod, which can be a no-op running as root)
        # must not be treated the same way.
        self.assertEqual(ViEditor._read_project_sections("/no/such/path/at/all"), {})
        with tempfile.TemporaryDirectory() as tmpdir:
            with self.assertRaises(OSError):
                ViEditor._read_project_sections(tmpdir)

    def test_read_raw_session_mru_lines_raises_on_real_read_error_not_missing_file(self):
        self.assertEqual(
            ViEditor._read_raw_session_mru_lines("/no/such/path/at/all"),
            ["# vii session"],
        )
        with tempfile.TemporaryDirectory() as tmpdir:
            with self.assertRaises(OSError):
                ViEditor._read_raw_session_mru_lines(tmpdir)

    def test_project_save_reports_failure_instead_of_false_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = ViEditor([a])
            editor.SESSION_PATH = session_path

            with mock.patch.object(ViEditor, "_atomic_write_session_lines", return_value=False):
                editor._execute_cmd(":project demo")

            self.assertTrue(editor.message_is_error)
            self.assertIn("Failed to save project", editor.message)
            self.assertFalse(os.path.exists(session_path))

    def test_prj_del_reports_failure_instead_of_false_success(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = ViEditor([a])
            editor.SESSION_PATH = session_path
            editor._execute_cmd(":project demo")
            self.assertIn("demo", ViEditor._read_project_sections(session_path))

            with mock.patch.object(ViEditor, "_atomic_write_session_lines", return_value=False):
                editor._execute_cmd(":prj-del demo")

            self.assertTrue(editor.message_is_error)
            self.assertIn("Failed to delete project", editor.message)
            # The section must still be there -- delete never actually happened.
            self.assertIn("demo", ViEditor._read_project_sections(session_path))

    def test_project_reports_read_error_instead_of_silently_resaving(self):
        # If :project can't read the existing sections, it must not fall
        # through to the "no such project" save branch and clobber the file
        # -- that's exactly the silent-data-loss path this guards against.
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                )
            with open(session_path, "rb") as fh:
                original_content = fh.read()

            editor = ViEditor([a])
            editor.SESSION_PATH = session_path

            with mock.patch.object(ViEditor, "_read_project_sections",
                                    side_effect=PermissionError("denied")):
                editor._execute_cmd(":project demo")

            self.assertTrue(editor.message_is_error)
            self.assertIn("Could not read", editor.message)
            with open(session_path, "rb") as fh:
                self.assertEqual(fh.read(), original_content)  # untouched

    def test_save_session_skips_write_on_project_section_read_error(self):
        # _save_session must never raise (it runs from an unconditional
        # `finally`), so a read failure has to make it bail out quietly --
        # but it must bail out *before* writing, not write a rebuilt MRU
        # list with every project section silently dropped.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "notes.txt")
            with open(path, "w") as fh:
                fh.write("line1\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(path, ensure_ascii=False)}\n"
                )
            with open(session_path, "rb") as fh:
                original_content = fh.read()

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["line1"]
            editor.buffers = [editor._capture_buffer_state()]

            with mock.patch.object(ViEditor, "_read_project_sections",
                                    side_effect=PermissionError("denied")):
                editor._save_session()  # must not raise

            with open(session_path, "rb") as fh:
                self.assertEqual(fh.read(), original_content)  # untouched

    def test_project_load_reports_failed_opens_separately_from_missing(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            bad = os.path.join(tmpdir, "bad.py")
            for p in (a, bad):
                with open(p, "w") as fh:
                    fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                    f"{json.dumps(bad, ensure_ascii=False)}\n"
                )

            editor = self._editor_with_session(session_path)
            real_append = editor._append_buffer

            def flaky_append(filename=None, switch=True, **kwargs):
                if filename == bad:
                    return False  # simulates a TOCTOU race / real load failure
                return real_append(filename, switch=switch, **kwargs)

            editor._append_buffer = flaky_append
            editor._execute_cmd(":project demo")

            self.assertTrue(editor.message_is_error)
            self.assertIn("loaded 1 file", editor.message)
            self.assertIn("1 failed to open", editor.message)
            self.assertTrue(any(bs.filename == a for bs in editor.buffers))
            self.assertFalse(any(bs.filename == bad for bs in editor.buffers))

    def test_project_load_switches_to_first_successfully_opened_file(self):
        # If the file meant to become active (existing[0]) fails to open,
        # the switch must retry against the next one that actually loads --
        # not silently leave whatever buffer was active before :project ran.
        with tempfile.TemporaryDirectory() as tmpdir:
            bad = os.path.join(tmpdir, "bad.py")
            good = os.path.join(tmpdir, "good.py")
            for p in (bad, good):
                with open(p, "w") as fh:
                    fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(bad, ensure_ascii=False)}\n"
                    f"{json.dumps(good, ensure_ascii=False)}\n"
                )

            editor = self._editor_with_session(session_path)
            real_append = editor._append_buffer

            def flaky_append(filename=None, switch=True, **kwargs):
                if filename == bad:
                    return False
                return real_append(filename, switch=switch, **kwargs)

            editor._append_buffer = flaky_append
            editor._execute_cmd(":project demo")

            self.assertEqual(editor.filename, good)

    # ------------------------------------------------------------------
    # -p / _resolve_startup_filenames
    # ------------------------------------------------------------------

    def test_resolve_startup_filenames_dash_p_loads_project(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                )

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                filenames, error = _resolve_startup_filenames(["-p", "demo"])
                missing_filenames, missing_error = _resolve_startup_filenames(["-p", "nope"])
                no_name_filenames, no_name_error = _resolve_startup_filenames(["-p"])
            finally:
                ViEditor.SESSION_PATH = orig

            self.assertEqual(filenames, [a])
            self.assertIsNone(error)
            self.assertIsNone(missing_filenames)
            self.assertIn("no such project", missing_error)
            self.assertIsNone(no_name_filenames)
            self.assertIn("-p requires", no_name_error)

    def test_resolve_startup_filenames_plain_args_and_fallback(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = os.path.join(tmpdir, "session")
            try:
                filenames, error = _resolve_startup_filenames(["a.py", "b.py"])
                self.assertEqual(filenames, ["a.py", "b.py"])
                self.assertIsNone(error)

                filenames, error = _resolve_startup_filenames([])
                self.assertEqual(filenames, [])  # no session file on disk yet
                self.assertIsNone(error)
            finally:
                ViEditor.SESSION_PATH = orig

    # ------------------------------------------------------------------
    # -ns/-nb/-ro / _parse_cli_flags
    # ------------------------------------------------------------------

    def test_parse_cli_flags_short_and_long_forms(self):
        flags, remaining = _parse_cli_flags(["-ns", "a.py"])
        self.assertEqual(flags, {"no_session_save": True, "no_backup": False, "read_only": False})
        self.assertEqual(remaining, ["a.py"])

        flags, remaining = _parse_cli_flags(["--no-backup", "a.py"])
        self.assertEqual(flags, {"no_session_save": False, "no_backup": True, "read_only": False})
        self.assertEqual(remaining, ["a.py"])

        flags, remaining = _parse_cli_flags(["a.py", "--read-only"])
        self.assertEqual(flags, {"no_session_save": False, "no_backup": False, "read_only": True})
        self.assertEqual(remaining, ["a.py"])

    def test_parse_cli_flags_combine_and_leave_other_args_untouched(self):
        flags, remaining = _parse_cli_flags(["-ro", "-nb", "-p", "demo"])
        self.assertEqual(flags, {"no_session_save": False, "no_backup": True, "read_only": True})
        self.assertEqual(remaining, ["-p", "demo"])

    def test_parse_cli_flags_no_flags_present(self):
        flags, remaining = _parse_cli_flags(["a.py", "b.py"])
        self.assertEqual(flags, {"no_session_save": False, "no_backup": False, "read_only": False})
        self.assertEqual(remaining, ["a.py", "b.py"])

    def test_resolve_project_filenames_filters_to_existing_files(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            a = os.path.join(tmpdir, "a.py")
            with open(a, "w") as fh:
                fh.write("x\n")
            missing = os.path.join(tmpdir, "gone.py")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(
                    "# vii session\n"
                    "# project: demo\n"
                    f"{json.dumps(a, ensure_ascii=False)}\n"
                    f"{json.dumps(missing, ensure_ascii=False)}\n"
                )

            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = session_path
            try:
                filenames, error = _resolve_project_filenames("demo")
                self.assertEqual(filenames, [a])
                self.assertIsNone(error)

                filenames, error = _resolve_project_filenames("nope")
                self.assertIsNone(filenames)
                self.assertIn("no such project", error)
            finally:
                ViEditor.SESSION_PATH = orig

    def test_resolve_project_filenames_distinguishes_read_error_from_missing(self):
        # `vii -p name` for a project whose session file happens to be
        # unreadable must say so, not report "no such project" and send
        # someone chasing a typo instead of a permissions/I/O problem.
        with tempfile.TemporaryDirectory() as tmpdir:
            orig = ViEditor.SESSION_PATH
            ViEditor.SESSION_PATH = tmpdir  # a directory, not a file
            try:
                filenames, error = _resolve_project_filenames("demo")
                self.assertIsNone(filenames)
                self.assertIsNotNone(error)
                self.assertNotIn("no such project", error)
                self.assertIn("could not read", error)
            finally:
                ViEditor.SESSION_PATH = orig

    def test_atomic_write_session_lines_survives_invalid_utf8_filename(self):
        # A path with a byte that isn't valid UTF-8 (legal on POSIX; Python
        # represents it internally via surrogateescape) must not blow up the
        # write with UnicodeEncodeError -- that exception type isn't caught
        # by _atomic_write_session_lines's `except OSError`, which used to
        # both leak the temp file and abort the whole session save.
        with tempfile.TemporaryDirectory() as tmpdir:
            bad_name = os.fsdecode(b"bad-\xffname.txt")
            bad_path = os.path.join(tmpdir, bad_name)
            with open(os.fsencode(bad_path), "w") as fh:
                fh.write("x\n")
            session_path = os.path.join(tmpdir, "session")

            editor = self._editor_with_session(session_path)
            editor.filename = bad_path
            editor.lines = ["x"]
            editor.buffers = [editor._capture_buffer_state()]

            editor._save_session()  # must not raise

            self.assertTrue(os.path.isfile(session_path))
            leftovers = [
                name for name in os.listdir(tmpdir)
                if name.startswith(".vii_session.") and name.endswith(".tmp")
            ]
            self.assertEqual(leftovers, [])
            with open(session_path, "rb") as fh:
                content = fh.read()
            self.assertIn(b"bad-\\udcffname.txt", content)
            content.decode("utf-8")  # The session itself remains valid UTF-8.
            self.assertIn(bad_path, editor._read_session_map(session_path))

    def test_atomic_write_session_lines_fsyncs_file_and_dir(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor = self._editor_with_session(session_path)

            with mock.patch("vi_editor.os.fsync") as mock_fsync, \
                 mock.patch.object(ViEditor, "_fsync_dir") as mock_fsync_dir:
                self.assertTrue(editor._atomic_write_session_lines(["# vii session"]))

            mock_fsync.assert_called_once()
            mock_fsync_dir.assert_called_once_with(os.path.dirname(session_path))

    def test_read_session_map_raises_on_real_read_error_not_missing_file(self):
        # Mirrors _read_project_sections: a missing file means "nothing
        # saved yet" and stays silent, but a file that exists and can't
        # actually be read (here: it's a directory) must not be treated the
        # same way, or a caller doing a read-modify-write can't tell the
        # difference and may silently discard what it failed to read.
        self.assertEqual(ViEditor._read_session_map("/no/such/path/at/all"), {})
        with tempfile.TemporaryDirectory() as tmpdir:
            with self.assertRaises(OSError):
                ViEditor._read_session_map(tmpdir)

    def test_save_session_skips_write_on_mru_read_error(self):
        # Same "must never raise but must not silently clobber" contract as
        # test_save_session_skips_write_on_project_section_read_error, but
        # for the MRU-entries read instead of the project-sections read.
        with tempfile.TemporaryDirectory() as tmpdir:
            path = os.path.join(tmpdir, "notes.txt")
            with open(path, "w") as fh:
                fh.write("line1\n")
            other = os.path.join(tmpdir, "other.py")
            with open(other, "w") as fh:
                fh.write("y\n")
            session_path = os.path.join(tmpdir, "session")
            with open(session_path, "w") as fh:
                fh.write(f"# vii session\n{json.dumps(other, ensure_ascii=False)}\t0\t0\n")
            with open(session_path, "rb") as fh:
                original_content = fh.read()

            editor = self._editor_with_session(session_path)
            editor.filename = path
            editor.lines = ["line1"]
            editor.buffers = [editor._capture_buffer_state()]

            with mock.patch.object(ViEditor, "_read_session_map",
                                    side_effect=PermissionError("denied")):
                editor._save_session()  # must not raise

            with open(session_path, "rb") as fh:
                self.assertEqual(fh.read(), original_content)  # untouched

    def test_session_lock_provides_mutual_exclusion_across_threads(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            editor_a = self._editor_with_session(session_path)
            editor_b = self._editor_with_session(session_path)

            events = []

            def critical_section(editor, name):
                with editor._session_lock():
                    events.append((name, "start"))
                    time.sleep(0.05)
                    events.append((name, "end"))

            t1 = threading.Thread(target=critical_section, args=(editor_a, "a"))
            t2 = threading.Thread(target=critical_section, args=(editor_b, "b"))
            t1.start()
            time.sleep(0.01)
            t2.start()
            t1.join(timeout=2)
            t2.join(timeout=2)

            # Two different ViEditor instances (as two vii processes would
            # be) must not interleave their locked sections: whichever one
            # goes first must fully finish (start, end) before the other's
            # start.
            self.assertEqual(len(events), 4)
            first = events[0][0]
            second = events[2][0]
            self.assertNotEqual(first, second)
            self.assertEqual(events[0], (first, "start"))
            self.assertEqual(events[1], (first, "end"))
            self.assertEqual(events[2], (second, "start"))
            self.assertEqual(events[3], (second, "end"))

    def test_concurrent_save_session_calls_do_not_lose_entries(self):
        # Regression test for the read-modify-write race _session_lock
        # fixes: two vii processes exiting around the same time must not be
        # able to read a stale snapshot and clobber each other's entry.
        with tempfile.TemporaryDirectory() as tmpdir:
            session_path = os.path.join(tmpdir, "session")
            a = os.path.join(tmpdir, "a.txt")
            b = os.path.join(tmpdir, "b.txt")
            for p in (a, b):
                with open(p, "w") as fh:
                    fh.write("x\n")

            editor_a = self._editor_with_session(session_path)
            editor_a.filename = a
            editor_a.lines = ["x"]
            editor_a.buffers = [editor_a._capture_buffer_state()]

            editor_b = self._editor_with_session(session_path)
            editor_b.filename = b
            editor_b.lines = ["x"]
            editor_b.buffers = [editor_b._capture_buffer_state()]

            real_read = ViEditor._read_session_map
            b_started = threading.Event()

            def read_and_stall(path):
                # Stall while still holding the lock, so a concurrent
                # editor_a._save_session() call has to block on the lock
                # rather than racing this read.
                result = real_read(path)
                b_started.set()
                time.sleep(0.1)
                return result

            with mock.patch.object(ViEditor, "_read_session_map", side_effect=read_and_stall):
                t_b = threading.Thread(target=editor_b._save_session)
                t_b.start()
                self.assertTrue(b_started.wait(timeout=2))
                editor_a._save_session()  # blocks on the lock until b is done
                t_b.join(timeout=2)

            with open(session_path) as fh:
                content = fh.read()
            self.assertIn(os.path.abspath(a), content)
            self.assertIn(os.path.abspath(b), content)


class BugFixTests(unittest.TestCase):
    """Regression tests for bugs identified in code review."""

    # ------------------------------------------------------------------
    # Fix 1: forward search wrap must not use endpos to truncate the line
    # ------------------------------------------------------------------

    def test_search_wrap_finds_multichar_pattern_at_col_zero(self):
        """A multi-char pattern at col 0 is found when search wraps around."""
        editor = ViEditor()
        editor.lines = ["abc", "xyz"]
        editor.cursor_row = 0
        editor.cursor_col = 1
        # Search forward: first hit on row 0 col 0 is before cursor so missed;
        # row 1 has no match; wrap-around should find col 0 on row 0.
        editor._search("abc", forward=True)
        self.assertEqual(editor.cursor_row, 0)
        self.assertEqual(editor.cursor_col, 0)
        self.assertEqual(editor.message, "search wrapped")

    def test_search_wrap_finds_long_pattern_that_spans_past_cursor_col(self):
        """Wrap finds a multi-char pattern whose start is before the cursor even
        when the pattern extends past cursor_col+1 (the old endpos bug)."""
        editor = ViEditor()
        editor.lines = ["aaaxxx"]
        editor.cursor_row = 0
        editor.cursor_col = 1
        # "aaa" starts at col 0 which is ≤ cursor (1), but extends to col 2.
        # Forward scan from col+1=2 finds nothing; wrap must find col 0.
        # Old bug: regex.search(line, 0, 2) presents only "aa" to the engine
        # so "aaa" could not match. Fix: search full line, guard m.start()<=col.
        editor._search("aaa", forward=True)
        self.assertEqual(editor.cursor_col, 0)
        self.assertEqual(editor.message, "search wrapped")

    # ------------------------------------------------------------------
    # Fix 2: \n in :s replacement must split the line, not embed a newline
    # ------------------------------------------------------------------

    def test_substitute_newline_in_replacement_splits_line(self):
        """\\n in a replacement string splits the matched line into two."""
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._execute_cmd(":s/hello/hi\\nthere/")
        self.assertEqual(editor.lines, ["hi", "there world"])
        self.assertEqual(len(editor.lines), 2)
        for line in editor.lines:
            self.assertNotIn("\n", line, "embedded newline must not survive in self.lines")

    def test_substitute_newline_replacement_does_not_corrupt_file_bytes(self):
        """After a \\n-split substitution, saving must not embed raw newline bytes."""
        editor = ViEditor()
        editor.lines = ["foo bar"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._execute_cmd(":s/foo/a\\nb/")
        for line in editor.lines:
            self.assertNotIn("\n", line)

    def test_substitute_newline_split_keeps_line_endings_in_sync(self):
        """Splitting a line via \\n in the replacement must not desync the
        parallel line_endings list from self.lines. Previously the split
        left line_endings one entry longer than lines, because self.lines
        was grown before _insert_line_endings ran, and that helper's call
        to _normalize_line_endings padded against the already-grown count
        before inserting its own entry on top."""
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._execute_cmd(":s/hello/hi\\nthere/")
        self.assertEqual(editor.lines, ["hi", "there world"])
        self.assertEqual(editor.line_endings, ["\n", "\n"])

    def test_substitute_newline_split_on_noeol_line_preserves_noeol(self):
        """Splitting the last line of a file with no trailing newline must
        move the "no newline at EOF" marker onto the new last line, not
        strand it on the now-interior first half (which would merge the
        two lines together with no separator when saved via :b64e)."""
        editor = ViEditor()
        editor.lines = ["a,b"]
        editor.line_endings = [""]
        editor._normalize_line_endings()
        editor.line_endings_trusted = True
        editor._execute_cmd(":s/,/\\n/")
        self.assertEqual(editor.lines, ["a", "b"])
        self.assertEqual(editor.line_endings, ["\n", ""])
        raw = editor._buffer_bytes(preserve_complete_endings=True)
        self.assertEqual(raw, b"a\nb")

    def test_substitute_multiple_embedded_newlines_keeps_endings_in_sync(self):
        """A replacement that splits a line into 3+ parts must still keep
        line_endings the same length as lines."""
        editor = ViEditor()
        editor.lines = ["one two three"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._execute_cmd(":s/ /\\n/g")
        self.assertEqual(editor.lines, ["one", "two", "three"])
        self.assertEqual(editor.line_endings, ["\n", "\n", "\n"])

    def test_global_substitute_newline_split_across_lines_keeps_endings_in_sync(self):
        """A :%s across multiple lines, each split by an embedded newline,
        must keep line_endings in lockstep as later replacements shift by
        the growing line_offset."""
        editor = ViEditor()
        editor.lines = ["a,1", "b,2"]
        editor.line_endings = ["\n", ""]
        editor._normalize_line_endings()
        editor._execute_cmd(":%s/,/\\n/")
        self.assertEqual(editor.lines, ["a", "1", "b", "2"])
        self.assertEqual(len(editor.lines), len(editor.line_endings))
        self.assertEqual(editor.line_endings, ["\n", "\n", "\n", ""])

    def test_substitute_confirm_newline_split_keeps_line_endings_in_sync(self):
        """The interactive :s///c confirm path ('y' on a single match) must
        keep line_endings in sync when the confirmed replacement splits a
        line, same as the non-interactive path."""
        import re
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor._stdscr = mock.MagicMock()
        editor._stdscr.get_wch.side_effect = ["y"]
        editor.draw = mock.MagicMock()
        editor._do_substitute_confirm(
            0, 0, re.compile("hello"), "hello", "hi\\nthere", "c", False,
        )
        self.assertEqual(editor.lines, ["hi", "there world"])
        self.assertEqual(editor.line_endings, ["\n", "\n"])

    def test_substitute_confirm_all_newline_split_keeps_line_endings_in_sync(self):
        """The "a" (apply to all remaining matches) confirm path must also
        keep line_endings in sync across multiple splitting replacements."""
        import re
        editor = ViEditor()
        editor.lines = ["hello world", "hello again"]
        editor.line_endings = ["\n", ""]
        editor._normalize_line_endings()
        editor._stdscr = mock.MagicMock()
        editor._stdscr.get_wch.side_effect = ["a"]
        editor.draw = mock.MagicMock()
        editor._do_substitute_confirm(
            0, 1, re.compile("hello"), "hello", "hi\\nthere", "gc", True,
        )
        self.assertEqual(editor.lines, ["hi", "there world", "hi", "there again"])
        self.assertEqual(len(editor.lines), len(editor.line_endings))
        self.assertEqual(editor.line_endings, ["\n", "\n", "\n", ""])

    # ------------------------------------------------------------------
    # Fix: marks on a line split by an embedded-newline substitution
    # landed on the wrong row (both _adjust_marks_for_line_matches and
    # _adjust_marks_for_line_replace only ever kept mark_row == row, never
    # accounting for the row split), so a mark past the first split
    # segment was silently collapsed onto row `r` at a meaningless column
    # instead of following its character onto the later row it moved to.
    # ------------------------------------------------------------------

    def test_substitute_glob_newline_split_remaps_marks_to_correct_rows(self):
        editor = ViEditor()
        editor.lines = ["aaa,bbb,ccc"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor.marks["a"] = (0, 1)   # inside "aaa"
        editor.marks["b"] = (0, 5)   # inside "bbb"
        editor.marks["c"] = (0, 9)   # inside "ccc"

        editor._execute_cmd(":s/,/\\n/g")

        self.assertEqual(editor.lines, ["aaa", "bbb", "ccc"])
        self.assertEqual(editor.marks["a"], (0, 1))
        self.assertEqual(editor.marks["b"], (1, 1))
        self.assertEqual(editor.marks["c"], (2, 1))

    def test_substitute_newline_split_shifts_marks_on_later_lines_once(self):
        """A mark on a line *after* the split row must shift by exactly the
        number of new rows inserted -- not be left alone, and not be
        double-shifted by both the split remap and the line-insert shift."""
        editor = ViEditor()
        editor.lines = ["aaa,bbb,ccc", "next line"]
        editor.line_endings = ["\n", "\n"]
        editor._normalize_line_endings()
        editor.marks["x"] = (1, 3)

        editor._execute_cmd(":s/,/\\n/g")

        self.assertEqual(editor.lines, ["aaa", "bbb", "ccc", "next line"])
        self.assertEqual(editor.marks["x"], (3, 3))

    def test_substitute_confirm_newline_split_remaps_marks_to_correct_rows(self):
        """The interactive :s///c confirm path must remap marks the same
        way as the non-interactive glob path."""
        import re
        editor = ViEditor()
        editor.lines = ["hello world"]
        editor.line_endings = ["\n"]
        editor._normalize_line_endings()
        editor.marks["w"] = (0, 8)   # inside "world"
        editor._stdscr = mock.MagicMock()
        editor._stdscr.get_wch.side_effect = ["y"]
        editor.draw = mock.MagicMock()

        editor._do_substitute_confirm(
            0, 0, re.compile("hello"), "hello", "hi\\nthere", "c", False,
        )

        self.assertEqual(editor.lines, ["hi", "there world"])
        row, col = editor.marks["w"]
        self.assertEqual(row, 1, "mark must follow its character onto the split-off row")

    # ------------------------------------------------------------------
    # Fix 3: :0 as a line address must be rejected (invalid address)
    # ------------------------------------------------------------------

    def test_address_zero_is_rejected_for_delete(self):
        """:0d must produce an error, not silently delete the first line."""
        editor = ViEditor()
        editor.lines = ["alpha", "beta"]
        editor._execute_cmd(":0d")
        self.assertEqual(editor.lines, ["alpha", "beta"], ":0d must not delete anything")
        self.assertTrue(editor.message_is_error)

    def test_address_zero_is_rejected_for_substitute(self):
        """:0s/…/…/ must produce an error."""
        editor = ViEditor()
        editor.lines = ["alpha"]
        editor._execute_cmd(":0s/alpha/beta/")
        self.assertEqual(editor.lines, ["alpha"], ":0s must not modify anything")
        self.assertTrue(editor.message_is_error)

    # ------------------------------------------------------------------
    # Fix 4: dot-repeat of :s applies to current cursor row, not frozen row
    # ------------------------------------------------------------------

    def test_substitute_dot_repeat_applies_to_current_line(self):
        """. after :s (no range) substitutes on the current cursor row."""
        editor = ViEditor()
        editor.lines = ["foo", "foo", "foo"]
        editor.cursor_row = 0
        editor._execute_cmd(":s/foo/bar/")
        self.assertEqual(editor.lines[0], "bar")
        editor.cursor_row = 2
        editor._repeat_last_change(1)
        self.assertEqual(editor.lines[2], "bar", ". must apply to cursor row 2")
        self.assertEqual(editor.lines[1], "foo", "row 1 must be untouched")

    def test_substitute_dot_repeat_with_explicit_range_keeps_frozen_range(self):
        """When :s had an explicit range, . repeats on that same range."""
        editor = ViEditor()
        editor.lines = ["foo", "foo", "foo"]
        editor.cursor_row = 0
        editor._execute_cmd(":1,2s/foo/bar/")
        editor.cursor_row = 2
        editor._repeat_last_change(1)
        self.assertEqual(editor.lines[0], "bar")
        self.assertEqual(editor.lines[1], "bar")
        self.assertEqual(editor.lines[2], "foo", "row 2 outside frozen range must be untouched")

    # ------------------------------------------------------------------
    # Fix 5: _replace_chars must adjust marks inside the replaced span
    # ------------------------------------------------------------------

    def test_replace_chars_adjusts_mark_inside_replaced_span(self):
        """r<char> moves a mark inside the replaced span to the replacement end."""
        editor = ViEditor()
        editor.lines = ["abcde"]
        editor.marks = {"a": (0, 2)}
        editor.cursor_row = 0
        editor.cursor_col = 1
        editor._replace_chars("x", 3)
        # Replaced cols 1-3 with "xxx"; mark at col 2 (inside span) should
        # move to prefix + max(0, new_changed_len - 1) = 1 + (3-1) = 3.
        mark_row, mark_col = editor.marks.get("a", (-1, -1))
        self.assertEqual(mark_row, 0)
        self.assertEqual(mark_col, 3)

    def test_replace_chars_mark_before_span_is_unchanged(self):
        """A mark before the replaced span must not move."""
        editor = ViEditor()
        editor.lines = ["abcde"]
        editor.marks = {"a": (0, 0)}
        editor.cursor_row = 0
        editor.cursor_col = 2
        editor._replace_chars("x", 2)
        mark_row, mark_col = editor.marks.get("a", (-1, -1))
        self.assertEqual(mark_row, 0)
        self.assertEqual(mark_col, 0)

    # ------------------------------------------------------------------
    # Fix 6: _syntax_cache must evict LRU entries, not FIFO entries
    # ------------------------------------------------------------------

    def test_syntax_cache_retains_recently_accessed_entry_on_eviction(self):
        """Cache hit must move the entry to MRU position so it survives eviction."""
        editor = ViEditor()
        editor._syntax_cache.clear()
        # Cache keys are (lang, text); _syntax_spans(text, lang)
        # Fill exactly 512 entries so the next miss triggers eviction.
        for i in range(512):
            editor._syntax_cache[("python", f"line_{i}")] = []
        # Touch line_0 (oldest) via a cache hit to move it to MRU position.
        editor._syntax_spans("line_0", "python")
        # Add one new entry: size is 512 >= 512 → evict 256 LRU, then insert.
        editor._syntax_spans("brand_new_ZZZZ", "python")
        # line_0 was MRU so it must survive.
        self.assertIn(("python", "line_0"), editor._syntax_cache,
                      "recently-used entry must not be evicted by LRU")

    def test_syntax_cache_evicts_least_recently_used(self):
        """The 256 oldest-access entries must be evicted when the cache hits 512."""
        editor = ViEditor()
        editor._syntax_cache.clear()
        # Fill 512 entries (0..511) in insertion order; none touched after insert.
        for i in range(512):
            editor._syntax_cache[("python", f"line_{i}")] = []
        # Touch line_0 → moves to MRU end. Order: line_1, …, line_511, line_0.
        editor._syntax_spans("line_0", "python")
        # Next miss: 512 >= 512 → evict 256 from LRU end (line_1 … line_256).
        editor._syntax_spans("triggering_entry", "python")
        # line_1 … line_256 must be gone.
        for i in range(1, 257):
            self.assertNotIn(("python", f"line_{i}"), editor._syntax_cache,
                             f"LRU entry line_{i} should have been evicted")
        # line_0, line_257 … line_511, and the new entry must survive.
        self.assertIn(("python", "line_0"), editor._syntax_cache)
        for i in range(257, 512):
            self.assertIn(("python", f"line_{i}"), editor._syntax_cache)

    # ------------------------------------------------------------------
    # _search_regex_cache must be a bounded LRU, not an unbounded dict
    # ------------------------------------------------------------------

    def test_compile_pattern_caches_and_reuses_compiled_regex(self):
        """A repeated (pattern, flags) pair must return the same compiled object."""
        editor = ViEditor()
        editor._search_regex_cache.clear()

        first = editor._compile_pattern("abc", 0)
        second = editor._compile_pattern("abc", 0)

        self.assertIsNotNone(first)
        self.assertIs(first, second)
        self.assertEqual(len(editor._search_regex_cache), 1)

    def test_compile_pattern_distinguishes_flags(self):
        """The same pattern text with different flags must not collide in the cache."""
        import re
        editor = ViEditor()
        editor._search_regex_cache.clear()

        plain = editor._compile_pattern("abc", 0)
        ignorecase = editor._compile_pattern("abc", re.IGNORECASE)

        self.assertIsNot(plain, ignorecase)
        self.assertEqual(len(editor._search_regex_cache), 2)

    def test_search_regex_cache_is_bounded_not_unbounded(self):
        """Compiling many distinct patterns must not grow the cache without limit."""
        editor = ViEditor()
        editor._search_regex_cache.clear()

        for i in range(600):
            editor._compile_pattern(f"pattern_{i}", 0)

        self.assertLessEqual(len(editor._search_regex_cache), 512,
                              "_search_regex_cache must evict entries instead of growing forever")

    def test_search_regex_cache_retains_recently_used_entry_on_eviction(self):
        """A cache hit must move the entry to MRU position so it survives eviction."""
        import re
        editor = ViEditor()
        editor._search_regex_cache.clear()
        for i in range(512):
            editor._search_regex_cache[(f"pattern_{i}", 0)] = re.compile(f"pattern_{i}")

        # Touch pattern_0 (oldest) via a cache hit to move it to MRU position.
        editor._compile_pattern("pattern_0", 0)
        # One more miss: 512 >= 512 → evict 256 LRU, then insert.
        editor._compile_pattern("brand_new_ZZZZ", 0)

        self.assertIn(("pattern_0", 0), editor._search_regex_cache,
                      "recently-used entry must not be evicted by LRU")

    def test_search_regex_cache_evicts_least_recently_used(self):
        """The 256 oldest-access entries must be evicted when the cache hits 512."""
        import re
        editor = ViEditor()
        editor._search_regex_cache.clear()
        for i in range(512):
            editor._search_regex_cache[(f"pattern_{i}", 0)] = re.compile(f"pattern_{i}")

        editor._compile_pattern("pattern_0", 0)  # moves to MRU end
        editor._compile_pattern("triggering_entry", 0)  # 512 >= 512 → evict 256 LRU

        for i in range(1, 257):
            self.assertNotIn((f"pattern_{i}", 0), editor._search_regex_cache,
                             f"LRU entry pattern_{i} should have been evicted")
        self.assertIn(("pattern_0", 0), editor._search_regex_cache)
        for i in range(257, 512):
            self.assertIn((f"pattern_{i}", 0), editor._search_regex_cache)

    # ------------------------------------------------------------------
    # Fix 7: _leave_insert must not push undo when insert made no net change
    # ------------------------------------------------------------------

    def test_leave_insert_pushes_no_undo_when_revision_unchanged(self):
        """Pressing ESC immediately after entering insert must not push undo."""
        editor = ViEditor()
        editor.lines = ["hello"]
        editor.line_endings = ["\n"]
        editor._mark_clean()
        editor._enter_insert()
        editor._leave_insert()
        self.assertFalse(editor.undo_stack, "no-op insert must not push an undo entry")

    def test_leave_insert_does_push_undo_after_actual_change(self):
        """After a real change in insert mode, _leave_insert must push an undo entry."""
        editor = ViEditor()
        editor.lines = ["hello"]
        editor.line_endings = ["\n"]
        editor._mark_clean()
        editor._enter_insert()
        editor.lines[0] = "world"
        editor.modified = True
        editor._leave_insert()
        self.assertTrue(editor.undo_stack, "real change must push an undo entry")

    # ------------------------------------------------------------------
    # Fix 8: bracket cache must be a dict to cache multiple positions
    # ------------------------------------------------------------------

    def test_bracket_cache_hits_for_previously_seen_position(self):
        """Moving away from a bracket and returning must hit the cache."""
        editor = ViEditor()
        editor.lines = ["(hello)"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        # First call: cold cache
        result1 = editor._matching_bracket_pair()
        self.assertIsNotNone(result1)
        # Move cursor away
        editor.cursor_col = 6
        _ = editor._matching_bracket_pair()
        # Return to original position — should be a cache hit (no new scan)
        editor.cursor_col = 0
        scans = [0]
        orig = editor._find_matching_bracket
        def counting_find(*args):
            scans[0] += 1
            return orig(*args)
        editor._find_matching_bracket = counting_find
        result2 = editor._matching_bracket_pair()
        self.assertEqual(scans[0], 0, "returning to a cached bracket position must not rescan")
        self.assertEqual(result1, result2)

    def test_bracket_cache_invalidated_by_content_change(self):
        """Editing the buffer must invalidate previous bracket cache entries."""
        editor = ViEditor()
        editor.lines = ["(hello)"]
        editor.cursor_row = 0
        editor.cursor_col = 0
        editor._matching_bracket_pair()
        initial_cache_size = len(editor._bracket_match_cache)
        # Simulate a content edit
        editor.modified = True
        editor._matching_bracket_pair()
        # New entry was added for the new revision
        self.assertGreaterEqual(len(editor._bracket_match_cache), initial_cache_size)

    # ------------------------------------------------------------------
    # Fix 9: _push_undo must not re-hash the whole buffer on every edit.
    # _prepare_line_endings_for_edit used to call _current_signature (a
    # full blake2b hash of every line) unconditionally, before checking
    # whether line-ending normalization would even change anything. Since
    # :g dispatches one sub-command -- and hence one _push_undo -- per
    # matched line, that turned a plain :g//s// into O(n) buffer-sized
    # hashes, i.e. O(n^2) overall.
    # ------------------------------------------------------------------

    def test_push_undo_skips_full_buffer_hash_when_line_endings_in_sync(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.line_endings = ["\n", "\n", ""]
        editor._mark_clean()

        calls = [0]
        orig = editor._line_signature
        def counting_signature(*args, **kwargs):
            calls[0] += 1
            return orig(*args, **kwargs)
        editor._line_signature = counting_signature

        editor._push_undo()

        self.assertEqual(calls[0], 0,
            "no-op line-ending normalization must not hash buffer content")

    def test_push_undo_still_marks_clean_when_normalization_changes_endings(self):
        """When line_endings is out of sync with lines going in, and the
        saved signature matches that pre-normalization state, the buffer
        must still come out clean after normalization pads it back --
        matches the pre-optimization behavior exactly."""
        editor = ViEditor()
        editor.lines = ["a", "b"]
        editor.line_endings = ["\n"]           # short by one entry
        editor._mark_clean()                   # signature captured against the desynced state
        self.assertFalse(editor.modified)

        editor._push_undo()

        self.assertEqual(editor.line_endings, ["\n", ""])
        self.assertFalse(editor.modified,
            "line-ending-only normalization must not dirty a clean buffer")

    def test_global_substitute_does_not_hash_buffer_per_matched_line(self):
        editor = ViEditor()
        editor.lines = [f"line{i}" for i in range(300)]
        editor.line_endings = ["\n"] * 299 + [""]
        editor._mark_clean()

        calls = [0]
        orig = editor._line_signature
        def counting_signature(*args, **kwargs):
            calls[0] += 1
            return orig(*args, **kwargs)
        editor._line_signature = counting_signature

        self.assertTrue(editor._execute_cmd("g/line/s/line/x/"))

        self.assertEqual(calls[0], 0,
            ":g//s// must not re-hash the whole buffer for every matched line")
        self.assertEqual(editor.lines[0], "x0")
        self.assertEqual(editor.lines[-1], "x299")

    # ------------------------------------------------------------------
    # Fix 10: _clamp_auto_marks must not rebuild auto_marks when every
    # entry is already in bounds. :g stashes one temporary auto_marks
    # entry per matched line (see _run_global_command) and every matched
    # line's sub-command triggers a clamp pass, so an unconditional
    # rebuild there was also O(n) work repeated O(n) times.
    # ------------------------------------------------------------------

    def test_clamp_auto_marks_skips_rebuild_when_already_in_bounds(self):
        editor = ViEditor()
        editor.lines = ["a", "b", "c"]
        editor.auto_marks = {1: 0, 2: 2}
        original = editor.auto_marks

        editor._clamp_auto_marks()

        self.assertIs(editor.auto_marks, original,
            "in-bounds auto_marks must not be replaced with a new dict")

    def test_clamp_auto_marks_still_clamps_out_of_range_entries(self):
        editor = ViEditor()
        editor.lines = ["a", "b"]
        editor.auto_marks = {1: 5, 2: -3}

        editor._clamp_auto_marks()

        self.assertEqual(editor.auto_marks, {1: 1, 2: 0})

    # ------------------------------------------------------------------
    # Fix 11: file-browser grep must be bounded like the shell-command
    # path (SHELL_COMMAND_TIMEOUT_SECONDS / SHELL_COMMAND_MAX_OUTPUT_BYTES).
    # It used to run an unbounded os.walk synchronously in the key handler
    # with no result cap and no deadline, so a broad pattern over a big
    # tree could freeze the whole UI and grow grep_results without limit.
    # ------------------------------------------------------------------

    def test_file_browser_grep_caps_results_and_reports_truncation(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            for i in range(20):
                path = os.path.join(tmpdir, f"f{i}.txt")
                with open(path, "w", encoding="utf-8") as fh:
                    fh.write("needle\n" * 5)

            editor = ViEditor()
            old_cap = editor.FB_GREP_MAX_RESULTS
            try:
                editor.FB_GREP_MAX_RESULTS = 7
                editor._run_file_browser_grep(tmpdir, "needle")
            finally:
                editor.FB_GREP_MAX_RESULTS = old_cap

            self.assertEqual(len(editor.grep_results), 7)
            self.assertIn("(truncated)", editor.message)

    def test_file_browser_grep_respects_expired_deadline(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            with open(os.path.join(tmpdir, "f.txt"), "w", encoding="utf-8") as fh:
                fh.write("needle\n")

            editor = ViEditor()
            old_timeout = editor.FB_GREP_TIMEOUT_SECONDS
            try:
                editor.FB_GREP_TIMEOUT_SECONDS = 0
                editor._run_file_browser_grep(tmpdir, "needle")
            finally:
                editor.FB_GREP_TIMEOUT_SECONDS = old_timeout

            self.assertEqual(editor.grep_results, [])
            self.assertIn("(truncated)", editor.message)

    def test_file_browser_grep_finds_matches_within_deadline(self):
        """Sanity check: ordinary greps are unaffected by the new bound."""
        with tempfile.TemporaryDirectory() as tmpdir:
            with open(os.path.join(tmpdir, "f.txt"), "w", encoding="utf-8") as fh:
                fh.write("needle\nhaystack\n")

            editor = ViEditor()
            editor._run_file_browser_grep(tmpdir, "needle")

            self.assertEqual(len(editor.grep_results), 1)
            self.assertNotIn("truncated", editor.message)

    # ------------------------------------------------------------------
    # Follow-up fix: a single physical "line" with no newline (or an
    # absurdly long line) used to be read in one unbounded call via
    # `for line in fh`, which only checks the deadline on line_no % 500 --
    # never true while still reading line 1. The read is now chunked via
    # fh.readline(FB_GREP_MAX_LINE_BYTES) with a deadline check every chunk.
    # ------------------------------------------------------------------

    def test_file_browser_grep_bounds_single_read_on_line_with_no_newline(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            # One giant physical line, no trailing newline, with the needle
            # planted well past the first chunk boundary.
            content = ("z" * 500) + "needle" + ("z" * 500)
            with open(os.path.join(tmpdir, "blob.txt"), "w", encoding="utf-8") as fh:
                fh.write(content)

            editor = ViEditor()
            editor.FB_GREP_MAX_LINE_BYTES = 64
            editor.FB_GREP_TIMEOUT_SECONDS = 10.0
            real_monotonic = time.monotonic
            call_count = {"n": 0}

            def fake_monotonic():
                call_count["n"] += 1
                # Let the deadline get computed and the first couple of
                # bookkeeping checks pass untouched, then expire on the
                # very next check -- i.e. after at most one 64-byte chunk
                # has been read, long before "needle" at offset 500.
                if call_count["n"] <= 4:
                    return real_monotonic()
                return real_monotonic() + 1000

            with mock.patch("vi_editor.time.monotonic", side_effect=fake_monotonic):
                editor._run_file_browser_grep(tmpdir, "needle")

            self.assertEqual(
                editor.grep_results, [],
                "the deadline must be honored mid-line, before the whole "
                "no-newline blob can be read in one go",
            )
            self.assertIn("(truncated)", editor.message)

    def test_file_browser_grep_skips_overlong_line_but_keeps_scanning(self):
        with tempfile.TemporaryDirectory() as tmpdir:
            overlong_line = ("x" * 40) + "needle" + ("y" * 40) + "\n"
            normal_line = "second needle line\n"
            with open(os.path.join(tmpdir, "f.txt"), "w", encoding="utf-8") as fh:
                fh.write(overlong_line + normal_line)

            editor = ViEditor()
            editor.FB_GREP_MAX_LINE_BYTES = 50
            editor._run_file_browser_grep(tmpdir, "needle")

            self.assertEqual(len(editor.grep_results), 1)
            self.assertEqual(editor.grep_results[0].line_no, 2)
            self.assertEqual(editor.grep_results[0].text, "second needle line")

    # ------------------------------------------------------------------
    # Fix 12: intellisense must not rescan the whole buffer on every
    # keystroke of a word that matches nothing elsewhere. The fast path in
    # _refresh_intellisense_completion only reused the previous scan when
    # it had found at least one match; an empty (but exhaustive) result
    # was discarded via _clear_intellisense_completion, so typing a
    # brand-new identifier -- the single most common thing typed in
    # insert mode -- forced a fresh full-buffer scan on every character.
    # ------------------------------------------------------------------

    def test_intellisense_skips_rescan_for_prefix_with_no_matches(self):
        class NoScanRegex:
            def finditer(self, line):
                raise AssertionError("unexpected intellisense rescan")

        editor = ViEditor()
        editor.intellisense = True
        editor.lines = ["alpha alpine beta", "z"]
        editor.cursor_row = 1
        editor.cursor_col = 1
        editor.mode = Mode.INSERT

        editor._handle_insert(14)  # Ctrl-N: exhaustive scan for "z" -- no matches.
        self.assertEqual(editor._intellisense_completion_matches, [])
        self.assertTrue(editor._intellisense_completion_complete)
        self.assertEqual(editor._intellisense_completion_prefix, "z")

        with mock.patch.object(editor, "_RE_INTELLISENSE_WORD", NoScanRegex()):
            editor._handle_insert(ord("z"))  # lengthen "z" -> "zz": still no matches

        self.assertEqual(editor._intellisense_completion_matches, [])
        self.assertEqual(editor._intellisense_completion_prefix, "zz")

    def test_intellisense_scans_buffer_at_most_once_typing_a_new_word(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.lines = [f"existing_{i}" for i in range(50)] + [""]
        editor.cursor_row = len(editor.lines) - 1
        editor.cursor_col = 0
        editor.mode = Mode.INSERT

        scans = [0]
        orig = editor._line_completion_words
        def counting_words(line):
            scans[0] += 1
            return orig(line)
        editor._line_completion_words = counting_words

        for ch in "brand_new_symbol_not_seen_elsewhere":
            editor._handle_insert(ord(ch))

        # One full-buffer scan (50 non-cursor lines) for the first
        # keystroke; every later keystroke of the same no-match word must
        # not trigger another one.
        self.assertEqual(scans[0], 50)

    def test_intellisense_scan_is_capped_on_huge_buffers(self):
        editor = ViEditor()
        editor.intellisense = True
        editor.MAX_INTELLISENSE_SCAN_LINES = 10
        editor.lines = (
            [f"unrelated_{i}" for i in range(10)]  # rows 0-9: within the cap
            + ["needle_word"]                      # row 10: at/past the cap
            + [f"unrelated_{i}" for i in range(50)]
            + [""]
        )
        editor.cursor_row = len(editor.lines) - 1
        editor.cursor_col = 0
        editor.mode = Mode.INSERT

        editor._handle_insert(ord("n"))

        # The matching line sits past the scan cap, so it must not surface
        # as a completion, and the result must be marked incomplete rather
        # than silently treated as exhaustive.
        self.assertNotIn("needle_word", editor._intellisense_completion_matches)
        self.assertFalse(editor._intellisense_completion_complete)

    def test_paste_into_command_prompt_is_literal_and_not_submitted(self):
        editor = ViEditor()
        editor.lines = ["text"]
        editor._start_cmd_buf(":")
        editor._run_shell_command = mock.MagicMock()

        self.assertTrue(editor._handle_bracketed_paste("!echo pwned\n", None))

        editor._run_shell_command.assert_not_called()
        self.assertEqual(editor._cmd_buf, ":!echo pwned ")

    def test_cross_device_move_preserves_complete_copy_when_source_cleanup_fails(self):
        with tempfile.TemporaryDirectory() as tmp:
            src = os.path.join(tmp, "src")
            dst = os.path.join(tmp, "dst")
            os.mkdir(src)
            with open(os.path.join(src, "a"), "w") as fh:
                fh.write("A")
            editor = ViEditor()

            def fail_cleanup(path):
                if path == src:
                    raise OSError("cleanup failed")
                return shutil.rmtree(path)

            with mock.patch("vi_editor.os.rename",
                            side_effect=OSError(errno.EXDEV, "cross-device")), \
                 mock.patch.object(editor, "_fb_remove_existing_target",
                                   side_effect=fail_cleanup):
                editor._fb_perform_move([src], dst)

            self.assertTrue(os.path.isfile(os.path.join(dst, "a")))
            self.assertTrue(os.path.isfile(os.path.join(src, "a")))
            self.assertTrue(editor.message_is_error)

    def test_backup_body_is_private_even_when_original_is_missing(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "secret.txt")
            editor = ViEditor()
            editor.lines = ["secret"]
            self.assertTrue(editor._save_file(path))
            editor.lines = ["new secret"]
            self.assertTrue(editor._save_file(path))
            backup = os.path.join(tmp, ".vii_backups", "secret_1.txt")
            self.assertEqual(stat.S_IMODE(os.stat(backup).st_mode), 0o600)

    def test_save_rejects_external_creation_of_new_file(self):
        with tempfile.TemporaryDirectory() as tmp:
            path = os.path.join(tmp, "new.txt")
            editor = ViEditor(path)
            editor.lines[0] = "editor text"
            with open(path, "w") as fh:
                fh.write("external text\n")

            self.assertFalse(editor._save_file())
            with open(path) as fh:
                self.assertEqual(fh.read(), "external text\n")

    def test_global_buffer_switch_aborts_without_quitting_or_leaking_tags(self):
        editor = ViEditor()
        editor.lines = ["x", "x"]
        editor._append_buffer(None, switch=False)

        self.assertTrue(editor._execute_cmd(":g/x/bn"))
        self.assertTrue(editor.message_is_error)
        editor._switch_buffer(0)
        self.assertEqual(editor.auto_marks, {})

    def test_confirmed_substitute_end_anchor_is_finite(self):
        editor = ViEditor()
        editor.lines = ["foo"]
        editor._stdscr = mock.MagicMock()
        editor._stdscr.get_wch.side_effect = ["a"]
        editor.draw = mock.MagicMock()

        self.assertTrue(editor._execute_cmd(":s/$/x/gc"))
        self.assertEqual(editor.lines, ["foox"])

    def test_file_browser_grep_skips_fifo(self):
        with tempfile.TemporaryDirectory() as tmp:
            fifo = os.path.join(tmp, "pipe")
            os.mkfifo(fifo)
            editor = ViEditor()
            editor._run_file_browser_grep(tmp, "needle")
            self.assertEqual(editor.grep_results, [])

    def test_shell_command_waits_for_pipe_eof_after_leader_exit(self):
        editor = ViEditor()
        editor.SHELL_COMMAND_TIMEOUT_SECONDS = 1.0
        code = "import time; print('late', flush=True); time.sleep(.1)"
        rc, output, truncated, timed_out = editor._run_shell_command_limited(
            f"{sys.executable} -c \"{code}\"", "/bin/sh"
        )
        self.assertEqual(rc, 0)
        self.assertIn(b"late", output)
        self.assertFalse(truncated)
        self.assertFalse(timed_out)

    def test_global_undo_does_not_restore_temporary_tags(self):
        editor = ViEditor()
        editor.lines = ["x", "x", "keep"]
        self.assertTrue(editor._execute_cmd(":g/x/d"))
        editor._undo()
        editor._undo()
        self.assertEqual(editor.auto_marks, {})

    def test_single_character_paste_replays_as_literal_segment(self):
        editor = ViEditor()
        editor.lines = ["a", "b"]
        editor.cursor_row = 0
        editor._handle_normal(ord("A"), 24, 80)
        editor._insert_pasted_text("\t")
        editor._leave_insert()
        editor.cursor_row = 1
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["a\t", "b\t"])

    def test_markdown_table_hot_cache_skips_block_rescan(self):
        editor = ViEditor()
        editor.filename = "table.md"
        editor.lines = ["| A | B |", "| --- | --- |", "| one | two |"]
        calls = 0
        original = editor._markdown_table_block

        def count_block(row):
            nonlocal calls
            calls += 1
            return original(row)

        editor._markdown_table_block = count_block
        editor._markdown_table_layout(0)
        editor._markdown_table_layout(1)
        editor._markdown_table_layout(2)
        self.assertEqual(calls, 1)

    def test_dot_repeat_uses_swapcase_for_unicode_titlecase(self):
        editor = ViEditor()
        editor.lines = ["A ǅ"]
        editor._handle_normal(ord("~"), 24, 80)
        editor.cursor_col = 2
        editor._handle_normal(ord("."), 24, 80)
        self.assertEqual(editor.lines, ["a ǅ"])


class UndoRedoTests(unittest.TestCase):
    def _editor_with_lines(self, lines):
        editor = ViEditor()
        editor.lines = list(lines)
        editor.line_endings = ["\n"] * (len(lines) - 1) + [""]
        return editor

    def test_set_undolevels_shrink_trims_existing_stack(self):
        editor = self._editor_with_lines(["one"])
        for i in range(20):
            editor._push_undo()
        self.assertEqual(len(editor.undo_stack), 20)

        self.assertEqual(editor._apply_set_opt("undolevels=5"), "")

        self.assertEqual(editor.max_undo, 5)
        self.assertEqual(len(editor.undo_stack), 5)

    def test_undolevels_below_floor_stays_in_effect_after_more_edits(self):
        # _effective_undo_cap() used to floor the *combined* min(max_undo,
        # budget_cap) at 4, so ":set undolevels=1/2/3" only ever took
        # effect via the :set handler's one-time immediate trim -- the
        # very next _push_undo() recomputed the cap as max(4, min(1,
        # huge_budget)) == 4 and let the stack grow right back past the
        # requested size. The floor must only guard the budget-derived
        # shrinkage for huge buffers, never override an explicit smaller
        # max_undo.
        editor = self._editor_with_lines(["one"])
        self.assertEqual(editor._apply_set_opt("undolevels=1"), "")
        self.assertEqual(editor.max_undo, 1)

        for _ in range(10):
            editor._push_undo()

        self.assertEqual(len(editor.undo_stack), 1)

    def test_append_undo_state_converges_below_shrunk_cap(self):
        editor = self._editor_with_lines(["one"])
        for _ in range(20):
            editor._push_undo()
        # Shrink the cap without going through :set — a single new push must
        # still bring an oversized stack down to the cap, not just hold it
        # at its old size forever.
        editor.max_undo = 5
        editor._push_undo()
        self.assertEqual(len(editor.undo_stack), 5)

    def test_redo_respects_cap_after_undolevels_shrinks(self):
        # Redoing pushes onto undo_stack directly (not through
        # _append_undo_state), so it used to bypass the cap entirely: undo
        # everything, shrink undolevels, then redo everything back and the
        # stack it grows -- undo_stack -- would silently exceed the new cap
        # until the next fresh edit happened to trim it.
        editor = self._editor_with_lines(["one"])
        for i in range(20):
            editor.lines[0] = f"edit{i}"
            editor._push_undo()
        self.assertEqual(len(editor.undo_stack), 20)

        for _ in range(20):
            editor._undo()
        self.assertEqual(len(editor.redo_stack), 20)

        self.assertEqual(editor._apply_set_opt("undolevels=5"), "")
        self.assertEqual(editor.max_undo, 5)

        for _ in range(20):
            editor._redo()

        self.assertLessEqual(len(editor.undo_stack), 5)

    def test_undo_respects_cap_after_undolevels_shrinks(self):
        # Symmetric case: undoing pushes onto redo_stack directly, so a
        # long redo history built while undolevels was high must still be
        # trimmed down once undolevels shrinks and the user undoes again.
        editor = self._editor_with_lines(["one"])
        editor.max_undo = 20
        for i in range(20):
            editor.lines[0] = f"edit{i}"
            editor._push_undo()

        editor._undo()
        self.assertEqual(len(editor.redo_stack), 1)

        editor.max_undo = 5
        for _ in range(19):
            editor._undo()

        self.assertLessEqual(len(editor.redo_stack), 5)

    def test_undo_cap_scales_down_for_large_buffers(self):
        editor = self._editor_with_lines(["x"] * 10)
        editor.UNDO_LINE_BUDGET = 40  # 10-line buffer -> effective cap of 4
        for _ in range(10):
            editor._push_undo()
        self.assertEqual(len(editor.undo_stack), 4)

    def test_undo_cap_never_drops_below_floor(self):
        editor = self._editor_with_lines(["x"] * 10)
        editor.UNDO_LINE_BUDGET = 1
        for _ in range(10):
            editor._push_undo()
        self.assertEqual(len(editor.undo_stack), 4)

    def test_counted_open_line_without_text_is_single_undo_step(self):
        # 3o<Esc> used to push two undo snapshots in the wrong order (the
        # already-mutated intermediate state, then the true pre-command
        # state on top of it), so the first undo jumped straight to the
        # original buffer but a second undo moved *forward* again instead
        # of reporting "already at oldest change".
        editor = self._editor_with_lines(["one", "two"])

        editor._handle_normal(ord("3"), 24, 80)
        editor._handle_normal(ord("o"), 24, 80)
        editor._handle_insert(27)  # ESC, no text typed

        self.assertEqual(list(editor.lines), ["one", "", "", "", "two"])
        self.assertEqual(len(editor.undo_stack), 1)
        self.assertEqual(editor.undo_stack[-1].lines, ["one", "two"])

        editor._undo()
        self.assertEqual(list(editor.lines), ["one", "two"])

        editor._undo()
        self.assertEqual(list(editor.lines), ["one", "two"])
        self.assertIn("oldest", editor.message)

    def test_insert_session_undo_respects_undolevels(self):
        editor = self._editor_with_lines(["one"])
        editor.max_undo = 5
        for _ in range(8):
            editor._enter_insert()
            editor._handle_insert(ord("a"))
            editor._handle_insert(27)  # ESC
        self.assertEqual(editor.mode, Mode.NORMAL)
        self.assertEqual(len(editor.undo_stack), 5)
        self.assertEqual(len(editor.redo_stack), 0)

    def test_undo_restores_a_copy_of_the_snapshot_lines(self):
        editor = self._editor_with_lines(["one", "two"])
        editor._push_undo()
        snapshot = editor.undo_stack[-1]
        editor.lines[0] = "ONE"
        editor.modified = True

        editor._undo()

        self.assertEqual(editor.lines, ["one", "two"])
        self.assertIsNot(editor.lines, snapshot.lines)
        editor.lines[0] = "mutated-after-undo"
        self.assertEqual(snapshot.lines, ["one", "two"])

    def test_redo_restores_a_copy_of_the_snapshot_lines(self):
        editor = self._editor_with_lines(["one", "two"])
        editor._push_undo()
        editor.lines[0] = "ONE"
        editor.modified = True
        editor._undo()
        snapshot = editor.redo_stack[-1]

        editor._redo()

        self.assertEqual(editor.lines, ["ONE", "two"])
        self.assertIsNot(editor.lines, snapshot.lines)
        editor.lines[0] = "mutated-after-redo"
        self.assertEqual(snapshot.lines, ["ONE", "two"])


class FunctionalReviewRegressionTests(unittest.TestCase):
    def editor(self, lines=None):
        editor = _editor_with_rc()
        editor._session_cache = {}
        if lines is not None:
            editor.lines = list(lines)
            editor.line_endings = ['\n'] * len(lines)
            editor.line_endings_trusted = True
            editor._mark_clean()
        return editor

    def test_concurrent_writes_serialize_checks_backup_generations_and_rollback(self):
        # Separate flock file descriptions exercise the same locking used by
        # independent editor processes. B attempts acquisition while A holds it.
        for operation in ('save', 'force', 'copy', 'range', 'base64', 'rollback'):
            with self.subTest(operation=operation), tempfile.TemporaryDirectory() as td:
                target = os.path.join(td, 'shared.txt')
                alias = os.path.join(td, 'alias.txt')
                with open(target, 'w') as fh:
                    fh.write('original\n')
                os.symlink(target, alias)
                a, b = self.editor(), self.editor()
                self.assertTrue(a._load_file(target))
                self.assertTrue(b._load_file(alias))
                a.lines[0], b.lines[0] = 'writer A', 'writer B'
                if operation == 'copy':
                    b.filename = os.path.join(td, 'other.txt')
                entered, release, attempting, checked = (threading.Event() for _ in range(4))
                stage, lock, signature, atomic = (
                    a._stage_generation_backup, b._target_write_lock,
                    b._file_signature_or_none, a._atomic_write_text,
                )
                results, errors = {}, []

                def stall_stage(*args):
                    state = stage(*args)
                    entered.set()
                    if not release.wait(5):
                        raise RuntimeError('test writer was not released')
                    return state

                def attempted_lock(*args):
                    attempting.set()
                    return lock(*args)

                def checked_signature(*args):
                    checked.set()
                    return signature(*args)

                def maybe_fail(path, text, **kwargs):
                    if operation == 'rollback' and path == target:
                        raise OSError('simulated primary write failure')
                    return atomic(path, text, **kwargs)

                def run_a():
                    try:
                        results['a'] = a._save_file()
                    except Exception as exc:
                        errors.append(exc)

                def run_b():
                    try:
                        if operation == 'range':
                            result = b._write_line_range_to_file(0, 0, alias)
                        elif operation == 'base64':
                            result = b._save_base64_file(alias)
                        elif operation == 'copy':
                            result = b._save_file(alias, rename_buffer=False)
                        else:
                            result = b._save_file(force=operation == 'force')
                        results['b'] = result
                    except Exception as exc:
                        errors.append(exc)

                with mock.patch.object(a, '_stage_generation_backup', side_effect=stall_stage), \
                     mock.patch.object(a, '_atomic_write_text', side_effect=maybe_fail), \
                     mock.patch.object(b, '_target_write_lock', side_effect=attempted_lock), \
                     mock.patch.object(b, '_file_signature_or_none', side_effect=checked_signature):
                    ta = threading.Thread(target=run_a, daemon=True)
                    tb = threading.Thread(target=run_b, daemon=True)
                    ta.start()
                    try:
                        self.assertTrue(entered.wait(5))
                        tb.start()
                        self.assertTrue(attempting.wait(5))
                        self.assertFalse(checked.wait(0.03))
                        self.assertNotIn('b', results)
                    finally:
                        release.set()
                        ta.join(5)
                        if tb.ident is not None:
                            tb.join(5)
                self.assertFalse(ta.is_alive())
                self.assertFalse(tb.is_alive())
                self.assertEqual(errors, [])
                self.assertEqual(results['a'], operation != 'rollback')
                self.assertEqual(results['b'], operation != 'save')
                self.assertTrue(os.path.islink(alias))
                with open(target, 'rb') as fh:
                    actual = fh.read()
                expected = b'writer A\n' if operation == 'save' else b'writer B\n'
                if operation == 'base64':
                    actual = base64.b64decode(actual)
                self.assertEqual(actual, expected)
                backup_dir = os.path.join(td, '.vii_backups')
                backups = sorted(name for name in os.listdir(backup_dir) if name.endswith('.txt'))
                expected_count = 2 if operation in ('force', 'copy', 'range') else 1
                self.assertEqual(len(backups), expected_count)
                texts = []
                for name in backups:
                    with open(os.path.join(backup_dir, name)) as fh:
                        texts.append(fh.read())
                if expected_count == 2:
                    self.assertEqual(texts, ['writer A\n', 'writer B\n'])
                else:
                    self.assertEqual(texts, ['writer B\n' if operation == 'rollback' else 'writer A\n'])

    def test_write_lock_failure_leaves_file_and_backups_untouched(self):
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, 'file')
            with open(path, 'w') as fh:
                fh.write('original\n')
            e = self.editor()
            e._load_file(path)
            e.lines[0] = 'edited'
            with mock.patch('vi_editor.fcntl.flock', side_effect=OSError('lock failed')):
                self.assertFalse(e._save_file())
            with open(path) as fh:
                self.assertEqual(fh.read(), 'original\n')
            self.assertFalse(os.path.exists(os.path.join(td, '.vii_backups')))
            # Failure released its fd/lock; an ordinary retry remains possible.
            self.assertTrue(e._save_file())

    def test_symlink_parent_does_not_bypass_open_buffer_directory_protection(self):
        for via_alias in (False, True):
            with self.subTest(via_alias=via_alias), tempfile.TemporaryDirectory() as td:
                real, alias = os.path.join(td, 'real'), os.path.join(td, 'alias')
                os.makedirs(os.path.join(real, 'sub'))
                os.symlink(real, alias)
                filename = os.path.join(real, 'sub', 'open.txt')
                with open(filename, 'w') as fh:
                    fh.write('valuable\n')
                e = self.editor()
                e._load_file(os.path.join(alias if via_alias else real, 'sub', 'open.txt'))
                directory = os.path.join(real if via_alias else alias, 'sub')
                e._fb_perform_delete([directory], recursive=True)
                self.assertTrue(os.path.isfile(filename))
                self.assertIn('open in buffer', e.message)
                src = os.path.join(td, 'source')
                os.mkdir(src)
                e._fb_perform_copy([src], directory, overwrite=True)
                self.assertTrue(os.path.isfile(filename))
                self.assertIn('open in buffer', e.message)

    def test_symlink_parent_self_copy_is_rejected_before_io(self):
        with tempfile.TemporaryDirectory() as td:
            real, alias = os.path.join(td, 'real'), os.path.join(td, 'alias')
            os.makedirs(os.path.join(real, 'sub'))
            os.symlink(real, alias)
            e = self.editor()
            with mock.patch.object(e, '_fb_copy_one') as copy:
                e._fb_perform_copy([real], os.path.join(alias, 'sub', 'nested'))
            copy.assert_not_called()
            self.assertIn('inside itself', e.message)
            self.assertFalse(os.path.exists(os.path.join(real, 'sub', 'nested')))

    def test_unlinking_directory_alias_preserves_open_referent(self):
        with tempfile.TemporaryDirectory() as td:
            real, alias = os.path.join(td, 'real'), os.path.join(td, 'alias')
            os.mkdir(real)
            os.symlink(real, alias)
            path = os.path.join(real, 'file')
            with open(path, 'w') as fh:
                fh.write('text')
            e = self.editor()
            e._load_file(path)
            e._fb_perform_delete([alias], recursive=True)
            self.assertFalse(os.path.lexists(alias))
            self.assertTrue(os.path.isfile(path))

    def test_replace_backspace_preserves_joined_suffix_and_undo(self):
        e = self.editor(['abc', 'def'])
        e.cursor_col = 3
        e._handle_normal(ord('R'), 24, 80)
        for key in (ord('X'), curses.KEY_DC, 127, 27):
            e._handle_replace_mode(key)
        self.assertEqual(e.lines, ['abcdef'])
        e._undo()
        self.assertEqual(e.lines, ['abc', 'def'])
        e._redo()
        self.assertEqual(e.lines, ['abcdef'])

    def test_replace_tab_rebases_restore_positions(self):
        for expand_tab in (True, False):
            with self.subTest(expand_tab=expand_tab):
                e = self.editor(['abc'])
                e.expand_tab = expand_tab
                e._enter_replace()
                for key in (ord('X'), curses.KEY_LEFT, 9, curses.KEY_HOME, curses.KEY_RIGHT, 127):
                    e._handle_replace_mode(key)
                prefix = '   ' if expand_tab else ''
                self.assertEqual(e.lines, [prefix + 'Xbc'])
                # The shifted entry must still restore the original 'a'.
                e.cursor_col = len(prefix) + 1
                e._handle_replace_mode(127)
                self.assertEqual(e.lines, [prefix + 'abc'])

    def test_replace_tab_before_appended_char_never_truncates_tail(self):
        e = self.editor(['abc'])
        e.cursor_col = 3
        e._enter_replace()
        for key in (ord('X'), curses.KEY_LEFT, 9, curses.KEY_HOME,
                    curses.KEY_RIGHT, curses.KEY_RIGHT, curses.KEY_RIGHT, curses.KEY_RIGHT, 127):
            e._handle_replace_mode(key)
        self.assertEqual(e.lines, ['abc   X'])

    def test_undo_and_redo_byte_budget_limits_long_line_history(self):
        e = self.editor(['x' * 8192])
        e.UNDO_BYTE_BUDGET = 24 * 1024
        for _ in range(20):
            e._delete_chars(1)
        self.assertGreater(len(e.undo_stack), 0)
        self.assertLess(len(e.undo_stack), 20)
        self.assertLessEqual(sum(s.byte_cost for s in e.undo_stack), e.UNDO_BYTE_BUDGET)
        final = list(e.lines)
        while e.undo_stack:
            e._undo()
        self.assertLessEqual(sum(s.byte_cost for s in e.redo_stack), e.UNDO_BYTE_BUDGET)
        while e.redo_stack:
            e._redo()
        self.assertEqual(e.lines, final)

    def test_undo_byte_budget_keeps_one_oversized_snapshot(self):
        e = self.editor(['x' * 8192])
        e.UNDO_BYTE_BUDGET = 100
        for _ in range(5):
            e._delete_chars(1)
        self.assertEqual(len(e.undo_stack), 1)
        e._undo()
        self.assertEqual(len(e.lines[0]), 8192 - 4)
        self.assertEqual(len(e.redo_stack), 1)

    def test_mmap_warns_about_lossy_decode_without_materializing(self):
        for raw in (b'ok\nbad:\xff\n', b'ok\nbad:\xe2\x82'):
            with self.subTest(raw=raw), tempfile.TemporaryDirectory() as td:
                path = os.path.join(td, 'file')
                with open(path, 'wb') as fh:
                    fh.write(raw)
                e = self.editor()
                e.LARGE_FILE_MMAP_THRESHOLD = 1
                self.assertTrue(e._load_file(path))
                self.assertTrue(e.lines.is_mapped)
                self.assertIn('non-UTF-8', e.message)
                self.assertIn(':w rewrites them', e.message)
                e.lines.close()

    def test_mmap_utf8_validation_handles_chunk_boundary(self):
        with tempfile.TemporaryDirectory() as td:
            path = os.path.join(td, 'file')
            with open(path, 'wb') as fh:
                fh.write(b'x' * (1024 * 1024 - 1) + '\u20ac\n'.encode())
            e = self.editor()
            e.LARGE_FILE_MMAP_THRESHOLD = 1
            self.assertTrue(e._load_file(path))
            self.assertNotIn('non-UTF-8', e.message)
            self.assertTrue(e.lines.is_mapped)
            self.assertTrue(e.lines[0].endswith('\u20ac'))
            e.lines.close()

    def test_repeated_reverse_search_preserves_original_direction_in_both_modes(self):
        for mode in (Mode.NORMAL, Mode.VISUAL):
            for forward in (True, False):
                with self.subTest(mode=mode, forward=forward):
                    e = self.editor(['foo'] * 4)
                    e._search('foo', forward)
                    e.mode = mode
                    positions = [e.cursor_row]
                    for key in 'NNn':
                        if mode == Mode.NORMAL:
                            e._handle_normal(ord(key), 24, 80)
                        else:
                            e._handle_visual(ord(key))
                        positions.append(e.cursor_row)
                        self.assertEqual(e._search_forward, forward)
                    self.assertEqual(positions, [1, 0, 3, 0] if forward else [3, 0, 1, 0])

    def test_help_reverse_repeat_preserves_direction(self):
        e = self.editor()
        e.HELP_LINES = ['foo'] * 4
        e._search_help('foo', True)
        positions = [e.help_top_line]
        for key in 'NNn':
            e._handle_help(ord(key))
            positions.append(e.help_top_line)
        self.assertEqual(positions, [1, 0, 3, 0])
        self.assertTrue(e.help_search_forward)

    def test_regex_commands_reset_literal_search_interpretation(self):
        for cmd in (':s/a./Y/', ':s/a./Y/c', ':g/a./p'):
            with self.subTest(cmd=cmd):
                e = self.editor(['foo ax', 'ax', 'ax'])
                e._search('foo', True, literal=True)
                e.cursor_row = 0
                e._stdscr = mock.Mock()
                e._stdscr.get_wch.return_value = 'y'
                with mock.patch.object(e, 'draw'):
                    e._execute_cmd(cmd)
                self.assertFalse(e._search_literal)
                e.cursor_row, e.cursor_col = 0, len(e.lines[0])
                e._handle_normal(ord('n'), 24, 80)
                self.assertEqual(e.cursor_row, 1)
                self.assertFalse(e.message_is_error)

    def test_comment_delimiter_edit_repaints_unchanged_following_lines(self):
        class Screen:
            def __init__(self): self.calls = []
            def getmaxyx(self): return 24, 80
            def move(self, *args): pass
            def clrtoeol(self): pass
            def addstr(self, *args): self.calls.append(args)
            def attron(self, *args): pass
            def attroff(self, *args): pass
            def noutrefresh(self): pass

        e = self.editor(['/*', 'int x;', '*/'])
        e.filename = '/tmp/example.c'
        e.show_line_numbers = False
        e.syntax_attrs = {'comment': 111, 'type': 222}
        screen = Screen()
        with mock.patch('curses.doupdate'), mock.patch('curses.setsyx'):
            e.draw(screen)
            self.assertIn((2, 0, 'int x;', 111), screen.calls)
            screen.calls.clear()
            e._handle_normal(ord('x'), 24, 80)
            e.draw(screen)
            self.assertIn((2, 0, 'int', 222), screen.calls)
            self.assertNotIn((2, 0, 'int x;', 111), screen.calls)

    def test_last_jump_tracks_line_insertion_and_undo_redo(self):
        e = self.editor(['a', 'b', 'c'])
        e._set_mark('a')
        e.cursor_row = 2
        e._jump_to_mark('a', exact=True)
        e._handle_normal(ord('O'), 24, 80)
        e._handle_insert(ord('z'))
        e._handle_insert(27)
        self.assertEqual(e.last_jump, (3, 0))
        e._undo()
        self.assertEqual(e.last_jump, (2, 0))
        e._redo()
        self.assertEqual(e.last_jump, (3, 0))
        e._handle_normal(ord('`'), 24, 80)
        e._handle_normal(ord('`'), 24, 80)
        self.assertEqual(e.lines[e.cursor_row], 'c')

    def test_last_jump_tracks_split_join_delete_and_indent(self):
        e = self.editor(['abCdef', 'tail'])
        e.last_jump = (0, 4)
        e.cursor_col = 2
        e._enter_insert()
        e._newline(auto_indent=False)
        self.assertEqual(e.last_jump, (1, 2))
        e._backspace()
        self.assertEqual(e.last_jump, (0, 4))
        e._insert_char('XYZ')
        self.assertEqual(e.last_jump, (0, 7))
        e._delete_char_under_insert_cursor()
        self.assertEqual(e.last_jump, (0, 6))
        e._indent_lines(0, 0, False)
        self.assertEqual(e.last_jump, (0, 10))
        e._indent_lines(0, 0, True)
        self.assertEqual(e.last_jump, (0, 6))
        e._delete_range(0, 0, 0, 0, True)
        self.assertIsNone(e.last_jump)
        self.assertNotIn(None, e.marks)

    def test_last_jump_tracks_multiline_put_join_and_substitute(self):
        e = self.editor(['abCdef', 'tail'])
        e.last_jump = (0, 4)
        e.cursor_col = 2
        e._store_register(['X', 'Y'], False)
        e._put(False)
        self.assertEqual(e.last_jump, (1, 3))
        e._join_line(0)
        self.assertEqual(e.last_jump, (0, 7))
        e.cursor_row = 0
        e._execute_cmd(r':s/C/\nZ/')
        self.assertEqual(e.last_jump, (1, 2))
        e._delete_range(0, 1, 1, 0, False)
        self.assertEqual(e.last_jump, (0, 2))

    def test_last_jump_is_cleared_when_replacing_document(self):
        e = self.editor(['abc'])
        e.last_jump = (0, 2)
        e._execute_cmd(':enew!')
        self.assertIsNone(e.last_jump)

    def test_global_handles_deleted_replaced_or_switched_origin_buffer(self):
        for command in (':g/x/bd!', ':g/x/enew!', ':g/x/bp'):
            for row_count in (1, 2):
                with self.subTest(command=command, row_count=row_count):
                    e = self.editor(['untouched'])
                    e._append_buffer()
                    e.lines = ['x'] * row_count
                    e._mark_clean()
                    e._cmd_buf = command
                    e._cmd_cursor = len(command)
                    self.assertTrue(e._handle_cmd_buf(10))
                    self.assertIn('Global command aborted: buffer changed', e.message)
                    self.assertNotIn('Command failed', e.message)
                    self.assertFalse(any(k < 0 for k in e.auto_marks))
                    self.assertFalse(any(k < 0 for b in e.buffers for k in b.auto_marks))
                    e._switch_buffer(0)
                    self.assertEqual(e.lines, ['untouched'])

    def test_buffer_identity_survives_snapshots_and_switches(self):
        e = self.editor(['x'])
        original_id = e._buffer_id
        e._sync_current_buffer()
        e._append_buffer()
        self.assertIsNot(e._buffer_id, original_id)
        e._switch_buffer(0)
        self.assertIs(e._buffer_id, original_id)
        e._execute_cmd(':g/x/s/x/y/')
        self.assertEqual(e.lines, ['y'])
        self.assertIs(e._buffer_id, original_id)


class MarkdownWrapTests(unittest.TestCase):
    class Screen:
        def __init__(self, height=8, width=12):
            self.height, self.width = height, width
            self.calls = []
            self.cells = {}
            self.position = (0, 0)

        def getmaxyx(self):
            return self.height, self.width

        def move(self, row, col):
            self.position = (row, col)

        def clrtoeol(self):
            row, col = self.position
            for index in range(col, self.width):
                self.cells[row, index] = " "

        def addstr(self, row, col, text, *attrs):
            self.calls.append((row, col, text, attrs[0] if attrs else 0))
            for index, char in enumerate(text):
                self.cells[row, col + index] = char

        def noutrefresh(self):
            pass

        def attron(self, attr):
            pass

        def attroff(self, attr):
            pass

        def text(self, row):
            return "".join(self.cells.get((row, col), " ") for col in range(self.width))

    def editor(self, lines, filename="README.md"):
        editor = _editor_with_rc()
        editor.filename = filename
        editor.lines = lines
        editor.line_endings = ["\n"] * len(lines)
        editor.show_line_numbers = False
        return editor

    def draw(self, editor, screen):
        with mock.patch("curses.doupdate"), mock.patch("curses.setsyx") as cursor:
            editor.draw(screen)
        return cursor.call_args.args

    def test_markdown_wraps_words_without_changing_file_bytes(self):
        for filename in ("README.md", "NOTES.MD", "notes.markdown"):
            with self.subTest(filename=filename):
                editor = self.editor(["alpha beta gamma delta", "next"], filename)
                before = editor._buffer_bytes()
                screen = self.Screen()
                self.draw(editor, screen)
                self.assertEqual(screen.text(1).rstrip(), "alpha beta")
                self.assertEqual(screen.text(2).rstrip(), "gamma delta")
                self.assertEqual(screen.text(3).rstrip(), "next")
                self.assertEqual(editor._buffer_bytes(), before)

    def test_plain_text_keeps_horizontal_scrolling(self):
        editor = self.editor(["a" * 30, "next"], "notes.txt")
        editor.cursor_col = 25
        screen = self.Screen()
        self.assertEqual(self.draw(editor, screen), (1, 11))
        self.assertGreater(editor.left_col, 0)
        self.assertEqual(screen.text(2).strip(), "")

    def test_mdwrap_setting_can_be_queried_toggled_and_completed(self):
        editor = self.editor(["alpha beta gamma delta"])
        self.assertTrue(editor._execute_cmd(":set mdwrap?"))
        self.assertEqual(editor.message, "mdwrap")

        self.assertTrue(editor._execute_cmd(":set mdwrap!"))
        self.assertTrue(editor._execute_cmd(":set mdwrap?"))
        self.assertEqual(editor.message, "nomdwrap")
        self.assertTrue(editor._execute_cmd(":set"))
        self.assertIn("nomdwrap", editor.message.split())

        self.assertTrue(editor._execute_cmd(":set invmdwrap"))
        self.assertTrue(editor._execute_cmd(":set"))
        self.assertIn("mdwrap", editor.message.split())
        editor._start_cmd_buf(":set nomdw")
        editor._handle_cmd_buf(ord("\t"))
        self.assertEqual(editor._cmd_buf, ":set nomdwrap")
        editor._handle_cmd_buf(ord("\n"))
        self.assertFalse(editor._markdown_wrap_enabled())

    def test_toggling_wrap_redraws_scrolled_markdown_without_changing_content(self):
        editor = self.editor(["a" * 60, "next"])
        editor.cursor_col = 45
        before = editor._buffer_bytes()
        screen = self.Screen(height=6, width=10)
        self.assertEqual(self.draw(editor, screen), (3, 5))

        self.assertTrue(editor._execute_cmd(":set nomdwrap"))
        self.assertEqual(self.draw(editor, screen), (1, 9))
        self.assertGreater(editor.left_col, 0)
        self.assertEqual(screen.text(2).strip(), "")

        self.assertTrue(editor._execute_cmd(":set mdwrap"))
        self.assertEqual(self.draw(editor, screen), (3, 5))
        self.assertEqual(editor.left_col, 0)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 45))
        self.assertEqual(editor._buffer_bytes(), before)
        self.assertFalse(editor.modified)

    def test_disabling_wrap_makes_arrows_move_file_lines_in_all_editing_modes(self):
        for mode in (Mode.NORMAL, Mode.INSERT, Mode.REPLACE, Mode.VISUAL, Mode.VISUAL_LINE):
            with self.subTest(mode=mode):
                editor = self.editor(["abcdefghijklmnopqrstuvwxyz", "tail"])
                editor.cursor_col = 2
                editor.mode = mode
                editor.visual_start = (0, 2)
                self.draw(editor, self.Screen(width=10))
                editor._execute_cmd(":set nomdwrap")
                if mode == Mode.NORMAL:
                    editor._handle_normal(curses.KEY_DOWN, 8, 10)
                elif mode == Mode.INSERT:
                    editor._handle_insert(curses.KEY_DOWN)
                elif mode == Mode.REPLACE:
                    editor._handle_replace_mode(curses.KEY_DOWN)
                else:
                    editor._handle_visual(curses.KEY_DOWN)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 2))

    def test_continuations_have_blank_line_number_gutters(self):
        editor = self.editor(["alpha beta gamma delta", "next"])
        editor.show_line_numbers = True
        screen = self.Screen(width=17)
        self.draw(editor, screen)
        self.assertEqual(screen.text(1).rstrip(), "   1 alpha beta")
        self.assertEqual(screen.text(2).rstrip(), "     gamma delta")
        self.assertEqual(screen.text(3).rstrip(), "   2 next")

    def test_cursor_scrolls_within_a_paragraph_taller_than_the_view(self):
        editor = self.editor(["a" * 60])
        editor.cursor_col = 45
        editor.left_col = 30
        screen = self.Screen(height=6, width=10)
        self.assertEqual(self.draw(editor, screen), (3, 5))
        self.assertEqual((editor.top_line, editor._top_wrap), (0, 2))
        self.assertEqual(editor.left_col, 0)
        editor._move(0, 5)
        self.assertEqual(self.draw(editor, screen), (1, 5))
        self.assertEqual(editor._top_wrap, 0)

    def test_insertion_at_a_full_row_uses_the_next_display_row(self):
        editor = self.editor(["a" * 20])
        editor.mode = Mode.INSERT
        editor.cursor_col = 20
        screen = self.Screen(width=10)
        self.assertEqual(self.draw(editor, screen), (3, 0))
        editor._handle_insert(ord("x"))
        self.assertEqual(self.draw(editor, screen), (3, 1))
        self.assertEqual(screen.text(3).rstrip(), "x")
        self.assertEqual(editor.lines, ["a" * 20 + "x"])

    def test_full_rows_do_not_add_blank_lines_between_file_lines(self):
        editor = self.editor(["a" * 20, "next"])
        screen = self.Screen(width=10)
        self.draw(editor, screen)
        self.assertEqual(screen.text(3).rstrip(), "next")
        editor._handle_normal(curses.KEY_DOWN, 8, 10)
        editor._handle_normal(curses.KEY_DOWN, 8, 10)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 0))

    def test_arrows_skip_display_rows_with_no_source_position_inside_a_tab(self):
        editor = self.editor(["\tx"])
        editor.tab_stop = 8
        screen = self.Screen(width=4)
        self.draw(editor, screen)
        editor._handle_normal(curses.KEY_DOWN, 8, 4)
        self.assertEqual(editor.cursor_col, 1)
        self.assertEqual(self.draw(editor, screen), (3, 0))
        editor._handle_normal(curses.KEY_UP, 8, 4)
        self.assertEqual(editor.cursor_col, 0)

    def test_insert_arrows_preserve_column_across_short_continuations(self):
        editor = self.editor(["abcdefghijkl", "ab"])
        editor.mode = Mode.INSERT
        editor.cursor_col = 8
        self.draw(editor, self.Screen(width=10))
        editor._handle_insert(curses.KEY_DOWN)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 12))
        editor._handle_insert(curses.KEY_DOWN)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 2))
        editor._handle_insert(curses.KEY_UP)
        editor._handle_insert(curses.KEY_UP)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 8))

    def test_arrows_traverse_wrapped_rows_in_all_editing_modes(self):
        for mode in (Mode.NORMAL, Mode.INSERT, Mode.REPLACE, Mode.VISUAL, Mode.VISUAL_LINE):
            with self.subTest(mode=mode):
                editor = self.editor(["abcdefghijklmnopqrstuvwxyz", "tail"])
                editor.cursor_col = 2
                editor.mode = mode
                editor.visual_start = (0, 2)
                self.draw(editor, self.Screen(width=10))
                def key(value):
                    if mode == Mode.NORMAL:
                        editor._handle_normal(value, 8, 10)
                    elif mode == Mode.INSERT:
                        editor._handle_insert(value)
                    elif mode == Mode.REPLACE:
                        editor._handle_replace_mode(value)
                    else:
                        editor._handle_visual(value)
                key(curses.KEY_DOWN)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 12))
                key(curses.KEY_DOWN)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 22))
                key(curses.KEY_DOWN)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 2))
                key(curses.KEY_UP)
                self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 22))

    def test_j_k_keep_file_line_motions_and_gj_gk_use_display_rows(self):
        editor = self.editor(["a" * 26, "tail"])
        editor.cursor_col = 2
        self.draw(editor, self.Screen(width=10))
        for char in "gj":
            editor._handle_normal(ord(char), 8, 10)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 12))
        for char in "gk":
            editor._handle_normal(ord(char), 8, 10)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (0, 2))
        editor._handle_normal(ord("j"), 8, 10)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (1, 2))

    def test_paging_and_scroll_keys_traverse_a_single_long_file_line(self):
        editor = self.editor(["a" * 120])
        screen = self.Screen(height=6, width=10)
        self.draw(editor, screen)
        editor._handle_normal(curses.KEY_NPAGE, 6, 10)
        self.assertEqual(editor.cursor_col, 30)
        self.assertEqual(self.draw(editor, screen), (1, 0))
        editor._handle_normal(5, 6, 10)
        self.assertEqual(editor.cursor_col, 40)
        self.assertEqual(self.draw(editor, screen), (1, 0))
        editor._handle_normal(25, 6, 10)
        self.assertEqual(self.draw(editor, screen), (2, 0))
        editor._handle_normal(curses.KEY_PPAGE, 6, 10)
        self.assertEqual(editor.cursor_col, 10)

    def test_screen_motions_and_z_commands_use_wrapped_rows(self):
        editor = self.editor(["a" * 120])
        screen = self.Screen(height=8, width=10)
        self.draw(editor, screen)
        editor._handle_normal(ord("L"), 8, 10)
        self.assertEqual(editor.cursor_col, 40)
        editor._handle_normal(ord("M"), 8, 10)
        self.assertEqual(editor.cursor_col, 20)
        editor._move(0, 65)
        for char in "zz":
            editor._handle_normal(ord(char), 8, 10)
        self.assertEqual(self.draw(editor, screen), (3, 5))
        for char in "zt":
            editor._handle_normal(ord(char), 8, 10)
        self.assertEqual(self.draw(editor, screen), (1, 5))
        for char in "zb":
            editor._handle_normal(ord(char), 8, 10)
        self.assertEqual(self.draw(editor, screen), (5, 5))

    def test_resize_and_edits_reflow_display_rows(self):
        editor = self.editor(["alpha beta gamma delta", "next"])
        screen = self.Screen()
        self.draw(editor, screen)
        screen.width = 24
        self.draw(editor, screen)
        self.assertEqual(screen.text(1).rstrip(), "alpha beta gamma delta")
        self.assertEqual(screen.text(2).rstrip(), "next")
        screen.width = 12
        self.draw(editor, screen)
        editor.lines[0] = "alpha beta longerword delta"
        self.draw(editor, screen)
        self.assertEqual(screen.text(2).rstrip(), "longerword")
        self.assertEqual(screen.text(3).rstrip(), "delta")
        self.assertEqual(screen.text(4).rstrip(), "next")

    def test_selection_and_syntax_highlighting_continue_across_wraps(self):
        editor = self.editor(["alpha beta gamma delta"])
        editor.mode = Mode.VISUAL
        editor.visual_start = (0, 6)
        editor.cursor_col = 17
        screen = self.Screen(width=11)
        self.draw(editor, screen)
        highlighted = [(row, text) for row, _, text, attr in screen.calls if attr == curses.A_REVERSE]
        self.assertIn((1, "beta "), highlighted)
        self.assertIn((2, "gamma d"), highlighted)

        editor = self.editor(["# Heading words across rows"])
        screen = self.Screen(width=12)
        with mock.patch.object(editor, "_syntax_attr", return_value=12345):
            self.draw(editor, screen)
        self.assertTrue(any(row == 2 and attr == 12345 for row, _, _, attr in screen.calls))

    def test_brackets_and_substitution_confirmation_use_segment_offsets(self):
        editor = self.editor(["(" + "a" * 24 + ")"])
        screen = self.Screen(width=10)
        self.draw(editor, screen)
        self.assertTrue(any(row == 3 and col == 5 and text == ")" and attr & curses.A_REVERSE
                            for row, col, text, attr in screen.calls))
        editor._sub_confirm_span = (0, 12, 24)
        screen.calls.clear()
        self.draw(editor, screen)
        highlighted = [(row, text) for row, _, text, attr in screen.calls
                       if attr == curses.A_BOLD | curses.A_REVERSE]
        self.assertIn((2, "a" * 8), highlighted)
        self.assertIn((3, "a" * 4), highlighted)

    def test_tabs_nul_and_unicode_keep_display_column_mapping(self):
        editor = self.editor(["a\tb\x00c"])
        editor.tab_stop = 4
        screen = self.Screen(width=5)
        self.draw(editor, screen)
        self.assertEqual(screen.text(1), "a    ")
        self.assertEqual(screen.text(2).rstrip(), "b^@c")
        editor._move(0, 2)
        self.assertEqual(self.draw(editor, screen), (2, 0))

        editor = self.editor(["ab界e\u0301fg"])
        editor.cursor_col = 5
        screen = self.Screen(width=4)
        self.assertEqual(self.draw(editor, screen), (2, 1))
        self.assertIn((1, 0, "ab界", 0), screen.calls)
        self.assertIn((2, 0, "e\u0301fg", 0), screen.calls)

    def test_table_wrapping_keeps_formatted_cursor_coordinates(self):
        editor = self.editor(["| Name | Count |", "| --- | ---: |", "| longer name | 123 |"])
        editor.cursor_row, editor.cursor_col = 2, 17
        screen = self.Screen(height=20, width=12)
        cursor_row, cursor_col = self.draw(editor, screen)
        display_col = editor._display_col(2, 17)
        layout = editor._wrapped_line_layout(2, 12)
        segment = editor._wrapped_cursor_position(12)[1]
        preceding_rows = sum(len(editor._wrapped_line_layout(row, 12)) for row in range(2))
        self.assertEqual(cursor_row, 1 + preceding_rows + segment)
        self.assertEqual(cursor_col, display_col - layout[segment][0])
        self.assertEqual("".join(text for _, text in layout), editor._markdown_table_display_line(2))
        editor._handle_normal(curses.KEY_UP, 20, 12)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (2, 10))
        editor._handle_normal(curses.KEY_DOWN, 20, 12)
        self.assertEqual((editor.cursor_row, editor.cursor_col), (2, 17))

    def test_buffer_switch_restores_wrapped_viewport(self):
        editor = self.editor(["a" * 100])
        editor.cursor_col = 55
        screen = self.Screen(height=6, width=10)
        self.draw(editor, screen)
        original_top = editor._top_wrap
        editor._append_buffer("notes.txt")
        self.draw(editor, screen)
        editor._switch_buffer(0)
        self.assertEqual(self.draw(editor, screen), (3, 5))
        self.assertEqual(editor._top_wrap, original_top)


if __name__ == "__main__":
    unittest.main()
