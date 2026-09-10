"""Focused tests for the source-only unfinished-proof gate."""

import importlib.util
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
CHECKER = ROOT / "scripts" / "check_no_sorry.py"


def load_checker():
    spec = importlib.util.spec_from_file_location("check_no_sorry", CHECKER)
    module = importlib.util.module_from_spec(spec)
    sys.path.insert(0, str(CHECKER.parent))
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


checker = load_checker()


def test_scan_reports_commands_with_exact_lines(tmp_path):
    theory = tmp_path / "Broken.thy"
    theory.write_text(
        "theory Broken\nbegin\nlemma one: True sorry\nlemma two: True\n  oops\nend\n"
    )

    assert [(hole.line, hole.command) for hole in checker.scan(theory)] == [
        (3, "sorry"),
        (5, "oops"),
    ]


def test_scan_ignores_prose_comments_strings_and_longer_names(tmp_path):
    theory = tmp_path / "Clean.thy"
    theory.write_text(
        "theory Clean\nbegin\n"
        "text \\<open>There is no sorry here.\\<close>\n"
        "(* oops *)\n"
        "definition sorry_message :: string where \\\"sorry_message = STR ''oops''\\\"\n"
        "lemma ok: True by simp\nend\n"
    )

    assert checker.scan(theory) == []


def test_theory_paths_ignore_editor_backups(tmp_path):
    source = tmp_path / "src"
    source.mkdir()
    (source / "Live.thy").write_text("lemma ok: True by simp\n")
    (source / "Backup.thy~").write_text("lemma bad: True sorry\n")

    assert checker.theory_paths((source,)) == [source / "Live.thy"]
