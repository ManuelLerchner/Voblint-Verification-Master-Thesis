"""The thesis's repository figures: one measurement, and no hand-typed copies."""

import importlib.util
from pathlib import Path

import pytest

REPO = Path(__file__).resolve().parent.parent


@pytest.fixture
def tool(monkeypatch):
    monkeypatch.syspath_prepend(str(REPO / "scripts"))
    spec = importlib.util.spec_from_file_location(
        "thesis_stats", REPO / "thesis/tools/stats.py"
    )
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture
def scan(tool, tmp_path, monkeypatch):
    monkeypatch.setattr(tool, "REPO", tmp_path)
    monkeypatch.setattr(tool, "ALLOW", {("ch.typ", "1161"): "pull request number"})

    def run(text):
        (tmp_path / "ch.typ").write_text(text)
        return tool.hand_typed(tmp_path)

    return run


def test_flatten_addresses_nested_ints_only(tool):
    stats = {"a": {"b": 3, "c": {"d": 4}}, "e": [1, 2], "f": "x", "g": 5}
    assert dict(tool.pages_stats.flatten(stats)) == {"a.b": 3, "a.c.d": 4, "g": 5}


def test_hand_typed_statistic_is_reported(scan):
    problems, _ = scan("The corpus holds 289 VIMP fixtures in 25 groups.\n")
    assert [p.split(": ")[1].split()[0] for p in problems] == ["289", "25"]


def test_noun_on_the_next_line_counts(scan):
    problems, _ = scan("counted 62,098 physical\nlines in the theories.\n")
    assert len(problems) == 1 and "62,098" in problems[0]


def test_derived_figures_code_and_math_pass(scan):
    problems, _ = scan(
        'The corpus holds #stat("corpus.cases") fixtures in #stat-sum("a", "b") groups.\n'
        "The fixture `42-down_call_string_100` and $x in [-10, 10]$ in two lines.\n"
        "```c\nx = 100; // lines\n```\n"
        "A single digit, 5 cases, is a parameter.\n"
    )
    assert problems == []


def test_numbers_without_a_statistic_noun_pass(scan):
    problems, _ = scan("With call strings of length 100 the check is proved.\n")
    assert problems == []


def test_allowlist_is_used_and_reported(scan):
    problems, used = scan("Pull request 1161 restricted the cases.\n")
    assert problems == [] and used == {("ch.typ", "1161")}


def test_breakdowns_add_up(tool):
    stats = tool.measure()
    directories = sum(
        v for k, v in stats.items() if k.startswith("isabelle.directories.")
    )
    groups = sum(v for k, v in stats.items() if k.startswith("corpus.by_group."))
    kinds = sum(v for k, v in stats.items() if k.startswith("corpus.kinds."))
    assert directories == stats["isabelle.lines"]
    assert groups == kinds == stats["corpus.cases"]
