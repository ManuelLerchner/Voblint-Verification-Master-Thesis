"""The fixture header reader shared by tests/run.py, the HTML-report audit and
the playground's example corpus."""

import sys
from pathlib import Path

import pytest

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "scripts"))

import pages_examples  # noqa: E402
import vimp_fixture  # noqa: E402


def test_settings_read_every_analysis_flag():
    args = (
        "--analysis int,interval --context call-string --context-depth 2 --globals join"
    )
    assert vimp_fixture.analysis_settings(args.split()) == {
        "analyses": ["int", "interval"],
        "context": "call-string",
        "context_depth": 2,
        "globals": "join",
    }


def test_output_and_runner_flags_select_nothing():
    args = "--analysis sign --dot --timeout 5".split()
    assert vimp_fixture.analysis_settings(args) == {"analyses": ["sign"]}


@pytest.mark.parametrize("args", [["--frobnicate"], ["--context"]])
def test_unknown_or_valueless_flags_are_errors(args):
    with pytest.raises(ValueError):
        vimp_fixture.analysis_settings(args)


def test_header_is_line_one_only(tmp_path):
    fixture = tmp_path / "01-case.vimp"
    fixture.write_text("fun main() {}\n// PARAM: --analysis sign\n")
    assert vimp_fixture.param_args(fixture) is None


def test_every_fixture_becomes_an_example_with_its_settings():
    corpus = pages_examples.corpus()
    fixtures = [f for group in corpus["groups"] for f in group["fixtures"]]
    assert len(fixtures) == len(list(pages_examples.CORPUS.rglob("*.vimp")))
    for fixture in fixtures:
        assert fixture["settings"]["analysis"] == fixture["analyses"][0]
        assert not fixture["source"].startswith("// PARAM:")
        assert vimp_fixture.GRAPH_BEGIN not in fixture["source"]
