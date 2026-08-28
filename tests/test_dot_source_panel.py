"""The DOT source panel must render a program the frontend still accepts.

Under strict declarations a panel that omits the declaration prologue is not a
VIMP program at all: it references names the parser will reject as undeclared
and it hides their kinds. And once names resolve to scoped identities, a panel
that prints the identity rather than the source name is equally wrong -- the
separator is not in the lexer's identifier class, so `f#acc := ...` does not
parse either.

Feeding the panel back through the CLI catches both at once, which no
`.vimp` fixture can: the assertion is about output being valid input, and the
corpus format compares output against text rather than re-running on it.
"""

from __future__ import annotations

import html
import re
import subprocess
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
VOBLINT = ROOT / "cli" / "voblint"

# One fixture per shape the panel has to get right: procedure-scoped locals at
# two different kinds, a declared local in main, and a declared global written
# across calls.
CASES = [
    "24-scoped-names/precision/03-same_local_name_two_kinds.vimp",
    "24-scoped-names/precision/01-same_formal_name_two_kinds.vimp",
    "22-integer-kinds/precision/12-uint8_local_in_main.vimp",
    "04-globals/known-imprecision/01-repeated_call_site_widening.vimp",
]

PANEL = re.compile(r'source \[shape=plain,label=<(.*?)>\];', re.S)


def _panel_text(dot: str) -> str:
    match = PANEL.search(dot)
    assert match, "the DOT output carries no source panel"
    body = re.sub(r'<BR ALIGN="LEFT"/>', "\n", match.group(1))
    body = re.sub(r"<[^>]+>", "", body)
    return html.unescape(body).replace("\xa0", " ").strip() + "\n"


@pytest.mark.parametrize("case", CASES)
def test_source_panel_reparses(case, tmp_path):
    src = ROOT / "tests" / "regression" / case
    dot = subprocess.run(
        [str(VOBLINT), "--analysis", "interval", "--dot", str(src)],
        capture_output=True, text=True, check=True,
    ).stdout
    panel = tmp_path / "panel.vimp"
    panel.write_text(_panel_text(dot))
    back = subprocess.run(
        [str(VOBLINT), "--analysis", "interval", str(panel)],
        capture_output=True, text=True,
    )
    assert back.returncode == 0, (
        f"the panel rendered for {case} is not a program the frontend accepts:\n"
        f"{back.stderr}\n--- panel ---\n{panel.read_text()}"
    )


@pytest.mark.parametrize("case", CASES)
def test_source_panel_shows_source_names(case, tmp_path):
    src = ROOT / "tests" / "regression" / case
    dot = subprocess.run(
        [str(VOBLINT), "--analysis", "interval", "--dot", str(src)],
        capture_output=True, text=True, check=True,
    ).stdout
    text = _panel_text(dot)
    assert "#" not in text, (
        f"the panel for {case} prints a resolved identity rather than the name "
        f"the source wrote:\n{text}"
    )
