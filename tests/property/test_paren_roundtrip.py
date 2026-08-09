"""Positive counterpart to test_nonexpressible_regression.py: that suite
pins Times(Plus a b, c)-shaped trees as needing parentheses to round-trip
at all (VIMP_Source_Print.thy's string_of_aexp still can't print them --
that's the point of test_nonexpressible_regression.py, pinned against
ast_driver's own printer). Against the shipped grammar directly
(grammar/vimp.yaml's aexp_paren production), the same class of tree does
round-trip when printed with actual parentheses: arbitrary aexp shapes, not
just left-associated ones, since the printer here (paren_strategies.py)
inserts parentheses wherever the precedence table says a subtree needs
them, and the shipped parser reconstructs the exact same tree.
"""

import subprocess
from pathlib import Path

from hypothesis import given, settings

from paren_strategies import arbitrary_aexp, print_aexp
from strategies import sexp

PROPERTY_DIR = Path(__file__).resolve().parent
DRIVER = PROPERTY_DIR / "paren_roundtrip"
TIMEOUT = 5.0


@given(arbitrary_aexp())
@settings(max_examples=300, deadline=None)
def test_arbitrary_aexp_roundtrips_via_parens(aexp):
    printed = print_aexp(aexp)
    src = f"void main() {{ x := {printed} }}"
    result = subprocess.run(
        [str(DRIVER)], input=src, capture_output=True, text=True, timeout=TIMEOUT
    )
    expected = sexp(aexp)
    assert result.stdout.strip() == expected, (
        f"aexp {aexp!r} printed as {printed!r} did not round-trip:\n{result.stdout}"
    )


def test_shape_pinned_non_expressible_by_the_printer_still_parses_with_parens():
    # The exact shape test_nonexpressible_regression.py pins as needing
    # parens: Times(Plus(a,b), c). The printer can't produce those parens
    # (VIMP_Source_Print.thy has no aexp-paren case); the shipped grammar
    # accepts them when they're supplied directly, as here.
    aexp = ("Times", ("Plus", ("V", "a"), ("V", "b")), ("V", "c"))
    printed = print_aexp(aexp)
    assert printed == "(a+b)*c"
    src = f"void main() {{ x := {printed} }}"
    result = subprocess.run(
        [str(DRIVER)], input=src, capture_output=True, text=True, timeout=TIMEOUT
    )
    assert result.stdout.strip() == sexp(aexp), result.stdout
