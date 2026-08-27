"""Property 1: AST -> print -> parse round-trips to a structurally equal AST.

This is the primary correctness property. Hypothesis generates arbitrary exp
trees (see strategies.py) -- grammar/vimp.yaml's exp_paren production and
VIMP_Source_Print.thy's precedence-climbing printer make every shape
source-expressible -- so every generated example is expected to print to
text that Vimp_parser reads back into the same tree; a mismatch here is a
real printer or parser bug. test_nonexpressible_regression.py pins a few
concrete shapes that specifically exercise printer-inserted parentheses.

`programs` generates no declarations itself: pretty_string_of_program emits
none either, so ast_driver derives them -- one fixed kind throughout, a local
per variable a body touches, a return kind for a value-returning procedure --
and builds both the AST and the printed source from that one derivation. Which
kind a name carries is thus held constant here; that a declaration survives
printing at all is what the structural comparison below still checks, since
the parser has to reconstruct exactly the `declared_kinds`/`declared_locals`
the original was built with.

As a secondary, more readable invariant: printing the re-parsed AST again
must reproduce the same source text as the first print. Structural equality
of the ASTs already implies this (pretty_string_of_program is a pure
function of the AST), but a source-text diff is a far more useful failure
message than "the trees differ" when something regresses.
"""

from hypothesis import given, settings

from oracle import dump_reprinted, dump_source, run_ast_driver
from strategies import programs


@given(programs())
@settings(max_examples=200, deadline=None)
def test_ast_print_parse_roundtrip(prog):
    result = run_ast_driver(prog)
    assert result.stdout.strip() == "OK", (
        f"round-trip mismatch for program {prog!r}:\n{result.stdout}"
    )


@given(programs())
@settings(max_examples=100, deadline=None)
def test_reprint_matches_first_print(prog):
    result = run_ast_driver(prog)
    assert result.stdout.strip() == "OK", f"round-trip mismatch for {prog!r}:\n{result.stdout}"
    # Already implied by the round-trip above (pretty_string_of_program is a
    # pure function, so structurally equal ASTs print identically), but
    # checking it directly gives a source-text diff on failure instead of
    # "the trees differ".
    first = dump_source(prog)
    second = dump_reprinted(prog)
    assert first == second, (
        f"printer is not stable across a print/parse cycle for {prog!r}:\n"
        f"--- first print ---\n{first}\n--- reprint ---\n{second}"
    )
