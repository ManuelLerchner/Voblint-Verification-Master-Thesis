"""Property 1: AST -> print -> parse round-trips to a structurally equal AST.

This is the primary correctness property. Hypothesis generates arbitrary exp
trees (see strategies.py) -- grammar/vimp.yaml's exp_paren production and
VIMP_Source_Print.thy's precedence-climbing printer make every shape
source-expressible -- so every generated example is expected to print to
text that Vimp_parser reads back into the same tree; a mismatch here is a
real printer or parser bug. test_nonexpressible_regression.py pins a few
concrete shapes that specifically exercise printer-inserted parentheses.

`programs` is the declaration-free fragment of VIMP on purpose. A program
carrying procedure-local declarations (or a typed global) is outside this
property, not accidentally omitted from it: pretty_string_of_program prints
neither, so such a program's printed source re-parses into an AST with an
empty `declared_locals`/`declared_kinds` and cannot be structurally equal to
the original. Declaration-carrying source is covered by parse acceptance
instead, in test_local_decls.py.

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
