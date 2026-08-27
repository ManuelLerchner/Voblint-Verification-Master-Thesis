"""Property 2: the parser is robust against mutated (usually invalid) source.

Not a semantic-correctness property like the round-trip test -- a mutated
program has no expected AST at all, since it may not even be syntactically
valid VIMP. The only thing asserted is robustness:

  - terminates within a bounded timeout (see oracle.TIMEOUT / Hung)
  - no crash (no signal-terminated process)
  - no uncaught exception escaping to the OCaml runtime's default handler

A clean parse (exit 0) and a clean, structured parse-rejection (exit 2,
"file:line:col: parse error: ...") are both acceptable outcomes.

Mutations start from real, valid VIMP source (dumped by ast_driver
--print-source from a Hypothesis-generated program -- see strategies.py),
not from arbitrary bytes: garbage from the very first byte would exercise
the lexer's first-token path over and over and rarely reach deeper parser
states (statement sequencing, block nesting, procedure declarations).
Perturbing valid programs reaches those states while still covering the
lexer/parser boundary through the punctuation/whitespace/identifier/digit
mutation characters below.

The base source is fully declared -- kinds on globals and formals, a return
kind where a procedure returns a value, a local declaration prologue -- so the
mutations also land inside and around declaration lines: a kind keyword, a
declaration's comma list, and the prologue/first-statement boundary the
parser's locals_star/stmts_opt split hinges on.
"""

from hypothesis import given, settings
from hypothesis import strategies as st

from oracle import dump_source, run_parse_only
from strategies import programs_with_locals, source_with_locals

MUTATION_CHARS = list(" \t\n(){};,:=+-*<!&|_0123456789abcXYZ@#%\"'")


def mutation_ops():
    index = st.integers(min_value=0, max_value=10_000)
    char = st.sampled_from(MUTATION_CHARS)
    return st.one_of(
        st.tuples(st.just("delete"), index),
        st.tuples(st.just("insert"), index, char),
        st.tuples(st.just("replace"), index, char),
    )


def apply_mutation(src: str, op: tuple) -> str:
    kind = op[0]
    idx = op[1] % max(1, len(src))
    if kind == "delete":
        return src[:idx] + src[idx + 1 :]
    if kind == "insert":
        return src[:idx] + op[2] + src[idx:]
    if kind == "replace":
        return (src[:idx] + op[2] + src[idx + 1 :]) if src else op[2]
    raise AssertionError(kind)


@given(programs_with_locals(), st.lists(mutation_ops(), min_size=1, max_size=5))
@settings(max_examples=150, deadline=None)
def test_parse_only_never_crashes_on_mutated_source(prog_and_locals, ops):
    prog, prologues = prog_and_locals
    src = source_with_locals(dump_source(prog), prologues)
    for op in ops:
        src = apply_mutation(src, op)

    result = run_parse_only(src)

    assert result.returncode in (0, 2), (
        f"unexpected exit code {result.returncode} (expected 0 or 2) on mutated source:\n"
        f"{src!r}\nstderr:\n{result.stderr}"
    )
    assert "Fatal error" not in result.stderr, (
        f"uncaught exception on mutated source:\n{src!r}\nstderr:\n{result.stderr}"
    )
