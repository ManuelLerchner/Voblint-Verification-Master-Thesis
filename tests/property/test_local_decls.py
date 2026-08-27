"""Property 3: procedure-local declarations parse, and only where the grammar
puts them.

A local declaration is `<kind> name1, name2, ...;`, and all of a procedure's
declarations form a prologue between the body's `{` and its first statement
(grammar/vimp.yaml's function_decl: `locals_star` then `stmts_opt`). The
positive property below generates that prologue for every procedure of a
Hypothesis-generated program -- main included -- and asserts the frontend
accepts the result.

Parse acceptance is the whole property, not a weaker stand-in for the
round-trip one: VIMP_Source_Print.thy's pretty_string_of_program prints no
declaration at all, so declaration-carrying source has no printer output to
compare against. Printing a program whose `declared_locals` is non-empty
yields text that re-parses with `declared_locals = []`, which is why
strategies.programs stays declaration-free and the prologue is spliced into
its printed source here instead.

The three negative cases are the shapes `programs_with_locals` refuses to
build, and all three are rejections. The placement one closes structurally:
locals_star closes as soon as stmts_opt starts. The two shadowing ones are
name-collision rules vimp_parser.mly's program action checks explicitly,
mirroring VIMP_Notation.thy's prog_tr -- a local may repeat neither a
declared global nor one of its own procedure's formals.
"""

from hypothesis import given, settings

from oracle import dump_source, run_parse_only
from strategies import programs_with_locals, source_with_locals


@given(programs_with_locals())
@settings(max_examples=150, deadline=None)
def test_locals_prologue_parses(prog_and_locals):
    prog, prologues = prog_and_locals
    src = source_with_locals(dump_source(prog), prologues)

    result = run_parse_only(src)

    assert result.returncode == 0, (
        f"frontend rejected a well-formed locals prologue (exit {result.returncode}):\n"
        f"{src}\nstderr:\n{result.stderr}"
    )


DECL_AFTER_STATEMENT = """\
void main() {
    int32 a;
    a := 1;
    int32 b;
    b := 2
}
"""

LOCAL_SHADOWS_GLOBAL = """\
global uint8 counter;
void main() {
    int32 counter;
    counter := 1
}
"""

LOCAL_SHADOWS_FORMAL = """\
void f(n) {
    int32 n;
    return n
}
void main() {
    skip
}
"""


def test_declaration_after_statement_is_rejected():
    result = run_parse_only(DECL_AFTER_STATEMENT)
    assert result.returncode == 2, (
        "a declaration after the first statement is outside the prologue and must be "
        f"a parse error, but --parse-only exited {result.returncode}:\n{result.stdout}"
    )


def test_local_shadowing_global_is_rejected():
    result = run_parse_only(LOCAL_SHADOWS_GLOBAL)
    assert result.returncode == 2, (
        "a local colliding with a declared global must be rejected, but --parse-only "
        f"exited {result.returncode}:\n{result.stdout}"
    )


def test_local_shadowing_formal_is_rejected():
    result = run_parse_only(LOCAL_SHADOWS_FORMAL)
    assert result.returncode == 2, (
        "a local colliding with one of its procedure's formals must be rejected, but "
        f"--parse-only exited {result.returncode}:\n{result.stdout}"
    )
