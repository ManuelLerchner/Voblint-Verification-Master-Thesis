"""The source grammar's statement boundaries and braced conditional chains."""

import pytest
from oracle import dump_source, run_ast_driver, run_parse_only
from strategies import main_program


@pytest.mark.parametrize(
    "source",
    [
        "fun main() {}",
        "fun f() { return; } fun main() { f(); }",
        "fun i32 f(i32 x) { return x; } fun main() { i32 x = f(1); }",
        "fun main() { i32 x = 1; if (x) { x = 2; } x = 3; }",
        "fun main() { if (0) {} else if (1) {} else {} }",
        "fun main() { if (0) {} else if (1) {} }",
        "fun main() { while (0) {} if (1) { __voblint_check(1); } }",
    ],
)
def test_c_style_statements_parse(source):
    result = run_parse_only(source)
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize(
    "source",
    [
        "fun main() { i32 x; x = 1 }",
        "fun main() { i32 x = 1; if (x) { x = 2; }; }",
        "fun main() { i32 x; if (1) x = 1; }",
        "fun main() { i32 x; if (1) {} else x = 1; }",
        "fun main() { i32 x; if ((x = 1)) {} }",
        "fun main() { i32 x; x := 1; }",
        "void main() { skip; }",
    ],
)
def test_invalid_statement_shapes_are_rejected(source):
    result = run_parse_only(source)
    assert result.returncode == 2
    assert "parse error" in result.stderr


COMPARISONS = ("<", "<=", ">", ">=", "==", "!=")


@pytest.mark.parametrize("operator", COMPARISONS)
def test_comparisons_parse_with_arithmetic_and_logic(operator):
    result = run_parse_only(
        f"fun main() {{ i32 x, y; __voblint_check(x + 1 {operator} y * 2 && x != y); }}"
    )
    assert result.returncode == 0, result.stderr


@pytest.mark.parametrize("first", COMPARISONS)
@pytest.mark.parametrize("second", COMPARISONS)
def test_comparison_precedence_groups(first, second):
    result = run_parse_only(
        f"fun main() {{ i32 x, y, z; __voblint_check(x {first} y {second} z); }}"
    )
    same_group = (first in ("==", "!=")) == (second in ("==", "!="))
    if same_group:
        assert result.returncode == 2
        assert "parse error" in result.stderr
    else:
        assert result.returncode == 0, result.stderr

    parenthesized = run_parse_only(
        f"fun main() {{ i32 x, y, z; __voblint_check((x {first} y) {second} z); }}"
    )
    assert parenthesized.returncode == 0, parenthesized.stderr


@pytest.mark.parametrize(
    "expr, source",
    [
        (("Eq", ("V", "x"), ("Less", ("V", "y"), ("V", "z"))), "x == y < z"),
        (("NotEq", ("GreaterEq", ("V", "x"), ("V", "y")), ("V", "z")), "x >= y != z"),
        (("Less", ("Eq", ("V", "x"), ("V", "y")), ("V", "z")), "(x == y) < z"),
        (("Greater", ("V", "x"), ("NotEq", ("V", "y"), ("V", "z"))), "x > (y != z)"),
    ],
)
def test_mixed_comparison_grouping_roundtrips(expr, source):
    program = main_program(["x", "y", "z", "result"], ("Assign", "result", expr))
    assert f"result = {source};" in dump_source(program)
    result = run_ast_driver(program)
    assert result.stdout.strip() == "OK", result.stdout


@pytest.mark.parametrize(
    "expr, source",
    [
        (("Div", ("Times", ("V", "x"), ("V", "y")), ("V", "z")), "x * y / z"),
        (("Mod", ("Div", ("V", "x"), ("V", "y")), ("V", "z")), "x / y % z"),
        (("Div", ("V", "x"), ("Times", ("V", "y"), ("V", "z"))), "x / (y * z)"),
        (("Mod", ("V", "x"), ("Div", ("V", "y"), ("V", "z"))), "x % (y / z)"),
    ],
)
def test_multiplicative_grouping_roundtrips(expr, source):
    program = main_program(["x", "y", "z", "result"], ("Assign", "result", expr))
    assert f"result = {source};" in dump_source(program)
    result = run_ast_driver(program)
    assert result.stdout.strip() == "OK", result.stdout


@pytest.mark.parametrize(
    "source, message",
    [
        ("fun main() { x = 10; }", "1:14: parse error: 'x' is not declared"),
        ("fun main() { i32 y = x + 1; }", "1:22: parse error: 'x' is not declared"),
        ("fun main() { y = f(); }", "1:14: parse error: 'y' is not declared"),
        (
            "fun main() { x = 1; i32 x; }",
            "1:14: parse error: 'x' is used before its declaration",
        ),
        (
            "fun main() { while (1) { x = 1; } i32 x; }",
            "1:26: parse error: 'x' is used before its declaration",
        ),
        (
            "fun main() { { i32 x = 1; } x = 2; }",
            "1:29: parse error: 'x' is used outside the scope of its declaration",
        ),
        ("global g; fun main() {}", "1:8: parse error: global 'g' needs a kind"),
        ("fun f(n) {} fun main() {}", "1:7: parse error: formal 'n' needs a kind"),
        (
            "fun f(i32 n) { return n; } fun main() {}",
            "1:1: parse error: 'f' returns a value but declares no return kind",
        ),
        # Checks that need the whole procedure or program still point at the
        # offending token, not at the end of the file.
        (
            "fun main() {\n  i64 x = 99999999999999999999;\n}\n",
            "2:11: parse error: literal 99999999999999999999 does not fit i64",
        ),
        (
            "fun main() { i64 y = -9223372036854775809; }",
            "1:22: parse error: literal -9223372036854775809 does not fit i64",
        ),
        (
            "global i32 g; fun f(i32 a, i32 g) {} fun main() {}",
            "1:32: parse error: formal 'g' of 'f' shadows a global",
        ),
        (
            "fun f(i32 a, i8 a) {} fun main() {}",
            "1:17: parse error: duplicate formal 'a' of 'f'",
        ),
        ("fun main(i32 x) {}", "1:1: parse error: 'main' must have no formals"),
        ("fun u8 main() {}", "1:1: parse error: 'main' cannot declare a return kind"),
        (
            "fun i32 f(i32 n) { return n; } fun main() { i32 x = f(x); }",
            "parse error: the initializer of 'x' reads 'x' itself",
        ),
    ],
)
def test_undeclared_and_out_of_scope_names_are_rejected(source, message):
    result = run_parse_only(source)
    assert result.returncode == 2
    assert message in result.stderr, result.stderr


@pytest.mark.parametrize(
    "source",
    [
        # An inner block may shadow an outer declaration, a formal or a global.
        "fun main() { i32 x = 1; { u8 x = 2; __voblint_check(x == 2); }"
        " __voblint_check(x == 1); }",
        "global i32 g; fun f(i32 n) { { i32 n = 2; g = n; } }"
        " fun main() { i32 g = 1; f(g); }",
        # Arguments of other kinds convert to the formal's kind.
        "fun u16 f(u8 a, i64 b) { return a + b; } fun main() { i32 x = f(300, -1); }",
        # A recursive procedure and its locals.
        "fun u8 f(u8 n) { if (n > 0) { u8 r = f(n - 1); return r + 1; } return 0; }"
        " fun main() { u16 a = f(5); }",
    ],
)
def test_declared_programs_parse(source):
    result = run_parse_only(source)
    assert result.returncode == 0, result.stderr
