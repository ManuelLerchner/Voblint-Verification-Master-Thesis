# Arithmetic diagnostics

These fixtures check arithmetic table findings while VIMP keeps its total arithmetic semantics.
Each file opts in with `// EXPECT-ARITHMETIC`. Inline annotations identify the
expected findings at that source line:

```text
// ARITH: ERROR division-by-zero
// ARITH: WARN remainder-by-zero
// ARITH: ERROR division-by-zero; ERROR division-by-zero
// ARITH: NONE
```

`ERROR` requires a definite zero divisor; `WARN` requires a possible zero divisor.
Semicolons preserve multiple occurrences on one line. `NONE` adds no expected
findings and documents a safe or unreachable operation. The runner compares the
complete file's diagnostics, including severity, source line, operation, and count.
Any missing or unexpected finding fails, including one on an unannotated line.
Locations identify the containing statement's start. Put an annotation on that
first line when an assignment, call, condition, or return spans several lines.

Verdict annotations can coexist on the same line:

```text
__voblint_check(0 && 1 / 0); // REFUTED // ARITH: ERROR division-by-zero
```

Both Boolean operands are inspected. These findings describe arithmetic hazards;
they do not change the resulting value or make execution fault.

Run with `pixi run python3 tests/run.py 23-arithmetic-diagnostics`.
Existing fixtures without the
directive continue to check their verdicts alone.

The dead-branch fixture checks silence after branch refinement. The entry-state
fixtures cover mixed safe/unsafe calls (one warning), all unsafe calls (one
error), and all safe calls (no diagnostic).
