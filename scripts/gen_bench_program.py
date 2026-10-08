#!/usr/bin/env python3
"""Write a scalable VIMP program for timing the generated analyzer.

`chain N`: N assignments x_i = x_{i-1} + 1 in main, then one check.
`procs N`: N assignments split into procedures of 8 statements, each called
once from main. The thesis's before/after measurement of the
init_publications code equation (Section 12.2) uses both shapes.
"""

import sys


def chain(n: int) -> str:
    body = ["  x0 = 0;"] + [f"  x{i} = x{i - 1} + 1;" for i in range(1, n + 1)]
    body.append(f"  __voblint_check(x{n} == {n});")
    return "fun main() {\n" + "\n".join(body) + "\n}"


def procs(n: int, size: int = 8) -> str:
    count = max(1, n // size)
    out = []
    for p in range(count):
        steps = "\n".join(f"  y{i} = y{i - 1} + 1;" for i in range(1, size))
        out.append(f"fun f{p}(a) {{\n  y0 = a;\n{steps}\n  return y{size - 1};\n}}")
    calls = "\n".join(f"  x{p + 1} = f{p}(x{p});" for p in range(count))
    out.append(
        f"fun main() {{\n  x0 = 0;\n{calls}\n  __voblint_check(x{count} >= 0);\n}}"
    )
    return "\n".join(out)


if __name__ == "__main__":
    shapes = {"chain": chain, "procs": procs}
    if len(sys.argv) != 3 or sys.argv[1] not in shapes:
        sys.exit("usage: gen_bench_program.py chain|procs N")
    print(shapes[sys.argv[1]](int(sys.argv[2])))
