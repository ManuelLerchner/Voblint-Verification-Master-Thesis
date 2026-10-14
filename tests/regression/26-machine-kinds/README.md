# Machine kinds

Programs that declare machine kinds in C style: on a `global` line
(`global u8 g;`), on a formal (`fun f(u8 n)`), as a return kind
(`fun u16 f(...)`), or as a local declared before a body's first statement
(`u8 x;`). A program that writes any kind must write one on every global and
formal, and must declare every local. A declared local starts at an arbitrary
value of its kind unless it has an initializer (`i8 x = 2;`), which assigns the
value converted to the local's kind, as any assignment does; a global starts at
zero. `11` checks initializers. A call converts each argument to its formal's
kind; `04` and `12` check that, `12` also through a global and a recursive
call.

The frontend elaborates a typed program with the verified `typed_prog`: every
operation computes at its C kind, every conversion becomes an explicit `Cast`,
and the analyzer then runs on that lowered program. Signed overflow wraps (the
`-fwrapv` reading), so these verdicts are about wrapping arithmetic, not about
C programs whose signed arithmetic overflows.

A program that writes no kind gives every variable the default kind i32;
`08` checks that.

Run with `pixi run python3 tests/run.py 26-machine-kinds`.
