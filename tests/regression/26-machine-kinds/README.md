# Machine kinds

Programs that declare machine kinds in C style: on a `global` line
(`global u8 g;`), on a formal (`fun f(u8 n)`), as a return kind
(`fun u16 f(...)`), or as a local declared anywhere in a body (`u8 x;`). A
program that writes any kind must write one on every global and
formal, and must declare every local. A declared local starts at an arbitrary
value of its kind unless it has an initializer (`i8 x = 2;`), which assigns the
value converted to the local's kind, as any assignment does; a global starts at
zero. `11` checks initializers, `12` their left-to-right order, `13` and `14`
declarations after statements and inside loops, `15` to `18` C block scoping
and its rejections, and `19` the three overflow hazards' wording. A call
converts each argument to its formal's kind; `04` and `20` check that, `20`
also through a global and a recursive call. A local without an initializer is
fresh on every activation: `21` calls the same procedure twice, `22` recurses
with locals of three kinds, and `23` checks that an initializer replaces the
arbitrary value each time. `24` checks the conversion of a library `min` or
`max` result: an error, a warning or silence by whether the result itself fits
the destination's kind.

Isabelle elaborates the parsed program (`elab_ptable`, an Isabelle definition):
every operation computes at its C kind, every conversion becomes an explicit
`TCast`, and the analyzer runs on the elaborated core program. The concrete
semantics wraps a signed overflow (the `-fwrapv` reading), so check verdicts are
about wrapping arithmetic; the signed-overflow diagnostics of `27-signed-overflow`
name the operations that may overflow in C.

A program that writes no kind gives every variable the default kind i32;
`08` checks that.

Run with `pixi run python3 tests/run.py 26-machine-kinds`.
