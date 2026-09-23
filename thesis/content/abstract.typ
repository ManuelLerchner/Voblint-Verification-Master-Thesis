= Abstract <abstract>

Abstract interpretation is a static program analysis technique that
over-approximates every execution of a program. One way to implement it is to
reduce the program to a system of equations over abstract values and hand it
to a generic fixpoint solver. Goblint, a static analyzer for C, works this way.
The soundness of such an analyzer depends on every step of this pipeline: the
equations must describe the program, the solver must solve them, and the
reported verdicts must follow from the solution. For Goblint's top-down
solver, only the middle step had been verified @stade24 @tilscher26. To use it for program
analysis, one had to supply the equations and trust, without proof, that they
describe the program.

We show that the whole pipeline can be verified. We build Voblint, an
Isabelle/HOL formalization of a constraint-based, context-sensitive
interprocedural analyzer for a small imperative language with recursive
procedures, and prove it sound from source executions to the verdicts of its
analysis function. The analyzer generated from that function runs on the
command line and in the browser.

The thesis makes four contributions. First, an end-to-end soundness theorem
for the exported analysis function, covering every offered domain, update rule and context policy.
Second, an activation-local trace semantics with a relational, trace-derived
semantics of calling contexts, and a totality condition under which the
context-indexed collection loses no executions. Third, a compositional proof.
Domains, context policies and an existing verified top-down solver discharge
separate obligations, the solver only through its post-solution certificate,
and one theorem composes them for every configuration. Fourth, machine-checked counterexamples showing that
weakened obligations allow unsound claims, together with non-vacuity and
precision witnesses proved by evaluation for named programs.

The main theorem states that if the solver terminates and the analysis returns
a result, that result covers every store a finite source execution reaches,
and each definite verdict holds there. Further theorems justify `DEAD` and the
absence of zero divisors where no arithmetic diagnostic is reported. A
definite verdict holds whenever a run reaches its check, but it does not
assert that any run does. Executable instances cover Sign,
Interval, Parity, Congruence and their reduced product, with four update rules
and bounded call strings or entry-state contexts.

The guarantee is partial correctness: solver termination is a per-program
premise. The development does not establish completeness, a
general precision ordering, or correctness of Goblint's implementation or of C
analysis. Parsing, code generation, compilation and presentation lie outside the
proof, and the source semantics is checked against C11 and regression
programs, not proved adequate.
