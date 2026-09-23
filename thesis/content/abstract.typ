= Abstract <abstract>

Abstract interpretation is a static program analysis technique that
over-approximates every execution of a program. One way to implement it is to
reduce the program to a system of equations over abstract values and hand it
to a generic fixpoint solver. Goblint, a static analyzer for C, works this way.
The soundness of such an analyzer depends on every step of this pipeline: the
equations must describe the program, the solver must solve them, and the
reported verdicts must follow from the solution. A verified solver covers only
the middle step.

This thesis asks whether the soundness of a constraint-based,
context-sensitive interprocedural analyzer can be machine-checked across the
whole pipeline, from source executions to the verdicts of the exported
executable. It also asks what a calling context means concretely, whether
domain, context policy and solver can discharge their obligations
independently, and whether the necessity of obligations and the precision of
results can be proved as theorems. We answer these questions with Voblint, an
Isabelle/HOL formalization of such an analyzer for a small imperative language
with recursive procedures.

The thesis makes four contributions. First, an end-to-end soundness theorem
for the analysis function behind the command-line and browser analyzers,
covering every offered domain, update rule and context policy.
Second, an activation-local trace semantics with a relational, trace-derived
semantics of calling contexts, and a totality condition under which the
context-indexed collection loses no executions. Third, a compositional proof.
Domains, context policies and an existing verified top-down solver discharge
separate obligations, the solver only through its post-solution certificate,
and one theorem composes them for every configuration. A relational instance
meets the same contract. Fourth, machine-checked counterexamples showing that
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
analysis. Parsing, code generation, target-language compilation and
presentation lie outside the proof. The adequacy of the source semantics is
argued through its recorded departures from C11 and reproducible regression
programs.
