= Abstract <abstract>

Analyzers in the style of Goblint reduce a program to an equation system and
hand it to a generic solver. When a verified solver terminates, it guarantees a
solution of the equations it receives. It does not establish that those
equations describe the source program, or that the reported verdicts follow
from the solution. This thesis asks whether the soundness of a
constraint-based, context-sensitive interprocedural analyzer of this kind can
be machine-checked from source executions to the verdicts of the exported
executable, what concrete meaning a calling context has, whether domain,
context policy and solver can discharge their obligations independently, and
whether the necessity of obligations and the precision of results can be
proved as theorems. It answers them with Voblint, an Isabelle/HOL
formalization of such an analyzer for a small imperative language with
recursive procedures.

The thesis makes four contributions. First, an end-to-end soundness theorem
for the public analysis function exported to the command-line and browser
analyzers, covering every offered domain, update rule and context policy.
Second, an activation-local trace semantics with a relational, trace-derived
semantics of calling contexts, and a totality condition under which the
context-indexed collection loses no executions. Third, a compositional proof:
domains, context policies and the vendored verified top-down solver discharge
separate obligations, the solver only through its post-solution certificate,
and one theorem composes them for every configuration; a relational instance
meets the same contract. Fourth, machine-checked counterexamples showing that
weakened obligations allow unsound claims, together with non-vacuity and
precision witnesses proved by evaluation for named programs.

The main theorem states: if the solver terminates and the analysis returns a
result, that result covers every store a finite source execution reaches, and
each definite verdict holds there. Further theorems justify `DEAD` and the
absence of zero divisors where no arithmetic diagnostic is reported. A
definite verdict holds whenever a run reaches its check, but it does not
assert that any run does. Sign, Interval, Parity, Congruence and their reduced product
are executable instances, combinable with four update rules for shared
unknowns and with bounded call strings or entry-state contexts.

The guarantee is partial correctness: solver termination is a per-program
premise. The development does not establish completeness, a general precision
ordering, or correctness of Goblint's implementation or of C analysis.
Parsing, code generation, target-language compilation and presentation lie
outside the proof, and the adequacy of the source semantics is argued through
its recorded departures from C11 and reproducible regression programs.
