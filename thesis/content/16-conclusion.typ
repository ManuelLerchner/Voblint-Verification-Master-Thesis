#import "../lib/code.typ": isaconst, isalocale, isathm, isatype, oblig
#import "../lib/figures.typ": verdict

= Conclusion <ch:conclusion>

The thesis shows that the soundness of a Goblint-style analyzer with contexts,
side effects and a verified solver can be machine-checked from source
executions to the verdicts of the exported function. The result holds for a
scalar language with recursive procedures and is a partial-correctness result,
so it covers every answer the analyzer returns. The proof follows one chain.
Graph runs simulate source executions, and valid activation traces represent
graph runs. Each activation carries the contexts its policy admits, and the
activation collecting semantics groups the traces by these contexts, so one
trace may lie in the sets of several contexts. Context-indexed equations with routed calls
cover this semantics at every context, provided the analysis and the context
policy meet their separate obligations. The solver enters only through a
post-solution certificate, and the source-level theorem reads the verdicts off
its result.

The central contribution is this composition. A context-free activation
semantics, relational context routing, analysis-local soundness obligations and
a verified side-effecting solver together yield one guarantee from source
executions to verdicts. The proved function is the analyzer that the
command-line tool and the browser playground run (@ch:executable).

== Discussion <sec:discussion>

The design states its choices as obligations, and each choice buys generality
at a known price. Contexts admitted by a relation let entry-state routing read
contexts off the analysis's result. The price is totality (#oblig("TOTAL")),
which functional policies meet directly (#isaconst("context_policy_of_fun")).
Analysis globals in the analysis contract let the flow-insensitive placement
give each program global its own unknown. The price is a frame obligation and
lost precision on the `set`/`get` program (@sec:mixed-flow). Consuming the solver only through its
post-solution certificate makes soundness independent of the update rule
(@sec:update-rules). In exchange, nothing is said about termination or about
which post-solution the solver returns (@sec:certificate). Exporting one
dispatcher makes the constant of the theorem the one the tools run
(@sec:codegen).

How far the results carry beyond VIMP depends on the layer. Goblint analyzes C
after CIL normalization, with pointers, a heap, threads, machine integers and
further update rules. The certificate is stated over right-hand sides and
unknowns and mentions no VIMP construct. The coverage contract has one
obligation per rule of #isaconst("valid_activation_trace"). It refers to VIMP
only through the graph, its stores and three step functions,
#isaconst("edge_step"), #isaconst("call_enter") and #isaconst("combine_collect")
(@sec:contract). We therefore expect three parts to carry over to a language
whose activations do not interfere: the shape of the coverage contract, the
theorem that the contexts exhaust the node collecting semantics, and the
composition of @sec:eq-discharge. The step functions and every proof that
unfolds them would have to be redone.

Machine integers fit this case. They change the step functions, the generic
derivation in #isalocale("sound_nonrelational_ops") and each domain's
soundness proofs for its primitives. Routing and the solver certificate do not
mention arithmetic. For signed overflow, a domain could keep its ideal-integer
bounds and report an overflow when they exceed the type, as Goblint does
@saan26phd[§3.3.2]. Unsigned wrap-around would need domain variants, since
classical numeric domains describe ideal integers @mine13. A C-like treatment of division
by zero changes more. The semantics would need an error outcome, and the
verdicts of @sec:verdict-meaning a meaning for it.

Pointers into the stack break the assumption that activations do not
interfere. A return keeps the caller's locals (@sec:calls), and this fails once
a callee can write them through a pointer. #cite(<sotin11>, form: "prose")
introduce their local semantics for this case. A heap adds a store component
that caller and callee share, so #oblig("RETURN"), the entry pairs and the one
value per variable in the domains (@sec:vimp) would all change. Threads
interleave activations, which #isaconst("valid_activation_trace") cannot
express. The local traces of Schwarz et al. @schwarz21 give threads a
semantics, but that semantics has no procedures @schwarz25phd[§8, p. 277],
and the interface would also need synchronization, which it lacks. A new update rule
that meets the vendored interface requires comparatively little change, since
only
#isathm("update_rule_update_global_of") splits on the rule. A C front end such
as CIL would join the parser in the trust boundary unless it is verified.

== Limitations <sec:limitations>

The first limits concern what the theorem covers. It is a partial-correctness
result and covers every answer the analyzer returns. Termination is proved
neither for the solve nor for the reduction of Int, and regression programs
exist whose solves do not finish (@sec:termination, @sec:reduced-product). The
theorem concerns VIMP, a scalar language without pointers, heap or memory
model. VIMP has unbounded integers, defined division by zero and
zero-initialized callee locals, so a verdict about a VIMP program does not
transfer to a C program with the same text (@sec:vimp-vs-c). That
#isaconst("pstep") models the intended language is argued, not proved. The
simulation from source runs to graph runs and the representation of graph runs
by valid traces are proved in the forward direction only (@sec:csim,
@sec:valid). Within the analyzer, only the combined state as a whole publishes
to analysis globals. #isaconst("rel_order_spec") is therefore selectable only in
its local form, and one update rule serves every global unknown of a run
(@sec:mixed-flow, @sec:relational, @sec:update-rules).

The delivered tools rest on the trusted components of @sec:trust-boundary, and
every theorem proved by evaluation trusts the code generator. No test runs VIMP
programs concretely, since the development has no executable form of
#isaconst("pstep"). No time or memory measurement is reported. The executable
keeps proof-oriented data representations, and no data refinement to efficient
sets and maps has been carried out (@sec:generated-code). A refinement of the solver's state would require
the proof of the vendored solver to be redone. The rest of the chain uses the
solver only through its certificate (@sec:certificate) and would be
unaffected.

No general precision,
optimality or completeness theorem is proved. Completeness would mean that
every check that holds in all executions is reported as proved. Each precision
example concerns one program with fixed analysis settings (@sec:eval-precision).
The regression corpus is small and was written or adapted for this work, and
its expected verdicts were set by hand, not checked against an independent
analyzer (@sec:eval-corpus). The Goblint defect of @sec:eval-1161 was not re-run.
The correspondence with Goblint is architectural. No theorem transfers to its
OCaml implementation, and no agreement rate between the two analyzers is
measured (@sec:rel-goblint). The comparison with prior work rests on a targeted
search rather than a systematic review (@ch:related).

== Outlook <sec:outlook>

=== Extending Voblint <sec:outlook-extending>

A richer source language, up to a subset of C, needs the new obligations that
@sec:discussion names for machine integers, pointers, a heap and threads. It
also needs a semantics and a preservation argument per construct at every
layer.

Such a language would benefit from an elaboration phase between the parser and
the compiler. Already for VIMP, the source-level theorem only asserts that
_some_ node $v$ is related to the reached source configuration
(@sec:headline). A residual command records nothing about the occurrence it
came from (@sec:csim). An elaboration phase would annotate every statement with
the node the compiler emits for it. Each source configuration would then name
its node, and the theorem could drop the existential. The same phase is where a front end for C resolves names, types
expressions and makes conversions explicit.

The adequacy of #isaconst("pstep") is argued and checked against example
programs (@sec:vimp-vs-c). A fuel-bounded evaluator whose runs are proved to be
#isaconst("pstep") runs would make this check systematic. A run that violates a check
reported as #verdict("PROVED") would then point to a fault in the trusted base. Comparing the evaluator's runs with a C
compiler on the common subset would test the adequacy argument itself.

Richer analyses need their own soundness proofs. A relational domain with
stronger transfer functions than the order analysis could also answer the
numeric analyses at branches (@sec:relational). Further query kinds would each
need a truth relation, and analyses with their own globals would need the
combination to keep these globals apart, as Goblint's MCP does
(@sec:coop-catalogue).

Every shipped analysis answers a single entry pair per call, although the
interface admits several (@sec:calls). Path-sensitive analyses that split a
call into cases therefore remain future work. The contexts of an activation
depend only on how the activation was entered. Digests refine unknowns by
other abstractions of a local trace (@sec:rel-goblint). Generalizing
#isaconst("activation_context_rel") to such abstractions of activation traces
would allow path- or history-sensitive unknowns, each with its own
admissibility conditions.

Voblint adapts its equations to the interface of the vendored solver
(@sec:eq-encoding). Goblint's solvers publish to local unknowns and join the
writes of one evaluation per target. A version of the vendored solver that does
the same would let callers publish into callee entries directly and make
activation seeds and buffering unnecessary. Its partial-correctness proof would
have to be redone for local side effects.

A termination theorem would guarantee an answer for every program. The
total-correctness result of Tilscher et al. covers the top-down solver without
side effects. It assumes finitely many unknowns, a precise widening, and
monotonic right-hand sides with monotonic dependencies
@tilscher26jar[Cor. 1]. Their widening stabilizes every widening sequence by
definition @tilscher26jar[Def. 2]. The vendored class #isalocale("warrowing")
states no stabilization law (@sec:widening), so even finitely many unknowns may
take values that increase forever (@sec:termination).

=== Agent-assisted development <sec:outlook-agents>

Each new analysis only has to meet its own obligations, which mention neither
the other analyses nor contexts, the solver or the equations
(@sec:coop-catalogue). This suits development with
AI agents (see #link(<ai-use>)[the statement on the use of generative AI]).
Formal verification and agents complement each other here. An agent may
propose definitions and proofs, but Isabelle checks every proof, and the batch
build and the drift checks of @ch:tooling reject anything that does not check.
Counterexample theorems for weakened obligations (@sec:eval-1161,
@sec:discussion) act as negative tests. Human review can therefore concentrate
on what no proof settles: whether the base definitions and the obligations state
the intended meaning (@sec:vimp-vs-c), and whether the trusted base of
@sec:trust-boundary is acceptable.

The same division applies beyond single analyses. Extending the framework with
a construct from C, or with a Goblint feature such as path-sensitive entry
alternatives or further query kinds, changes definitions at several layers.
Isabelle then reports every proof the change breaks, at whichever layer it
sits, so an agent can work through the failures one by one while a reviewer
checks the new definitions, above all the extended source semantics. Goblint
supplies both the design to follow and test material: its regression programs
can be adapted as fixtures, as part of the corpus already is (@sec:eval-corpus),
and its documented defects can be replayed as counterexample theorems
(@sec:eval-1161). We expect this to make larger extensions practical.

=== Voblint and Goblint <sec:outlook-goblint>

Within the architectural correspondence of @sec:rel-goblint, Voblint can serve
as an executable specification of the architecture with proved soundness
obligations. In one direction, a Goblint feature gives the design that a
Voblint extension follows, as the query mechanism did for @ch:cooperation. A
documented Goblint defect can be replayed as a regression fixture and as a
counterexample theorem, as the congruence remainder was (@sec:eval-1161). The
same obligations could be consulted before a change to Goblint lands. A
proposed domain operation with a counterpart in Voblint would be transliterated
by hand and checked against the obligation that its counterpart meets, as
#isathm("congruence_mod_sound") states it for the remainder. Operations on
pointers or threads have no such counterpart.

In the other direction, a verified component exported as OCaml could replace
its unverified counterpart in Goblint. That needs more than the export. It
needs the data refinement of @sec:limitations, a correspondence between the
component's interface and Goblint's, and soundness for C's integers, since the
component's proofs assume VIMP's unbounded ones (@sec:vimp-vs-c).

Voblint verifies neither Goblint nor an analyzer for C. It establishes a
smaller result. For a Goblint-style architecture with recursive procedures,
routed contexts, cooperating analyses and a generic side-effecting solver, one
machine-checked chain connects source executions to the verdicts of executable
code. Its remaining gaps, a richer language, termination, efficient representations
and the handwritten code around the analyzer, are places where the same proof
structure can be extended.
