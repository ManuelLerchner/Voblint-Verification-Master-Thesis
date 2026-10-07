#import "../lib/code.typ": isaconst, isalocale, isathm, isatype, oblig
#import "../lib/theme.typ": vb

#let _todo(body) = text(fill: vb.unproved)[TODO: #body]

= Conclusion <ch:conclusion>

The thesis shows that the soundness of a Goblint-style analyzer with contexts,
side effects and a verified solver can be machine-checked from source
executions to the verdicts of the exported function, for a scalar language
with recursive procedures, as partial correctness: for every answer the
analyzer returns. The
proof follows one chain. Graph runs simulate source executions, and valid
activation traces represent graph runs, sorted by the context read
off each activation into the activation collecting semantics. Context-indexed
equations with routed calls cover it at every context, provided the analysis and the context policy meet their
separate obligations. The solver enters only through a post-solution
certificate, and the source-level theorem reads the verdicts off its result. A
non-relational domain supplies only primitives proved sound, from which
a generic builder in the style of Nipkow and Klein derives its analysis.
Analyses that answer one another's queries combine under the same theorem, each
proving one obligation that names no partner.
The evidence for this, its strength and its gaps are assessed in
@ch:evaluation. This chapter discusses the design, collects the limitations in
one place, and outlines future work.

== Discussion <sec:discussion>

Several design choices trade one cost for another. A context policy that returns a set of contexts lets entry-state routing read
contexts off the analysis's result, at the price of the obligation
#oblig("TOTAL"). Functional policies return singletons and satisfy it directly
(#isaconst("context_policy_of_fun")). Stating the analysis contract over an
environment of analysis globals lets the flow-insensitive placement give each
program global its own unknown, at the price of a frame obligation on the
carrier and of precision on the `set`/`get` program (@sec:mixed-flow). The cost
of neither placement was measured. Consuming
the solver only through #isaconst("part_post_solution", thy: "Basics_side") makes soundness
independent of the update rule (@sec:update-rules), but says nothing about
termination or about which post-solution is returned (@sec:certificate). Exporting one dispatcher makes
the constant of the theorem the one the tools run (@sec:codegen).

How far the results carry beyond VIMP depends on the layer. Goblint analyzes C after CIL normalization, with pointers,
a heap, threads, machine integers and further update rules. The certificate is
stated over right-hand sides and unknowns and mentions no VIMP construct. The
coverage contract has one obligation per rule of #isaconst("valid_activation_trace") and
refers to VIMP only through the graph, its stores and three step functions,
#isaconst("edge_step"), #isaconst("call_enter") and #isaconst("combine_collect")
(@sec:contract). We therefore expect the coverage contract's shape,
the theorem that the contexts exhaust the node collecting semantics and the
composition of @sec:eq-discharge to carry over to a
language whose activations do not interfere, with the step
functions and every proof that unfolds them redone. Machine integers fit this
case: they change the step functions, the generic derivation in
#isalocale("sound_nonrelational_ops") and each domain's soundness proofs for
its primitives, while routing and the solver certificate do not mention
arithmetic. The numeric domains
themselves would need wrap-around-aware variants, since classical numeric
domains describe ideal integers @mine13. A possible overflow could then be
reported like the arithmetic diagnostics of @sec:verdicts. A C-like treatment of
division by zero changes more, because the semantics would need an error
outcome and the verdicts of @sec:verdicts a meaning for it.

Pointers into the stack break the non-interference assumption. A return keeps
the caller's locals (@sec:calls), which fails once a callee can write them
through a pointer. #cite(<sotin11>, form: "prose") introduce their local
semantics for this case. A heap adds a store
component that caller and callee share, so #oblig("RETURN"), the entry pairs
and one value per variable in the domains (@sec:vimp) would all change. Threads
interleave activations, which #isaconst("valid_activation_trace") cannot express. The local
traces of Schwarz et al. @schwarz21 handle them, but the interface
would also need synchronization, which it lacks. A new update
rule that meets the vendored interface needs the least work, since only
#isathm("update_rule_update_global_of") splits on the rule. A C front end such as CIL would join the parser in the trust
boundary unless verified.

For other verified analyzers, the development suggests an order of work. State
soundness against a context-free trace semantics and read contexts off traces,
so that policies are proved against one fixed semantics. Consume the solver
through a certificate that also bounds published contributions and closes the
reached set (@sec:certificate). Export the constant the theorem is about.
Counterexample theorems for weakened obligations are easy to state, and two
of them determined the shape of the call interface (@sec:revealed).

== Limitations <sec:limitations>

The first limits concern what the theorem covers. It is a partial-correctness
result: it covers every answer the analyzer returns, and termination is proved
neither for the solve nor for the reduction of Int, so regression
programs exist whose solves do not finish (@sec:termination,
@sec:reduced-product). It concerns VIMP, a scalar language without pointers,
heap or memory model, with unbounded integers, defined division by zero and
zero-initialized callee locals, so a verdict about a VIMP program does not
transfer to a C program with the same text (@sec:vimp-vs-c). That
#isaconst("pstep") models the intended language is argued, not proved, and the
simulation from source runs to graph runs and the representation of graph runs
by valid traces are proved in the forward direction only (@sec:csim,
@sec:valid). Within the analyzer, only the combined state as a whole publishes
to analysis globals, so #isaconst("rel_order_spec") is selectable only in its
local form, and one update rule serves every global unknown of a run
(@sec:mixed-flow, @sec:relational, @sec:update-rules).

The delivered tools rest on the trusted components of @sec:trust-boundary, and
every witness proved by evaluation trusts the code generator. No test runs VIMP
programs concretely, since the development has no executable form of
#isaconst("pstep"). No time or memory measurement is reported. The executable
keeps the data representations of the proofs: finite sets are unordered lists
and the solver's value table is a function, so membership, insertion and lookup
take linear time @haftmann10 #_todo[check that the cited work states this.].
Measured once on one machine, each doubling of a chain of assignments
multiplied the running time by about 7, close to the cubic factor of 8, mostly
from the list unions in #isaconst("compile")
#_todo[register the command, input and data.]. A data refinement to red-black
trees, which Isabelle's library and the Isabelle Collections Framework provide
with refinement proofs @lammich26collections[§1.1]
#_todo[check locator.], would remove this cost. It would change the state of
the vendored solver and require its proof to be redone, while the rest of the
chain uses the solver only through its certificate (@sec:certificate).

The evidence beyond the theorem is narrow. Each counterexample theorem weakens
one selected condition on one program, and none shows that the coverage contract as a
whole is minimal (@sec:falsification). No general precision, optimality or
completeness theorem is proved, where completeness would mean that every check
that holds in all executions is reported as proved, and each precision witness concerns one program
with fixed analysis settings (@sec:eval-precision). The regression corpus is small
and written for this work, and its expected behaviour is the author's reading
of each program (@sec:eval-corpus). The Goblint defect of @sec:eval-1161 was
not re-run, and the playground is illustrative; no study measures whether it
helps a reader. The correspondence with Goblint is architectural: no theorem
transfers to its OCaml implementation, and no agreement rate between the two
analyzers is measured (@sec:eval-goblint). The comparison with prior work rests
on a targeted search rather than a systematic review (@ch:related).

== Outlook and future work <sec:outlook>

=== Extending Voblint <sec:outlook-extending>

A richer source language, up to a subset of C, needs the new
obligations that @sec:discussion names for machine integers, pointers, a heap
and threads, and a semantics and a preservation argument per construct at
every layer.

Such a language would benefit from an elaboration phase between the parser and
the compiler. Already for VIMP, the source-level theorem only asserts that
_some_ node $v$ is related to the reached source configuration (@sec:headline).
The existential is forced by the representation. A residual command records
nothing about the occurrence it came from, so two equal assignments in one body
are indistinguishable, and #isaconst("control_at") can only place a residual at
some node of a fragment that produced it (@sec:csim). An elaboration phase would
annotate every statement with the node the compiler emits for it, and the
source semantics would run the annotated program. Each source configuration would then
name its node, and the theorem could state its conclusions at that node without
an existential. The compiler already numbers its statement nodes
deterministically (#isaconst("csize"), #isaconst("prog_stmt_post_order")). If
elaboration and compilation shared this numbering, annotated and emitted nodes
would agree by construction instead of through a correspondence proof. The same
phase is where a C-like front end resolves names to declarations, fixes the type
of every expression and makes implicit conversions explicit, so that the
compiler and the analyses never reconstruct them. Annotated syntax that is
parametric in its variable and expression types would let such resolution and
typing be added later without changing the statement nodes or the location
proof.

On the analysis side, the order analysis drops the pairs of an assigned variable before
relearning some by asking, and it keeps nothing across calls. A useful relational domain needs its own transfer proofs, and
through the query channel it could answer the numeric analyses at branches as
well as at assignments (@sec:relational). The combined state admits one query
kind and components without globals (@sec:coop-queries, @sec:coop-catalogue). Further query kinds
need their own truth relation, and a component with globals needs the
combination to keep each analysis's globals apart, as Goblint's MCP tags them
with the analysis they belong to. In the shipped analyzer the global unknowns
carry activation seeds and, under the flow-insensitive placement, one value per
program global. Threads and locks with a thread-local trace semantics would
allow thread-modular uses of these global unknowns.

Every shipped analysis answers a single entry pair per call, although the
interface admits several (@sec:calls), so path-sensitive analyses that split a
call into cases remain future work. The contexts of an activation depend only
on how it was entered. Digests refine
unknowns by other abstractions of a local trace (@sec:rel-goblint).
Generalizing #isaconst("activation_context_rel") to such abstractions over
activation traces would allow path- or history-sensitive unknowns, each
with its own admissibility conditions.

Voblint adapts its equations to the interface of the vendored solver
(@sec:eq-encoding). A version of the solver that publishes to local unknowns
and joins the writes of one evaluation per target, as Goblint's solvers do,
would let callers publish into callee entries directly and make activation
seeds and buffering unnecessary. It would need its partial-correctness proof
redone for local side effects. The rest of the chain consumes the solver only
through the post-solution certificate (@sec:certificate).

A termination theorem would guarantee an answer for every program. The
total-correctness result of Tilscher et al. covers the top-down solver without
side effects, for finitely many unknowns, a precise widening, and monotonic
right-hand sides with monotonic dependencies @tilscher26jar[Cor. 1]. Their
widening stabilizes every widening sequence by definition @tilscher26jar[Def. 2].
The vendored class #isalocale("warrowing") states no stabilization law
(@sec:widening), so even finitely many unknowns may take values that increase
forever (@sec:termination).

The adequacy of #isaconst("pstep") is argued and checked against example
programs (@sec:vimp-vs-c). A fuel-bounded evaluator whose runs are proved to be
#isaconst("pstep") runs would make this check systematic. A run that reaches and violates
a check the analyzer reports as `PROVED` would then point to a fault in the
trusted base: the code generator, the target toolchain or the handwritten
OCaml, and the parser if the evaluator reads the source independently. Comparing its runs with a
C compiler on the common subset would test the adequacy argument itself.

A faster executable needs the data refinement of @sec:limitations.

=== Voblint and Goblint <sec:outlook-goblint>

Within the architectural correspondence of @sec:eval-goblint, Voblint can serve as an executable specification of the
architecture with proved soundness obligations. From Goblint to Voblint, a
Goblint feature gives the design that an extension follows, as the query
mechanism did for @ch:cooperation. A documented Goblint defect can be replayed
as a regression fixture and as a counterexample theorem, as the congruence
remainder was (@sec:eval-1161). The same obligations could
be consulted before a change to Goblint lands: a proposed domain operation with
a counterpart in Voblint would be transliterated by hand and checked against
the obligation that counterpart meets, as #isathm("congruence_mod_sound")
states it for the remainder. Operations on pointers or threads have no such
counterpart.

From Voblint to Goblint, a verified component exported as OCaml could replace
its unverified counterpart in Goblint. That needs more than the export: the
data refinement of @sec:limitations, a correspondence between the
component's interface and Goblint's, and soundness for C's integers, since the
component's proofs assume VIMP's unbounded ones (@sec:vimp-vs-c).

=== Agent-assisted development <sec:outlook-agents>

A new analysis enters Voblint through obligations that name no partner,
context, solver or equation (@sec:coop-catalogue). This suits development with
AI agents (see #link(<ai-use>)[the statement on the use of generative AI]).
The obligations are the specification, and the batch build and the drift
checks of @ch:tooling are the oracle. Counterexample theorems for weakened
obligations (@sec:falsification, @sec:revealed) act as negative tests. The
order analysis and the query layer of @ch:cooperation were written this way.
This is the experience of one author on one extension, not a measured result.
An agent that delivers an analysis with its proof against these obligations
need not be trusted. The guarantee still rests on the adequacy of the
obligations and on the trusted base of @sec:trust-boundary.
