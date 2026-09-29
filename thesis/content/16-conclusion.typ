#import "../lib/code.typ": isaconst, isalocale, isathm, isatype, oblig

= Conclusion <ch:conclusion>

== Answers to the questions

*Can soundness be machine-checked end to end?* Yes, for a scalar language with recursive procedures and under a
per-program termination premise. Fix a list of activated analyses, a global
update rule and a context policy. If the solve terminates on an accepted program and
#isaconst("run_voblint") returns a result, then every store that a finite source
execution reaches from a store whose declared globals are zero is collected at
a graph node that simulates the source configuration, the returned result
covers it there, and every definite verdict listed at that node holds for it
(#isathm("run_voblint_certified_source_sound"), @sec:headline). The theorem is
about the function exported to the command-line and browser analyzers. The
premises that remain are an initial store, an answer of the analyzer and
termination of the abstract solve. Termination of the analyzed program is not
required. The delivered artifacts additionally trust the parser, code
generator, compilers, runtimes and presentation code (@sec:trust-boundary).

*What does a calling context denote?* A calling context is a property of an activation-local trace, read off
how the activation was entered (@sec:contexts). Under entry-state routing, the relation reads the context off the analysis's result. When every covered call admits some callee context (totality,
#isaconst("call_context_total_on")), the context buckets jointly equal the context-free trace collection
(#isathm("ltr_collect_eq_Union_activation_collect")).

*Can the ingredients be verified separately?* Yes. A non-relational domain
proves certificates about its primitive operations
(#isatype("nonrelational_ops")) without contexts or solver, and
#isalocale("sound_nonrelational_ops") derives its transfer, branch, entry and
check classifier, with their executable counterparts, and proves them sound
once. A context policy proves its obligations without a domain, and the solver
enters only through #isaconst("part_post_solution"). The routed locale
discharges the coverage contract once for all policies and domains
(#isathm("activation_collect_dg_sound"), @sec:eq-discharge), and the
source-level theorem covers every configuration #isaconst("run_voblint")
offers. A relational carrier meets the same contract without framework
changes, as a specification with a shared state (#isaconst("rel_order_spec"))
and as the local order analysis the analyzer runs
(#isathm("order_spec_sound"), @sec:relational). Analyses that exchange facts
through queries are verified separately as well: each proves its operations
against every sound query channel, and any list of independent analyses
combines into one that meets the analysis soundness contract
(#isathm("mcp_combine_sound"), @ch:cooperation).

*Is the theorem informative?* Partly. Counterexample theorems show that reading a callee's result in the caller's own context (#isathm("return_at_caller_context_unsound")) admits unsound claims, that a claim meeting every obligation except #oblig("TOTAL")
misses a store of the context-indexed collection
(#isathm("total_dropped_unsound")), and that Goblint's congruence remainder
before #link("https://github.com/goblint/analyzer/pull/1161")[pull request 1161] violates the domain obligation (#isathm("prefix_congruence_mod_unsound")).
Evaluation inside Isabelle, trusting the code generator, discharges every
premise of the main theorem for named programs, which then yields `PROVED`
verdicts (#isathm("nv_source_certified"),
#isathm("certificate_demo_full_certificate")), and a strict precision
separation between call strings of length 1 and 2 holds on one program
(#isathm("sign_k2_strictly_more_precise_than_k1_at_g")). @sec:eval-rq4
collects this evidence.

== Discussion <sec:discussion>

*Design trade-offs.* Relational context admission lets the context of a call depend on the analysis's result, as entry-state routing needs (@sec:contexts). A function always yields a context, while a relation may yield none. The contract
therefore needs #oblig("TOTAL"), and under entry-state routing it must be
discharged against the computed result (@sec:contexts). A functional policy embeds
as a relation (#isaconst("call_context_rel_of_fun")) and satisfies totality
directly, so the generality adds no cost for call strings.

Keeping program globals in the flow-sensitive local state lets the analysis
soundness contract name a single global and leaves the global unknowns with entry seeds only. Every unknown then carries every global. The flow-insensitive
placement, which Seidl et al. present as a choice for efficiency @seidl26,
loses precision on the `set`/`get` program (@sec:mixed-flow). We measured
neither placement's cost, so the choice is based on proof effort and precision.

Consuming the solver only through #isaconst("part_post_solution") lets one
proof cover four update rules (@sec:update-rules), and a solver meeting the
same certificate could replace the vendored one. The certificate says nothing
about termination or about which post-solution the solver returns. Termination
therefore stays a premise, and each precision statement concerns one evaluated
result (@sec:eval-rq4). Widening goes above the least solution by design
(@sec:certificate), so we expect any stronger characterization of the result
to depend on the solver's iteration strategy and to tie the proof to it.

Exporting one dispatcher makes the constant the theorem mentions the one the
tools run, so no entry point needs an agreement lemma (@sec:codegen). On the
other hand, a configuration reaches users only through the assembly behind
#isaconst("run_voblint"). Since the analyzer runs every configuration as a
combination of components, a new analysis becomes selectable once it proves its
component obligation (@sec:coop-catalogue) and is entered in the analysis
manifest. The entry names the domain, its value type, its constant prefix and
its theories, and the registrations and the combined state are generated from
it. The command-line interface's name tables and display key are still edited
by hand. An analysis that needs globals of its own is not selectable
(@sec:coop-limits). @sec:outlook-agents returns to this division as a basis
for development with AI agents.

*Generalizability.* Goblint analyzes C after CIL normalization, with pointers,
a heap, threads, machine integers and further update rules. The certificate is
stated over right-hand sides and unknowns and mentions no VIMP construct. The
coverage contract has one obligation per rule of #isaconst("valid_ltr") and
refers to VIMP only through the graph, its stores and three step functions,
#isaconst("edge_step"), #isaconst("call_enter") and #isaconst("combine_collect")
(@sec:contract). We therefore expect the contract's shape,
the bucket theorem and the composition of @sec:eq-discharge to carry over to a
language whose activations do not interfere, with the step
functions and every proof that unfolds them redone. Machine integers fit this
case: they change the step functions, the generic derivation in
#isalocale("sound_nonrelational_ops") and each domain's certificates for its
primitive operations, while routing and certificate do not mention arithmetic. The numeric domains
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
interleave activations, which #isaconst("valid_ltr") cannot express. The local
traces of #cite(<schwarz21>, form: "prose") handle them, but the interface
would also need synchronization, which it lacks. A new update
rule that meets the vendored interface needs the least work, since only
#isathm("update_rule_update_global_of") splits on the rule. A C front end such as CIL would join the parser in the trust
boundary unless verified.

*For a verified analyzer.* The development suggests an order of work. State
soundness against a context-free trace semantics and read contexts off traces,
so that policies are proved against one fixed semantics. Consume the solver
through a certificate that also bounds side contributions and closes the
reached set (@sec:certificate). Export the constant the theorem is about.
Counterexample theorems for weakened obligations are easy to state, and two
of them determined the shape of the call interface (@sec:revealed).

== Limitations

The answers above hold within the following limits, each also stated where it
arises. @sec:eval-threats collects the threats to the evaluation.

+ *Partial correctness.* Solver termination is a per-program premise.
  Regression programs exist whose solves do not finish, under entry-state
  contexts on intervals and under the joining update rules (@sec:termination).
+ *Source language.* VIMP is scalar, without pointers, heap or memory model.
  Its integers are unbounded, division by zero is defined, and a callee's
  locals start at zero, so a verdict about a VIMP program does not transfer
  to a C program with the same text (@sec:vimp-vs-c).
+ *Adequacy and converse directions.* That #isaconst("pstep") models the
  intended language is argued, not proved. The simulation from source runs to
  graph runs and the representation of graph runs by valid traces are proved
  in the forward direction only (@sec:csim, @sec:valid).
+ *Trust.* The delivered tools rest on the trusted components of
  @sec:trust-boundary, and every witness proved by evaluation trusts the code
  generator (@tab:oracles-audit).
+ *Running time.* The executable keeps the data representations of the
  proofs: finite sets and maps are lists, and the solver's value table is a
  function. Its cost grows faster than linearly, cubically in the length of a
  straight-line program through compilation. No benchmark exists, and the data
  refinement to red-black trees that would remove these costs is not done
  (@sec:eval-absent).
+ *Analysis globals.* The analysis soundness contract admits a single global
  name (@sec:sound-core). The selectable analyses keep program globals in the
  flow-sensitive local state, and the flow-insensitive placement is proved sound for every program at the level of the analysis soundness contract (#isathm("ownership_split_lift_contract")), but end to end only for one program, whose routing obligations are evaluated (#isathm("mf_ltr_collect_sound"), @sec:mixed-flow).
+ *Coverage of the configuration space.* The combined state admits
  only components without globals, so #isaconst("rel_order_spec") is not
  selectable; its local form, the order analysis, is (@sec:relational).
+ *Necessity.* Each counterexample theorem weakens one selected condition
  on one program. None shows that the contract as a whole is minimal
  (@sec:falsification).
+ *Precision.* No general precision, optimality or completeness theorem is
  proved. Each precision witness concerns one program at fixed configurations
  (@sec:eval-rq4).
+ *Goblint.* The correspondence is architectural (@app:goblint-alignment).
  No theorem transfers to Goblint's OCaml implementation, and no agreement
  rate between the two analyzers is measured (@sec:eval-goblint).

== Outlook and future work <sec:outlook>

=== Extending Voblint <sec:outlook-extending>

*Semantics.* A richer source language, up to a subset of C, needs the new
obligations that @sec:discussion names for machine integers, pointers, a heap
and threads, and a semantics and a preservation argument per construct at
every layer.

*Analyses.* The order analysis forgets a variable on assignment and everything
across calls. A useful relational domain needs its own transfer proofs, and
through the query channel it could answer the numeric analyses at branches as
well as at assignments (@sec:relational). The combined state admits one query
kind and components without globals (@sec:coop-limits). Further query kinds
need their own truth relation, and a component with globals needs the
combination to route each analysis's analysis globals, as Goblint's MCP tags
them with the analysis they belong to. In the shipped analyzer the global unknowns carry only callee-entry seeds. One unknown per program global needs a
concretization over an environment of analysis-global values in place of the single
global name of the analysis soundness contract. Threads and locks with a
thread-local trace semantics would then allow the thread-modular uses of
globals discussed in @sec:mixed-flow.

The context relation reads only how an activation was entered. Digests refine
unknowns by other abstractions of a local trace, such as held locks or thread
identifiers @schwarz24digest. Generalizing #isaconst("trace_context") to such
history abstractions over activation-local traces would allow path- or
history-sensitive unknowns. Each abstraction would need its own admissibility
conditions in place of the context clauses of the coverage contract.

*Guarantees.* A termination theorem would remove the per-program premise. The total
correctness result of #cite(<tilscher26jar>, form: "prose") covers the top-down
solver without side effects and assumes finitely many unknowns, a precise
widening and monotonic right-hand sides with monotonic dependencies
(@sec:rel-solvers). Voblint's systems have side effects, and its unknowns pair
nodes with contexts. Bounding the contexts does not suffice on its own. For call strings over a compiled program the candidate space is
finite, but that the solved unknowns stay inside it is a hypothesis of
#isathm("compiled_call_string_vars_finite"), not a theorem about the routed
solve. Entry-state contexts over infinite domains need a bound such as the
context lifters of #cite(<erhard25>, form: "prose"). Even a finite space of unknowns
admits values that increase forever, because stabilization is not a law of #isalocale("warrowing")
(@sec:eq-finite, @sec:termination).

The adequacy of #isaconst("pstep") is argued and checked against example
programs (@sec:vimp-vs-c). A fuel-bounded evaluator whose runs are proved to be
#isaconst("pstep") runs would make this check systematic. A run that reaches and violates
a check the analyzer reports as `PROVED` would then point to a fault in the
trusted base: the code generator, the target toolchain or the handwritten
OCaml, and the parser if the evaluator reads the source independently. Comparing its runs with a
C compiler on the common subset would test the adequacy argument itself.

A faster executable needs the data refinement outlined in @sec:eval-absent,
which changes the vendored solver's state and hence its proof but leaves the
rest of the chain, which sees the solver only through its certificate.

=== Voblint and Goblint <sec:outlook-goblint>

Voblint shares Goblint's split into local and global unknowns, its unknowns
indexed by node and context, and its enter/combine protocol at calls. Only this
architectural correspondence is established (@app:goblint-alignment). Within
that limit, Voblint can serve as an executable specification of the
architecture with proved soundness obligations. From Goblint to Voblint, a
Goblint feature gives the design that an extension follows, as the query
mechanism did for @ch:cooperation, and the feature often has an obvious place in the formalization. A
documented Goblint defect can be replayed as a regression fixture and as a
counterexample theorem that shows the defective operation violating an
obligation. The congruence remainder of @sec:eval-1161 was replayed in both
forms (#isathm("prefix_congruence_mod_unsound")). The same obligations could
be consulted before a change to Goblint lands: a proposed domain operation with
a counterpart in Voblint would be transliterated by hand and checked against
the obligation that counterpart meets, as #isathm("congruence_mod_sound")
states it for the remainder. Operations on pointers or threads have no such
counterpart.

From Voblint to Goblint, a verified component exported as OCaml could replace
its unverified counterpart in Goblint. That needs more than the export: the
data refinement above (@sec:eval-absent), a correspondence between the
component's interface and Goblint's, and soundness for C's integers, since the
component's proofs assume VIMP's unbounded ones (@sec:vimp-vs-c).

=== Agent-assisted development <sec:outlook-agents>

A new analysis enters Voblint at one of two levels. A non-relational value
domain proves the certificate #isalocale("sound_nonrelational_ops") for its
operation bundle, and #isathm("sound_nonrelational_ops.dg_analysis_execI")
discharges every obligation about the domain. Any other analysis supplies a
component meeting the obligations of @sec:coop-catalogue. Neither names a
partner or mentions a context, solver or equation. This division suits
development with AI agents (see #link(<ai-use>)[the statement on the use of
  generative AI]), because it fixes the parts of an agent's task that a test
harness would. The certificate or the catalogue is the specification. The
batch build and the drift checks of @ch:tooling are the oracle, and a change
counts as done only when they pass. Counterexample theorems for weakened
obligations (@sec:falsification, @sec:revealed) act as negative tests of the
catalogue: each shows on one program that dropping a selected condition admits
an unsound claim, so the conditions they cover cannot be dropped as
unnecessary. The order analysis and the query layer of @ch:cooperation were
written this way: agents read Goblint's MCP for the architecture, and the batch
build and the checks of @ch:tooling held them to the obligations. This is the
experience of one author on one extension, not a measured result.

In the long run, an agent asked for an analysis of a given property would have
to deliver it together with its modular soundness proof against the fixed
catalogue. Isabelle checks the proof, so the guarantee would not depend on
trusting the agent. It would still rest on the adequacy of the catalogue and on
the trusted base of @sec:trust-boundary. The catalogue constrains soundness
only, so precision would still need fixtures that demand definite verdicts
(@sec:eval-corpus). Other
analyzers that separate the abstract domain from a fixpoint engine proved sound
once against a fixed interface could adopt the same pattern.

== Summary

The thesis shows that the soundness of a Goblint-style analyzer with contexts,
side effects and a verified solver can be machine-checked from source
executions to the verdicts of the exported function, for a scalar language
with recursive procedures and under a per-program termination premise. The
proof factors into a trace semantics with contexts read off activations, a
coverage contract that one theorem discharges from separate obligations of
analysis and context policy, and a certificate through which the solver enters.
A non-relational domain supplies only certified primitive operations, from
which a generic builder in the style of Nipkow and Klein derives its analysis. Analyses that answer one
another's queries combine under the same theorem, each proving one obligation
that names no partner.
