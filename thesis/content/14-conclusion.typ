#import "../lib/code.typ": isaconst, isalocale, isathm, oblig

= Conclusion <ch:conclusion>

== Answers to the research questions

*RQ1 (K1).* Yes, for a scalar language with recursive procedures and under a
per-program termination premise. Fix a domain, a global update rule and a
context policy. If the solve terminates on an accepted program and
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

*RQ2 (K2).* A calling context is a property of an activation-local trace, read off
how the activation was entered (@sec:contexts). The context relation may admit
one call at several contexts, and #isathm("ov_two_contexts_admitted") shows
such a call. Totality is the condition that loses no executions: when every
covered call admits some callee context (#isaconst("call_context_total_on")),
the context buckets jointly equal the context-free trace collection
(#isathm("ltr_collect_eq_Union_activation_collect")).

*RQ3 (K3).* Yes. A domain proves transfer soundness without contexts or solver, a
context policy proves its obligations without a domain, and the solver enters
only through #isaconst("part_post_solution"). The routed locale discharges the
coverage contract once for all policies and domains
(#isathm("activation_collect_dg_sound"), @sec:eq-discharge), and the
source-level theorem covers every configuration #isaconst("run_voblint")
offers. A relational carrier meets the same contract without framework changes
(#isaconst("rel_order_spec"), @sec:relational).

*RQ4 (K4).* Partly. Counterexample theorems show that reading a callee's result in
the caller's own context (#isathm("return_at_caller_context_unsound")) and
unpaired entry coverage (#isathm("unpaired_entry_cover_unsound")) admit
unsound claims, that a claim meeting every obligation except #oblig("TOTAL")
misses a store of the context-indexed collection
(#isathm("total_dropped_unsound")), and that Goblint's congruence remainder
before pull request 1161 violates the domain obligation (#isathm("prefix_congruence_mod_unsound")).
Evaluation inside Isabelle, trusting the code generator, discharges every
premise of the main theorem for named programs, which then yields `PROVED`
verdicts (#isathm("nv_source_certified"),
#isathm("certificate_demo_full_certificate")), and a strict precision
separation between call strings of length 1 and 2 holds on one program
(#isathm("sign_k2_strictly_more_precise_than_k1_at_g")). @sec:eval-rq4
collects this evidence.

== Discussion <sec:discussion>

*Design trade-offs.* Relational context admission lets one call be analyzed
at several contexts, as Goblint's `enter` permits (@sec:contexts). A function
always yields a context, while a relation may yield none. The contract
therefore needs #oblig("TOTAL"), and under entry-state routing it must be
discharged against the computed result (@sec:cover). A functional policy embeds
as a relation (#isaconst("call_context_rel_of_fun")) and satisfies totality
directly, so the generality adds no cost for call strings. Only one specification uses it
(#isathm("ov_two_contexts_admitted")).

Keeping program globals in the flow-sensitive local state lets the analysis
soundness contract name a single global and leaves the shared unknowns with
entry seeds only. Every unknown then carries every global. The flow-insensitive
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
#isaconst("run_voblint"). The relational witness is proved but not selectable
because the assembly fixes a reachability-lifted whole-store carrier
(@sec:engineering).

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
case: they change the step functions and each domain's transfer proofs, while
routing and certificate do not mention arithmetic. The numeric domains
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
would also need synchronization, which it lacks (@sec:omissions). A new update
rule that meets the vendored interface is the easy case, since only
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

The answers above hold within the following limits. Each is stated where it
arises, and @sec:eval-threats collects the threats to the evaluation.

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
+ *Shared unknowns.* The analysis soundness contract admits a single global
  name (@sec:sound-core). The selectable analyses keep program globals in the
  flow-sensitive local state, and the flow-insensitive placement is proved
  sound for one program only (#isathm("mf_ltr_collect_sound"),
  @sec:mixed-flow).
+ *Coverage of the configuration space.* Every shipped entry operation
  answers a call with one alternative, so admission at several contexts is
  exercised outside #isaconst("run_voblint") only, and the relational witness
  is not selectable (@sec:relational).
+ *Necessity.* Each counterexample theorem weakens one selected condition
  on one program. None shows that the contract as a whole is minimal
  (@sec:falsification).
+ *Precision.* No general precision, optimality or completeness theorem is
  proved. Each precision witness concerns one program at fixed configurations
  (@sec:eval-rq4).
+ *Goblint.* The correspondence is architectural (@app:goblint-alignment).
  No theorem transfers to Goblint's OCaml implementation, and no agreement
  rate between the two analyzers is measured (@sec:eval-goblint).

== Future work

A termination theorem would remove the per-program premise. The total
correctness result of #cite(<tilscher26jar>, form: "prose") covers the top-down
solver without side effects and assumes finitely many unknowns, a precise
widening and monotonic right-hand sides with monotonic dependencies
(@sec:rel-solvers). Voblint's systems have side effects, and its unknowns pair
nodes with contexts. Bounding the contexts is a first step, but it is not
enough on its own. For call strings over a compiled program the candidate space is
finite, but that the solved keys stay inside it is a hypothesis of
#isathm("compiled_call_string_vars_finite"), not a theorem about the routed
solve. Entry-state contexts over infinite domains need a bound such as the
context lifters of #cite(<erhard25>, form: "prose"). Even a finite key space
admits values that increase forever, because stabilization is not a law of #isalocale("bounded_warrowing")
(@sec:eq-finite, @sec:termination).

The adequacy of #isaconst("pstep") is argued and checked against example
programs (@sec:vimp-vs-c). A fuel-bounded evaluator whose runs are proved to be
#isaconst("pstep") runs would make this check systematic. A run that violates
a check the analyzer reports as `PROVED` would then point to a fault in the
trusted parser, code generator or handwritten OCaml. Comparing its runs with a
C compiler on the common subset would test the adequacy argument itself.

The relational witness forgets a variable on assignment and everything across
calls. A useful relational domain needs its own transfer proofs, although the
framework already accepts its carrier (@sec:relational). A richer source language needs
the new obligations @sec:discussion names, a semantics and a preservation
argument per construct at every layer. Composing analyses that exchange
information needs a query channel that the interface lacks (@sec:omissions), a semantic account of
the exchanged facts, and a proof that each component's guarantees survive the
exchange.

The context relation reads only how an activation was entered. Digests refine
unknowns by other abstractions of a local trace, such as held locks or thread
identifiers @schwarz24digest. Generalizing #isaconst("trace_context") to such
history abstractions over activation-local traces would allow path- or
history-sensitive keys. Each abstraction would need its own admissibility
conditions in place of the context clauses of the coverage contract.

In the shipped analyzer the shared unknowns carry only callee-entry seeds. One
unknown per program global needs a concretization over an environment of
shared values in place of the single global name of the analysis soundness
contract. Threads and locks with a thread-local trace semantics would then
allow the thread-modular uses of globals discussed in @sec:mixed-flow.

== Summary

The thesis shows that the soundness of a Goblint-style analyzer with contexts,
side effects and a verified solver can be machine-checked from source
executions to the verdicts of the exported function, for a scalar language
with recursive procedures and under a per-program termination premise. The
proof factors into a trace semantics with contexts read off activations, a
coverage contract that domain, context policy and solver discharge separately,
and a certificate through which the solver enters.
