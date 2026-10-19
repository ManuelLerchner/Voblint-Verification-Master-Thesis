#import "../lib/code.typ": fixture, isaconst, isalocale, isathm, isatype, oblig
#import "../lib/figures.typ": verdict

= Conclusion <ch:conclusion>

The thesis shows that the soundness of a Goblint-style analyzer with contexts,
side effects, and a verified solver can be machine-checked from source
executions to the verdicts of the exported function. The result holds for a
scalar language with recursive procedures and is a partial-correctness result,
so it covers every answer the analyzer returns. Graph runs simulate source
executions, valid activation traces represent graph runs, and the activation
collecting semantics groups the traces by the contexts their policy admits,
possibly several per trace. Context-indexed equations with routed calls cover
this semantics at every context, provided the analysis and the context policy
meet their separate obligations, and the solver enters only through a
post-solution certificate. The central contribution is this composition of an
activation semantics that stores no calling context, routing to contexts
admitted by a relation, analysis-local soundness obligations, and a verified
side-effecting solver into
one guarantee about the analyzer that the command-line tool and the browser
playground run (@ch:executable).

== Discussion <sec:discussion>

Two design choices shape what the theorem says. A context policy is a
relation, so it may place one call in several contexts, and entry-state
routing can read contexts off the analysis's own result. The price is the
totality obligation #oblig("TOTAL"), which gives every call at least one
context. Without it, a call that gets no context meets #oblig("CALL") and
#oblig("RETURN") vacuously, and a claim may miss the stores after the call
(#isathm("total_dropped_unsound")). Policies that compute one context per call
from the call site and the entered store, such as call strings, meet it
directly (#isathm("call_context_total_on_of_fun")). The solver, in turn, enters only through
its post-solution certificate. Soundness is therefore independent of the update
rule (@sec:update-rules), but the theorem says nothing about termination or
about which post-solution the solver returns (@sec:certificate).

How far the results carry beyond VIMP, toward the C that Goblint analyzes,
depends on the layer. The certificate mentions no VIMP construct, and the
coverage contract refers to VIMP only through the graph, its stores, and three
step functions, the edge transfer #isaconst("edge_step"), the call entry
#isaconst("call_enter"), and the return combination
#isaconst("combine_collect") (@sec:contract). We therefore expect the shape
of the coverage contract, the theorem that the contexts exhaust the node
collecting semantics, and the composition of @sec:eq-discharge to carry over
to a language whose activations do not interfere, that is, in which a callee
cannot change its caller's locals. The step functions and every proof that
unfolds them would have to be redone.

Machine integers show this split. Because elaboration makes the kind of every
operation and conversion explicit (@sec:elaboration), adding them changed the
step functions and the domains but neither routing nor the certificate. Signed
overflow wraps in the semantics and division by zero yields a value, where C
leaves both undefined, and the
analyzer reports where they may occur instead
(#isathm("run_voblint_arithmetic_safe")), as Goblint reports overflow
@saan26phd[§3.3.2]. Treating them as undefined behavior would need an error
outcome in the semantics and a meaning for it in the verdicts of
@sec:verdict-meaning.

Pointers into the stack break the assumption that activations do not
interfere. A return keeps the caller's locals (@sec:calls), which fails once a
callee can write them through a pointer, the case for which
#cite(<sotin11>, form: "prose") introduce their local semantics. A heap adds a
store component that caller and callee share, so #oblig("RETURN"), the entry
pairs, and the one value per variable in the domains (@sec:vimp) would all
change. Threads interleave activations, which
#isaconst("valid_activation_trace") cannot express, and the local traces that
give threads a semantics @schwarz21 have no procedures
@schwarz25phd[§8, p. 277]. The interface would also need synchronization.
A C front end such as CIL would join the parser in the trust boundary unless it
is verified.

== Limitations <sec:limitations>

The theorem is a partial-correctness result. Termination is proved neither for
the solve nor for the reduction of Int, and the regression corpus contains
programs whose solve gives no answer within its time limit (@sec:termination,
@sec:reduced-product). The theorem concerns VIMP, a scalar language without
pointers, heap, or memory model, whose integers have fixed widths and wrap,
whose division by zero is defined, and whose locals declared without an
initializer hold some value of their kind. A
call additionally resets the callee's locals to $0$, which no program the
parser accepts observes, because every local is declared and written before it
is read. A verdict about a VIMP program therefore does not transfer to a C
program with the same text. The arithmetic diagnostics cover the operations
whose result C leaves undefined or implementation-defined, and a point without
diagnostics is still not shown free of every undefined behavior of C
(@sec:vimp-vs-c). We argue, but do not prove, that elaboration and the core
semantics, #isaconst("pstep") among them, model the intended language, and the
parser's resolution of block scopes and the kind declarations it builds are
trusted. The simulation from source runs to graph runs and the representation
of graph runs by valid traces are proved in the forward direction only
(@sec:csim, @sec:source-bridge). Within the analyzer, only the combined state
as a whole publishes to analysis globals, since its components cannot
(@sec:coop-catalogue). Even when program globals are flow-insensitive, the
order analysis therefore keeps all its relations in the local state, and one
update rule serves every global unknown of a run (@sec:mixed-flow,
@sec:relational, @sec:update-rules).

The delivered tools rest on the trusted components of @sec:trust-boundary, and
every theorem proved by evaluation trusts the code generator. No test runs VIMP
programs concretely, since the development has no executable form of
#isaconst("pstep"). No systematic time or memory measurement is reported. The executable keeps proof-oriented data representations without a data refinement
to efficient sets and maps (@sec:generated-code). Refining the solver's state
would require the proof of the vendored solver to be redone, whereas the rest
of the chain uses the solver only through its certificate (@sec:certificate)
and would be unaffected. The vendored solver is itself a modified copy whose
changes await upstream review, and its repository is private, so the
development cannot yet be built from public sources alone
(@sec:upstream-td).

No general precision, optimality, or completeness theorem is proved, where
completeness would mean that every check that holds in all executions is
reported as proved. Each precision example concerns one program with fixed
analysis settings (@sec:eval-precision). The regression corpus is small and was
written or adapted for this work, and its expected verdicts were set by hand
(@sec:eval-corpus). Only the C versions of the flavors programs were also run
through Goblint (@sec:eval-flavors), and the rest of the corpus was not
checked against an independent analyzer. The Goblint
defect of @sec:eval-1161 was not re-run. The correspondence with Goblint is
architectural. No theorem transfers to its OCaml implementation, and no
agreement rate between the two analyzers is measured (@sec:rel-goblint). The
comparison with prior work rests on a targeted search rather than a systematic
review (@ch:related).

== Outlook <sec:outlook>

=== Extending Voblint <sec:outlook-extending>

A richer source language, up to a subset of C, needs the new obligations that
@sec:discussion names for signed overflow, pointers, a heap, and threads, and a
semantics and a preservation argument per construct at every layer. A C front
end would extend the elaboration into core VIMP (@sec:elaboration) to C's
types and expressions, and the meaning of the result would be argued as for
VIMP.

That argument is checked against example programs only (@sec:vimp-vs-c). A
fuel-bounded evaluator whose runs are proved to be #isaconst("pstep") runs
would make this check systematic. A run that violates a check reported as
#verdict("PROVED") would then point to a fault in the trusted base, and
comparing the evaluator's runs with a C compiler on the common subset would
test the adequacy argument itself.

Richer analyses need their own soundness proofs. A relational domain with
stronger transfer functions than the order analysis could also answer the
numeric analyses at branches (@sec:relational). Further query kinds would each
need a truth relation, and analyses with their own globals would need the
combination to keep these globals apart, as Goblint's MCP does
(@sec:coop-catalogue). Every shipped analysis answers a single entry pair per
call, although the interface admits several (@sec:calls), so path-sensitive
analyses that split a call into cases remain future work. Since the contexts of
an activation depend only on how it was entered, generalizing the context
relation of @sec:contexts to other abstractions of activation traces, as
digests are for local traces (@sec:rel-goblint), would allow path- or
history-sensitive unknowns, each with its own admissibility conditions.

A new update rule that meets the solver's interface changes little in
Voblint, since only #isathm("update_rule_update_global_of") splits on the
rule. Other extensions change the vendored solver itself, and with it its
partial-correctness proof. Goblint publishes into the callee's entry unknown
directly, and its per-origin narrowing rule for globals joins the writes of one
evaluation per target. A vendored solver that did both would let callers publish into callee entries directly and make activation
seeds and buffering unnecessary (@sec:eq-encoding). Of the losses in
@sec:eval-flavors, those not repaired by a partitioned local state come from
how the solver iterates. Goblint delays widening per widening point
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/config/options.schema.json#L2545")[`solvers.td3.widen_gas`])
and can widen to thresholds
(#link("https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/config/options.schema.json#L453")[`ana.int.interval_threshold_widening`]).
A delay needs a counter per widening point in the vendored solver, and
thresholds need the widening to know the constants of the program, which a
parameterless #isalocale("warrowing") operation cannot. Either change also
touches the solver's traced executable form (@sec:tracing).

A termination theorem would guarantee an answer for every program. The
total-correctness result of Tilscher et al. for the top-down solver without
side effects assumes finitely many unknowns, monotonic right-hand sides with
monotonic dependencies, and a precise widening @tilscher26jar[Cor. 1] that
stabilizes every widening sequence by definition @tilscher26jar[Def. 2]. The
vendored class #isalocale("warrowing") states no stabilization law
(@sec:widening), so it does not bound how long the values of even finitely
many unknowns keep increasing (@sec:termination).

=== Agent-assisted development <sec:outlook-agents>

Each new analysis only has to meet its own obligations, which mention neither
the other analyses nor contexts, the solver, or the equations
(@sec:coop-catalogue). This suits development with AI agents (see
#link(<ai-use>)[the statement on the use of generative AI]). An agent may
propose definitions and proofs, but Isabelle checks every proof, and the batch
build and the drift checks of @ch:tooling reject anything that does not check.
A build does not detect a theorem that holds only vacuously, however. An agent
once added a premise to the end-to-end theorem that no program satisfied, and
an audit of the theorem statements, not the build, exposed it.
The counterexample theorems for weakened obligations (@sec:eval-1161)
therefore act as negative tests, and the non-vacuity instances of
@sec:nonvacuity as positive tests that the premises of
#isathm("run_voblint_source_sound") and #isathm("run_voblint_check_sound") can
be met. The arithmetic theorems have no such instance. Human review can then concentrate on what no proof settles, namely whether
the base definitions and the obligations state the intended meaning
(@sec:vimp-vs-c) and whether the trusted base of @sec:trust-boundary is
acceptable. The same division applies to extensions
that change definitions at several layers, such as a construct from C or a
Goblint feature like path-sensitive entry alternatives. Isabelle reports every
proof the change breaks, so an agent can work through the failures while a
reviewer checks the new definitions, above all the extended source semantics.
Whether this division carries a larger extension remains to be tried.

=== Voblint and Goblint <sec:outlook-goblint>

Within the architectural correspondence of @sec:rel-goblint, Voblint can serve
as an executable specification of the architecture with proved soundness
obligations. In one direction, a Goblint feature gives the design that a
Voblint extension follows, as the query mechanism did for @ch:cooperation.
Goblint's regression programs can be adapted as fixtures, as part of the corpus
already is (@sec:eval-corpus), and a documented Goblint defect can be replayed
as a counterexample theorem, as the congruence remainder was (@sec:eval-1161).
The same obligations could be consulted before a change to Goblint lands, by
transliterating a proposed domain operation by hand and checking it against
the obligation its Voblint counterpart meets, such as
#isathm("congruence_mod_sound") for the remainder. Operations on pointers or
threads have no such counterpart.

In the other direction, a verified component exported as OCaml could replace
its unverified counterpart in Goblint, as extracted code replaced the SSA
construction of CompCertSSA @buchwald16. Besides the export, that needs the data
refinement of @sec:limitations, a correspondence between the component's
interface and Goblint's, and soundness for C's integers, since the component's
proofs assume VIMP's wrapping integers and defined division by zero
(@sec:vimp-vs-c).

Voblint verifies neither Goblint nor an analyzer for C. Its remaining gaps
are a richer language, termination, efficient representations, and the
handwritten code around the analyzer. The certificate and the shape of the
coverage contract would carry over to a language whose activations do not
interfere (@sec:discussion). Pointers into the stack and threads break that
assumption, termination needs a new theorem about the solver, and efficient
representations need the solver's proof redone. Within these limits, Voblint
connects, for a Goblint-style architecture, source executions to the verdicts
of executable code by one machine-checked chain.
