#import "../lib/code.typ": isaconst, isalocale, isathm, isatype, oblig, repo-blob, site
#import "../lib/figures.typ": verdict
#import "../lib/stats.typ": stat

= Conclusion <ch:conclusion>

Static analyzers such as Goblint report properties intended to hold for every
execution of a program, but their implementations generally lack machine-checked
end-to-end soundness proofs. This thesis shows that the soundness of a
Goblint-style analyzer with calling contexts, side effects, and a verified TD
solver can be machine-checked from source executions to the verdicts of the
analysis function. The result holds for a scalar language with recursive
procedures. It is a partial-correctness result, so its guarantee holds whenever
the analyzer returns an answer. For a user, a #verdict("PROVED") verdict therefore
establishes the reported property for every covered execution that reaches the
check, instead of resting on
the tests the analyzer has passed.

The current implementation of Voblint lies between existing formalized
analyzers, such as Verasco @jourdan15 and the abstract interpreter of Nipkow and
Klein @nipkow14, and Goblint. The formalized analyzers state their theorem about
the analyzer they run, but avoid the mechanisms Goblint relies on for
interprocedural precision. Verasco reanalyzes a function at every call site
and raises an alarm at a possible recursive call, and the interpreter of
Nipkow and Klein analyzes IMP, which has no procedures. Goblint instead solves
equations over unknowns indexed by program point and calling context, publishes
side effects to global unknowns, and computes the solution with a top-down
solver. The TD solver itself has been verified @tilscher26, but no proof connects
Goblint's solved equations to the executions of the program. Voblint keeps Goblint's architecture and
states a CompCert-style theorem about the analyzer it runs. As far as the author is aware, a proof that connects context-indexed,
side-effecting equations and their solver to source executions has not been
mechanized before (@sec:rel-summary).

The end-to-end soundness theorem holds for every report #isaconst("run_voblint") returns,
under every analysis configuration it offers (@sec:headline). Activation traces give
contexts a concrete meaning, and splitting the collected stores by context
loses no execution (@sec:contract). Domains, context policies, cooperating
analyses, and the solver each meet their own obligations, and generic theorems
compose them (@sec:eq-discharge). The command-line tool and the
playground execute code generated from #isaconst("run_voblint") through an
unverified harness (@ch:executable). The theorem therefore applies to the
analysis function itself. Carrying it over to the displayed reports
additionally relies on correct parsing, code generation, and presentation
(@fig:intro-trust).

Concrete analysis configurations satisfy the premises of the end-to-end theorem, and the
remainder obligation rejects a real Goblint defect (@ch:evaluation). On the
external benchmarks of @sec:eval-flavors, Voblint proves every check that Goblint
proves with its plain interval domain or with full calling contexts, and
#stat("corpus.kinds.precision") fixtures of the regression corpus record the
precise verdicts it computes on further programs (@sec:eval-corpus). The analyzer runs in
acceptable time on that corpus, although its list-based sets and maps limit how far it
scales (@sec:eval-runtime).

== Recommendations for similar formalizations <sec:lessons>

Formalizing Voblint required more than proving the components of an analyzer
sound. Much of the work went into finding definitions and interfaces that let
these proofs compose, and into checking that the theorems describe the intended
analyzer. The following observations summarize this experience and suggest what
a similar formalization might do differently.

*Reuse the architecture, but reconsider the model.* Goblint's architecture is
documented in the literature and has been exercised on real programs. Following
it closely settled the analyzer's design, so the work could concentrate on the
soundness proof. The concrete semantics, however, had to
be designed for the proof. The first prototype used whole-program executions
with calls inlined. To account for one call, the soundness proof built a
separate execution starting at the callee's entry and spliced it into the
caller's trace. This handled individual calls, but it did not reflect the
program's call stack and was hard to extend to recursion. Activation traces
replaced it after two weeks (@ch:traces). Each procedure activation is its own
trace, a call starts a nested one, and a return resumes exactly the suspended
caller, as a
#link(repo-blob + "docs/ACTIVATION_LOCAL_TRACE_CONVERGENCE.md")[design record]
explains. The idea came from the local traces of Schwarz et al. @schwarz21,
against which Goblint's thread-modular analyses are proved sound, and not from
Goblint's implementation.

*Design the interfaces before completing the proofs.* The development began by
following Goblint's architecture, with every proof obligation left open as
`sorry`. This
made it inexpensive to try definitions, find missing assumptions, and move
interfaces without repairing finished proofs. The largest revisions indeed
concerned the semantics rather than individual arguments. Because Voblint
followed Goblint's structure, most interfaces were settled before the proofs
were written, and later changes seldom reached finished proofs. The end-to-end
theorem itself, however, took shape only as the components were connected.
Stating it first and deriving each component's obligations from it would likely
have saved some rework.

*Separate independent soundness obligations.* Voblint separates the soundness
of abstract operations, the coverage of executions by calling contexts, and the
correctness of the solver, which enters only through its certificate
(@sec:certificate). Because each has its own obligation, a new domain, context
policy, or cooperating analysis needed proofs of its own obligations but reused
the generic soundness arguments unchanged. Revising the concrete semantics, by contrast, affected every layer whose
obligations depend on it.

*Validate the executable analyzer.* The main theorem concerns the exported
function #isaconst("run_voblint"), and the command-line tool, the playground, and
the regression tests all run code generated from this function. Regression tests committed to the repository
record the expected verdicts on representative programs and detect changes in
the analyzer's observed precision. Generated theorem statements, registered
claims, and repository checks keep the thesis and documentation from drifting
away from the theories (@sec:voblint-repo).

*Make the solver observable.* The
#link(repo-blob + "cli")[command-line tool] and the browser
#link(site("playground.html"))[playground] were also important for understanding the analyzer's behavior. The
solver trace of the command-line tool and the playground's rendered graph and
trace replay (@sec:tracing) show where an analysis loses precision or where the
solver does needless work. The trace hook lies outside the proof. Only traced runs execute it, and
for them the trusted base assumes that it leaves the analysis results unchanged
(@sec:tracing). Because the analyzer is exported to OCaml, standard profiling and
debugging tools also remain available. The author used them to profile the
generated code and to attach a debugger to solves that did not terminate. The trace of
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/issues/251")[issue 251],
for instance, showed every newly entered context solved once from $bot$ before
its seed was published, and
#link(
  "https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/256",
)[pull request 256]
reordered the two into Goblint's order.

*Proof correctness and proof quality require different checks.* Isabelle checks
that the theorems follow from the definitions and assumptions, but not that the
definitions model the intended analyzer. Once the definitions and interfaces had
stabilized, generative AI tools produced many of the proofs. Isabelle checked
their validity relative to the formal assumptions, while human review focused on
the definitions, the assumptions, and the intended meaning of the theorems. Acceptance by Isabelle does not make a proof readable
or reusable, however. Unused and duplicated lemmas accumulated during the
development, and some arguments stayed more specialized than necessary. To find
such problems, the author developed
#link("https://github.com/ManuelLerchner/isar-tools")[`isar-tools`] alongside
the formalization (@sec:isar-tools). It
detects maintenance issues such as duplicated or subsumed lemmas, unused
lemmas, leftover proof-search and diagnostic commands, redundant brackets, and
inconsistent indentation.
Full Isabelle builds and these maintenance checks complement each other. A full
build of the development takes several minutes on the author's laptop (an Apple M4 Pro),
whereas the checks of `isar-tools` are deterministic and complete in seconds.
Agents that edit the theories can therefore run them after individual changes,
while full Isabelle builds remain necessary to establish correctness.

In retrospect, three questions required different kinds of evidence. The
soundness theorem establishes that the analysis results satisfy their formal
specification. The design of the semantics, the comparison with Goblint, and
executable examples support the adequacy of that specification, which proved
the most consequential challenge. Benchmarks, regression tests, tracing, and
profiling revealed the analyzer's practical behavior, including precision losses
and needless solver work, which the soundness theorem does not address.

== Relevance to Goblint and limitations <sec:limitations>

The proofs do not show that Goblint is correct, since they concern
Voblint's definitions and the correspondence with Goblint is architectural
(@sec:rel-goblint). They show, however, that Goblint's architecture admits a
soundness proof that composes along its own boundaries, provided each analysis
and each context policy meets its obligations.

A documented Goblint defect can be replayed as a regression
fixture and as a counterexample theorem, as the congruence remainder was
(@sec:eval-1161). A proposed domain operation with a counterpart in Voblint
could be checked against the obligation that its counterpart meets before the
change lands in Goblint. Conversely, a verified component exported as
OCaml could replace its unverified counterpart in Goblint.

For Goblint's developers, however, the current formalization is still largely
a proof of concept. It lacks many concepts that their work depends on, such as
pointers, a heap, threads, machine integers, and most of Goblint's analyses, so its
immediate applicability to Goblint development is limited, although it already
provides a reference for selected components and proof obligations
(@sec:outlook-extending). Among the limitations identified in @sec:intro-scope, the gap between VIMP and
C is the largest. VIMP has no pointers, heap, or threads and
computes with unbounded integers, so a verdict about a VIMP program does not
carry over to a C program with the same text (@sec:vimp-vs-c), and the
adequacy of #isaconst("pstep") itself is argued rather than proved. As far as the author is aware, no commonly
accepted C11 semantics exists in Isabelle against which #isaconst("pstep")
could be checked @brecknell24autocorres2 @tuong19isabellec @krebbers15phd
@memarian23phd.

A second limitation concerns the evaluation of precision. No precision or completeness theorem is proved, so the evidence for precision
rests on examples. The regression corpus is small and its expected verdicts were set by hand (@sec:eval-corpus),
and beyond the small comparison of @sec:eval-flavors, no agreement rate with
Goblint is measured (@sec:rel-goblint).

== Extensions towards C and Goblint <sec:outlook-extending>

Addressing these limitations requires extending Voblint towards the language
features and analyses that Goblint supports. Some analyses and concepts could be added to the current proof of concept
without much change, since each soundness proof stays within its own
obligations. For example, relational domains such as octagons or polyhedra @mine17
could follow the order analysis (@sec:relational), and path-sensitive
analyses could split a call into several entry pairs, which the interface
already admits (@sec:calls). Other features of Goblint, such as machine
integers, pointers, or threads, would require extensive changes to Voblint. Machine integers illustrate the scale of such an extension.
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/357")[Pull request 357],
developed separately from the version this thesis describes, introduces
machine-integer kinds from `i8` to `u64` and a typed core language translated from VIMP. Integrating it requires revisiting several layers and their
soundness proofs, which is left as future work. With machine integers, Goblint's bitfield domain, which tracks each
bit separately and which the author co-developed
(#link("https://github.com/goblint/analyzer/pull/1623")[Goblint pull request 1623]),
is a natural next analysis.

Whether a further C feature needs such a rewrite depends on how deeply it
reaches into the formalization. Several central results are independent of the details of VIMP. The solver certificate is stated over unknowns and right-hand sides, and
the coverage contract refers to the language only through a few step functions
(@sec:contract), so a feature that changes only these step functions leaves
the rest of the proof intact. The trace semantics, however, assumes that a callee cannot touch its caller's
locals, so a return can
resume the caller with the locals it had before the call (@sec:calls).
Features that keep this assumption, such as machine integers, change the
step functions and the proofs that unfold them, while the contract and its
composition keep their shape. Pointers, shared mutable memory, and threads would invalidate this assumption. With
a pointer into the caller's frame or into the heap, a callee can modify data the
caller reads after the return, and with threads, other code can run between a
call and its return. Such features
would require extending the trace semantics @sotin11 @schwarz21, and the
soundness arguments that depend on its current separation of caller and callee
state would need substantial revision.

Revisions of this scale may become more feasible as AI-assisted tools improve. Such tools
have already made large-scale mathematical formalization practical
@hales26lean[Sec. "Autoformalization is a practical reality"] and played an important role
in the formalization presented in this thesis. Over the course of this project, the models
behind these tools, including Anthropic's Claude, OpenAI's ChatGPT and Codex, and Cursor,
handled the formalization consistently better, and the surrounding
Isabelle tooling improved as well. Continued progress in both areas may make ambitious formalization projects
and large-scale refactorings increasingly practical.
