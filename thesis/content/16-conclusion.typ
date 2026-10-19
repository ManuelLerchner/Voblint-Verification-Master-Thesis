#import "../lib/code.typ": isaconst, isalocale, isathm, isatype, oblig, repo-blob
#import "../lib/figures.typ": verdict

= Conclusion <ch:conclusion>

Analyzers such as Goblint report facts about every execution of a program, yet
their soundness usually rests on testing (@ch:intro). This thesis shows that
the soundness of a Goblint-style analyzer with calling contexts, side effects,
and a verified solver can be machine-checked from source executions to the
verdicts of the exported function. The result holds for a scalar language with
recursive procedures and is a partial-correctness result, so it covers every answer the analyzer returns. For a user, a
#verdict("PROVED") verdict thus holds in every covered execution that reaches
the check, instead of resting on the tests the analyzer has passed.

The end-to-end theorem holds for every report #isaconst("run_voblint") returns,
under every configuration it offers (@sec:headline). Activation traces give
contexts a concrete meaning, and splitting the collected stores by context
loses no execution (@sec:contract). Domains, context policies, cooperating
analyses, and the solver each meet their own obligations, and generic theorems
compose them (@sec:eq-discharge). The proved function is the analyzer that the
command-line tool and the playground run (@ch:executable). Finally, the
premises of the main theorems can hold, and the remainder obligation rejects a
real defect (@ch:evaluation). On concrete programs, the evaluation also shows
that neither contexts nor update rules have a setting that is best everywhere
(@sec:eval-precision).

== How the formalization was built <sec:building>

Goblint's architecture served as the specification to follow. Each construct was compared with Goblint's sources and papers at a pinned
revision, and the decision to model it, simplify it, or leave it out was
recorded with its reason in an alignment register, which the project site and
@sec:rel-goblint summarize. The main questions were therefore architectural.
They concerned which parts of Goblint to keep, which to simplify, and where a
proof could state something that Goblint leaves implicit. Context sensitivity
is the clearest example. In Goblint, routing a call to a context is part of the
constraint system, and no formal statement says which concrete activations the
result for a context describes. Voblint states this as an obligation and proves
that the contexts together cover every activation (@sec:eq-routing).

In the first weeks of the project, a prototype mirrored Goblint's interfaces with every proof obligation
left open as `sorry`, so that definitions and locale boundaries could still
change cheaply. Only after they had stabilized were the obligations discharged,
and many of them then followed with little search for invariants, because
Goblint keeps analyses, contexts, and the solver apart. Goblint's architecture
already fixes what each layer may assume about the others, so the assumptions
of each proof were largely in place before it was written. The analysis contract, for
instance, mentions neither contexts nor the solver (@sec:sound-core), and the
solver enters only through its certificate (@sec:certificate). The same
separation supports incremental additions, such as entry-state contexts or
queries between analyses, each copied from Goblint and proved on its own.

Voblint was built iteratively, and its architecture changed several times
along the way. The first version compiled single-procedure programs to a flat
control-flow graph and solved them with a plain top-down solver. Within six
weeks, a trace semantics and interprocedural graphs replaced it, and the
side-effecting solver became the only one. Contexts were first built on a
digest-indexed concrete semantics, which was removed again after two weeks in
favor of the activation traces of @ch:traces. A
#link(repo-blob + "docs/ACTIVATION_LOCAL_TRACE_CONVERGENCE.md")[design record]
explains this change, and an earlier
#link(repo-blob + "docs/history/ACTIVATION_SEMANTICS_MODEL_DECISION.md")[decision study]
had judged the alternatives by their fidelity to Goblint and by whether
the concrete semantics stays independent of the analysis. Local and global values, call strings, the
relational domain, and finally cooperating analyses were then each added on top
of this foundation without major rewrites of it. Each larger change followed a written
plan, and more than a hundred of these documents remain in the repository's
#link(repo-blob + "docs/history")[history folder]. They are not part of the
argument, but they record why the definitions look as they do.

Generative AI tools widened the scope that one thesis could take on. Once the structure was
fixed, agents wrote many of the proofs. They also largely wrote the software
around the formalization, including the browser playground (@ch:executable), the
regression corpus with its ports of Goblint tests, the source tooling
`isar-tools` (@sec:isar-tools), and the checks that keep the theories, the
analyzer, the website, and this thesis consistent (@sec:voblint-repo). This
tooling, `isar-tools` in particular, proved valuable for maintaining a codebase
that kept growing throughout the project (@sec:isar-tools). Without this help, the work would likely have been limited to the core theorems. Collaborating with agents proved effective for moving the formalization
forward, and the same approach suits future extensions. A change to the
definitions makes Isabelle report every proof it breaks, at whichever layer, so
an agent can work through the failures while a reviewer checks the new
definitions.

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
pointers, a heap, threads, machine integers, and most of Goblint's analyses, so
Voblint becomes useful to them only once it is extended
(@sec:outlook-extending). Of the limits listed in @sec:intro-scope, the
distance to C weighs most. VIMP has no pointers, heap, or threads and
computes with unbounded integers, so a verdict about a VIMP program does not
carry over to a C program with the same text (@sec:vimp-vs-c), and the
adequacy of #isaconst("pstep") itself is argued rather than proved. A
commonly accepted semantics of C11 in Isabelle, against which
#isaconst("pstep") could be checked, would benefit Voblint and the wider
formalization community, but as far as the author is aware, none currently exists.
Existing work covers either parts of C in Isabelle
@brecknell24autocorres2 @tuong19isabellec or C11 in other settings
@krebbers15phd @memarian23phd.

A second limit concerns precision. The theorems guarantee soundness only, so
the evidence for precision rests on examples. No precision or completeness theorem is proved, the regression
corpus is small and its expected verdicts were set by hand (@sec:eval-corpus),
and no agreement rate with Goblint is measured (@sec:rel-goblint).

Neither limit weakens the soundness theorem itself. Both instead mark where the
result currently stops, and each names a direction in which Voblint can be extended.

== Extending Voblint towards C and Goblint <sec:outlook-extending>

Both limits point to the same next step. Voblint would have to be extended
towards the language and the analyses that Goblint's developers work with. Some analyses and concepts could be added to the current proof of concept
without much change, since each soundness proof stays within its own
obligations. For example, relational domains such as octagons or polyhedra @mine17
could follow the order analysis (@sec:relational), and path-sensitive
analyses could split a call into several entry pairs, which the interface
already admits (@sec:calls). Other features of Goblint, such as machine
integers, pointers, or threads, would require a drastic rewrite of large parts
of Voblint. For machine integers, a first step has been started outside this
thesis. #link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/357")[Pull request 357] adds machine-integer kinds from `i8` to `u64` with a typed
core language elaborated from VIMP, wraparound, diagnostics for overflow and
value-changing conversions, and a mandatory declaration for every variable. Its
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/31e267925ed730b8edc9c38aa2b2c21101d75531/docs/history/TYPED_CFG_PLAN.md")[plan] and
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/31e267925ed730b8edc9c38aa2b2c21101d75531/docs/history/TYPED_IR.md")[design notes] are part of that branch.
Since these additions and the change to a strongly typed semantics touch
almost every layer and amount to a rewrite of the formalization, they are left
as future work, and the results of this thesis concern the version without
them. Once machine integers are in place, Goblint's bitfield domain, which
tracks each bit of an integer separately and which the author co-developed
(#link("https://github.com/goblint/analyzer/pull/1623")[Goblint pull request 1623]),
becomes a natural next analysis.

Whether a further C feature needs such a rewrite depends on how deeply it
reaches into the formalization. Much of the proof does not mention VIMP at
all. The solver certificate is stated over unknowns and right-hand sides, and
the coverage contract refers to the language only through a few step functions
(@sec:contract), so a feature that changes only these step functions leaves
the rest of the proof intact. The trace semantics, however, assumes that a callee cannot touch its caller's
locals, so a return can
resume the caller with the locals it had before the call (@sec:calls).
Features that keep this assumption, such as machine integers, change the
step functions and the proofs that unfold them, while the contract and its
composition keep their shape. Pointers, a shared heap, and threads break the assumption. Through a pointer or the
heap, a callee could change data its caller still uses, and threads let other
activations run in between. Such features
would require extending the trace semantics @sotin11 @schwarz21, and with it
every soundness proof built on traces, which amounts to a large rewrite of the
whole formalization.
