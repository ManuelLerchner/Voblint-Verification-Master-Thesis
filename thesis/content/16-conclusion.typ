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

== Approach and lessons <sec:building>

Goblint's architecture served as the specification to follow. For each
construct, the author read Goblint's sources and papers at a pinned revision, decided
whether to model it, simplify it, or leave it out, and recorded the decision
with its reason in an alignment register, which the project site and
@sec:rel-goblint summarize. The main questions were therefore architectural.
They concerned which parts of Goblint to keep, which to simplify, and where a
proof could state something that Goblint leaves implicit. Context sensitivity
is the clearest example. In Goblint, routing a call to a context is part of the
constraint system, and no formal statement says which concrete activations the
result for a context describes. Voblint states this as an obligation and proves
that the contexts together cover every activation (@sec:eq-routing).

The development started from structure rather than proofs. During the first
weeks, a prototype mirrored Goblint's interfaces with every proof obligation
left open as `sorry`, so that definitions and locale boundaries could still
change cheaply. Only after they had stabilized were the obligations discharged,
and many of them then followed with little search for invariants, because
Goblint keeps analyses, contexts, and the solver apart. The analysis contract
mentions neither contexts nor the solver (@sec:sound-core), the solver enters
only through its certificate (@sec:certificate), and each analysis of a
combination is proved against any channel (@sec:coop-channels).  The
same separation let precision grow step by step. Entry-state contexts, the
reduction inside Int, and queries between analyses each copied one more concept
from Goblint and were proved at their own layer.

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
had judged the alternatives by fidelity to Goblint and by clean layering. Local and global values, call strings, the
relational domain, and finally cooperating analyses were then each added on top
of this foundation without replacing it. Each larger change followed a written
plan, and more than a hundred of these documents remain in the repository's
#link(repo-blob + "docs/history")[history folder]. They are not part of the
argument, but they record why the definitions look as they do.

Generative AI tools widened the scope that one thesis could take on
(#link(<ai-use>)[statement on the use of generative AI]). Once the structure was
fixed, agents wrote many of the proofs, but much of their effect lay around the
formalization. They largely wrote the browser playground (@ch:executable), the
regression corpus with its ports of Goblint tests, the source tooling
`isar-tools` (@sec:isar-tools), and the checks that keep the theories, the
analyzer, the website, and this thesis consistent (@sec:voblint-repo). Without this help, the work would likely have been limited to the core theorems. For future extensions, a change to the definitions makes Isabelle report every
proof it breaks, at whichever layer, so an agent can work through the failures
while a reviewer checks the new definitions.

== Implications for Goblint <sec:outlook-goblint>

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

== Limitations <sec:limitations>

@sec:intro-scope listed the limits of the result, and two of them weigh most.
The first is the distance to C. VIMP has no pointers, heap, or threads and
computes with unbounded integers, so a verdict about a VIMP program does not
carry over to a C program with the same text (@sec:vimp-vs-c), and the
adequacy of #isaconst("pstep") itself is argued rather than proved. The second
is that the guarantee depends on an answer. Termination is not proved, some
regression programs do not finish within their time limit
(@sec:eval-precision), and the executable keeps the data representations of
the proofs, so the analyzer can also be slow (@sec:generated-code). Beyond
these, the evidence for precision rests on examples. No precision or
completeness theorem is proved, the regression corpus is small and its
expected verdicts were set by hand (@sec:eval-corpus), and no agreement rate
with Goblint is measured (@sec:rel-goblint).

== Outlook <sec:outlook-extending>

The adequacy of #isaconst("pstep") is argued and checked against example
programs (@sec:vimp-vs-c). A fuel-bounded evaluator whose runs are proved to be
#isaconst("pstep") runs would make this check systematic. A run that violates a check
reported as #verdict("PROVED") would then point to a fault in the trusted base.

Richer analyses need their own soundness proofs. A relational domain with
stronger transfer functions than the order analysis could also answer the
numeric analyses at branches (@sec:relational), and further query kinds would
each need a truth relation. Every shipped analysis answers a single entry pair
per call, although the interface admits several (@sec:calls), so path-sensitive
analyses that split a call into cases remain future work.

The solver leaves two directions open. A version of the vendored solver that,
like Goblint's, publishes to local unknowns would let callers write into callee
entries directly and make activation seeds and buffering unnecessary
(@sec:eq-encoding). Its termination also remains open. The existing total-correctness results
do not apply to any configuration of Voblint (@sec:certificate). Following
them, a termination theorem would need finitely many unknowns and a widening that stabilizes, a law the vendored class
#isalocale("warrowing") does not state (@sec:widening).

A richer source language, up to a subset of C, would affect the layers
differently. The solver certificate mentions no VIMP construct, and the
coverage contract refers to the language only through a few step functions
(@sec:contract). For a language whose activations do not interfere, such as
VIMP with machine integers, the author therefore expects the contract, the
exhaustiveness of the contexts, and the composition of @sec:eq-discharge to
carry over, while the step functions and the proofs that unfold them would be
redone. Pointers into the stack, a shared heap, and threads break the
assumption that activations do not interfere and would change the trace
semantics itself @sotin11 @schwarz21.

A first step towards C has been started outside this thesis.
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/pull/357")[Pull request 357] adds machine-integer kinds from `i8` to `u64` with a typed
core language elaborated from VIMP, wraparound, diagnostics for overflow and
value-changing conversions, and a mandatory declaration for every variable. Its
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/31e267925ed730b8edc9c38aa2b2c21101d75531/docs/history/TYPED_CFG_PLAN.md")[plan] and
#link("https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis/blob/31e267925ed730b8edc9c38aa2b2c21101d75531/docs/history/TYPED_IR.md")[design notes] are part of that branch.
The typed semantics touches almost every layer and amounts to a rewrite of
the formalization. It is therefore left as future work, and
the results of this thesis concern the version without it.
