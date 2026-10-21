# Review: "Calling Contexts Made Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL"

Reviewer 2 (abstract interpretation, interprocedural analysis)

## Summary

The paper presents Voblint, an Isabelle/HOL development that proves partial
correctness of an executable, context-sensitive abstract interpreter for VIMP, a
scalar imperative language with globals and recursive procedures. The chain is:
small-step source semantics, forward simulation to a procedure-aware CFG,
"activation traces" (one activation plus a pointer to the trace of its creator,
adapted from the local traces of Schwarz et al.), a context policy given as a
relation from a concrete call to a set of callee contexts, an activation
collecting semantics A(v, c) indexed by node and context, and a "coverage
contract" of five local obligations (Init, Intra, Call, Return, Total) whose
satisfaction implies A(v, c) is contained in the cover. Every post-solution of
the generated side-effecting, context-routed equation system meets the
contract, given an analysis contract, routing adequacy and totality. The
vendored top-down solver of Tilscher et al. supplies the post-solution
certificate. The headline theorem (run_voblint_source_sound) is stated about the
constant exported to OCaml, for all configurations. The evaluation consists of
non-vacuity instances proved by `eval`, a lemma showing that a pre-fix Goblint
congruence remainder violates the domain obligation, a k=2 versus k=1 precision
witness, a comparison with Goblint on eight checks from Monniaux's "flavors"
tutorial, and running times over the regression corpus.

The engineering is substantial and the claim discipline is, for the most part,
careful: PROVED/REFUTED/DEAD are given their exact meaning, the trust boundary is
drawn, and partial correctness is stated up front. My concerns are about the
framing of the problem as new, the novelty of the concrete construction relative
to classical interprocedural theory, the absence of central related work, and
how much the evaluation actually tests the contribution.

## Recommendation and confidence

Major revision. Confidence: 4 (expert in the area; I read the paper in full,
spot-checked the thesis and theories, but did not rebuild the development).

## Strengths

1. An end-to-end theorem about the shipped constant, for every configuration,
   with no termination, coverage, or well-formedness premise left to the user
   (Section 5, lines 529-535). For context-sensitive analysis of recursive
   programs this is, as far as I know, not available elsewhere in a proof
   assistant. Verasco (cited) rejects recursion; Dabrowski and Pichardie (cited)
   do not compute their constraints.
2. The solver enters through a narrow certificate (certified_solver,
   part_post_solution), and the semantic layer never unfolds it. This is the
   right decomposition and a useful template for anyone reusing the verified TD
   solvers.
3. The Total obligation and the counterexample total_dropped_unsound
   (Section 3.3) identify a real and easily missed gap: a call admitted in no
   context makes Call and Return vacuous while the resumed caller keeps its
   contexts. Making this explicit and proving it necessary is a good point.
4. The result semantics is stated precisely (Section 5, "What verdicts mean"),
   including that REFUTED is not a counterexample and that PROVED does not imply
   reachability.
5. The GenAI declaration is detailed and honest, including AI participation in
   the design of activation traces.

## Major weaknesses

### 1. The problem is framed as open, but concrete meanings for calling contexts are classical

The abstract and introduction (lines 11-13, 66-75) say that "the ordinary
collecting semantics lacks" a concrete meaning for contexts and present giving
one as the first contribution. This has been standard since the origin of the
field. The paper never cites the classical sources:

- Sharir and Pnueli define the call-string approach over interprocedurally
  valid paths, where a call string is a concrete, path-derived tag of each fact,
  and prove it coincides with the meet over valid paths. A per-context claim is
  checked against the set of valid paths with a given call-string suffix.
  M. Sharir, A. Pnueli. Two approaches to interprocedural data flow analysis. In
  S. S. Muchnick, N. D. Jones (eds.), Program Flow Analysis: Theory and
  Applications, ch. 7, Prentice-Hall, 1981. (Standard reference; no DOI.)
- Jeannet and Serwe derive interprocedural analyses, call-string and functional
  alike, by abstracting the standard stack-based operational semantics, so that
  the "context" is an abstraction of the concrete call stack.
  B. Jeannet, W. Serwe. Abstracting call-stacks for interprocedural verification
  of imperative programs. AMAST 2004, LNCS 3116, pp. 258-273, Springer.
  doi:10.1007/978-3-540-27815-3_22. (Verified via Crossref.)
- Seidl and Fecht give a small-step operational semantics covering imperative
  procedures and compare call-string/relational/functional interprocedural
  analyses formulated as equation systems solved by local solvers. This is the
  direct precursor of the Goblint formulation the paper mechanizes.
  H. Seidl, C. Fecht. Interprocedural analyses: a comparison. Journal of Logic
  Programming 43(2):123-156, 2000. doi:10.1016/S0743-1066(99)00058-8. (Verified
  via Crossref.)
- In the higher-order setting, abstracting abstract machines makes contexts
  concrete as instrumented time-stamps/addresses in the concrete machine, and
  polyvariance is characterized entirely by the allocation policy.
  D. Van Horn, M. Might. Abstracting abstract machines. ICFP 2010, pp. 51-62.
  doi:10.1145/1863543.1863553 (verified via Crossref); extended version:
  Systematic abstraction of abstract machines, JFP 22(4-5):705-746, 2012,
  doi:10.1017/S0956796812000238 (from search results; DOI not checked against
  Crossref). T. Gilray, M. D. Adams, M. Might. Allocation characterizes
  polyvariance: a unified methodology for polyvariant control-flow analysis.
  ICFP 2016, pp. 407-420. doi:10.1145/2951913.2951936. (Verified via Crossref.)
- Knoop and Steffen's interprocedural coincidence theorem and Reps, Horwitz,
  Sagiv's IFDS framework (both cited in the thesis, chapter 14, but dropped from
  the paper) belong here too. J. Knoop, B. Steffen. The interprocedural
  coincidence theorem. CC 1992, LNCS 641, pp. 125-140. T. Reps, S. Horwitz,
  M. Sagiv. Precise interprocedural dataflow analysis via graph reachability.
  POPL 1995, pp. 49-61. doi:10.1145/199448.199462 (verified via Crossref).

The paper's own Section 8 already credits Rival and Mauborgne with calling
contexts as an indexing of traces, including coverings in which one trace has
several indices. Combined with the above, the new part is the *mechanization*
of such an indexing over a specific trace representation, and its connection to
a verified side-effecting solver. The abstract, introduction and contribution
list should say exactly that. "We give calling contexts a concrete meaning"
(line 76) overstates it.

### 2. The relational context policy closely matches a posteriori soundness, which is not cited

Section 4.2 (lines 410-413) defines the entry-state policy *from the analysis
result*: adm admits the context that an entry pair of the solved caller state is
routed to. The paper argues that no circularity arises because the final
guarantee concerns C, which no policy changes. This is the idea behind Might and
Manolios's a posteriori soundness. They allow non-deterministic, precision-guided
context/allocation choices and justify them with an abstraction map built after
the analysis has run:

M. Might, P. Manolios. A posteriori soundness for non-deterministic abstract
interpretations. VMCAI 2009, LNCS 5403, pp. 260-274, Springer.
doi:10.1007/978-3-540-93900-9_22. (Verified via Crossref.)

Two consequences for the paper:

(a) The comparison has to be made, and the novelty of "contexts as a relation"
(Section 3.2, Section 6 "Contexts as a relation") rests on it. Rival and
Mauborgne already allow relational coverings (the thesis cites their
Rem. 3.2.4). Might and Manolios already allow solution-dependent context
choices. What remains is the specific use of totality in the mechanized proof.

(b) For entry-state contexts, which are Goblint's default and the setting of
the running example, A(v, c) depends on σ. Saying that the activation collecting
semantics gives contexts "a concrete meaning" is then misleading for exactly the
policy the paper motivates with. A(v, c) is a proof-internal device that is
re-instantiated per analysis result. Please state this plainly in Section 3 and
in the abstract, not only in a subordinate clause of Section 4.2.

### 3. Activation traces are not compared with the standard alternative

Section 6 compares activation traces only to a discarded prototype that inlined
calls (lines 572-577). The obvious alternative is a ghost-instrumented
small-step semantics whose frames carry contexts, as in Dabrowski and Pichardie
[6] and as implied by Jeannet and Serwe. Its invariant would say that every
frame's store at its node is in γ(σ(node, context of that frame)). The Return
case then needs only the frame below the top, which the stack provides. In the
paper's own words (lines 237-238), an activation trace "stores its creator
exactly", so `caller_of` chains are a tree-shaped encoding of the frame stack
with histories attached. The paper should:

- state what the trace representation buys over an instrumented stack
  semantics, for this language (where lines 778-781 concede that pointers into
  frames would break it anyway);
- justify the analogy with local traces (lines 243-248) more carefully. The
  paper itself notes that the objects differ and that no concurrency result
  transfers (line 763). Then the adaptation is mostly naming, and the claimed
  lineage should be weakened or justified by a concrete property that local
  traces have and frame stacks lack.

If the authors tried the instrumented-stack route and it failed in Isabelle,
that is valuable and should be reported.

### 4. The motivating defect does not exercise the contribution

The introduction (lines 46-48) and Section 7 ("The obligations reject a real
defect") use Goblint issue 1156, a wrong abstract remainder in the congruence
domain. That bug violates a pointwise domain law. Any verified domain library
(Nipkow-Klein style, Verasco's domains, Blazy et al.) rejects it, with no
contexts, traces or routing. The introduction then argues that *calling
contexts* make the missing link hard. The evaluation never shows a defect that
only the context-indexed obligations catch: a wrong `combine`, an
enter/routing mismatch, a context that is created but not published, a dropped
alternative. Goblint's tracker should contain such issues among the "more than a
hundred" unsound ones (line 46). One verified rejection of a context or routing
defect, preferably a real one, would make the evaluation support the paper's
thesis. total_dropped_unsound is a constructed cover and does not substitute.

The figure "more than a hundred issues labeled as unsound" also needs a
reproducible source: the query, the date, and whether labels were applied
retroactively. The SV-COMP "no false negative since 2021" claim should cite the
SV-COMP competition reports rather than [24].

### 5. The evaluation is thin for a journal and partly not like-for-like

- Non-vacuity (Section 7) is established for one program, plus companion
  instances, by `eval`. That shows the premises can hold together. It is fine,
  but it is the minimum. A stronger result would be a theorem that is
  universally quantified over a class, for example "for unit contexts and a
  finite-height domain under the joining update rule, run_voblint returns
  Analysed on every well-formed program". The JAR total-correctness result [27]
  seems close to giving this for finitely many unknowns (see Question 3).
- The k=2 witness is a single program and the paper says so. Fine, but it
  belongs in an example, not in the evaluation.
- Table 1 has eight checks. The Goblint settings were chosen by the author ("the
  settings that give it its best chance", line 663), without stating how they
  were selected or which other options were tried. The `reset i >= 0` column
  compares unbounded VIMP integers with Goblint's machine integers (lines
  696-698), so it measures a semantic difference, not precision. Either
  configure Goblint to treat signed overflow as impossible, if it offers such
  an option, or drop the column from the precision comparison. The "Int, Order"
  row is identical to "Int" and carries no information as shown.
- The thesis (chapter 14) states that the regression corpus has not been run
  through Goblint and that no agreement rate is reported. With 369 fixtures
  available, a corpus-wide verdict comparison under fixed, documented settings
  would be much more convincing than eight hand-picked checks.
- Running time: 21 of 5,535 runs time out, and solve time grows with exponents
  between 2 and 3 on generated families. The paper attributes this to list-based
  sets and maps (lines 603-606, 709-710) but does not test the claim. Swapping in
  the Containers or Collections setup in the code generator alone, as the paper
  suggests, would turn a conjecture into a measurement. Report program sizes
  too: a 0.23 ms median says more about the corpus than the analyzer.

### 6. Scope: the language restriction is acceptable, but the "Goblint-style" framing outruns it

A scalar language is a legitimate first target for this kind of proof, and the
conclusion (lines 773-781) is honest that pointers into the caller's frame, a
shared heap or threads would break the trace semantics itself. For a JAR
readership, however, the title and abstract suggest the mechanization covers what
makes Goblint distinctive. In VIMP:

- side effects are used for entry seeds and, optionally, for flow-insensitive
  program globals (configuration "placement of program globals", line 478). The
  paper never explains the second use or states that the headline theorem
  covers it (the thesis does, chapter 6). Without it, the "side-effecting
  constraint system" in the title of the contribution reduces to a seeding
  device;
- the paper does not mention that Voblint publishes the entry state to a global
  seed while Goblint publishes to the local entry unknown, so widening applies
  at a different place (thesis chapter 14). The analysis is therefore not
  operationally Goblint's even at the level of equations. This belongs in
  Section 8, "Goblint and local traces";
- the enter alternatives that motivate the relational policy (line 263) are
  used by no shipped analysis (thesis chapter 14: "the shipped analyses do not
  use it"). The only witness is ov_two_contexts_admitted. Say so in Section 3.2.

I would not reject the paper for the language restriction. I ask for a title,
abstract and introduction that match the delivered scope, and for a concrete
statement of which parts of the development carry over to a language with
pointers to locals (cf. Sotin and Jeannet, ESOP 2011, below).

### 7. Missing mechanized and semantic related work

Besides items 1 and 2:

- D. Darais, N. Labich, P. C. Nguyen, D. Van Horn. Abstracting definitional
  interpreters (functional pearl). PACMPL 1(ICFP), 2017.
  doi:10.1145/3110256. (Verified via Crossref.) Pushdown-precise call/return
  matching obtained from the defining language. Directly relevant to "a return
  resumes exactly the activation that made the call".
- D. Darais, D. Van Horn. Constructive Galois connections: taming the Galois
  connection framework for mechanized metatheory. ICFP 2016, pp. 311-324.
  doi:10.1145/2951913.2951934. (Verified via Crossref.) Mechanized (Agda)
  calculational abstract interpretation, including a CFA case study as I recall.
  The CFA detail is from memory and not checked.
- S. Keidel, C. Bach Poulsen, S. Erdweg. Compositional soundness proofs of
  abstract interpreters. PACMPL 2(ICFP), 2018. doi:10.1145/3236767. (Verified via
  Crossref.) A k-CFA for PCF proved sound compositionally, on paper as far as I
  could determine. Cited in the thesis but not in the paper.
- J. Breitner. Shivers' Control Flow Analysis. Archive of Formal Proofs,
  November 2010. <https://www.isa-afp.org/entries/Shivers-CFA.html> (verified).
  A control-flow analysis proved sound in Isabelle/HOLCF. Cited in the thesis but
  not in the paper, whose sentence "interprocedural analyses have been verified
  [13, 29]" (line 747) omits it.
- P. Sotin, B. Jeannet. Precise interprocedural analysis in the presence of
  pointers to the stack. ESOP 2011, LNCS 6602, pp. 459-479.
  doi:10.1007/978-3-642-19718-5_24. (Verified via Crossref.) Replaces a stack
  semantics by a local one, for exactly the extension the conclusion names as out
  of reach. Cited in the thesis but not in the paper.
- V. Robert, X. Leroy. A formally-verified alias analysis. CPP 2012, LNCS 7679.
  doi:10.1007/978-3-642-35308-6_5 (DOI from a publisher listing, not checked
  against Crossref). Together with CompCert's own verified ValueAnalysis, these
  CompCert-based analyses are intraprocedural. That supports the paper's
  positioning, but it should be stated with citations rather than left implicit.
- J. Erhard, J. F. Schinabeck, M. Schwarz, H. Seidl. Context gas and friends:
  taming context-sensitivity on the fly. STTT 27(2):289-307, 2025.
  doi:10.1007/s10009-025-00803-3. (Taken from the thesis bibliography; I could
  not confirm it independently.) Relevant to the unbounded context space under
  entry-state policies and hence to termination (Section 7, running time).

The dismissal "none of these entries claims an extracted analyzer or represents
an activation with its caller chain" (lines 747-748) distinguishes on
representation rather than on results. Wasserrab's slicing framework, for
instance, works over interprocedurally valid (call/return-matched) paths in
Isabelle, which is the classical concrete counterpart of call-string contexts.
Please compare on what is proved.

### 8. The paper is an ITP-format conference paper, not a journal article

The submission is typeset as LIPIcs ITP 2027, article 1, 17 pages. For JAR I
expect the full formal statements: the locale assumptions behind Theorem 2,
which the paper summarizes as "side conditions on call resolution and the shape
of the graph" (line 418); the definition of routing_adequate; the
at_node relation; the definitions of R_res and V_res; and the key proof
invariants (valid_activation_trace_covered, live_unknowns_cover). The hidden
locale context is exactly where an analyzer proof can quietly assume what it
needs. At present Theorem 2 cannot be checked from the paper. The thesis
contains most of this material, so the expansion is feasible.

Reproducibility is also incomplete: the vendored solver theories "come from a
repository that is not yet public" (lines 788-790). A JAR artifact must build
from public sources, or the Zenodo archive must contain the vendored theories
under a license that permits it. Please clarify which.

## Minor comments

1. Line 175, equation (1): C(v) = ∪_c A(v, c) holds only under Total
   (node_collect_eq_Union_activation_collect, within the contract). State that
   condition at the equation.
2. Section 3.3, Return obligation: it pairs any covered caller store s with any
   covered exit store t in context c′. The contract therefore cannot express the
   correlation between an entry and its exit that a relational/functional
   summary keeps. That is a precision limit, not a soundness issue, but it
   should be stated, since the paper aligns the entry-state policy with the
   functional approach (thesis chapter 14).
3. Lines 501-503 versus 554: main's locals are unconstrained initially while a
   callee's locals start at zero. Explain the asymmetry and its consequence for
   verdicts about uninitialized locals.
4. Line 186: "Each inclusion may add stores that no execution reaches". The
   first inclusion (reached ⊆ C) is exact up to the at_node relation, is it
   not? Clarify.
5. Section 4.3: "Every node of a procedure reaches its result node, because
   the compiler ends every body with a return edge". This is a syntactic
   reachability claim in the CFG. It presumably relies on every loop guard
   compiling to both a true and a false edge, so that `while (1)` still has an
   exit edge in the graph. Please state the exact graph property used and the
   lemma that proves it.
6. Section 4.3 lists five update rules for global unknowns. Name them, or cite
   the paper that defines them (Stemmler et al., cited in the thesis but not in
   the paper).
7. Line 263: "Goblint's enter may return several alternatives". Cite the
   interface at a pinned revision.
8. Line 630: proofs by `eval` trust the code generator. Since the non-vacuity
   facts are about one fixed program, say whether `value`/`code_simp` or a
   `by simp` replay was attempted to remove that dependency.
9. Section 6 "Feedback on the proof assistant": the linter paragraph is
   tooling, not a research result. Cut or shorten it for the journal version.
10. Figure 1 caption, "Without contexts ... both checks are UNKNOWN": mark this
    as analyzer output from a registered command, as done elsewhere.
11. Table 1 header abbreviations ("not ind.", "reset eq.") need a key in the
    caption.
12. Line 71: "forgets which call produced which store". The collecting
    semantics over *paths* does not forget this. Only the per-node store
    collection does. Be precise, since this sentence carries the motivation.

## Questions for the authors

1. What does the activation-trace representation give that a context-annotated
   frame stack (ghost state in cstep) would not? Did you try the latter?
2. For entry-state contexts, adm depends on σ. Is there a σ-independent policy
   (for example the concrete entry store, abstracted) from which the shipped
   routing can be shown adequate? If not, how does your A(v, c) differ in kind
   from the a posteriori abstraction maps of Might and Manolios?
3. For the unit and k-call-string policies, the set of unknowns reachable from
   the query is finite for a fixed program. Does the total-correctness result of
   [27], or a variant of it, apply once unknowns are restricted to that finite
   set? Which side-effect condition blocks it?
4. Is the headline theorem, with flow-insensitive global placement, proved for
   every update rule including warrowing? What precisely is widened at the seed
   unknowns, and does this ever lose precision relative to Goblint's direct
   publication to the entry unknown?
5. Which Goblint unsoundness issues concern contexts, enter/combine, or
   routing, and does any of them violate one of your obligations in a way you
   can mechanize, as for issue 1156?
6. How were Goblint's configurations for Table 1 chosen, and does Goblint offer
   an option to treat signed overflow as impossible, which would make the reset
   column comparable?
7. Can the contract express relational procedure summaries (Cousot and Cousot
   1977; Jeannet and Serwe 2004), or does it inherently assume tabulation by
   entry context?
8. Will the vendored solver theories be public, or included in the Zenodo
   archive, at publication time?
