# Editor's decision — round 3

**Decision: Major revision.**

The submission makes a credible mechanization contribution: it connects activation-trace coverage, context routing, side-effecting equations, a solver certificate, and a source-level theorem about the exported analyzer. The inspected statements support this chain. Neither the specialist reviews nor my checks establish a false theorem, a vacuous endpoint, or an equivalent previously mechanized pipeline. The decision rests on the incomplete public proof artifact and on the amount of explanation still needed to assess the central interfaces from a journal article. These are remediable issues; rejection is not justified by the evidence gathered here.

The most consequential release requirement is concrete: the cited archive lacks the solver dependency required by `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:2`, as well as current paper evidence. The technical corrections are mostly textual. No new context-row theorem, general termination theorem, or analysis algorithm is required for this revision.

| Reviewer | Recommendation | Confidence |
| --- | --- | --- |
| A — Isabelle/proof engineering | Minor revision | 4/5 |
| B — abstract interpretation/contexts | Major revision | 3/5 |
| C — semantics/soundness | Minor revision | 4/5 |
| D — general JAR reader, paper only | Major revision | 4/5 |
| E — artifact | Major revision | 4/5 |
| F — devil's advocate | Minor revision | 4/5 |

## Scope and procedure

The reviewed submission is the 19-page `submission.pdf`, SHA-256 `56755f5ab29d58880315c945115e010815a038b3a7f53154cb825ab5c485a7d0`, with its frozen text extraction. Reviewers received independent expertise assignments and the restriction against earlier rounds and author planning documents. The available concurrency limit required waves. A final audit found earlier-round comparisons in several on-disk reports; those versions were excluded and replaced with a restored independent report or fresh independent assessments. The retained A–F reports are the basis of this decision. An additional `reviewer-G.md` appeared in the shared directory; it was not commissioned by this editor and was left unread and untouched. No earlier-round file was opened for this editorial assessment.

I applied the receiving-code-review procedure by checking criticisms against the current paper, source declarations, data and primary references rather than treating a review as authoritative. The ledger below covers all 13 numbered major weaknesses in the retained reports. Source inspection and executable tests do not constitute an independent kernel replay: no full Isabelle build was run, as requested. The paper and formalization were not edited.

## Verification ledger

IDs refer to numbered items under each review's Major weaknesses heading.

| Issue | Classification | Editor's checked reason |
| --- | --- | --- |
| A1 — incomplete public artifact | **VALID** | §9 acknowledges the gap; the current Zenodo ZIP contains only an empty `vendor/td-verification/` directory, while `TD_Solver_Bridge.thy:2` imports the solver. |
| B1 — context-specific guarantee lost at reporting | **PARTLY VALID** | `src/Executable_Surface/CLI/Analysis_Report.thy:517` bounds each indexed collection by the node union; this is already disclosed in §5 and does not invalidate the scoped theorem. Clarify the abstract/figure, but do not require a new theorem. |
| B2 — context evaluation hides cost | **PARTLY VALID** | §7 pools the configurations and omits aggregation details; existing data support disaggregation, but a second benchmark and four-policy instrumentation are useful suggestions rather than necessary new research. |
| B3 — operational novelty/overlap example | **PARTLY VALID** | The cited predecessors have genuine semantic overlap, and `src/Examples/Sign/Example_Sign_DG_Overlapping_Enter.thy:93` supplies a useful example; absence of that example is an exposition issue, not evidence against the claimed composition novelty. |
| B4 — public artifact cannot substantiate composition | **VALID** | The archive misses required code and current evidence; local access permits inspection but does not establish that the cited public package can be rebuilt. |
| C1 — incomplete `post_bounded` and misplaced entry law | **VALID** | `Basics_side.thy:588,619` includes local and side-effect bounds; `DG_Spec_Sound.thy:337` has transfer/combine laws, while routed entry witnesses occur at `Routed_Context.thy:86`. Table 1 conflates these. |
| D1 — equations-to-cover construction too implicit | **VALID** | §4.2 lists contributions verbally; the publish/read/combine construction exists at `src/Abstract_Interpreter/Framework/Context/Routed_Call_Programs.thy:143` and deserves a compact displayed counterpart. |
| D2 — source/observation interface too implicit | **VALID** | §5 names frames and lifted runs but does not expose the rules determining the endpoint; `VIMP_Proc.thy:71,140,153` and `Elaborated_Compilation.thy:791` provide a short precise interface. |
| D3 — no reviewable artifact for main claim | **PARTLY VALID** | The public distribution is incomplete, but the locally supplied supplementary sources include the solver and permitted direct review. The stronger suggestion that no reviewable supplement exists is not established. |
| E1 — missing public solver dependency | **VALID** | My independent API/ZIP checks reproduce the empty dependency and unauthenticated HTTP 404; this establishes public unavailability, not whether the repository is private or nonexistent. |
| E2 — archive does not match current experiments | **VALID** | The checked ZIP lacks `paper/` and current context claims; locally reproduced outputs do not repair the archived version mismatch. |
| F1 — public archive does not support submission | **VALID** | The distribution gap is real; inability to redistribute legally remains UNVERIFIED and is not presumed. |
| F2 — title's context guarantee ends before individual rows | **PARTLY VALID** | The row limitation is real, but Theorem 2 remains context-indexed and Theorem 3 explicitly certifies node-level results; the title is defensible with the stated scope. |

## Evidence checks and limits

**Formal statements.** I checked the principal cited locations and the assumptions used by the criticisms. `src/Executable_Surface/CLI/Analysis_Certified.thy:196` has the initial-store, finite source-run and returned-answer premises and concludes both existence of an observed node and coverage at every observed node. `src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:585` retains entry coverage and the initial global-environment bound. `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:58` really has the broad cross-edge Return condition. These are not omissions to repair in the formalization.

The missing detail in Table 1 matters: the return proof at `Routed_Context.thy:534` uses the global publication bound as well as the returned local-value bound. Transfer soundness at `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy:345` interprets outputs in the prior global environment joined with publications. Section 4.3 already states the stronger certificate, which makes the table an internal exposition inconsistency rather than evidence of an unsound solver bridge.

The dynamic part of the bridge is also present. `src/Analyses/Shared/Result/DG_Live_Unknowns.thy:186` obtains a callee-result dependency for non-bottom entry; lines 291–303 use it to obtain callee-entry coverage. The definition of `live_unknowns` begins at line 230, not line 227 cited in A's table. A's substantive description is correct; its anchor is three lines early. No other checked anchor changed the editorial outcome. The `at_node` relation at `src/Program_Model/Compile/Elaborated_Compilation.thy:791` requires an actual lifted run and simulation, so it is not an arbitrary assignment of a convenient node to a residual command.

**Execution and numbers.** E independently reproduced all 13 paper-specific claim outputs, checked all 54 distinct `isaname` references, and confirmed the scoped no-`sorry`/`oops` claim. The unrelated vendor theory with admissions is outside the imported closure and is not a contradiction. Independent theory/line counts agree with Table 2; proved-statement totals were reproduced using the repository's syntax-aware counter, not a second independent parser. This is adequate consistency evidence, with that limitation recorded. The paper builds; E also completed a fresh LaTeX build. These successes say nothing by themselves about replay of all Isabelle proofs.

I independently reduced the pinned profiling snapshot: 380 fixtures produce 5,700 configuration rows; 165 invalid rows account for 11 fixtures, leaving 369 fixtures and 5,535 cases, of which 5,514 succeed and 21 time out. All 21 timeouts use entry-state contexts. `scripts/profile_corpus.py:189` uses per-case medians for successful repetitions and returns early on a failed repetition. The reported quantiles summarize successful cases; they are not quantiles over all 5,535 cases. The measurements were not rerun as a campaign.

Both E and I replayed the historical congruence defect with the documented macOS header adaptation at Goblint revision `8440ff01c6f63e9480b578e79bb7dc28893ed5e1`. The adaptation replaces only the Goblint header include with the check declaration. The incorrect success for `c % 2 == 1` and failure for `c % 2 == -1` reproduce. The primary [fix PR 1161](https://github.com/goblint/analyzer/pull/1161) was checked through GitHub's API. This is an adapted reproduction of a historical case, not a claim about the current Goblint release.

**Public release.** The [Zenodo version record 23484950](https://zenodo.org/records/23484950), resolved through the concept-record API, serves the v2.2.0 ZIP with MD5 `882281371606554a59e2a77b9bc1cf14`. I verified that checksum and inspected the archive members. Besides the solver source, it lacks the paper tooling, flavors fixtures and profiling script. The configured solver repository returned HTTP 404 through the unauthenticated API. The complete artifact therefore does not yet merit Available, Functional or Reusable recommendations, although the prepared local CLI is functional on the tested claims.

**References.** I checked the primary manuscripts underlying B3/F's comparison: Bertrand Jeannet and Wendelin Serwe, *Abstracting Call-Stacks for Interprocedural Verification of Imperative Programs*, AMAST 2004, LNCS 3116, 258–273, DOI [10.1007/978-3-540-27815-3_22](https://doi.org/10.1007/978-3-540-27815-3_22), [author PDF](https://pop-art.inrialpes.fr/people/bjeannet/publications/amast04.pdf); Frédéric Dabrowski and David Pichardie, *A Certified Data Race Analysis for a Java-like Language*, TPHOLs 2009, LNCS 5674, 212–227, DOI [10.1007/978-3-642-03359-9_16](https://doi.org/10.1007/978-3-642-03359-9_16), [author PDF](https://davidpichardie.github.io/papers/tphols09.pdf). Their stack/data separation and context-parameterized certified constraints justify a specific comparison, not an equivalence claim.

I also checked B's cited primary sources for [a posteriori soundness](https://matt.might.net/papers/might2009aposteriori.pdf), [trace partitioning](https://www.di.ens.fr/~mauborgn/publi/toplas29.pdf), [AAM](https://arxiv.org/abs/1007.4446), [Verasco](https://xavierleroy.org/publi/verasco-popl2015.pdf), and [local traces](https://arxiv.org/abs/2108.07613). These support the limited comparisons made; no reviewer established an equivalent earlier end-to-end mechanization. Seidl–Fecht's 2000 comparison has verified bibliographic metadata and abstract-level relevance, but full technical correspondence remains UNVERIFIED. Adding it is suggested, not a reason to reject. No conclusion depends on unchecked equivalences or on the absence of literature beyond this search.

## Consensus and individual issues

All six reviewers identify the public artifact gap. A/C identify the same incomplete side-effect/contract description. A/D/F ask for the dynamic dependency and call-construction bridge to be explained more concretely. B/D/E/F request interpretable context-cost reporting. B/F ask for the context-row boundary to be visible wherever the result is summarized. A/B/D/F independently question the overbroad shared-heap sentence.

D's source-observation request is worth acting on even though the formal statements match: readers need to know what the theorem observes. C's Boolean comment is also valid: `src/Program_Model/VIMP/VIMP_Expr.thy:119` gives a pure total denotation, not an operational evaluation-order theorem. E correctly distinguishes the proved `congruence_mod_sound` lemma (`src/Analyses/Congruence/Congruence_Arithmetic.thy:766`) from the generic locale obligation it discharges. I rendered page 11 and confirmed D's Figure 2 collision: the trace-hook box overlaps the proved-region heading. These are small, concrete corrections.

## Claims and demands not adopted

- **INVALID as a rejection argument:** solution-dependent contexts make soundness circular or vacuous. Totality is a substantive obligation over concrete reached calls, and the source theorem plus non-vacuity example constrains observable executions (`Routed_Context.thy:104`; `Example_Non_Vacuity.thy:151`). F correctly rejects its own attempted attack.
- **INVALID as an inference:** absence of a row-specific theorem makes Theorem 3 false or the title untenable. The submitted guarantee is explicitly node-level, alongside a separate indexed theorem. Clarification is required; scope expansion is not.
- **Not established:** the supplied supplement cannot be reviewed, the solver has a licensing prohibition, or the inspected proofs fail a clean build. Public incompleteness supports none of these stronger assertions. A clean distributed proof build remains outstanding.
- **Not required:** a full new benchmark campaign, a general precision ordering, an unconditional solver-termination theorem, or a new heap/concurrency model. The evidence and explanation requests below are narrower.

## Prioritized changes

1. **R1 — required, release and §9:** archive the exact complete development and current evidence, pin dependencies and a version DOI, document reproduction, and verify the distributed package. Correct availability wording until this is achieved.
2. **R2 — required, §4.1–4.2/Table 1:** state local and side-effect bounds, the publication environment, and the correct ownership of entry/routing obligations. Explain suppressed parameters and table scope.
3. **R3 — required, §3.1/§4.2–4.3/§5:** expose the call/seed equations, dynamic dependency bridge, representative source rules and `at_node` interface. A compact construction and worked call suffice; a second prose proof development is unnecessary.
4. **R4 — required, §7:** make denominators, repetitions, censoring and policy/domain costs explicit using existing data; identify the recursive example and external-check selection sufficiently for reproduction.
5. **R5 — required, abstract/Figs. 1–2/§5–6/§9/front matter:** preserve the context-row boundary, repair the figure collision, define necessary terms, and correct the Boolean, locale-obligation, representation and heap wording. Remove journal-inappropriate publication placeholders.

Suggested additions are a displayed overlapping-entry example (§3–4), context/work counts for Table 3 when readily available (§7), a narrowly supported Seidl–Fecht comparison (§8), and visible return values in Figure 1. The accompanying revision plan gives concrete sources, effort estimates, and draft responses. Acceptance should depend on satisfying the scoped requirements and checking the complete distributed artifact, rather than expanding the research claims.
