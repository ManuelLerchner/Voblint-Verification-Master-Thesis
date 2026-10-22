# Review G: "End-to-End Soundness of a Context-Sensitive Goblint-Style Analyzer in Isabelle/HOL"

Reviewer expertise: verified static analysis (Verasco/CompCert-style value analyses, Coq and Isabelle abstract interpreters).

Material used: submission.txt/PDF; `src/` (spot-checks listed below); `vendor/td-verification/`; the CLI at `_build/default/cli/voblint_main.exe`, run on the paper's examples and on probes I wrote. I did not read the earlier reviews or the planning documents.

## Summary

The paper connects a small-step semantics of VIMP, a scalar imperative language with globals and recursive procedures, to a Goblint-style side-effecting constraint system with calling contexts, solved by the top-down solver whose partial correctness Tilscher et al. verified. It has three layers:

1. **Activation traces and a coverage contract.** One trace per procedure activation, linked to its caller. A context policy, given as a relation, admits traces to contexts. Five local obligations (Init, Intra, Call, Return, Total) on a cover indexed by node and context bound the context-indexed collecting semantics A(v,c) (Theorem 1). Total ensures that every valid trace carries some context.
2. **A routing layer.** Every post-solution of the routed equations meets the contract, provided two routing conditions relate the abstract routing function to the concrete policy (Theorem 2). The solver enters only through its `part_post_solution` certificate, and the backward-closed solved set is restricted to a forward-closed "live" subset.
3. **An end-to-end theorem.** It is stated about the exported constant `run_voblint` (Theorem 3). For every returned report, every store reached by a finite source run lies in the node collecting semantics at each node where the run is observed, is described by some state of the report there, and satisfies every definite verdict there.

The evaluation is short: non-vacuity instances, an obligation counterexample, one context-precision table, Monniaux's tutorial examples, and running times.

## Recommendation

**For JAR: major revision.** In its current form this is a well-executed 19-page ITP paper (it is set in LIPIcs/ITP format, p. 1). It is not yet a journal article. As an ITP submission I would rate it weak accept to accept with minor revisions.

**Confidence: 4.**

## Strengths

S1. **The end-to-end theorem is about the shipped artifact and has few premises.** I checked `run_voblint_source_sound` (`src/Executable_Surface/CLI/Analysis_Certified.thy:196-259`) against the statement on p. 10.

- It matches the paper exactly.
- Its only premises are an initial store, a finite `pstep` run, and `run_voblint config p = Analysed res`.
- Termination, well-formedness and solved-set coverage are absorbed through the definition of `run_voblint` (`Analysis_Run.thy:475-482`: the malformed and invalid-configuration branches return other constructors) and through `live_unknowns_cover`.

Few verified analyzers state their guarantee about the extracted constant with this little residue, so this is a real strength.

S2. **The coverage contract is small, generic and machine-checked.**

- The locale `activation_coverage` (`src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:43-64`) has exactly the five obligations listed on p. 6.
- `activation_collect_sound` (`src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy:34-50`) is a short corollary of `valid_activation_trace_covered_at`.
- The proof idea on p. 6 (an invariant over the caller chain, with Total used in both the call case and the return case) faithfully describes `call_covered` and `return_covered` (lines 123-208).

S3. **Necessity is shown by checked counterexamples.**

- `total_dropped_unsound` (`src/Examples/Capstone/Example_Non_Vacuity.thy:610-660`) meets the other four obligations and misses a reached store. This shows that Total is necessary.
- `unpaired_entry_cover_unsound` (same file) shows why enter must return paired resume/entry states, a point Goblint users rarely see justified.
- `unknown_everywhere_sound` (line 290) is stated honestly as a limit of what soundness means.

S4. **The solver interface is clean.** The `certified_solver` locale (`src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:26`) assumes four facts. The live-unknowns bridge (`src/Analyses/Shared/Result/DG_Live_Unknowns.thy:230-310`) turns the solver's backward certificate into a forward-closed set using only structural reachability (`prog_node_reaches`). The paper correctly says this proves no reachability of the result (p. 9).

S5. **The paper is careful about claims.** It separates proved, trusted and argued. It names the trace hook as trusted (Fig. 2; `Solver_Trace.thy:31`; `Trace_Run.thy:142`). It states the semantic deviations from C (p. 11) and the meaning of REFUTED, DEAD and warnings (pp. 10-11). It also says that the guarantee is per program point and not per context (p. 10). A verified-analysis paper rarely states its limitations this explicitly.

S6. **The evaluation reproduces.** I reproduced Table 3 for all four context policies with the CLI (UNKNOWN [1,12] / UNKNOWN [1,12] / PROVED [2,2],[1,1] / PROVED). I also reproduced the Figure 1 verdicts (none: UNKNOWN with a=[-inf,6]; entry-state: both PROVED).

## Major weaknesses

**M1. The headline object, the context-indexed semantics, is a proof device that the delivered theorem does not use.**

- The paper concedes this: "The contexts appear only inside the proof ... The guarantee is therefore per program point" and "No theorem about run_voblint certifies the row of an individual context" (p. 10).
- At the report level, `context_sound` (`Analysis_Report.thy:517-524`) only bounds each A(v,c) by R_res(v), the union over all contexts.
- The end-to-end statement (Theorem 3) is therefore exactly what a context-insensitive soundness proof against `node_collect` would give.

This makes the case for activation traces rest on the claim that they make the proof easier than a frame-stack invariant. The paper concedes that it did not try this alternative: "The obvious alternative, which we did not implement, is the graph semantics itself, with a frame stack whose frames carry a ghost context" (p. 12).

For a journal contribution I would expect one of two things:

- (a) the per-context theorem (listed as future work, p. 16), which would make contexts part of the guarantee; or
- (b) a concrete argument, ideally a measured comparison or at least a worked proof obligation, showing what the ghost-context stack invariant would require and where it breaks.

Without either, the novelty claim on p. 2 ("What has not been mechanized ... is the connection from a source semantics through such a context-indexed semantics to a side-effecting constraint system") overstates the role of the middle layer. The middle layer is internal scaffolding, not part of the delivered guarantee.

**M2. For entry-state contexts the indexing depends on the analysis result, so Theorem 1/2 says little per context.**

- `routed_entry_context_rel` (`Routed_Context.thy:703-712`) defines the admitted contexts from the solved valuation sigma.
- `run_policy` for `Ctx_EntryState` reads them off "the program's own solve" (`Analysis_Report.thy:527-547`).
- The paper acknowledges that "A(v,c) is relative to the analysis that produced sigma" (p. 8).

So for the policy that matters most for precision (it is the one that proves Table 3 and Figure 1), the per-context inclusion A(v,c) ⊆ cover(v,c) holds largely because the policy was chosen to make it hold. The comparison with a posteriori soundness [20] is apt, but it should be developed further. The paper should state:

- which part of the entry-state argument is non-trivial (I believe it is Total via `routing_total` plus the paired-entry adequacy);
- that a policy built from an unsound solution would not make the theorem vacuous, because C is policy-independent (this is said, p. 8);
- and that an analysis with a wrong `enter` would be rejected at the obligation `routing_adequate` and not absorbed into the policy.

A short counterexample theorem for the last point would help, in the style of the existing ones: a wrong enter, the policy built from it, and a failed obligation.

**M3. Termination is a severe practical limitation, and the paper does not illustrate it.** The paper says termination is "a per-program fact, established by running the solver" (p. 16) and that entry-state contexts "need not be finitely many" (p. 15). It does not say how easily the analyzer diverges. A six-line probe:

```text
fun f(n) { r = f(n + 1); return r; }
fun main() { a = f(0); __voblint_check(a == 0); }
```

under `--analysis interval --context entry-state` gives "analysis did not finish within 10s (killed)". The same program with `f(500)` and a decreasing argument answers PROVED a=[500,500] after creating about 500 contexts. Goblint offers context widening for exactly this case. Its documentation says `--enable ana.context.widen` widens the contexts functions are analyzed in, to avoid stack overflows from recursive functions (<https://goblint.readthedocs.io/en/latest/user-guide/running/>).

Section 7 hides the issue in "21 cases exceed the 30 s limit" (p. 14) without listing them. For JAR, the paper should:

- report which fixtures and configurations time out and why;
- state that unbounded entry-state contexts make the analyzer diverge on simple non-terminating recursion;
- and discuss whether a context-widening or context-limiting policy fits the framework. The relational policy and Total suggest it might, since a widened context is still an admitted context.

**M4. The evaluation evidence for "the obligations have force" is thin, and one item is close to tautological.** `prefix_congruence_mod_unsound` (`Example_Non_Vacuity.thy:357-369`) assumes that an operator returns the constant 1 on (1+2Z) mod 2. It then shows that this contradicts the soundness law at -5. This is a five-line arithmetic fact. It shows that the law is stated with truncating remainder. It does not show that the framework would have caught the Goblint defect in a meaningful sense: any correct statement of soundness rejects any unsound operator.

The paper also misattributes the law. On p. 13, `congruence_mod_sound` is called "an assumption of the locale through which the domain is registered". In the theories, `congruence_mod_sound` is a *lemma* about the shipped operator (`src/Analyses/Congruence/Congruence_Arithmetic.thy:766`). The locale assumption is `mod_sound` of `sound_arith_ops` (`src/Analyses/Shared/Nonrelational/Abstract_Arithmetic.thy:65,120`).

Stronger evidence would come from the defects that are specific to the contribution. For example, an interprocedural or context-routing bug in Goblint's history that one of `routing_adequate`, `routing_total`, the pairing condition or Total rejects. The paper itself notes "This defect involves no contexts" (p. 13), which undercuts its relevance to a paper about contexts.

**M5. Precision is shown only by examples, and the comparison with Goblint is deferred to the thesis.**

- Table 3 is one program. Monniaux's examples are reported as "proves five" of eight (p. 13) with no table.
- The comparison with Goblint is entirely deferred ("The thesis [17] compares these verdicts with Goblint's", p. 14).

A journal version should include, from the existing regression corpus, a table of verdicts per context policy and domain, aggregated over the 369 fixtures the paper already runs for timing. It should also include the Goblint comparison with revision and flags. Without these, readers cannot judge whether the verified analyzer is useful or only sound. The paper explicitly says speed was not a goal; precision is the remaining measure of usefulness.

**M6. The artifact cannot be built from public sources.** "The vendored solver [33] is not yet public, so the theories cannot yet be built from public sources alone", and the archived version "predates the context-policy claims and the profiling data used here" (p. 16). For JAR, which has no deadline pressure, this is a blocking reproducibility issue. The vendored solver also carries "four changes made for this work ... a removed assumption, and added facts" (p. 11). Readers should be able to inspect at least the removed assumption, because it affects the trust argument. Please state what it was.

**M7. Related work misses directly relevant mechanizations and understates one it cites.**

- **Breitner's Shivers' Control Flow Analysis** (AFP, 16 Nov 2010, <https://www.isa-afp.org/entries/Shivers-CFA.html>) is an Isabelle/HOLCF formalization of a control-flow analysis with correctness proofs. It is the closest Isabelle precedent for a context-sensitive analysis in the k-CFA lineage (whether it treats contours with k>0 is UNVERIFIED). It is absent from Section 8.
- **Darais and Van Horn's constructive Galois connections** (ICFP 2016, mechanized in Agda; arXiv 1511.06965) are relevant to the "Verified analyzers" paragraph, since the paper discusses mechanized calculational derivations of interpreters.
- **Lammich and Müller-Olm [16].** The AFP abstract says they verify *soundness and precision* of a constraint-system-based analysis for programs with procedures, thread creation and monitors, against a flow-graph operational semantics. The submission says only that "interprocedural analyses have been verified [16, 36]" (p. 15). It should acknowledge that [16] proves a precision result, which Voblint does not ("No general precision ordering or completeness property is proved", p. 16). This is a dimension along which prior Isabelle work is stronger.
- **Dabrowski and Pichardie [6].** The paper says their analysis "is specified by constraints that no solver computes" (p. 15). This needs a precise statement of what [6] extracts or computes. UNVERIFIED: I did not re-read [6]. A claim about the absence of a solver in prior work needs a quote or a section reference.

## Minor comments

1. p. 4, return rule. The rule "takes some call edge from the caller's call site into p. It does not require the edge through which the callee was entered" (`Activation_Trace_Def.thy:120-130`). As a result, the Return obligation (p. 6) must quantify over p' and over the entered store, and `calls_unique` must repair it (Table 1). The paper should explain why the trace rule was not tied to the entering edge. That would remove one hypothesis and the p' quantifier.
2. p. 8, Theorem 2. The cover is described as "γ(σ(v,c),ρ) on solved unknowns and ∅ elsewhere". In `Routed_Context.thy` the cover is `γ_M (sg (Inl (v, ctx)))`, a reader over `sg`, with `sg_uncov` giving the empty set. Please mention the reader, or define it once.
3. p. 9. "These facts are proved for the vendored solver under each of its five update rules (td_certified_solver)". The paper should give the five rules by name. They are visible as CLI options (`join|per-origin|warrow|warrow-per-origin|bounded-narrowing`), but p. 9 names only three kinds.
4. p. 11. "Neither Voblint nor the imported solver theories contain sorry". This is correct for the seven imported theories: `TD_side_Interface`, its transitive imports, and `Warrowing`. But `vendor/td-verification/TD_plain_warrow.thy:354,411` contains two `sorry`s. The file is not imported by Voblint or by `Solvers.thy`. Say "the vendored directory contains an unbuilt theory with sorry", or remove the file from the artifact.
5. Table 2 recount. Lines and theory counts match my count exactly (e.g. Abstract_Interpreter 67 theories, 21,212 lines). My regex for proved statements gives 1,037/620/395 against 1,033/619/393 for Abstract_Interpreter/Analyses/Examples. The difference is probably due to the counting method; please state the counting script.
6. p. 11, OCaml size. My `wc` over `cli/**/*.ml` excluding `voblint.ml` gives 4,997 lines against 4,919 claimed. Also `cli/result/context_graph.ml` and `value_symbols.ml` are not obviously "printing". Please confirm that no handwritten module computes or filters verdicts. The verdict strings come from the generated `Check_Proved` constructor (`cli/result/result_text.ml:21`), which supports the trust claim.
7. p. 5. Calling Resume the analogue of the "binary rule for acquiring a lock" is suggestive but unexplained. Give one sentence on what is incorporated in each case.
8. p. 7. Paired entries are justified by soundness. Give the counterexample by name (`unpaired_entry_cover_unsound`) in Section 4.1. It is the best motivation for `entry_pairs_cover`.
9. p. 13. "Facts about one fixed program are proved by eval, which ... also trusts the code generator". Correct and appreciated. Please mark in Section 7 which of the non-vacuity theorems use `eval` (e.g. `ret_intra`, `nv_analysed`).
10. Figure 1 caption. "States are analyzer output with the warrowing update rule". The CLI without contexts shows a=[-inf,6] rather than ⊤-ish intervals. Saying what the context-insensitive states are would make the "joins both calls" claim visible.
11. p. 10. "every global is zero as for C objects of static storage duration and locals are unconstrained". Note that callee locals start at 0 (p. 11). This asymmetry deserves one sentence of motivation: it makes `main` locals fully nondeterministic, but callee locals deterministic.
12. Reference [30] (FM 2026), [33] (NFM 2026) and [34] (JAR 70(2), 2026). I could confirm only that the title of [33] appears on Seidl's TUM publication page. Venue details are UNVERIFIED.

## Questions for the author

1. Did you attempt the per-context report theorem (Section 9)? What blocks it: the report construction, the mapping from report contexts to solver contexts (`map_context_policy`), or the entry-state policy's dependence on sigma?
2. Can a context-widening policy, as in Goblint, be expressed as an admissible relation satisfying `routing_adequate` and `routing_total`, so that the f(n+1) example terminates without changing the semantic layer?
3. Which assumption did you remove from the vendored solver, and why is it not needed?
4. Which of the 21 timed-out cases are genuine non-termination of the solve, which are slow convergence, and which are list-based data-structure cost?
5. Is there a Goblint defect involving contexts or enter/combine (not domain arithmetic) that one of your routing obligations would reject?
6. Why does the trace return rule not record the call edge used at entry? Recording it would make `calls_unique` and the p' quantifier in Return unnecessary.

## Spot-checks performed (claim -> source)

| Paper claim | Source | Result |
| --- | --- | --- |
| Theorem 3 statement (p. 10) | `Analysis_Certified.thy:196-208` | matches verbatim |
| No termination or well-formedness premise | `Analysis_Run.thy:475-482`, `Analysis_Certified.thy:17-21` | confirmed |
| Five obligations (p. 6) | `Activation_Trace_Abstract.thy:43-64` | confirmed |
| Theorem 1 | `Activation_Backbone.thy:34` | confirmed |
| Datatype and four trace rules (p. 4) | `Activation_Trace_Def.thy:43-130` | confirmed, including the untied return edge |
| Routing conditions and Table 1 | `Routed_Context.thy:56-127` | confirmed |
| Theorem 2 | `Routed_Context.thy:585` | confirmed |
| Entry-state policy formula (p. 7) | `Routed_Context.thy:703-712` | confirmed |
| Live unknowns (p. 9) | `DG_Live_Unknowns.thy:230-310` | confirmed |
| `context_sound` is union-level (p. 10) | `Analysis_Report.thy:517-524` | confirmed |
| Trace hook trusted (p. 11) | `Solver_Trace.thy:31`, `Trace_Run.thy:142` | confirmed |
| Total needed | `Example_Non_Vacuity.thy:610` | confirmed |
| `congruence_mod_sound` is a locale assumption | `Congruence_Arithmetic.thy:766` | **incorrect**: it is a lemma; the assumption is `sound_arith_ops.mod_sound` |
| No sorry | grep | true for the imported closure; one unbuilt vendored file has two |
| Table 3 | CLI run | reproduced |
| Figure 1 verdicts | CLI run | reproduced |
