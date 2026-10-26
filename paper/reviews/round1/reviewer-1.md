# Review: "Calling Contexts Made Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL"

Reviewer 1. Expertise: Isabelle/HOL, mechanized semantics, proof engineering.

I read the submission (text and PDF) and checked the supplementary development in `src/` and `vendor/td-verification/`. Page numbers below are the LIPIcs page numbers printed on the submission (1:1 to 1:17).

## Summary

The paper describes Voblint, an Isabelle/HOL development that connects the verified side-effecting top-down solver of Tilscher et al. [26] to a small imperative language (VIMP) with recursive procedures. Activation traces are its central device: an inductive set of tree-shaped traces in which each procedure activation records the activation that created it. A context policy, a relation from call descriptions to sets of contexts, gives these traces calling contexts and yields a context-indexed collecting semantics A(v, c). The paper states a five-obligation "coverage contract" (Init, Intra, Call, Return, Total) that is sufficient to over-approximate A (Theorem 1). It shows that every post-solution of the generated context-routed equations meets the contract under analysis, routing, and graph-shape assumptions (Theorem 2). It then proves an end-to-end theorem about the exported analyzer function `run_voblint`: every store reached by a finite source execution from a zero-global initial store lies in the report's semantics and satisfies its definite verdicts (Theorem 3). The development has 212 theories, about 39k lines of formal text, and code generated to OCaml. Evaluation consists of non-vacuity instances, a counter-model for dropping Total, a lemma rejecting a historical Goblint congruence bug, a precision comparison with Goblint on Monniaux's "flavors" programs, and running times.

## Recommendation and confidence

**Major revision.** Confidence: **4** (I know Isabelle mechanizations of semantics and abstract interpretation well. I checked the theories but did not rebuild them.)

The engineering is real. As far as I checked, the theorems exist and say roughly what the paper claims. The proofs I looked at are well structured. As a journal paper on interactive theorem proving, the submission has two problems. First, its headline claim, a concrete meaning for calling contexts, is weaker at the level of the shipped tool than the title and contribution list suggest. Second, the mechanization contribution is under-argued: design alternatives, proof-effort data, and transferable lessons get about one page. The submission is also still a 17-page LIPIcs/ITP conference paper. A JAR article should give the deferred technical content (routing, compiler simulation and elaboration, the domain framework) the space it needs.

## Strengths

1. **A clean, checkable contract.** The `activation_coverage` locale (`Activation_Trace_Abstract.thy`, l. 43) is small, mentions no domain or solver, and is proved by one rule induction with an explicit invariant (`trace_covered`, `caller_chain_covered`). The paper's description of the proof of Theorem 1 (p. 1:6) matches the theory. The Return case recovers the creating caller through `caller_of` and `activation_context_rel_caller_entryE`.
2. **Counter-models for the contract.** `total_dropped_unsound` (`Example_Non_Vacuity.thy`, l. 610) exhibits a cover that satisfies Init/Intra/Call/Return, fails Total, and misses a reached store. The same theory contains counter-models for two other weakenings. Showing that each obligation is needed is good practice and rare in this literature.
3. **The end-to-end theorem is about the exported constant.** I checked that `run_voblint` appears in the `export_code` list (`Voblint_Codegen.thy`, l. 135). `run_voblint_source_sound` (`Analysis_Certified.thy`, l. 196) has no termination, coverage, or well-formedness premise, for the reasons the paper gives on p. 1:10. The first conjunct (∃v. … ▷ v) prevents vacuity through an empty observation relation, which is a careful touch.
4. **Solver isolation.** The `certified_solver` locale (`TD_Solver_Bridge.thy`, l. 26) has four assumptions. It is discharged once for all update rules (`td_certified_solver`, `Globals_Rule.thy`, l. 157), as the paper says on p. 1:8. This is a good, reusable interface.
5. **Claim discipline in prose.** The paper keeps PROVED, REFUTED, DEAD, and arithmetic warnings separate (p. 1:10), and labels its evaluation items as machine-checked, empirical, or single-program witnesses (p. 1:12–13). It is candid that `unknown_everywhere_sound` holds.

## Major weaknesses

### M1. At the level of the shipped tool, the per-context guarantee is weaker than the framing suggests (Title; Section 1 contributions, p. 1:2; Sections 4.2 and 5, pp. 1:7–1:10)

The introduction motivates the work with per-context claims: "An analysis whose contexts record the argument claims the result 6 in one context and 5 in the other… A per-context claim therefore has nothing to be checked against" (p. 1:2). The reader expects the paper to certify such claims. Two facts in the development cut against this.

(a) **The shipped per-context statement bounds each context by the union over contexts.** `context_sound` (`Analysis_Report.thy`, l. 517) states

> `∀v c. A_{…,adm,rc,…} v c ⊆ R_res v`

where `R_res v = ⋃ d ∈ report_states_at res v. γ_res d` (l. 41) is the union over all contexts' states at v. `run_voblint_contexts` therefore does not say that the report's state for context c₁ = [5,5] bounds A(v, c₁). The same holds for Theorem 3. The paper admits this indirectly ("The contexts appear only inside the proof", p. 1:10), but this conflicts with the motivation and with contribution 1. The report lists "the solved states of every solved context" (p. 1:9), and none of those per-context states is individually certified by a theorem about `run_voblint`. The context-level result exists only in the generic layer (Theorem 2, about σ).

(b) **For entry-state contexts, the "concrete" policy is defined from the analysis result.** `run_policy` (`Analysis_Report.thy`, l. 531) instantiates the entry-state policy with `admitted_contexts`. That definition (`DG_Analysis.thy`, l. 598) is built from `sol_env 𝒢 p` and `sol_global`, the logical solver's result on p. The paper says so in one sentence: "For entry-state contexts, adm is defined from the routing itself… The policy may depend on the analysis result without circularity, because the final guarantee concerns C" (p. 1:8). This sentence undercuts "a concrete semantics of calling contexts". For the one shipped policy that needs the relational generality, A(v, c) is not analysis-independent. It is the set of stores the analysis itself chose to put in c. The per-context inclusion A(v, c) ⊆ γ(σ(v, c)) then says little beyond the context-insensitive inclusion. The unit and call-string policies are functions (`context_policy_of_fun`), and for them the relational form is unnecessary (p. 1:11 says so).

(c) **Total, and with it ⋃_c A(v, c) = C(v), is relative to a cover.** `call_context_total_on cover adm 𝒢 g` quantifies over stores in `cover`, and `node_collect_eq_Union_activation_collect` is a theorem inside the `activation_coverage` locale. "Splitting the collecting semantics by context loses no store" (p. 1:2) is therefore a property of the semantics together with an analysis result, not of the semantics alone.

I do not think this invalidates the work. The context-indexed semantics seems indispensable as a *proof device*: a context-sensitive table is not a post-solution of the monovariant equations, so `node_collect_semantic_postfix` cannot be applied directly. That is a fine and defensible contribution. The paper should, however, say exactly this. One of two revisions is needed:

- prove and state, for `run_voblint`, the per-context theorem A(v, c) ⊆ γ_res(state of the report at (v, c)); or
- reframe contribution 1 and the title as a proof technique whose output is a context-insensitive guarantee, and discuss explicitly what A means when adm depends on σ.

The only multi-alternative instance is the example `ov_two_contexts_admitted` (`Example_Sign_DG_Overlapping_Enter.thy`). The shipped `admitted_contexts` uses a single alternative (`[entry_alt …]`), so the justification "A set, because Goblint's enter may return several alternatives" (p. 1:5) is not exercised by the tool.

### M2. Design choices and alternatives are under-argued for a journal paper on mechanization (Section 6, pp. 1:10–1:11)

The CPP/ITP criteria ask for design choices, alternatives, comparison with other libraries, and transferable lessons. Section 6 gives four short paragraphs, and only the first one names an alternative, an unpublished prototype ("whole-program executions with calls inlined"). Missing:

- **The obvious alternative to activation traces.** One could instrument the frame-stack semantics `cstep` with a ghost context per frame and prove a step invariant ("every frame's store lies in cover(node, ctx)"). This is the standard route in CompCert-style and Dabrowski–Pichardie-style developments. The paper must explain what activation traces buy over a ghost-instrumented stack semantics. One candidate answer is that a relational policy admits several contexts per frame, so a ghost value would have to be a set. Another is that the Return case needs the caller's context at call time. Without this argument, the central design decision is not justified.
- **Effort data.** There is no breakdown by layer: traces and contract, routing, domains, compiler simulation and elaboration, report, codegen. The reader cannot tell where the 39k lines went, which layer was hard, or what it costs to add a domain or a context policy. "Each domain registers with one locale interpretation per context policy" (p. 1:11) invites the question of how many lines such an interpretation takes.
- **The compiler correctness and elaboration story.** A non-injective map from residual commands to nodes, solved by elaborating to annotated commands (`at_node`, `csim_point_compile_prog`, p. 1:9), is a genuine and transferable proof-engineering point. It gets four sentences.
- **Comparison with existing Isabelle libraries.** The paper should compare with Nipkow–Klein's `Abs_Int` (reused how? adapted how?), with the AFP solver entry, and with Jinja/JinjaThreads-style frame stacks. "Comparison with other libraries" is a standard CPP criterion and is absent.
- **Proof-assistant feedback.** The feedback is generic. Lists in generated code are well known. The domain-predicate/`solve_c` pattern is the standard partial-function idiom. The linter is mentioned without any description. Given the GenAI declaration (p. 1:15), the most novel lesson this paper could offer is what AI-generated Isar proofs did to the development's structure, robustness, and maintenance. Section 6 says nothing about that beyond "human review concentrated on the definitions".

### M3. Theorem statements are not always presented faithfully or readably (Sections 3–5)

I spot-checked eight cited facts against the theories:

| Paper claim | Theory | Verdict |
| --- | --- | --- |
| `activation_trace` datatype (p. 1:4) | `Activation_Trace_Def.thy` l. 43 | Verbatim. |
| `valid_activation_trace` rules (p. 1:4) | ibid. l. 100 | The paper's Resume rule drops the call-edge premise `(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) ∈ calls g` and the option (`caller_of t'' = Some t'`). Both appear only in prose. Acceptable, but the rule as typeset is not the rule. |
| Theorem 1, `activation_collect_sound` (p. 1:6) | `Activation_Backbone.thy` l. 34 | Faithful. |
| Return obligation (p. 1:6) | `Activation_Trace_Abstract.thy` l. 58 | **Not faithful.** The Isabelle obligation uses `admits_call_context 𝒢 g adm u c p' s es c'` with `p'` and `es` universally quantified. c′ may be admitted along *any* call edge from u into *any* procedure p′, not the edge into p being returned through. The paper's "c′ admitted from s" for "a call edge from u into p with continuation k" hides this. The cause is that the `ret` rule of valid traces does not tie the return edge to the callee's entry edge. Compiled CFGs restore the tie through `calls_source_unique`, an assumption of `routed_context` (`Routed_Context.thy`, l. 74). This matters for the abstract's "over an arbitrary control-flow graph": on graphs with several call edges at one node, the trace semantics admits returns through an edge the callee was not entered by. The resulting semantics is still an over-approximation, but the paper should state and discuss it. |
| Theorem 2, `activation_collect_dg_sound` (p. 1:8) | `Routed_Context.thy` l. 56–115, 585 | Stated only informally. "Side conditions on call resolution and the shape of the graph" stands for `finite (calls g)`, `calls_source_unique g`, two seed-key disjointness assumptions, `is_bot_sound`, `resolve_sound`, `comb_fwd`, and the premise `e₀ ≤ genv global_of sigma`. `routing_adequate` is more specific than the prose: one alternative of a specific `enter_runs`, with the routed entry unknown in `vars`. The cover is `γ_M (sg (Inl (v, c)))` through a reader `sg`, not γ(σ(v, c)). For the paper's second main theorem, readers deserve the actual statement or a faithful mathematical rendering. |
| `part_post_solution` (p. 1:8) | `vendor/td-verification/Basics_side.thy` l. 337 | Verbatim. `dep_L`, `eq`, `sides_of_rhs`, and the `Inl` injection are not explained. |
| `certified_solver`, `td_certified_solver` (p. 1:8) | `TD_Solver_Bridge.thy` l. 26, `Globals_Rule.thy` l. 157 | Faithful. One of the "five update rules" is a family (`Globals_Bounded_Narrowing n`). |
| Theorem 3, `run_voblint_source_sound` (p. 1:9) | `Analysis_Certified.thy` l. 196 | Verbatim. See the readability issues below. |
| `prefix_congruence_mod_unsound`, `congruence_mod_sound` (p. 1:12) | `Example_Non_Vacuity.thy` l. 357, `Congruence_Arithmetic.thy` l. 766 | The theorems exist, but the paper overstates them; see M5. |
| `sign_k2_strictly_more_precise_than_k1_at_g` (p. 1:12) | `Example_Sign_DG_CallString_K2.thy` l. 291 | Exists. It compares solutions of hand-assembled equation systems (`sign_nest_2_eqs`, solved with `TD_side_always_join_Interp_solve`), not `run_voblint` output. The paper should say so. |

Readability of Theorem 3 (p. 1:9) for a reader who does not know the development:

- The listing never explains `Π` (`prog_table`), `frs`, `→p*`, the subscripted `C_{G,g,cinit_stores G}`, or `declared_global` as a predicate on variable names. The listing then switches from C(v) (Eq. 1) to subscripted C.
- `at_node` (`Elaborated_Compilation.thy`, l. 791) is *defined* through the compiler's own simulation relation and an elaborated run. So the node v in the conclusion is whatever the proof's simulation says, and the theorem's meaning at the source level depends on trusting that relation. `run_voblint_check_sound` (l. 286) is stated in source terms: it uses `next_check residual = Some (l, e)` and a report check with the same label and expression. It is the better headline for a reader who wants a source-level guarantee. I recommend presenting it as the main theorem and Theorem 3 as the node-level form.
- Section 4.1 mentions "two combine operations" (p. 1:7) and explains one. "γ is monotone" does not say in which arguments or orders.

### M4. The trust-boundary account is incomplete (Figure 3 and "What is trusted", p. 1:10)

Figure 3 says the handwritten OCaml only parses and prints. The development also contains

> `code_printing constant trace_event ⇀ (OCaml) "Solver'_trace'_hook.emit"` (`Trace_Run.thy`, l. 142)

and the exported code equation for the solve is replaced by a traced form (`mcp_solve_c_traced [code]`, `analysis_report_of_traced [code]`). The theory text itself says this mapping "is trusted… the hook must return, raise nothing and leave the solver's values alone". Handwritten OCaml (`cli/trace/solver_trace_hook.ml`) therefore runs *inside* the verified solve, and Figure 3 must show it. The paper should also state:

- whether the CLI's verdicts come from `res_checks` and `render_report`, which are exported, and whether those are proved to agree with `report_checks`, the field the theorems speak about;
- that `Code_Target_Numeral` maps `int` to Zarith, which is trusted;
- the exact vendored delta. "A removed assumption" (p. 1:10) in a verified upstream development is the kind of change a reviewer wants to see. The vendored source is not public (p. 1:15), so I cannot compare it with [26]. For an ITP journal, a development that "cannot yet be built from public sources alone" is a reproducibility problem the authors must resolve before publication.

### M5. Some evaluation claims are stronger than their evidence (Section 7, pp. 1:12–1:13)

- "The obligations reject a real defect (machine-checked)… The defective operator could not have been registered as a domain" (p. 1:12). `prefix_congruence_mod_unsound` is a two-step arithmetic fact: (−5) truncating-mod 2 = −1 ∉ γ(1 + 0ℤ). It follows from VIMP's choice of truncating remainder, not from any property of the framework's obligations. Under a floor-mod semantics the pre-fix answer would be sound. The theorem is about a generic soundness formula, not about the registration locale, so "could not have been registered" is an informal inference. Please either prove a statement about the registration interface or weaken the claim to "VIMP's semantics refutes the operator".
- "Contexts buy precision (machine-checked for one program)" is about hand-built equation systems, not the analyzer (see the M3 table).
- The termination discussion (p. 1:14) says that [27] does not apply because "Voblint's unknowns pair nodes, of an infinite type, with contexts". This argument is weak. For a fixed program the reachable nodes are finite, and for bounded call strings the reachable unknowns are finite as well. The real obstacles appear to be side effects and unbounded entry-state contexts with infinite-height domains (p. 1:13 says Interval "create[s] one context per recursion level"). Please state the obstacle precisely and say which configurations could plausibly receive a termination theorem.

### M6. Format and depth for a journal (whole paper)

The submission is formatted as LIPIcs ITP 2027 (header, DOI, page count). A JAR special-issue article is expected to extend the conference version. Concretely, it should contain the full contract and routing statements (M3), the elaboration and simulation argument (M2), the domain framework, which is now one paragraph in Section 4.1, the effort breakdown, and a real design-alternatives discussion. In its current form the journal version adds nothing over a conference paper.

## Minor comments

1. p. 1:1, Section 1. "has reported no false negative on the SV-COMP benchmark suite since its first participation in 2021 [24]": [24] is an FM 2026 paper on modularity. Cite the SV-COMP reports. "More than a hundred issues labeled as unsound" needs a source or a query date.
2. p. 1:1. "The defect (issue 1156) was reported only after Goblint had claimed the false result" says nothing. Every defect is reported after it manifests. Delete or rephrase.
3. p. 1:3, Figure 1 caption. "warrowing update rule" is used before it is defined. Cite Apinis, Seidl, and Vojdani (PLDI 2013) for warrowing. It does not appear in the bibliography.
4. p. 1:4. The Root rule uses "entry g", while Section 2 uses `FunctionEntry p` and the Isabelle text uses `cfg_entry g`. Pick one.
5. p. 1:4. Typeset the Resume rule with all its premises, including the call edge and `Some`; see M3.
6. p. 1:5, `context_policy`. "A description of the call" is `call_info`. Say what it contains. Also explain why the policy receives both the caller's store and the entered store when no shipped policy uses the caller's store.
7. p. 1:6. Total is stated as "some c′ is admitted from s". The Isabelle form says that, for every call edge from u and every s ∈ cover(u, c), adm(…) ≠ ∅. The quantification over edges matters at nodes with several call edges.
8. p. 1:6, listing of Theorem 1. The rendering "A G,adm,c 0 ,g,S v c" is garbled in the PDF text layer and hard to read in print. Use a mathematical rendering next to the listing.
9. p. 1:7. Section 4.1 says "two combine operations" but describes one. Name both, presumably the caller-environment combine and the result assignment, as in Goblint's `combine_env`/`combine_assign`.
10. p. 1:8. Explain `dep_L`, `eq`, `sides_of_rhs`, and the sum type `'x + 'g` in the `part_post_solution` listing, or replace the listing with its mathematical content.
11. p. 1:8. "live_unknowns_cover proves the forward closure". What happens at a call whose caller state is ⊥, or where enter returns no pair? Is the callee unknown left unsolved, and why is that harmless? One sentence would help.
12. p. 1:9. VIMP gives callees' locals zero while main's locals are unconstrained in `cinit_stores` (`VIMP_Globals.thy`, l. 71). Justify the asymmetry. The C analogy holds for neither choice.
13. p. 1:10, statistics. I count 213 `.thy` files under `src/` and 2,723 top-level `lemma`/`theorem`/`corollary` commands. The paper says 212 and 2,683. State the counting method, presumably `paper/tools/stats.py`. `vendor/td-verification/` holds 29 theories, and one of them (`TD_plain_warrow.thy`, l. 354, 411) contains `sorry`. It is not imported by the session Voblint uses, so the paper's claim is correct for the "7 reused theories". Say explicitly that the unused theory is not built.
14. p. 1:11. Either describe the Isar linter (checks, false-positive rate, what it found) or drop it.
15. p. 1:11. "Two-default executable states" is the most concrete refinement in the paper. Give the size of the refinement proof and say whether the Lifting/Transfer setup was reusable across domains.
16. p. 1:12, Table 1. "Int, Order" uses an "order analysis" that is never introduced (it is `Order_Analysis` in the export list).
17. p. 1:12, text vs. Table 1. "Goblint proves it only when Interval is refined by congruences, with a widening delay of 3 or with thresholds at the constants of comparisons". Only the row "Int, delay 3" has ✓ for i > 0. The rows "thresholds" and "comparisons" show –. Either the sentence or the table is wrong, or the row labels need explaining.
18. p. 1:13. "369 regression fixtures under 15 combinations… three repetitions each… 21 of 5,535 runs". 369 × 15 = 5,535, so a "run" here is a fixture–configuration pair, not a repetition. Say how repetitions were aggregated.
19. p. 1:13. "solve time grows with exponents between 2.01 and 2.86, because the generated code represents finite sets and maps as lists". The causal claim needs a profile or an experiment with a different container mapping.
20. Section 8, missing references. Sharir and Pnueli's call-string and functional approaches (1981), the origin of the context notions the paper formalizes. The warrowing paper (item 3). A comparison with mechanized frame-stack semantics for procedures in Isabelle (Jinja, or Nipkow's work on Hoare logics for recursive procedures) as the alternative to activation traces.
21. p. 1:14. "Activations do not interfere, so no concurrency result of that work transfers" is ambiguous. Do you mean that the concurrency-specific results are not needed?
22. Throughout. "Section 7" is cited for running time in Section 6 (p. 1:11) before the reader has seen the setup. Move the codegen-performance remark into Section 7.

## Questions for the authors

1. Can you prove, for `run_voblint`, a per-context theorem bounding A(v, c) by the γ of the report's state for context c, not by R_res(v)? If not, what blocks it?
2. Under the entry-state configuration, `admitted_contexts` is defined from `sol_env 𝒢 p`. What is A(v, c) for a program on which the logical solver's domain predicate fails? Is it still meaningful, and does any theorem quantify over it?
3. Why are activation traces preferable to a frame-stack semantics with a ghost context set per frame and a step invariant? Did you try it?
4. Is it intended that, without `calls_source_unique`, the `ret` rule may resume a callee through a call edge other than the one it was entered by? Would tying the two edges in the rule simplify the Return obligation, which now quantifies over `p'` and `es`?
5. Which assumption did you remove from the vendored solver, why is the solver still correct without it, and has upstream accepted the change?
6. Can the solver trace hook be compiled out of the certified build, so that no handwritten OCaml runs inside the solve? If not, please add it to Figure 3.
7. How many lines does adding a new non-relational domain cost, and how many does adding a new context policy cost?
8. What fraction of the proofs, by statement or by line, were AI-generated, and did you observe any systematic difference in their robustness under refactoring?
