# Review H (round 4): solver and constraint-system perspective

Submission: "End-to-End Soundness of a Context-Sensitive Goblint-Style Analyzer in Isabelle/HOL" (ITP 2027 draft, 19 pp.).
Reviewer expertise: local generic solvers, top-down solvers, side-effecting constraint systems, Goblint.
Material read: `paper/reviews/round4/submission.txt` and `submission.pdf`, `src/`, `vendor/td-verification/`, parts of `thesis/content/`, the CLI binary, Fecht and Seidl "Propagating Differences" (ESOP 1998), and Seidl and Fecht "Interprocedural analyses: a comparison" (JLP 43, 2000).

## Summary

The paper connects a small-step semantics of VIMP, a scalar imperative language with recursive procedures, to the side-effecting top-down solver of Tilscher et al. [34], which is vendored into the development. The chain has four steps.

1. Activation traces with a relational context policy, plus a five-obligation coverage contract over an arbitrary CFG (Thm 1).
2. A proof that a partial post-solution of the context-routed equations, on a set W with forward-closure and routing hypotheses, meets the contract (Thm 2).
3. A bridge from the solver's backward certificate `part_post_solution` to the forward hypotheses on W, via a "live set" of unknowns (Sec. 4.3).
4. An end-to-end theorem about the exported `run_voblint` (Thm 3).

The solver is a locale parameter (`certified_solver`) that the proof uses only through four facts. Those facts are discharged for all five update rules for globals.

From the solver side the construction is sound, and the certificate-only interface is well chosen. My main concerns are attribution and precision of description. Its central solver-side argument, the live-set bridge, is a mechanized and generalized form of a classical result of Seidl and Fecht (JLP 2000, Thm 9(2) with proviso (R)) that the paper does not cite. The TD lineage (Le Charlier and Van Hentenryck; Seidl and Vogler) and the origin of warrowing (Apinis et al.) are missing. Several statements about the solver as it actually runs are slightly inaccurate or incomplete: lifted update rules, warrowed seeds without contexts, buffered generator, and the termination literature.

## Recommendation and confidence

Recommendation: **weak accept for ITP**, conditional on fixing the related-work omissions in M1 and M2 and the accuracy points in M3 to M5. For JAR it is not yet sufficient (see "Venue fit").

Confidence: **4/5.** I checked the solver interface and bridge against the theories and ran the CLI. I did not re-run the Isabelle build, so "no sorry" and proof completion rest on the paper's statement.

## Spot-checks against the formalization

| # | Paper statement | Source | Verdict |
| --- | --- | --- | --- |
| 1 | `certified_solver` assumes four facts: a run in the domain yields `part_post_solution` and a finite solved set; a returned executable run lies in the domain and agrees with the logical solver (p. 9) | `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:26-36` (`solve_pp`, `solve_fin`, `dom_of_solve_c`, `solve_of_solve_c`) | Correct |
| 2 | `part_post_solution`: query in V, V closed under reads, σ bounds rhs and every side effect (p. 8) | `vendor/td-verification/Basics_side.thy:337-343` | Correct. Closure is under `dep_L` evaluated at the final σ, i.e. dynamic dependencies. The paper should say so (see m3). |
| 3 | A call alternative yields `combine(q, ⊥)` for bottom entry, else publish to `seed(p,c′)`, read `(FunctionResult p, c′)`, and combine (p. 7) | `src/Abstract_Interpreter/Framework/Context/Routed_Call_Programs.thy:152-170` | Correct |
| 4 | The rhs of `(v,c)` joins four sources (p. 7) | `src/Abstract_Interpreter/Framework/Constraints/DG_Indexed_Generator.thy:268-277` (`routed_node_rhs_parts`) | Correct, but `rhs_init g bot0 d0 v` does not depend on `c`, so the initial state enters the program entry in every context, not only c0 (m4). |
| 5 | Live set = solved `(u,c)` whose procedure's result is solved in `c`; covers entry; closure hypotheses hold given a well-formed program and a returned solve (p. 9) | `src/Analyses/Shared/Result/DG_Live_Unknowns.thy:230-234`, `:251-303` | Correct. The root query is `(FunctionResult main, root_ctx)` (`DG_Analysis.thy`, `root_query`), matching "the solver works backward from its query, the result of main". |
| 6 | A continuation in V reads the callee result when the routed entry is not bottom (`sol_vars_callee_result`) | `DG_Live_Unknowns.thy:186-213` | Correct. It is instantiated with the singleton alternative list `[?alt]` (line 202), consistent with "the shipped analyses' enter returns a single alternative" (p. 5). |
| 7 | Facts proved "for the vendored solver under each of its five update rules" (p. 9) | `src/Abstract_Interpreter/Solver/Globals_Rule.thy:126-163` | Partly correct. Four of the five rules run through a Voblint-side wrapper `lift_basic_rule`/`changed` (`Globals_Rule.thy:37-55`), which changes when the solver is told a global changed (M3). |
| 8 | Routing adequacy and totality (Table 1, p. 7) | `src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:86-110` | Correct |
| 9 | Entry-state policy defined from σ (p. 7) | `Routed_Context.thy:703-713` | Correct |
| 10 | Thm 2 premises: entry in W, initial state sound, ρ0 ≤ ρ (p. 8) | `Routed_Context.thy:585-590` | Correct |
| 11 | Termination result of [35] "assumes a finite type of unknowns" (p. 15) | `vendor/td-verification/Basics.thy:756` (`finite_vars: finite (UNIV :: 'x set)`) | Correct for the vendored termination locales, but incomplete as a statement about the literature (M4). |
| 12 | Solver "vendored with four changes … None changes the algorithm" (p. 11) | `git log` of `vendor/td-verification`: 11 author commits after upstream `af78761` | Plausible. The diff of `TD_side_upd_rule.thy` changes no algorithmic definition, only renames. "Four changes" is a grouping of 11 commits; acceptable. |
| 13 | Fig. 1 and Table 3 verdicts | CLI runs, see M5 | Verdicts reproduce. The no-context state description in the caption does not (M5). |

## Strengths

S1. **Certificate-only solver interface.** Thm 2 and the bridge consume only `part_post_solution` at the final valuation plus finiteness (`TD_Solver_Bridge.thy:26-36`). Soundness of a post-solution does not depend on how it was computed, so this is the right interface. It also makes the update rule, widening points, and destabilization strategy irrelevant to soundness. Discharging the locale once for all update rules via a rule-valued parameter (`Globals_Rule.thy:126-163`) is economical.

S2. **Backward certificate vs. forward hypotheses is handled correctly.** A demand-driven solver started at `(FunctionResult main, c0)` gives closure under reads, i.e. backward. Thm 2 needs forward closure from the entry. The bridge restricts V to procedures whose result is solved in the same context. It derives the needed forward closure from the structural property that every node reaches its procedure's result (`prog_node_reaches`, used at `DG_Live_Unknowns.thy:245-246`). The paper also states correctly that this is structural, so non-returning activations are covered (p. 9). The bottom-entry skip is handled soundly: `is_bot_sound` makes the skipped callee contribute no stores, and the combine with ⊥ remains an over-approximation.

S3. **Side effects to seed unknowns are a faithful model of Goblint's entry handling.** The callee entry reads a global `seed(p,c′)` that callers publish to (`routed_entry_seed_programs`, `Routed_Call_Programs.thy:249-262`), and Table 1 requires seed keys to be disjoint from other globals. Proving soundness for side-effect-based context entry, rather than for a direct read of the caller, is the right level of generality.

S4. **Termination evaluation is honest.** Partial correctness is stated in the abstract, Sec. 1, Sec. 5 and Sec. 9. Timeouts are reported per policy (Table 4). The concrete non-terminating fixture is named. I reproduced it: `13-recursion_grows_warrow.vimp` times out under entry-state contexts with `--globals join`, `warrow`, and `bounded-narrowing`, and is PROVED with `--context none`. The 21 timeouts, 369 fixtures and 5,535 runs match `thesis/shared/generated/profiling.json` (`timeouts: 21`, `fixtures: 369`, `runs: 5535`).

## Major weaknesses

**M1. The live-set bridge is a known result and is presented without attribution.**
Sec. 4.3 (p. 8-9) presents the live-set argument as part of the paper's own construction: "The bridge takes W to be the live part of V … The compiler ends every body with a return edge, so every node of a procedure reaches the procedure's result". Seidl and Fecht (JLP 43, 2000, §9.1, pp. 138-139) prove essentially this. Theorem 9(2): for a (not necessarily least) solution σ of the functional forward-accumulation system, every state reaching a program point v of p is below σ⟨v,d1⟩ for some d1 with p d1 ∈ dep({main d0}, σ). They also show (Example 8) that the argument needs proviso (R): "For every procedure p and every program point v ∈ N_p, there is a path in G_p from v to a return point of p". Page 140 adds: "We only have to guarantee that all variables ⟨v,d⟩, v a program point of the procedure p, are contained in the domain of σ whenever the variable ⟨p,d⟩ has been included. For local solvers … this is, under proviso (R), always the case."
`live_unknowns` (`DG_Live_Unknowns.thy:230-234`) is exactly the set {⟨v,d⟩ | ⟨p,d⟩ ∈ dep}, and "the compiler ends every body with a return edge" is proviso (R). The paper's contribution here is real but different: a mechanization; generalization to side effects, seed globals, dynamic dependencies of a partial post-solution, and a relational context policy; and discharge of (R) for the compiler. Please cite Seidl and Fecht at this point and state what is inherited and what is new. The sentence "This is structural reachability in the graph" should name (R).

**M2. Related work on solvers is incomplete and attributes inherited ideas only to the most recent papers.**
The "Verified solvers" paragraph (p. 15) and Sec. 4 cite only [11, 8, 33, 34, 35]. Missing:

- *The TD algorithm itself.* Le Charlier and Van Hentenryck, "A universal top-down fixpoint algorithm", TR CS-92-25, Brown Univ., 1992 (verified via the bibliographies of both supplied references: JLP 2000 ref [6] and ESOP 1998 ref 5). The paper says "A generic top-down solver" (p. 1) and "the verified top-down solver" (p. 8) without naming the algorithm's origin.
- *TD with side effects and non-monotonic rhs.* Seidl and Vogler, "Three improvements to the top-down solver", MSCS 31(9):1090-1134, 2021, doi:10.1017/S0960129521000499 (verified by web search; also listed in `vendor/td-verification/README.md`). This is the algorithm, for side-effecting systems, that [34] verifies, and it carries the termination statement relevant to M4.
- *Warrowing.* Sec. 4.3 (p. 9) attributes the operator to [34]: "warrowing, which combines widening and narrowing [34]". The operator is due to Apinis, Seidl and Vojdani, "How to combine widening and narrowing for non-monotonic systems of equations", PLDI 2013 (existence and authorship verified by web search; page numbers UNVERIFIED). Its TD application is Apinis, Seidl and Vojdani, "Enhancing top-down solving with widening and narrowing" (2016; verified that the paper exists, venue details UNVERIFIED). Cite [34] for the verified update-rule interface and these papers for the operator.
- *Local solving and partial post-solutions.* `part_post_solution` is Fecht and Seidl's "X-stable partial assignment" (Propagating Differences, ESOP 1998, LNCS 1381, §6). Their computation trees, (x, C) with dep(t,σ) (ibid. §3), are the ancestor of the `QueryL`/`QueryG`/`Side` strategy trees whose `dep_L` the bridge reasons about. One sentence placing the certificate in this lineage would help readers from the solver community. Hofmann, Karbyshev and Seidl [11] and de Vilhena et al. [8] verify local solvers with this certificate shape but without side effects. Saying so would make the comparison informative rather than a list.
- *Context-indexed unknowns.* Sec. 8 attributes the call-string and functional approaches only to Sharir and Pnueli [32] and says the entry-state policy "resembles a functional approach tabulated per input". Seidl and Fecht (JLP 2000, §6, pp. 131-133) describe both in constraint-system terms. Call strings record the topmost stack elements (p. 131). The functional approach introduces one unknown y_{f,d} per procedure and argument "which is going to receive the value of application f d", with "the least solution … only partially computed. This idea is exploited by local solvers" (pp. 132-133). This is the closest precedent for the paper's unknowns (v, c) with entry-state c, solved on demand. It should be cited in Sec. 2/4.2 where context-indexed unknowns are introduced and in Sec. 8. Jones and Mycroft's minimal function graphs (cited there as [34]) are the classical source; I have not checked that paper myself, so its bibliographic details are UNVERIFIED.

**M3. "Proved for the vendored solver under each of its five update rules" does not describe the solver that runs.**
`td_certified_solver` (`Globals_Rule.thy:157-163`) is proved for `update_global_of r`. For four of the five rules this is `lift_basic_rule f`, which wraps the vendored rule `f` with `changed`. `changed` suppresses the "value changed" signal when the merged value equals the old one (`Globals_Rule.thy:37-48`). The theory comment explains that the warrowing rules otherwise report a change "whenever an origin's contribution changes, even when the merge over all origins stays the same, and the solver destabilizes every reader". This is a Voblint-side modification of solver behavior. It is proved to satisfy `update_rule`, so soundness is unaffected, but it is not "the vendored solver" with its own rules, and Sec. 6 says "None changes the algorithm". Please state that the shipped rules are lifted variants and why. Relatedly, the paper lists three behaviors (join, per origin, warrowing) for five rules; bounded narrowing (`Globals_Bounded_Narrowing n`) should be named. The paper should also say that local unknowns are always warrowed at dynamically detected widening points (`vendor/td-verification/TD_side_upd_rule.thy:50`, `x ∈ point state`). The update rule only selects the treatment of globals, including seeds.

**M4. The termination discussion misstates the relevant hypothesis and omits a consequence of the vendoring changes.**
Sec. 9 (p. 16): "Known termination results for top-down solvers assume finitely many unknowns [35]". Sec. 8 (p. 15) says the result "assumes a finite type of unknowns … which Voblint's node and context types are not". The finite type holds in the vendored locales (`Basics.thy:756`). The on-paper results, Seidl and Vogler (MSCS 2021) and Apinis et al. (PLDI 2013), are stated for finitely many *encountered* unknowns: Seidl and Vogler's abstract says the earlier TD "was only guaranteed to terminate if finitely many unknowns are encountered". For call strings of bounded length, the encountered unknowns are finite (nodes × call sites^k), so a termination argument for call-string configurations is not blocked in principle. The obstruction is specific to entry-state contexts, which matches the evidence in Table 4. Please separate "the mechanized result requires a finite type" from "the paper results require finitely many encountered unknowns".
Sec. 6 also says the vendoring removed "from the widening and narrowing classes the stabilization assumptions that only termination proofs use". So Voblint's domains are not shown to satisfy the well-foundedness conditions any termination theorem would need. That belongs in the termination paragraph as a second gap, alongside unbounded contexts.

**M5. Figure 1's caption misdescribes the context-insensitive run under the stated update rule.**
The caption (p. 3) says: "States are analyzer output with the warrowing update rule … Without contexts, the single copy of bump joins both calls and both checks are UNKNOWN." Running the CLI on the Fig. 1 program with `--analysis interval --context none --globals warrow` gives `a=[-∞,6]` and `b=[-∞,6]`. With `--globals join` it gives `a=[5,6]` and `b=[5,6]`. Under warrowing the two entry contributions to the single seed are *widened*, not joined, although the program has no loop and no recursion. This follows directly from routing entry states through global seed unknowns, which are subject to the globals update rule. It is a solver-relevant design consequence: in this architecture, entry states are widened at every call site sharing a context, not only at recursion. Please correct the caption ("joins" → "merges", or report join-rule states), and mention this consequence in Sec. 4.2/4.3. The entry-state runs reproduce the caption (`a=[6,6]`, `b=[5,5]`, PROVED) under both rules.

## Minor comments

m1. Abstract (ii) and Sec. 1: "every post-solution of the generated, context-routed equations … meets the contract". Thm 2 is about a partial post-solution on a set W that also satisfies `fwd`, `comb_fwd`, and the routing conditions (Table 1). Those are not consequences of being a partial post-solution; Sec. 4.3 derives them only for compiled well-formed programs via `live_unknowns_cover`. Please qualify.

m2. Sec. 4.3, "Replacing the solver would not touch the semantic layer". Correct only for solvers over the same right-hand-side representation `('x,'g,'d) eqsT` with side effects (`TD_Solver_Bridge.thy:27`). A solver such as [11] or [8] would need a translation of rhs and of `dep_L`. Please qualify.

m3. Sec. 4.3 should state that closure in `part_post_solution` is with respect to the dependencies observed at the final σ (`Basics_side.thy:341`). The bridge (`sol_vars_callee_result`) relies on this: a continuation reads the callee result only for a non-bottom entry *under the final σ*. A reader familiar with static dependency graphs could otherwise miss this.

m4. `routed_node_rhs_parts` (`DG_Indexed_Generator.thy:274`) joins the initial state at the program entry in every context, not only c0. This is harmless for soundness, but Sec. 4.2's "the initial state at the program entry" suggests only c0.

m5. The executable equations are `routed_node_rhs_buffered` (`src/Analyses/Shared/Routing/Compiled_Routed_Equations.thy:45-51`). They fold the global parts of a node's contributions and publish once at a buffer key, while Sec. 4.2 describes per-contribution publication. Please mention the buffering and the lemma relating the two, since it changes which unknowns publish to globals.

m6. Sec. 7, "Running time": the globals update rule used for profiling is not stated. `scripts/profile_corpus.py:259` fixes `"warrow"`. Table 3 also does not state its rule. Since termination behavior depends on the rule (M4), state it. Call strings of length 2 are used in Table 3 but not profiled in Table 4; the paper says so, but a reason would help.

m7. Sec. 7: "solver evaluations grow about linearly (Section 6)". Section 6 contains no such data. The figures exist in the profiling snapshot (`depth_fits`: evals exponent ≈ 0.99, time ≈ 2.1). Fix the cross-reference or give the numbers.

m8. Sec. 6: the profile also attributes about 42% of samples to report construction (`flame.report_share` = 0.42 in `profiling.json`), next to `solver_share` = 0.44. "CPU profiles attribute most of the solve time to these scans" is accurate for the solve. The reader should also know that report construction is comparably expensive.

m9. Sec. 9, "Goblint bounds them with optional widening on contexts (ana.context.widen) or a context gas". I believe both options exist in current Goblint, but the paper gives neither a revision nor a citation. UNVERIFIED by me; please cite the option documentation or the corresponding paper.

m10. Sec. 4.3 lists "join per contributing right-hand side". The rule is per origin, i.e. per contributing *unknown* (`orig` in `Update_rules.thy`). Since one unknown has one rhs this is equivalent, but "per origin unknown" matches [34]'s terminology.

## Questions for the author

Q1. Beyond mechanization, side effects, and the relational policy, what does the live-set bridge add over Seidl and Fecht's Thm 9(2) and proviso (R)? In particular, does the dynamic-dependency setting introduce a case their argument does not cover, such as the bottom-entry skip?

Q2. Why route entry states through global seeds subject to the globals update rule, instead of treating seeds with join-only semantics? M5 shows a precision cost without recursion. Is this choice inherited from Goblint's TD side-effect handling, and does Goblint widen entry seeds under the same configuration?

Q3. For call-string configurations, which hypotheses of an existing termination theorem fail besides the finite-type formulation? Would the warrowing well-foundedness conditions removed in vendoring (Sec. 6) be provable for the shipped domains?

Q4. Does the `changed` wrapper affect only performance, or did you observe non-termination of the unwrapped warrowing rules on the corpus?

Q5. The report publishes states from all of V, but soundness uses W ⊆ V. How large is V \ W in practice? Are states in V \ W ever less precise than the semantics would suggest, for example stale values of unknowns no longer read?

## Venue fit

For ITP the scope is appropriate. The contribution is the mechanized chain and the interface design, and the solver is correctly treated as an imported verified component. For JAR, I would expect the following before the work is complete enough.

- The per-context certification that Sec. 5 leaves open.
- A precise positioning against the classical constraint-system literature (M1, M2).
- At least a termination statement for call-string configurations, or a mechanized reason why one is out of reach.
- A full treatment of the update-rule lifting and buffering.
