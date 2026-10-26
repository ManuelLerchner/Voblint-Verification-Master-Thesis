# Review: "Calling Contexts Made Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL"

Reviewer 3 (semantics and soundness proofs)

Line references `sub:N` point to `paper/reviews/round1/submission.txt`. Isabelle references are relative to `src/` unless they say otherwise.

## Summary

The paper connects a small-step semantics of VIMP, a scalar imperative language with recursive procedures and globals, to the verdicts of an executable Goblint-style analyzer. The central device is the *activation trace*: a tree-shaped record of one procedure activation together with the frozen caller that created it (`Call`) and, after a return, the finished callee (`Resume`). A *context policy* `adm` relates each call to a set of callee contexts. This induces a context-indexed collecting semantics A(v, c). A cover that meets five local obligations (Init, Intra, Call, Return, Total) bounds A (Theorem 1). Every suitably closed post-solution of the generated side-effecting equations meets the obligations (Theorem 2). The top-level theorem `run_voblint_source_sound` (Theorem 3) states that every store reached by a finite source run from a zero-globals store is collected, covered by the report, and consistent with its definite verdicts, at every node where the run is observed.

I compared Sections 3 to 5 against the theories. The formal development is careful. Theorem 1 matches `activation_collect_sound` exactly. Theorem 3 matches `run_voblint_source_sound` exactly. The design honestly avoids several traps: `admits_call_context` names the call edge by its effect rather than assuming it unique, the `Total` obligation is shown necessary by a counter-model, and the final theorem carries no termination, coverage or well-formedness premise. My concerns are with the *paper's* rendering of the formal objects. In one place the displayed contract is not the one proved, and it would be unsound if taken literally on the "arbitrary control-flow graph" the paper advertises. In several places the paper claims more for contexts than the end-to-end theorem delivers. And it leaves out assumptions that a reader needs before reusing the contract.

## Recommendation

**Major revision.** The mechanization is sound as far as I could check. The revision is needed so that the paper's statements match it. For a journal version I also expect the missing definitions (CFG, `call_enter`, `combine_collect`, γ, `routing_adequate`) to be stated rather than referenced by name.

**Confidence: 4/5.** I read the relevant theories in full. I did not re-run the build or inspect the vendored solver beyond `part_post_solution` and `certified_solver`.

## Strengths

1. **A real gap, closed at the right level.** The partial-correctness theorem of the TD solver says nothing about programs. The paper identifies the missing object, a concrete counterpart of a calling context, and supplies it without baking contexts into the trace semantics (`Activation_Trace_Def.thy:43-47`, `Activation_Trace_Context.thy:132-143`).
2. **The contract has no domain, solver or equation in it.** `activation_coverage` (`Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:43-64`) is stated over an arbitrary `cfg`, a store-set cover and a relational policy. Theorem 1 is a clean rule-induction consequence.
3. **Totality is treated honestly.** `total_dropped_unsound` exhibits a cover that meets the other four obligations and misses a reached store. The text at `sub:305-311` explains why `Total` is relative to the cover.
4. **The top-level statement is about the exported constant and has few premises.** `run_voblint_source_sound` (`Executable_Surface/CLI/Analysis_Certified.thy:196-208`) takes only an initial store, a finite run and an `Analysed` answer. Termination, coverage of the solved set (`live_unknowns_cover`, `Analyses/Shared/Result/DG_Live_Unknowns.thy:251`) and well-formedness are all derived.
5. **Partial correctness and verdict semantics are stated with care.** The paper says that PROVED does not assert reachability and that REFUTED is not a verified counterexample (`sub:538-545`), and the non-vacuity instance `nv_source_certified` discharges every premise.
6. **The relation between `at_node` and the source run is explained.** The paper says why the residual command does not determine a node (`sub:466-473`) and quantifies over all observation nodes rather than picking one.

## Major weaknesses

### 1. The displayed Return obligation is not the proved one, and taken literally it is unsound on arbitrary CFGs

The paper (`sub:286-304`) fixes one call edge and states:

> For a call edge from u into p with continuation k, the contract activation_coverage requires: … Return s ∈ cover(u, c), c′ admitted from s, t ∈ cover(FunctionResult p, c′) =⇒ combine(s, t) ∈ cover(k, c) … Here "c′ admitted from s" means that the policy admits c′ for the call from s in context c.

Isabelle (`Activation_Trace_Abstract.thy:58-63`):

```text
RETURN: (u, CallEdge dst pars args, FunctionEntry p, cont) ∈ calls g
  ⟹ s ∈ cover u c
  ⟹ admits_call_context 𝒢 g adm u c p' s es c'
  ⟹ t ∈ cover (FunctionResult p) c'
  ⟹ combine_collect 𝒢 dst s t ∈ cover cont c
```

Here `p'` and `es` are universally quantified and unrelated to `p` and the edge. Per `Activation_Trace_Context.thy:93-97`, `admits_call_context` holds for *some* call edge from `u` into `p'` with entered store `es`. The proved obligation is therefore strictly stronger than the displayed one whenever a node has more than one outgoing call edge, or a callee can reach another procedure's `FunctionResult` through intra edges.

The difference matters for soundness, not just presentation. The `ret` rule (`Activation_Trace_Def.thy:120-130`) resumes a caller through *any* call edge from its node into `p`, whichever edge created the callee. On a graph with two call edges at `u` (into `p1` and into `p`), a callee entered via the first edge that reaches `FunctionResult p` is resumed via the second. Its contexts come from the first edge's admission, so the displayed obligation, which only mentions contexts admitted for the second edge, does not force the combined store into `cover(k, c)`. The paper claims Theorem 1 holds "over an arbitrary control-flow graph" (`sub:15-16`). That is true of the Isabelle statement and false of the displayed one.

The prose at `sub:232` ("k is the continuation that the call edge from t′'s call site names") and at `sub:237-238` ("a return resumes exactly the activation that made the call") suggests a uniqueness that the trace semantics does not have. Uniqueness is introduced only later, as the `calls_unique: calls_source_unique g` assumption of `routed_context` (`Abstract_Interpreter/Framework/Context/Routed_Context.thy:74`; definition at `Program_Model/CFG/CFG_Def.thy:243-247`). Theorem 2 lists it only under "side conditions on … the shape of the graph" (`sub:418`).

**Requested:** state Return with the existential edge (or the `p'`, `es` quantification) exactly as proved. Alternatively, state Theorem 1 under `calls_source_unique` and show that the simpler form then suffices. Also say explicitly that the `ret` rule may pair the enter of one edge with the combine of another, and that compiled programs exclude this (`Analyses/Shared/Routing/Call_String_Routed_Context.thy:107`, `Entry_State_Routed_Context.thy:100`).

### 2. For entry-state contexts, the "concrete" context semantics is defined from the analysis result, which weakens contribution 1 and the title

The title and contribution 1 (`sub:80-84`) promise "a concrete semantics of calling contexts". For call strings and the unit policy, that is what `adm` is: `context_policy_of_fun` of a function of the call site and the caller context (`Executable_Surface/CLI/Analysis_Report.thy:531-547`). For entry-state contexts, which is the configuration of the running example and Figure 1, the shipped policy is

```text
admitted_contexts 𝒢 p = routed_entry_context_rel (λci d. [entry_alt 𝒢 p ci d (sol_global 𝒢 p)]) … (sol_env 𝒢 p) global_of (route 𝒢)
```

(`Analyses/Shared/Result/DG_Analysis.thy:598-603`). By `Routed_Context.thy:708-713`, this admits `c'` exactly when the *solved* caller state's entry alternative covers the concrete call and routes to `c'`. A(v, c) under this policy is therefore "the stores of traces that the solution routes to c". Theorem 2 for this policy is then a statement about the analysis's self-consistency, and it is not a comparison against an analysis-independent meaning of c. The paper acknowledges this in one sentence (`sub:412-413`: "The policy may depend on the analysis result without circularity, because the final guarantee concerns C, which no policy changes"). That sentence concedes that, for this policy, the per-context claim has no independent content: only C does.

**Requested:** separate the two cases in Sections 1 and 3. For functional policies, A is an analysis-independent semantics. For entry-state policies, A is relative to σ, and only the context-insensitive C is analysis-independent. Discuss whether an analysis-independent entry-state policy (for example via a best abstraction of the entered store) is possible, and why it was not used.

### 3. The end-to-end theorem does not certify any per-context state the report prints

Section 5 says the report "lists, per node, the solved states of every solved context" (`sub:480`). However, the report-level soundness fact is

```text
context_sound p res adm rc ⟷ (∀t ∈ 𝒯. ∃c. activation_context_rel … t c) ∧ (∀v c. 𝒜 … v c ⊆ ℛ_res v)
```

(`Executable_Surface/CLI/Analysis_Report.thy:517-524`). Here ℛ_res v is the union over all states at v (`Analysis_Report.thy:41-42`). No theorem about `run_voblint` relates A(v, c) to the printed state at (v, c). `run_voblint_spine` (`Analysis_Certified.thy:397-414`) also bottoms out in ℛ_res v. The paper's own sentence "The contexts appear only inside the proof" (`sub:526-528`) is accurate, but it sits uneasily with the abstract's framing and with the per-context frames of Figure 1, which a reader will take as certified. I do not ask for a new theorem. I do ask that the paper state plainly that the delivered guarantee is per node (the join over contexts), and that per-context entries of the report are covered only by Theorem 2 at the level of σ, not by a theorem about the exported function.

### 4. The proof sketch of Theorem 1 names the hard case but not the device that solves it

`sub:321-327` says the proof is "an induction over the four rules of valid traces … with the invariant that every valid trace carries some context and that its final store is covered in every context it carries". Taken literally, that induction does not go through. The premises of the `ret` rule include `callee ∈ 𝒯` and `caller_of callee = Some caller`, but not `caller ∈ 𝒯` (`Activation_Trace_Def.thy:120-125`). So rule induction supplies no hypothesis for the caller. The mechanized proof:

- strengthens the invariant to the whole caller chain (`caller_chain_closure`, `Activation_Trace_Def.thy:308-341`; `caller_chain_covered`, `Activation_Trace_Abstract.thy:216-245`), so that the caller's fact is recovered from the callee's;
- proves that a callee carries exactly the contexts admitted from contexts its caller carries (`activation_context_rel_caller_entry`, `Activation_Trace_Context.thy:206-246`, an equivalence proved by its own chain induction);
- uses `TOTAL` a second time *inside* the return case (`Activation_Trace_Abstract.thy:197-201`). For each context `c` of the resumed caller, it obtains a callee context `c'` admitted from that same `c`, and the backward direction of the equivalence lets the callee carry it.

These three steps are the substance of the proof, and the third is what makes `Total` a soundness obligation rather than an exhaustiveness one. A journal reader should see them. The current sentence "caller_of supplies exactly that caller" (`sub:325`) understates the argument.

### 5. Theorem 2's hypotheses are summarized too loosely to be checked or reused

`sub:415-420` compresses the `routed_context` and `dg_context_activation` assumptions into "side conditions on call resolution and the shape of the graph". The actual hypotheses (`Routed_Context.thy:73-114`, `Abstract_Interpreter/Framework/Activation/DG_Ctx_Activation.thy:43-58`) include:

- `finite (calls g)` and `finite (intra g)`;
- `calls_source_unique g` (see weakness 1);
- `resolve_sound`, a soundness condition on the call resolver;
- injectivity of the seed keys (`seed_ne_buffer_key`, `seed_ne_global_of`);
- `is_bot_sound`;
- `post_bounded` rather than `part_post_solution`, a different predicate from the one displayed in Section 4.3, and its relation to `part_post_solution` is not stated;
- `fwd`, closure under intra edges *only from unknowns with non-empty concretization* (`DG_Ctx_Activation.thy:55-58`), which is weaker than "closed under local edges" at `sub:417`;
- `comb_fwd`;
- the requirement, inside `routing_adequate`, that the routed entry unknown is in `vars` (`Routed_Context.thy:103`).

The cover is also γ_M(sg(Inl(v, c))), and γ takes the global environment `genv global_of sigma` as a second argument. The paper's "γ(σ(v, c))" hides that globals are read from global unknowns. Please state Theorem 2 with its hypotheses listed, at least in an appendix, and state the lemma that turns `part_post_solution` plus `live_unknowns_cover` into `post_bounded` plus the closure conditions.

### 6. "Under a totality condition" overstates the hypothesis of the context decomposition

Contribution 1 (`sub:83-84`): "Under a totality condition, splitting the collecting semantics by context loses no store". `node_collect_eq_Union_activation_collect` (`Activation_Trace_Abstract.thy:268-282`) is proved inside the `activation_coverage` locale, so it needs *all five* obligations for some cover. `call_context_total_on` is relative to the cover and says nothing about uncovered traces. The general form, `node_collect_eq_Union_activation_of_has_context` (`Program_Model/CFG/Collecting/Activation_Trace_Collect.thy:182-184`), assumes directly that every valid trace carries a context. Only functional policies get the decomposition unconditionally. Please state the hypothesis as proved.

### 7. Adequacy of VIMP: the listed deviations are incomplete, and no argument is given

`sub:553-555` lists three deviations from C: unbounded integers, defined division by zero, and zeroed callee locals. The conclusion repeats that adequacy "is argued, not proved" (`sub:774`), but the paper contains no argument, only the list. A semantics reader would also expect these to be mentioned:

- `__voblint_check` is a no-op step (`Program_Model/VIMP/VIMP_Proc.thy:132`). Execution continues past a failing check, so the verdicts of later checks quantify over runs that already violated earlier ones. This differs from `assert` and should be stated, since it changes what a REFUTED verdict upstream implies downstream.
- Division by zero yields 0, and remainder by zero yields the dividend (`Program_Model/VIMP/VIMP_Expr.thy:14-24`). The arithmetic-diagnostic theorems are therefore checks of an *auxiliary* predicate, not of a fault in the semantics. The paper should say so where it introduces `run_voblint_arithmetic_safe` (`sub:541-545`).
- VIMP has nondeterministic input `__voblint_nondet_int` and built-ins `min` and `max` (`Program_Model/VIMP/VIMP_Special.thy:15-58`; `pstep` rule `Special`, `VIMP_Proc.thy:149-152`). Section 1 (`sub:105-107`) does not list them, yet the evaluation's "every check holds in every execution" depends on them.
- Main's locals are unconstrained (`cinit_stores`, `Program_Model/VIMP/VIMP_Globals.thy:71-72`), while callee locals start at 0. This asymmetry is visible only by reading `sub:501-502` together with `sub:554`.
- Calls with arity mismatch or to undefined procedures are stuck rather than erroneous (`VIMP_Proc.thy:140-148`). Well-formedness rejects them, but "finite execution with any stopping point" interacts with stuck states, and that interaction should be mentioned.

I would also like the paper to say what evidence supports adequacy beyond inspection. For example: was `pstep` differentially tested against a C compiler on the regression corpus restricted to programs without the listed deviations?

## Minor comments

1. **Notation used before it is defined.** The subscript 𝒢 in T_{𝒢,g,S} (`sub:216`), A_{𝒢,adm,c0,g,S} (`sub:274`) and `activation_coverage g S cover adm c0 𝒢` (`sub:317`) is never introduced. It is the predicate of declared globals. `intra g`, `calls g` and their 4-tuple shape, `entry g` (Isabelle: `cfg_entry`) and `step_a` (Isabelle: `edge_step`) are used in Section 3.1 without definition. R_res and V_res appear in equation (1) (`sub:175`) but are defined only in Section 5.
2. The displayed Call and Resume rules drop parameters that matter. `enter e` is `call_enter 𝒢 (CallEdge dst pars args)`. `combine` is `combine_collect 𝒢 dst`, so it depends on the destination variable of the edge. The Resume rule omits its call-edge premise (`(sink_node t', CallEdge dst pars args, FunctionEntry p, cont) ∈ calls g`), which is exactly the premise at issue in weakness 1.
3. `sub:269-270`: "local steps and resumptions keep the caller's contexts". Local steps keep the trace's *own* contexts, and only `Resume` inherits from the frozen caller. The sentence should be reworded.
4. "c′ admitted from s" (`sub:304`) hides that `adm` also receives the call site, the `call_info` and the entered store. Since the paper later relies on entry-state policies reading the entered store, give the full signature in the obligation.
5. Overlapping enter alternatives (`sub:263-265`, `ov_two_contexts_admitted`) are exercised only in a hand-built example (`Examples/Sign/Example_Sign_DG_Overlapping_Enter.thy:1040`). The shipped entry-state policy passes a single alternative (`DG_Analysis.thy:601`). For the shipped analyzer, the relational form is needed for partiality (an empty set), not multiplicity. Please say so in Section 6's "Contexts as a relation".
6. `sub:239-241`: `source_run_has_activation_trace` is a one-way result. No theorem states that valid traces correspond to graph executions, so C may strictly over-approximate the reachable stores, for example through the mismatched-edge returns of weakness 1 on non-compiled graphs. This is harmless for soundness. However, "four rules that mirror the rules of graph execution" (`sub:217-218`) should not suggest an equivalence. DEAD is then a claim about C, which is strictly stronger than unreachability, and the paper should say that this is the direction it relies on.
7. Theorem 2 (`sub:419-420`): in the live instance, "solved unknowns" means `live_unknowns p`, a subset of the solver's solved set restricted to procedures whose result is solved in the same context (`DG_Live_Unknowns.thy:230-234`), not V itself. Say so.
8. `sub:444-447`: "Every node of a procedure reaches its result node" is graph reachability that ignores guards (`prog_node_reaches`, `Program_Model/Compile/Live_Nodes.thy:422`). Say this explicitly, because it is the reason non-terminating loops do not break closure.
9. `at_node` (`Program_Model/Compile/Elaborated_Compilation.thy:791-798`) existentially quantifies over a *fresh* elaborated run from s0, not necessarily the lift of the given run. The universal half of Theorem 3 therefore also covers nodes at which other runs reaching the same configuration are observed. This is harmless, but it is worth one sentence, since the paper says "nodes of its lifted runs" (`sub:469`), which a reader may read as "the lift of this run".
10. Check labels: `run_voblint_check_sound` identifies a check by node, and lookup by label needs a distinct-labels premise (`Analysis_Certified.thy:333-340`). The non-vacuity program uses the placeholder label `(0, 0)` for both checks (`Examples/Capstone/Example_Non_Vacuity.thy:160-161`). If the CLI reports by label, the paper should state the premise and who checks it.
11. The abstract (`sub:15-16`) says "every post-solution of the generated equations meets them". Theorem 2 needs adequacy, totality and closure hypotheses. "Every suitably closed post-solution, given adequate and total routing" would be accurate.
12. `sub:313-314`: Theorem 1 says "every node v and context c". Context ranges over an arbitrary type `'c`. Say that nothing requires finitely many contexts, which matters for the entry-state remark at `sub:706-707`.

## Questions for the authors

1. Is there a formal statement showing that, under `calls_source_unique g`, the displayed (single-edge) Return obligation implies the proved one? If so, cite it. If not, which form do the routed instances actually discharge? (`routed_context_comb` is invoked with an arbitrary `p'` at `Routed_Context.thy:614-620`, which suggests the general form.)
2. For entry-state contexts, can you characterize A(v, c) without reference to σ, for example as the traces whose entered store abstracts to c under a best abstraction α, at least for non-relational domains? If not, what exactly does Theorem 2 assert for this policy beyond C ⊆ ⋃_c γ(σ(v, c))?
3. Does any theorem relate a single report row (v, c) to A(v, c) under the run policy, or is ℛ_res v (a union) the only report-level interface?
4. Is there a converse of `source_run_has_activation_trace` for compiled programs, that is, does C(v) equal the set of stores reachable by `cstep` at v? If it holds, DEAD becomes an exact unreachability statement at the CFG level.
5. What is the relation between `post_bounded` (in `dg_context_activation`) and the solver's `part_post_solution`? Which lemma bridges them, and does it use the read-closure conjunct?
6. Why is `__voblint_check` a no-op instead of a blocking step? Would a blocking semantics change any theorem? (It should only shrink C.)
7. What evidence, beyond inspection, supports the adequacy of `pstep`? For example, differential tests against a C compiler on the deviation-free fragment of the regression corpus.
