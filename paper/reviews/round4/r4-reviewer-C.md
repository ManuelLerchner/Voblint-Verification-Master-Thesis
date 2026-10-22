# Round 4, returning reviewer C (semantics and soundness proofs)

## Summary

I re-read the revised submission (`paper/reviews/round4/submission.txt`, cited as `sub:<line>`, with the LaTeX sources in `paper/sections/`), my round-3 report, the round-3 summaries and the "Round 3" part of `paper/reviews/response.md`. I checked every displayed formula and every new or renamed item of §§3–5 against the Isabelle sources at commit 2127b9b76. Paths are relative to the repository root. This was source inspection only; I ran no Isabelle build, so kernel acceptance of the cited theorems is **UNVERIFIED**.

The revision fixes everything I asked for in round 3. Table 1 now lists every assumption of `dg_context_activation` and `routed_context`, states both bounds of `post_bounded` and the query membership, and §4.1 places entry coverage with the routing conditions instead of `analysis_contract`. The entry-state formula keeps the call (`enter_e`, `route(u,c,d,e)`) and matches `routed_entry_context_rel`. The return rule keeps `Some`. The Boolean sentence no longer claims an evaluation order. `path_of`, `extend`, `entry_g` and `c_0` are defined, the key set is `W`, and the verdict set is typeset as calligraphic 𝒱, distinct from the solver's set `V`. The new material (call-equation display, live-set bridge, source rules, `at_node`, the per-context paragraph) agrees with the sources apart from small imprecisions.

The revision introduces two notation problems. `enter_e` now names both the concrete entry function (§3) and the abstract enter operation (§4.2). The Theorem 3 preamble names the residual command `c`, which undoes the round-3 rename to `r`. The abstract's contribution (ii) names the routing condition but still omits the local soundness of the analysis, and its gloss "a valuation that satisfies all of them" describes a total post-solution, whereas Theorem 2 needs bounds only on `W`. I found no formal mismatch that affects the end-to-end claim.

## Recommendation and Confidence

**Accept with minor revisions. Confidence 4/5.**

What remains is wording and notation, each fixable in a sentence. Confidence is limited by the absence of a build and by not re-auditing the full dependency closure.

## Resolution table (my round-3 points)

| Round-3 point | Status | Evidence |
| --- | --- | --- |
| Major 1a: `pp` row omits the side-effect bound | RESOLVED | Table 1, `sub:395–396` / `equations.tex:115`: "σ bounds the right-hand side and every side effect it publishes". Matches `post_bounded` / `tree_covered_at`, `vendor/td-verification/Basics_side.thy:588–591, 621–622`. §4.2 proof sketch (`sub:434–435`) says why both bounds are used. |
| Major 1b: `pp` row omits query membership | RESOLVED | "the query is in W" (`sub:395`); `post_bounded T x σ vars ⟷ x ∈ vars ∧ …` (`Basics_side.thy:622`). |
| Major 1c: entry coverage misattributed to `analysis_contract` | RESOLVED | `sub:339–343`: "Enter is not part of that locale … (entry_pairs_cover) is used by the routing conditions". Matches `src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy:337–351` (no enter law) and `routing_adequate`, `src/Abstract_Interpreter/Framework/Context/Routed_Context.thy:86–106`. |
| Major 1d: table claims "the assumptions" but is a summary (`cmb_wf`, `extra_wf`, `is_bot_bot`, reader consistency) | RESOLVED | Caption `sub:412–415` now says "all assumptions of the locales routed_context and dg_context_activation", and the rows now cover them all: `src/Abstract_Interpreter/Framework/Activation/DG_Ctx_Activation.thy:26–58` (`analysis_contract`, `cmb_wf`, `extra_wf`, `finE`, `pp`, `sg_cov`, `sg_uncov`, `fwd`) and `Routed_Context.thy:77–117` (`finC`, `calls_unique`, `seed_ne_buffer_key`, `seed_ne_global_of`, `is_bot_bot`, `is_bot_sound`, `resolve_sound`, `routing_adequate`, `routing_total`, `comb_fwd`). The only gap is inside a row (minor 1 below). |
| Abstract: "every post-solution" overstates Theorem 2 | PARTLY | `abstract.tex:14` / `sub:15–17` now adds "when the context policy agrees with the routing". It still omits the soundness of the analysis's transfers and combine (`analysis_contract`, `DG_Ctx_Activation.thy:26`), and the gloss "a valuation that satisfies all of them" is the total notion. See New issue 3. |
| Minor 1: entry-state formula drops the call | RESOLVED | `sub:383–384` / `equations.tex:93–96`: `{route(u,c,d,e) \| (q,d) ∈ enter_e(σ(u,c)), s ∈ γ(q), s′ ∈ γ(d)}`; `Routed_Context.thy:708–713`. |
| Minor 2: Boolean operators read as evaluation order | RESOLVED | `sub:599–600`: "Expressions are pure and total, so && and \|\| have no evaluation order to model." Consistent with the total evaluator (`src/Program_Model/VIMP/VIMP_Expr.thy:110–111` for division/remainder; round-3 lines 119–120 for And/Or, not re-read). |
| Minor 3: `Some` erased in the return rule | RESOLVED | `sub:207`: `caller_of t″ = Some t′`; `src/Program_Model/CFG/Collecting/Activation_Trace_Def.thy:120–122`. |
| Q3: compact source mapping | PARTLY (accepted) | No separate index, but every displayed rule and theorem now names its Isabelle constant inline. I do not insist. |
| *V* names two sets | RESOLVED | Theorem 2's key set is now `W` (`equations.tex:129,139`). The verdict set is `\Verd` = `\mathcal{V}` (`paper/macros.tex:22`), so it is typographically distinct from the solver's `V` (`equations.tex:162,184`). |
| `c₀`, `path_of`, `extend`, `entry_g` undefined | RESOLVED | `sub:195–199` defines `path_of`, `sink_*`, `caller_of`, `extend` and `entry_g`. `c_0` is defined at `sub:251` ("the initial context c0"), shortly after its first use in Figure 1 and the Root rule (minor 4). |
| VIMP list omits that `main` has no `return`, and stuck calls | RESOLVED | `sub:602–603` ("main has no explicit return"; well-formedness: `no_return (prog_main p)`, `src/Program_Model/Compile/Compile_Invariants.thy:99`). Stuck calls: `sub:489–490`. One stuck case is missing (minor 5). |
| Shipped enter has a single alternative | RESOLVED | `sub:236–240`; `admitted_contexts` instantiates `alts` with a one-element list (`src/Analyses/Shared/Result/DG_Analysis.thy:598–603`); `ov_two_contexts_admitted` exists (`src/Examples/Sign/Example_Sign_DG_Overlapping_Enter.thy:1040`). |

## Formula-by-formula table (§§3–5)

| Paper item | Isabelle file:line | Verdict | Note |
| --- | --- | --- | --- |
| Observers `path_of`, `sink_node`, `sink_store`, `caller_of`, `extend` (`sub:195–197`) | `Activation_Trace_Def.thy:54–83` | OK | `caller_of` returns `Some caller`; for `Resume` it descends `current`, as the prose says. |
| Trace datatype `Root π \| Call t′ π \| Resume t′ t″ π` (`sub:193–194`) | `Activation_Trace_Def.thy:41–47` | OK | |
| Root rule (`sub:201–202`) | `Activation_Trace_Def.thy:104–106` | OK | |
| Intra rule (`sub:203–204`) | `Activation_Trace_Def.thy:107–111` | OK | `step_a` = `edge_step a`. |
| Call rule, `enter_e(sink_store t)` (`sub:205–206`) | `Activation_Trace_Def.thy:112–119` | OK | `e` is the action `CallEdge dst pars args` and `enter_e` is `call_enter G e` (`src/Program_Model/CFG/CFG_Transfer.thy:63–66`). |
| Resume rule with `Some t′` (`sub:207–210`) | `Activation_Trace_Def.thy:120–130` | OK | `combine_e` is `combine_collect G dst` (`CFG_Transfer.thy:52–53`). It depends only on `dst`, so the subscript `e` is harmless. |
| "some call edge … not the edge through which the callee was entered"; `calls_source_unique` (`sub:215–217`) | `src/Program_Model/CFG/CFG_Def.thy:243–247` | OK | Uniqueness of all edge components per source node. |
| `adm_{u,c}(e,s,s′)`, five-argument policy (`sub:232–234, 241–242`) | `src/Program_Model/CFG/Collecting/Activation_Trace_Context.thy:64–65` | OK | "described by e and p" = `call_info_of e p`. |
| `adm^∃_{u,c}(p,s,s′)` (`sub:242–244`) | `Activation_Trace_Context.thy:89–97` (`admits_call_context`) | OK | Existential over the edge, equality with `call_enter`, admission. |
| Three carries rules (`sub:247–250`) | `Activation_Trace_Context.thy:133–143` | OK | Call rule's subscript `sink_node t, c` and arguments `(p, sink_store t, s′)` match. |
| `A(v,c)` (`sub:257`) | `Activation_Trace_Context.thy:437–443` | OK | |
| Init (`sub:268`) | `src/Program_Model/CFG/Collecting/Activation_Trace_Abstract.thy:49` | OK | |
| Intra (`sub:269`) | `Activation_Trace_Abstract.thy:50–51` | OK | |
| Call (`sub:270–271`) | `Activation_Trace_Abstract.thy:52–57` | OK | |
| Return, quantified over `p′`, `s′` (`sub:272–273, 276–278`) | `Activation_Trace_Abstract.thy:58–63` | OK | `es` is free and bound by `admits_call_context`, as stated. |
| Total (`sub:274`) | `Activation_Trace_Abstract.thy:64`; `Activation_Trace_Context.thy:408–416` | OK | Restricted to covered stores, as the prose says. |
| "Call strings and the unit policy … meet it for every cover" (`sub:292–293`) | `Activation_Trace_Context.thy:427–429`; both policies are `context_policy_of_fun` (`src/Executable_Surface/CLI/Analysis_Report.thy:535–538`) | OK | |
| Theorem 1 (`sub:295–297`) | `src/Abstract_Interpreter/Framework/Activation/Activation_Backbone.thy:34–36` | OK | |
| Proof idea: invariant, `caller_chain_covered` as an instance of `caller_chain_closure`, Total used twice, `activation_context_rel_caller_entryI` (`sub:299–310`) | `Activation_Trace_Abstract.thy:83–86, 162–212, 216–217`; `Activation_Trace_Def.thy:308`; `Activation_Trace_Context.thy:267–282` | OK | `return_covered` obtains `c′` from `TOTAL` along the callee's entry edge `e′` and applies `RETURN` with `adm′`, exactly as described. |
| `C(v) = ⋃_c A(v,c)` (`sub:311–312`) | `Activation_Trace_Abstract.thy:268–269` | OK | Inside the contract locale, as stated ("Within the contract"). |
| `γ(d,ρ)`; ρ = solved globals (`sub:324–326`) | `genv global_of sigma`, `DG_Ctx_Activation.thy:50–52` | OK | |
| `analysis_contract` reading (`sub:339–341`; Table 1 row 1) | `DG_Spec_Sound.thy:337–351` | IMPRECISE | Omits `spec_wf: dg_spec_wf S` (line 342). Table 1 claims all assumptions, so the row should mention it. Minor 1. |
| "output is read in the previous global values joined with what it publishes" (`sub:337–338`) | `DG_Spec_Sound.thy:345–347` | OK | `genv key τ ⊔ edge_pub …`. |
| `entry_pairs_cover` (`sub:342–343`) | `DG_Spec_Sound.thy:39–43` | OK | |
| Four sources of the node RHS (`sub:349–354`) | `src/Abstract_Interpreter/Framework/Constraints/DG_Indexed_Generator.thy:268–278` (`routed_node_rhs_parts`) | OK | init, intra edges in context `c`, calls, seed reads (`rhs_seed`). |
| `route` arguments: site, caller context, entry state, call (`sub:355–356`) | `DG_Ctx_Activation.thy:32`: `route :: pp ⇒ 'c ⇒ 'D ⇒ call_action ⇒ 'c` | OK | |
| Call display: `combine(q,⊥)` if `d` bottom, else publish `d` to `seed(p,c′)`; `r ← read(FunctionResult p, c′)`; `combine(q,r)` (`sub:356–361`) | `src/Abstract_Interpreter/Framework/Context/Routed_Call_Programs.thy:143–167` | OK (with two IMPRECISE details) | The shape and the bottom case match. (a) The seed key is `seed (FunctionEntry p) c′` (line 160), so `seed(p,c′)` abbreviates it. Harmless. (b) The contribution is generated per call site and folds over the callees that `resolve` returns from the caller state (`routed_call_program`, lines 227–244), not over the callee `p` of a fixed edge. With static resolution the two coincide. Since `resolve_sound` appears in Table 1, say so in one clause. Minor 2. |
| Entry equation reads `seed(p,c′)` (`sub:363`) | `Routed_Call_Programs.thy:249–259` | OK | |
| routing_adequate (`sub:371–374`) | `Routed_Context.thy:86–106` | IMPRECISE | "The callee's entry unknown in c′ is solved." The locale requires `(FunctionEntry p, ctx′) ∈ vars` (line 106), and in Theorem 2 `vars` is `W`, not the solved set `V`. `W ⊆ V` (`src/Analyses/Shared/Result/DG_Live_Unknowns.thy:235`), so "solved" is weaker than the premise. Say "is in W". The same applies to `sub:379` ("the routed entry unknown being solved"). Minor 3. |
| routing_total (`sub:375–376`) | `Routed_Context.thy:107–112` | OK | |
| Entry-state policy formula (`sub:383–384`) | `Routed_Context.thy:703–713` | OK (notation clash) | It matches clause by clause: `alts ci (dg_local σ(u,c))`, `caller ∈ γ cont`, `entered ∈ γ entry`, `ctx′ = route u ctx entry (CallEdge …)`. The shipped `alts` is `λci d. [entry_alt …]` (`DG_Analysis.thy:598–603`), so writing `enter_e` for `alts ci` is a fair reading, but it reuses the symbol of §3's concrete `call_enter`. New issue 1. |
| Table 1 (`sub:393–415`) | `DG_Ctx_Activation.thy:26–58`; `Routed_Context.thy:58–117` | OK (exhaustive) | Every named assumption of both locales appears. "seed keys differ from all other global unknowns" = `seed_ne_buffer_key`, `seed_ne_global_of`. `fwd`'s "non-empty state" means non-empty concretization (line 56), which is acceptable. Only `spec_wf` is hidden inside the `analysis_contract` row. |
| Theorem 2 premises: `(entry_g,c0) ∈ W`, `S0 ⊆ γ(d0, ρ0)`, `ρ0 ≤ ρ` (`sub:426–429`) | `Routed_Context.thy:585–590` | OK | `e₀` is renamed `ρ0`. The conclusion is `A ⊆ cover` with `cover = γ_M ∘ sg`, which equals `γ(σ(v,c),ρ)` on `W` and `∅` elsewhere by `sg_cov`/`sg_uncov`. |
| Theorem 2 proof sketch (`sub:431–437`) | `Routed_Context.thy:591–600` (Init via `pp_entry_init_local_bound` and `gammaDG_mono`) | OK | Init also uses `pp` and monotonicity, not only "initial state and ρ0 ≤ ρ". Acceptable as a sketch. |
| `part_post_solution` (`sub:443–445`) | `Basics_side.thy:337–343` | OK | |
| `live_unknowns` (`sub:450–452`) | `DG_Live_Unknowns.thy:230–233` | IMPRECISE | The definition also requires `(u,c) ∈ V` itself. The paper's wording ("the unknowns (u,c) such that u belongs to a procedure q whose result … is in V") omits this conjunct. "Live part of V" implies it, and `live_unknowns_of_result` (lines 237–246) shows it follows under well-formedness and termination. Minor. |
| Bridge steps: back-reachability to the result, `sol_vars_callee_result` for non-bottom entry (`sub:452–459`) | `DG_Live_Unknowns.thy:186–216, 218–228, 237–246` | OK | `sol_vars_callee_result` requires `entry_of … ≠ Bot` for the single shipped alternative, matching "whenever the routed entry state is not bottom". "The compiler ends every body with a return edge" was not re-checked against the compiler. The bridge uses `prog_node_reaches` (line 244), whose statement I did not read: **UNVERIFIED**. |
| `live_unknowns_cover` conclusion (`sub:459–461`) | `DG_Live_Unknowns.thy:251–254`; `src/Abstract_Interpreter/Framework/Constraints/CFG_Enumeration.thy:574–585` | OK | `ctx_vars_cover_live` gives entry membership, intra closure (unconditional, stronger than `fwd`), continuation closure and callee-entry closure. |
| `certified_solver`, four facts (`sub:467–470`) | `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:26–36` | OK | |
| "five update rules" (`sub:471–473`) | `src/Abstract_Interpreter/Solver/Globals_Rule.thy:18–23, 157–165` | OK | Five constructors. `Globals_Bounded_Narrowing nat` is a family, and the prose names only three kinds. Acceptable. |
| `pstep` Call / RestoreStep (`sub:485–489`) | `src/Program_Model/VIMP/VIMP_Proc.thy:140–155` | OK | The pushed frame holds the caller store and destination. RestoreStep computes `combine_assign dst (s ret_var) (combine_env G fr s)` = `combine_collect G dst fr s`. An explicit `return` reaches the same pop through `UnwindAct` (lines 165–167), which the citation omits. Minor 6. |
| Stuck calls (`sub:489–490`) | `VIMP_Proc.thy:140–143` | IMPRECISE | `Call` also requires `distinct (formals decl)`. Minor 5. |
| `csim_star` (`sub:492`) | `src/Program_Model/Compile/Simulation/Simulation_Preservation.thy:726–732` | OK | |
| `at_node` (`sub:495–497`) | `src/Program_Model/Compile/Elaborated_Compilation.thy:791–798` | OK | "some run of the elaborated program from s0 reaches an annotated configuration that erases to (r,s,frs), names v, and is related to v by the simulation" matches all four conjuncts (`erase c = r` on the command; store and frames are shared). |
| `if (b) {x = 1;} else {x = 1;}` example (`sub:493–498`) | same | IMPRECISE | "the configuration after either branch is observed at both branch nodes". For a fixed `s0`, each run of a deterministic program takes one branch. Two observations need two runs from `s0` that reach the same configuration through different branches, for example via the nondeterministic input or a loop. Write "can be observed". Minor 7. |
| `source_reaches_node_collect` (`sub:507–508`) | `src/Analyses/Shared/Result/Source_Activation_Sound.thy:126–131` | OK | |
| `csim_point_compile_prog` (`sub:508–509`) | `Elaborated_Compilation.thy:464–469` | IMPRECISE | The corollary states only `v = point c`, the node an elaborated configuration names. "Holds at every node where the run is observed" is its combination inside `run_voblint_source_sound`. Cite it as the ingredient. Minor. |
| `run_voblint` branches (`sub:512–516`) | `src/Executable_Surface/CLI/Analysis_Run.thy:475–483` | OK | |
| `R_res`, `𝒱_res` (`sub:518–520`) | `Analysis_Report.thy:41–42, 140–147` | OK | DEAD imposes no store constraint (`check_stores … Dead ⇒ UNIV`). The prose names only PROVED/REFUTED, which is correct. |
| Theorem 3 display (`sub:525–539`) | `src/Executable_Surface/CLI/Analysis_Certified.thy:196–208` | OK | Exact. |
| Preamble to Theorem 3 (`sub:521–523` / `theorem.tex:52–54`) | — | MISMATCH (notation) | "from residual command c". §5 renamed the residual to `r` (`theorem.tex:13`), and `c` is a context everywhere else. New issue 2. |
| `run_voblint_contexts` / `context_sound` (`sub:549–553`) | `Analysis_Certified.thy:55–58`; `Analysis_Report.thy:517–523` | OK (incomplete) | It bounds each `A(v,c)` by `R_res(v)`, as stated. `context_sound` also contains the first conjunct "every valid trace carries some context", which is what makes `C = ⋃ A` available at report level (`run_voblint_covers`, `Analysis_Certified.thy:87–95`). Mention it in half a sentence. Minor 8. |
| "No theorem about run_voblint certifies the row of an individual context" (`sub:551`) | Searched `Analysis_Certified.thy` and `Analysis_Report.thy` | OK as far as inspected | Absence beyond these files is **UNVERIFIED**. |
| Verdict theorems (`sub:579–585`) | `Analysis_Certified.thy:128–150, 286–298` | OK | |
| VIMP adequacy list (`sub:597–603`) | `VIMP_Globals.thy:29–41, 71–72`; `VIMP_Proc.thy:132`; `Compile_Invariants.thy:99`; `VIMP_Expr.thy:110–111` | OK | Callee locals start at 0 (`enter_state_apply`). Main's locals are unconstrained (`cinit_stores` constrains only globals). Check continues. Main has no return. |

## Symbols: defined before use, one meaning?

- `enter_e`: two meanings. In §3 (`traces.tex:43,47,124–128`) it is the concrete `call_enter`. In §4.2 (`equations.tex:96`) it is the abstract enter's alternative list `alts`. The plain word "enter" in §4.1 and §4.2 means the abstract operation. New issue 1.
- `c`: context throughout, but the residual command at `theorem.tex:53`. New issue 2.
- `p`: procedure in §§2–4, program (`p :: imp_prog`) in Theorem 3. The display forces it. Acceptable if one clause says so.
- `k`: continuation node (`sub:105`) and call-string length (`sub:228, 513`). Minor overload. Tolerable.
- `a`: action (`sub:103`) and the program variable `a` (`sub:109`). Tolerable.
- `e`: §3.2 says "For a call edge e into p" (`sub:241`), but in the 4-tuple `(u, e, FunctionEntry p, k)` the symbol `e` is the call action, not the edge. Write "call action e" or "call (u,e,…)".
- `d`: "an abstract state d" generally (`sub:324`) and "the entry state d" of a pair (`sub:330`). Compatible.
- `σ`: first used at `sub:358` ("σ(u,c)") and first named at `sub:381` ("the solved valuation σ"). §1 introduces post-solutions without a symbol. Name σ in §4.1 next to ρ.
- `c_0`: used in Figure 1 (`sub:114`) and the Root rule (`sub:248`) before `sub:251` defines it. Acceptable.
- `W`, `V`, `𝒱_res`, `ρ0`, `seed`, `route`, `adm^∃`, `path_of`, `extend`, `entry_g`, post-solution, locale: defined before or at first use, one meaning each.
- `resolve`: appears only in Table 1 ("callee resolution"). The call display never mentions it. Minor 2.

## Does the abstract state contribution (ii) with its conditions?

Partly. `abstract.tex:14` / `sub:15–17` now names the routing condition ("when the context policy agrees with the routing") and the solver interface ("only through its certificate"). Two conditions are still missing.

1. **Local soundness of the analysis.** `analysis_contract` (transfer and combine soundness, monotone γ) is a hypothesis (`DG_Ctx_Activation.thy:26`). Without it, no post-solution meets the contract. Routing agreement does not imply it. The initial-state premises (`Routed_Context.thy:587–588`) are also absent, but those are routine.
2. **Total versus partial.** "(a valuation that satisfies all of them)" is a total post-solution. Theorem 2 is stronger and different: it needs bounds only on a set `W` closed under execution (`pp`, `fwd`, `comb_fwd`), and the pipeline instantiates it with the live subset of a partial solution. The gloss is correct for the total special case, but it describes neither the theorem as stated nor its use.

Suggested wording: "(ii) a proof that a valuation bounding the generated, context-routed equations on a set of unknowns closed under execution meets the contract, provided the analysis's transfers and combine are locally sound and the context policy agrees with the routing; the verified solver enters only through its certificate." The introduction (`introduction.tex:41`) has the same gap.

## New issues

1. **`enter_e` overloaded (introduced by the round-3 fix).** `traces.tex:43,47` defines `enter_e` as the concrete store transformer. `equations.tex:96` applies `enter_e` to an abstract state `σ(u,c)` and draws pairs `(q,d)` from it. A reader checking the formula against §3 sees a type error. Use `enter^♯_e` (the Isabelle source already writes `enter♯`, `src/Abstract_Interpreter/Framework/Spec/DG_Spec.thy:65`) or `alts_e`, and use the same symbol in the call display (`equations.tex:58`).
2. **Residual command named `c` again (`theorem.tex:52–54`).** The round-3 response says the residual command is now `r`, and `theorem.tex:13,27` use `r`. The Theorem 3 preamble reintroduces `c` and `c′`, two lines before a theorem whose surrounding text uses `c` for contexts (`theorem.tex:74–76`). Rename to `r, r′`, or use `residual` as in the display.
3. **Abstract (ii) and its gloss.** See the previous section. The gloss was added in this revision and now describes the total case.
4. **"Solved" where the premise is "in W"** (`equations.tex:83,90`). This sentence is new in the routing-conditions paragraph. Because §4.3 then separates `V` and `W` carefully, the reader may conclude that adequacy only needs `(FunctionEntry p, c′) ∈ V`. The locale needs membership in `vars = W` (`Routed_Context.thy:106`).
5. **Call display omits resolution** (`equations.tex:55–62`). The paper says "for a call edge (u,e,FunctionEntry p,k)", but `routed_call_program` (`Routed_Call_Programs.thy:227–244`) reads the caller state once and folds over `resolve v cc ca (caller_state)`. Table 1's `resolve_sound` row then has no antecedent in the text. One clause fixes it: "for each callee p that resolution returns (with static resolution, the callee of the edge)".

## Minor comments

1. Table 1, `analysis_contract` row (`equations.tex:114`), and `sub:339–341`: add `spec_wf` (well-formed specification, `DG_Spec_Sound.thy:342`) so the caption's "all assumptions" holds literally. Note also that γ is monotone in both arguments (line 343–344).
2. `equations.tex:57–62`: see New issue 5. Also note that `seed(p,c′)` abbreviates `seed(FunctionEntry p, c′)`.
3. `equations.tex:83,90`: "is in W" instead of "is solved" (New issue 4).
4. `c_0` first appears in Figure 1 and in the Root rule before `traces.tex:100` defines it. A forward phrase in §3.2 ("the root context c_0") would suffice.
5. `theorem.tex:17–19`: the `Call` rule is also stuck when the formals are not distinct (`VIMP_Proc.thy:142`). Add "or whose formals repeat", or say "ill-formed calls are stuck".
6. `theorem.tex:15–16`: "the marker pops the frame (rules Call and RestoreStep)". After an explicit `return`, the pop is `UnwindAct` (`VIMP_Proc.thy:165–167`), with the same store computation. Cite both, or say "Restore (directly or after Unwind)".
7. `theorem.tex:27–30`: "the configuration after either branch is observed at both branch nodes". This needs two runs from `s0` that reach the same configuration through different branches. Write "can be observed at both", and perhaps let `b` read the input.
8. `theorem.tex:72–76`: `context_sound` also requires that every valid trace carries a context (`Analysis_Report.thy:520–521`). That conjunct is what gives `C = ⋃_c A` at report level. One half-sentence would make the per-node/per-context paragraph complete.
9. `traces.tex:88` ("For a call edge e into p"): in the 4-tuple, `e` is the call action. Reword.
10. Name σ in §4.1 next to ρ (`equations.tex:15`), since `equations.tex:58` uses it before `equations.tex:93` defines it.
11. `sub:452` (`live_unknowns`): add "(u,c) ∈ V and" to match `DG_Live_Unknowns.thy:232`, or keep "live part of V" as the definition and drop the "such that" gloss.
12. `sub:508–509`: cite `csim_point_compile_prog` as the lemma that fixes the observed node (`v = point c`), not as the all-nodes statement.
