# Goblint Alignment Register

Status: **living audit.** This is the canonical long-term record of where the
formalization differs from upstream Goblint, why the difference exists, and what
would close it. It is an architecture register, not a thesis backlog. Active
work is tracked in GitHub Project 8; the migration plans this register once linked are in `docs/history/`.

## Target and evidence

**Target.** Model the semantic and solver-facing parts of Goblint's analysis
framework closely enough that each deliberate simplification is explicit,
justified, and replaceable. Exact source-level reproduction of CIL, every
analysis, and every manager service is not implied by this target.

**Upstream baseline.** Goblint `analyzer` `master`, checked 2026-07-16 at
`8d32b6b3d8cc08c5455817895b3af6eb5b00c21a`. The directly checked source is
[`constraints.ml`](https://github.com/goblint/analyzer/blob/8d32b6b3d8cc08c5455817895b3af6eb5b00c21a/src/framework/constraints.ml):
`FromSpec` defines local unknowns as `(node, S.C.t)` and its normal-call path
uses `enter`, derives a callee context, seeds the callee entry, and combines
callee exits through `combine_env` and `combine_assign`.
The explainer's comparison and the thesis pin the later `master` revision
`5320a6b741e50dc049f7a1b85e1709e9565cc54a` (checked 2026-09-15): `constraints.ml`
is unchanged from the baseline, and `analyses.ml` differs only in lattice
printing configuration, so the normal-call protocol reads the same at both.

Evidence labels:

| Label | Meaning |
| --- | --- |
| **source-checked** | Checked against the upstream baseline above. |
| **local-checked** | Checked against the named Isabelle source or migration document. |
| **inference** | Architectural conclusion from the checked facts; re-check before implementation. |

## Alignment snapshot

| Area | Current state | Difference from Goblint | Why it exists | Closure path | Status |
| --- | --- | --- | --- | --- | --- |
| Source language | Scalar, procedural **VIMP** (`manifests/vimp-grammar.yaml`, `src/Program_Model/VIMP/`). No AFP IMP2 bridge exists: `to_imp2`, `IMP2_Bridge.thy` and `backward_sim` are absent from the tree, and soundness is stated against VIMP's own semantics only. | Goblint analyzes C/CIL programs, including memory, types, and library semantics. | A small executable language permits end-to-end collecting and compiler proofs. | Arrays, then a C/CIL front-end model only after a concrete proof target is selected. | Deliberate scope boundary. |
| CFG and collecting semantics | Verified interprocedural CFG, trace collecting semantics, a separate four-place `calls` relation labelled `CallEdge`, and combine triples. | Goblint consumes its C CFG and has framework-specific node/edge forms. | The CFG is the proof-level semantic interface; reproducing CIL CFG construction would dominate the current proof. | Specify a translation relation from a selected Goblint CFG fragment before claiming CFG fidelity. | Inference; no active migration. |
| Unknown space and contexts | One generalized D/G executable generator over the elaborated CFG. `run_voblint` offers two context policies (`context_policy`, `Analysis_Config.thy`): call strings of bound `k`, where `k = 0` is context-insensitive, and entry states. Every activated analysis runs under both, with a routed collecting-soundness certificate (`activation_collect_dg_sound`) and source-level endpoints (`fun_route_result_node_sound` and `entry_state_activation_collect_sound_of_terminates` in `DG_Live_Unknowns.thy`; `run_voblint_call_string_chain` and `run_voblint_entry_state_chain` for the analyzer). | Goblint's `FromSpec` local variable is `(node, S.C.t)` and selects context at calls. | The semantic layer was built before the executable route; the generic route seeds the callee entry dynamically. | None; `docs/history/ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` records the route. | Done: generator, routing, certificate and source lift. |
| Context input boundary | Context is selected from the post-enter callee state (`route` on the entered frame; the relation `call_context_policy` on the entered store), matching `context man f callee_state`; argument-sensitive context is expressible. | Goblint's `Spec.context` receives a local `D.t`; global information is available through the manager/global channel, not by framework-level joining. | The prior caller-store / joined `side_env_cmp` read could not express argument context; routing on the entered callee state fixes it. | The manager/query channel remains a simplification. (`point_digest` and `ENTER_MONO`, named here previously, were removed with the digest layer and occur nowhere in `src/`.) | Callee-state routing done; the routed collecting certificate is proved: `entry_state_activation_collect_sound` (`dg_analysis`, `DG_Analysis.thy`) goes through `activation_collect_dg_sound`. The load-bearing assumption is `routing_adequate` (`routed_context`): at a real call edge, some alternative of the spec's own `enter♯` run covers the caller and entered stores, and the context `route` assigns to that alternative's entry is one the policy admits (through `routed_entry_context_rel`). Functional policies (call strings, of any bound) discharge it via `context_policy_of_fun`. A context selector that decodes the entered store, which no instance has, is where that obligation would have to be earned. |
| Context selector: function vs relation | The executable selector `route` (`context♯`) is a function applied per `enter` alternative. The collecting semantics selects through a relation, `('v, 'e, 'c) call_context_policy`, threaded over traces by the inductive `activation_context_rel`; `activation_collect` is indexed by it. | `Spec.context : man -> fundec -> D.t -> C.t` is a function; `enter` returns `(D.t * D.t) list`, and each alternative's callee state is routed separately. | Because `enter` returns a list and each alternative routes on its own, one concrete call may be admitted in several contexts; a function cannot state that, a relation can. Buckets are therefore a cover, not a partition. Totality is conditional: `call_context_total_on` rejects an empty relation only where a covered call exists, and routed instances derive it from `entry_pairs_cover`. | Nothing structural. An earlier relational layer (`admiss`/`ctx_key`) was removed in f0588428 because every instance wrapped a function and nothing exercised the generality. The multi-alternative overlapping-entry regression that exercised this one (`Example_Sign_DG_Overlapping_Enter`) was removed with the mathematical-integer analysis instances and has no port (`docs/theorem-migration.toml`); no shipped component answers more than one alternative (see `Call entry and return`). | Aligned. Recorded deviation in naming only: `context` is an Isar outer keyword, so the identifier stays `route` with notation `context♯`. The `TOTAL` obligation of `activation_coverage` is what makes the buckets exhaust `node_collect` (`node_collect_eq_Union_activation_collect`). |
| Call entry and return | VIMP's `CallEdge` carries the actuals, the formals and an optional destination. The concrete entry (`call_enter`) and return merge (`combine_collect`) are fixed; abstractly, `enter`, `combine_env` and `combine_assign` are component fields (`ls_enter`, `ls_combine_env`, `ls_combine_assign` of `local_spec`, `MCP_Spec.thy`). `ls_enter` yields a list of alternatives. | Goblint's `enter` can return several caller/callee states; `combine_env` and `combine_assign` are analysis operations. | The fixed concrete operations are VIMP's call semantics; the abstract ones follow `Spec`. | Multi-result entry through the analysis pipeline: lift `enter_single` from `dg_analysis`. The routed generator already folds a contribution list at the call site. | Analysis-defined `enter`, `combine_env` and `combine_assign` implemented. Multi-result `enter` is supported by the routed generator, which folds a list of alternatives, and by the collecting semantics, which admits each alternative's context through the policy. The analysis pipeline does not use it: `dg_analysis` assumes that a component's entry answers one alternative (`enter_single`, `DG_Analysis.thy`), and every shipped component answers one. Single-result entry through the pipeline is therefore a recorded deviation again; the regression that exercised several alternatives was removed (see the previous row). |
| Call-target resolution | The generator emits one program per call **site** (`call_site_list`). The site reads the caller local and the shared global once, asks a resolver which procedures it can enter, and joins their contributions with `side_rhs_fold_dg`; `routed_callee_call_program` carries one resolved callee's seed publication, exit read and combine, addressing the exit as `(FunctionResult p, ctx')` derived from the resolved name. The resolver `resolve :: pp => pp => ('vr, 'e) gcall_action => 'D => pname list` receives the caller's abstract state, so the target set is computed while solving, not while the equation system is built. | Goblint's `tf_proc` resolves a target set from the abstract state (`Queries.EvalFunvar`, direct-call fast path) and the call-site RHS iterates it. Goblint's call edge carries a callee *expression*; `('v, 'e) gcall_action = CallEdge ('v option) ('v list) ('e list)` carries none, so a resolver here can narrow the CFG's candidates but cannot dispatch on a function value. | The structural `calls` relation is what `wf_cfg`, `call_enter`, `valid_activation_trace` and the renderer read; it is retained for the concrete semantics. VIMP has no indirect-call syntax, so there is no callee designator to resolve from. | Done for the equation shape (#142 W1). Expressing dynamic dispatch additionally needs an indirect-call production in `manifests/vimp-grammar.yaml`, a callee designator in `gcall_action`, candidate `calls` edges from the compiler, a domain that can abstract a function value, and one resolver instance with its `resolve_sound` proof. | Closed for the equation shape. The resolver reads the caller state and may drop a target that a concrete store at the site rules out (`resolve_sound`); it may not drop one that a store reaches. Residual: every instance pins `static_resolve g`, which discards the state and answers from `calls g`, so the generated equations denote exactly what they denoted before and **no instance varies the parameter**; no indirect call is expressible. |
| Function-entry unknown | The callee entry state is side-effected into a **global** proxy `Inr (Seed (FunctionEntry f) ctx)`; the callee's local `(FunctionEntry f, ctx)` reads it back through `routed_entry_seed_programs`. | Goblint's `sidel (FunctionEntry f, fc) v` targets a **local** unknown in the same variable space as every program point, with no CFG predecessors, so its value is exactly the join of the contributions. | The vendored `TD_side` solver's `Side` targets globals only (`Basics_side.thy`); there is no `sidel`. | **Recorded decision not to pursue a `SideL`-capable solver** (#142 W2, 2026-08-24). Adding a `SideL` constructor is trivial; integrating it means forking the vendored `TD_side` solver and thereby owning its post-solution and termination proofs permanently, re-earning them on every upstream change, and generalizing `buffer_sides` against the repeated-contribution hazard of #123 -- against a fixed gain in architectural fidelity and no new theorem. Reopen only if `sidel` lands upstream. | Closed as a recorded deviation. Consequences: one extra unknown per (callee entry, context) with no Goblint counterpart; the proxy has no equation of its own, and `run_voblint` merges contributions into it with the selected global rule (`update_global_of`, `Globals_Rule.thy`) like any other global key, so under `Globals_Warrow` or `Globals_Warrow_Per_Origin` a seed can be widened; anything enumerating local unknowns sees a variable Goblint does not have; and `run_voblint`'s globals column lists each seed beside the analysis-wide global, where Goblint's globals pane has no entry-state rows. **No operational equivalence to Goblint's fixpoint is claimed**; in particular the placement of widening differs, and the direction of that difference is unproved. |
| Call protocol order | A call program publishes the callee's seed and then reads the callee's exit (`routed_call_alternative_program`). `buffer_sides publish_before` decides when the publication reaches the solver (`Strategy_Tree_Side_Buffering.thy`): `routed_node_rhs_buffered` flushes the pending writes before every local read at a node where at most one call returns, so there the seed is published before the exit is read, and flushes at the answer at a node where several calls return. | Goblint's `tf_normal_call` runs `sidel (FunctionEntry f, fc) v` for every non-bottom path, then `getl (Function f, fc)` for each ([`constraints.ml` L242-L245](https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/framework/constraints.ml#L242-L245)), and its solvers apply a side effect the moment the right-hand side issues it: `side` joins or widens it into `rho` and destabilizes the target at once ([`td3.ml` L475-L519](https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td3.ml#L475-L519), [`td_simplified.ml` L88-L108](https://github.com/goblint/analyzer/blob/5320a6b741e50dc049f7a1b85e1709e9565cc54a/src/solver/td_simplified.ml#L88-L108)). The callee is therefore first solved from the published entry state. | The vendored update rules keep one contribution per origin and overwrite it (`update_global_per_origin`, `update_global_warrowing_per_origin`, `Update_rules.thy`), so a right-hand side that writes one key twice records a partial contribution first in every evaluation. Two calls resuming at one node can write the same seed (both branches of a conditional ending in a call), and flushing before the first call's exit read would split that seed into two writes. Answer-only flushing there keeps `distinct_side_path_buffer_sides_answers_only`. | None without a solver that joins repeated writes from one origin, which is the fork W2 declined. | **Matches Goblint's order at nodes where at most one call returns** (#251): the callee is solved once, from its seed, instead of first from bottom and again after the answer's flush. Still different: (1) at a node where several calls return, every seed waits for the answer and the first call's callee is solved from bottom first; (2) Goblint publishes the seeds of all `enter` paths before reading any exit, Voblint publishes each alternative's seed before its own exit read, which differs only for a multi-alternative `enter`, and no shipped specification has one; (3) writes other than seeds still wait for a flush point, where Goblint applies every `sideg` at once. `distinct_side_path_buffer_sides` bounds the writes at one key to one per evaluation only under `settled_writes`; the generator meets it when no call program writes a seed again after reading an exit, an argument about the hooks rather than a theorem. |
| Local/global payloads | `dg_spec` takes separate local and global carriers (`'dl`, `'dg`). `dg_pipeline` wraps an analysis's component in one of two placements. By default it uses the whole-state placement (`dg_analysis_whole_stateI`): one abstract state carries locals and VIMP globals, and the global channel stays inert. Under `--program-globals flow-insensitive` the keyed lifter (`keyed_split_spec`, `DG_Keyed_Split_Spec.thy`; `dg_analysis_keyedI`) publishes each declared global at its own unknown `Analysis_Global x`. | Goblint distinguishes `D.t` local and `G.t` global lattices. | Whole-state routing keeps each domain's transfer and gamma proofs pointwise. | A shipped domain that publishes globals through `'dg`, with gamma over the pair. | Interface split; exercised by the keyed placement, with both channels over the same carrier. |
| Relational state | Pointwise abstract states in every numeric domain. The order analysis (`Order_Analysis.thy`, carrier `order_rel`) runs a non-pointwise carrier through the same generator. | Goblint analyses may use opaque relational local states; product maps cannot represent cross-variable constraints faithfully. | Pointwise Sign and Interval make executable transfer and gamma proofs direct. | Abstract-state interface with sound projection/merge operations; prerequisite for an Octagon result. | Deferred. |
| Named globals and side effects | `QueryG`/`Side`, finite keys, and D/G routing are modeled. An analysis now supplies its own global-name type `'v` and reaches shared state only through `man_global m v` / `man_sideg m v g` (`DG_Manager.thy`); `mk_dg_man d key` holds the embedding `'v => 'k`, so no transfer constructs a solver key. | Goblint's `Spec` supplies `module V : SpecSysVar` and its manager has `global : V.t -> G.t` and `sideg : V.t -> G.t -> unit`. `base.ml` uses a non-trivial namespace (privatization globals, thread-return globals) rather than one global cell. | Before this, the manager had one implicit global and `man_sideg` took only a value, which is the shape a single-cell analysis needs and no more. | Payload separation (`'dl` vs `'dg`) and per-global update rules remain. | `'v` aligned, 2026-09-02; exercised 2026-10-03. The combined analysis under `--program-globals flow-insensitive` takes `'v = var_id`: one unknown per declared global, each edge reading only the globals its expressions mention and publishing only the globals it may assign (`keyed_split_spec`, `mcp_cs_keyed`). Under the whole-state placement (`mcp_cs`, `mcp_es`) nothing is published at an analysis global. A call reads only the globals its arguments mention (`call_global_reads`) and passes every other global as `split_free`; the analyzer recomputes the call's context outside the solver from the same view of the solved environment. |
| D/G reconstruction and publication timing | One concretization target: `gamma_ownership_split gs` (`ownership_split_lift`; both removed from `DG_Ownership_Split_Spec.thy` 2026-10-07 as unused by `run_voblint`, whose flow-insensitive placement is `keyed_split_spec` with `keyed_split_contract`), exclusive local/global ownership routing via `combine_env`. The former second target `gamma_join` (`ownership_split_dg_spec_placed`, a non-exclusive covering by `keep_local`/`publish_side` joined through the raw lattice join) and its one-way refinement `gamma_ownership_split gs d g \<subseteq> gamma_join d g` are removed. | Goblint's own privatizations (`basePriv.ml`, e.g. `VojdaniPriv`) keep a protected global's current value in the local `CPA` without publishing it; publication happens later at unlock/thread-transition/escape. `base.ml`'s single-threaded path reads globals from local state without publication at all. | A declared global need not always live in the global summary right now — Goblint's criterion is protection/publication state, not the static local/global classifier `gs`. `combine_env gs` can only route on that static bit, so it is sound exactly for exclusive-ownership analyses and unsound for placements where a global's live value is routed by something else. `docs/history/DG_GAMMA_UNIT_VS_GAMMA_JOIN_AUDIT.md` retains the counterexamples and source citations; the Isabelle theories it cites no longer exist. | Removed the generic local/global placement-policy experiment. Current Goblint exposes no analogous framework abstraction: an analysis defines its own `D`, `G` and keyed global namespace `V`, and reaches globals through `man.global`/`man.sideg`, rather than declaring a component-placement policy the framework applies. An analysis-specific sharing policy such as Base privatization (`basePriv.ml`) should be modelled as that analysis's own semantics over a keyed manager, not as a generic placement layer. | Closed by removal, 2026-09-02. Deleted `Placement_Policy`, `Placement_Policy_Exec`, `Example_Sign_Placement`, `Example_Interval_Placement`, `Example_Placement_Regression` and `Example_Interval_Global_Flow_Sensitivity`, which was built on the same `ownership_split_dg_spec_placed_st` mechanism. Nothing in the analysis pipeline used any of them. |
| Update rules | Five vendored update rules for a side-effected global unknown, chosen per run by `globals_rule`: always-join, per-origin, Apinis warrowing, warrowing-per-origin and bounded narrowing (`Globals_Bounded_Narrowing`). Local unknowns are warrowed at widening points under every rule. | Goblint permits analysis-specific update/widening policies, including origin-sensitive behavior. | Solver interface was kept close to vendored TD. | Choose the rule per analysis or per unknown rather than per run. | Solver-level choice done: one `TD_side_rule_Interp` interpretation takes the rule as a parameter, and every domain answers every rule at every context policy. See the origin-sensitive boundary example below. |
| Analysis interface layering | An analysis supplies one `local_spec` (`MCP_Spec.thy`): a query handler and one pure transfer per edge kind, entry and both return stages, each receiving the query channel, with soundness obligation `sound_local_spec`. `dg_spec_of` turns it into a manager-native `dg_spec`, one transfer per edge action, matching `Spec`'s method-per-construct shape; `dg_spec_of_contract` proves that the result meets `analysis_contract`. The placement of `dg_pipeline` wraps it (whole-state, or `keyed_split_spec` for flow-insensitive program globals). | Goblint's `Spec` is the single analysis interface, and `Spec2Spec` functors (privatizations, `DeadCodeLifter`, path-sensitivity) transform one `Spec` into another. | The `domain_transfer` record predated the manager-native spec and survived as a second, pure interface beneath it, so each domain supplied two things where Goblint supplies one; its `tf_combine_env` field reached no compiled equation. | Make the reachability lift a `Spec2Spec` too. It changes the local carrier (`'D` to `'D lifted`), which the `strategy_program` state type does not currently let a lifter rewrite, so it needs a state-mapping natural transformation on trees first. | One interface, 2026-09-04. `domain_transfer`, `apply_tf` and the per-domain `*_tf_for` bundles are gone (listed in `scripts/retired_identifiers.txt`). The non-relational component, both proof-side (`nonrel_spec`) and executed (`nonrel_exec_spec`), splits the environment merge (`ls_combine_env`, the global merge `combine_env is_global` or `combine_default_st`) from the return write (`ls_combine_assign`), as Goblint does; the order component's `ls_combine_env` is the identity (`combine_env_identity`). `ls_enter` returns a list of pairs of caller continuation and callee entry, as Goblint's `enter` does, though the pipeline accepts one pair (`enter_single`). |
| Multi-analysis manager | `mcp_registry` (`MCP_Registry.thy`) over `local_spec` components (`MCP_Spec.thy`): the activated analyses share one combined state, one field each, in one solve. Every operation (handler, edge step, entry, both return stages) receives the query channel, and the return stages also the callee's. `mcp_combine_sound` proves a list of sound, pairwise-framed components sound (`mcp_comp_sound` for the registry); the state is `Bot` once one active field is (`mcp_norm`). A component is pure: no `man.global`/`man.sideg`, no `emit`, `spawn` or `split`, and `combine_assign` receives only the callee's channel. | `MCP2` (`mCP.ml` at `0dc12d355`) runs each activated `Spec` on its part of a `DomListLattice` state through `inner_man`, tags globals as `(n, v)`, raises `Deadcode` when one component does, enters with the cartesian product of the alternatives, and handles events, spawns and splits. `combine_assign` asks about the state `combine_env` produced (`constraints.ml`). | Globals, events and threads serve concurrent C. Return soundness is stated only for the composite of both stages, so the intermediate state has no concretization to ask about. | Per-analysis globals need components that are effectful `dg_spec`s and a routed pipeline over them. | Implemented and proved for local components; per-analysis globals open. |
| Value domains | Two integer families. The Int analysis `run_voblint` runs is `int_tuple` (`Int_Tuple_Kind.thy`): the reduced product of Interval and Congruence at machine kinds, after Goblint's `IntDomTuple`, whose type parameter (`int_never`, `int_once`, `int_fixpoint`) selects the refinement mode. The value-level library `int_dom` (`Int_Lattice.thy`) is a record of four always-present components (sign, interval, parity, congruence), with `Int_Refinement` reducing between them (`refine_interval`, `refine_congruence`); it is also the type query answers are expressed in (`answer = int_dom query_lift`). Sign and Parity run as analyses of their own. | Goblint's `IntDomTupleImpl` is six *optional* slots -- `DefExc`, `Interval`, `Enums`, `Congruence`, `IntervalSet`, `Bitfield` -- each switched by `ana.int.<name>`, with `None` handled throughout. | A fixed component set makes the componentwise lattice and gamma proofs direct. | Optional components, and further components in `int_tuple`. A general `DefExc`/exclusion-set component is **not planned**; see Status for the infeasibility argument. | **Divergence in both directions.** The CLI's default refinement mode is `Refine_Fixpoint` (`cli/result/analysis_request.ml`), where Goblint's `ana.int.refinement` defaults to `never` (source-checked in `docs/history/TYPED_CFG_PLAN.md`, "Stage 6 reference"); `--int-refinement never` selects Goblint's behaviour. `sign` and `parity` model nothing upstream; `DefExc`, `Enums`, `IntervalSet` and `Bitfield` are unmodelled here. The components of `int_tuple` are structurally mandatory, so `--disable ana.int.interval` has no analogue. `int_tuple` refines the congruence by the interval (`cong_refine_with_ivl`, Goblint's `Congruence.refine_with_interval`) and then the interval by the congruence (`refine_ivl_with_congruence`), never, once or to a fixpoint (`it_refine_mode`), a transliteration of `ana.int.refinement`. A comparison takes the interval's answer and falls back to the congruence's (`cmp_ik_int_tuple`); `IntDomTuple`'s `map2bool` takes the components' common answer (source-checked 2026-09-29 against `5320a6b7`, `intDomTuple.ml`). **Recorded decision not to add a general `DefExc` component** (issue #162, 2026-08-24, closed not planned), argued for `int_dom` over unbounded `int`: infeasible as a persistent, join-surviving field, not merely unproved. The `bounded_lattice` instance of `int_dom` (`Int_Lattice.thy`) requires each component's `\<squnion>` to be a genuine least upper bound. For any type combining an exact-singleton constructor (`Def x`) with a finite-exclusion/cofinite constructor (`Exc s`, `gamma = UNIV \ s`) over unbounded `int`, `join (Def x) (Def y)` for `x \<noteq> y` has no least upper bound: `Exc {p}` is a valid upper bound for every `p \<notin> {x, y}`, and these are pairwise incomparable (`Exc {p1} \<le> Exc {p2}` iff `p1 = p2`), so no single value is `\<le>` all of them simultaneously. The semilattice law (`y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x`, instantiated at every such `x`) forces `gamma (join (Def x) (Def y)) = {x, y}` exactly -- a finite two-element set -- which no cofinite (finite-exclusion) representation can express, regardless of how the carrier datatype is shaped: bounding the tracked-literal universe to a small closed set (mirroring `sign`'s existing `\<noteq> 0` special case) sidesteps the impossibility but drops genericity, since it can only ever exclude literals fixed at type-definition time, not arbitrary source-program constants. Goblint's own `DefExc` avoids the impossibility only because `Excluded (s, r)` is bounded by the ikind's bit-range `r`, making the exclusion-supersets of `{x, y}` finite and hence possessed of a genuine maximum; even there Goblint's actual `join` (exclude `0` unless one operand is `0`) is not that least upper bound, merely sound -- OCaml's `Lattice.S` does not enforce leastness the way this project's `semilattice_sup` class does. Over unbounded `int`, closing this would require weakening `bounded_semilattice_sup_bot` project-wide to an extensivity-and-monotonicity-only contract, which touches the sort constraint across the generic D/G/solver framework (`src/Abstract_Interpreter/Framework/*`, `Solver/Strategy_Tree_*`, `Exec/State/Default_St_*`, ...) and loses the free `comp_fun_idem` derivation every `Finite_Set.fold` join relies on (`comp_fun_idem_sup`, cited in `Contextual_Check_Report`). The argument depends on unbounded `int`. Analysis values carry their kind (`'a kd`, `Kind_Lifted.thy`), and every kind has a finite range, so a range-bounded exclusion set, as in Goblint's `Excluded (s, r)`, does have least upper bounds; a kind-bounded `DefExc` is not planned, but this obstruction does not rule it out. A *transient* refinement -- an immediate interval-endpoint shrink or `sign`'s existing `\<noteq> 0` special case applied at the guard itself, never materialized as a persistent field -- remains open and does not hit this obstruction, but only closes boundary-touching cases (the excluded literal sits at an interval endpoint, or is `0`), not an interior exclusion hole (`x \<in> [-5,5]`, exclude `0`), which no non-relational, non-`Enums` component can represent regardless of persistence. |
| Integer width and wraparound | Every program is machine-integer VIMP. Each variable has a kind (`ikind`, default `I32`); elaboration (`elaborate`, `elab_com`) makes every conversion explicit, `eval` wraps each arithmetic node into its kind with `ik_norm`, and assignment, arguments and returns convert to the destination's kind (`kind_conv`). Abstract values carry their kind (`Kind_Lifted.thy`), and each domain implements kind-parameterised operations (`*_Kind.thy`). Signed overflow is a run option, `Assume_Top` (default) or `Assume_Wraparound`, and every possible signed overflow (a signed `%` by its quotient), division or remainder by zero and conversion that may not fit its target kind is reported. | Goblint parameterises every `IntDomain` operation by `ikind`, normalizes with `norm ik` and `sem.int.signed_overflow`, and also warns about unsigned wraparound, which Voblint does not report (`tests/regression/27-signed-overflow/README.md`). | One language: the analyzer and its soundness theorem are about the machine-integer semantics `pstep` itself. | Report unsigned wraparound if a client needs Goblint's warning. | **Aligned, proved**: `run_voblint_source_sound` and `run_voblint_SAFE` hold for the machine-integer semantics. Goblint not re-run for this row. |
| Value printing | Each domain's `to_string` follows Goblint's `show`: congruence `5`, `3ℤ`, `1+3ℤ`, `ℤ`; interval `[l,u]`; Int (`int_tuple`) a constant as the integer, otherwise `intervals:…; congruences:…` (`to_string_int_tuple`); a standalone value's top as `⊤`, as `IntDomLifter` prints it. Isabelle string literals are ASCII-only, so printers emit symbol tokens (`<int>`, `<top>`, …) that the CLI's `Value_symbols` decodes to Unicode on the answer `run_voblint` returns. | Bottom is `⊥` in every domain, where Goblint's congruence prints `⟂` and its interval `bottom`. Unbounded interval ends print `-∞`/`+∞`, where Goblint prints the ikind's limits. Sign (`- ≤0 0 ≥0 +`), parity (`2ℤ`, `1+2ℤ`) and the ordering relational domain (`{x≤y ∧ y≤z}`) have no upstream domain; they borrow the tutorial sign analysis, congruence notation and the two-variable equality domain's `{… ∧ …}`. | One bottom glyph reads consistently across domains. | None planned: printing is outside every soundness claim. | **source-checked** 2026-09-15 against goblint `master` `5320a6b7` (`congruenceDomain.ml`, `intervalDomain.ml`, `intDomTuple.ml`, `intDomain0.ml`, `linearTwoVarEqualityDomain.apron.ml`). In Isabelle only the order printer is pinned (`to_string_order_rel_regression`); the others are pinned by `tests/test_value_rendering.py` and the CLI regression corpus. |
| Configuration surface | `run_voblint` takes one `voblint_conf` (`Analysis_Config.thy`): a list of analyses from the closed `analysis` datatype (Int carries its refinement mode), a `context_policy`, a `globals_rule`, a `program_globals` placement and a `sem_conf` (the signed-overflow policy), and answers every combination; the context policy and placement are read in one function, `report_run`. | `--set ana.activated '[...]'` takes an open list of composable analyses registered by string name, with orthogonal `ana.ctx.*` options. | Closed arguments keep the dispatch and its soundness theorem one case split each. | Registration rather than enumeration. | Adding an analysis here edits the `analysis` datatype, the combined carrier and its field dispatch (`MCP_Carrier.thy`) and the `export_code` root list (`Voblint_Codegen.thy`); upstream it is a registration. |
| Source admissibility | `wf_program_compile_input` (with `wf_source_program` inside it) is a precondition of the soundness theorems, and its executable sufficient form `wf_program_compile_input_exec` is `run_voblint`'s own gate: procedure declarations, arity, formals, reserved variables, return behaviour, and `no_return main`. The gate also requires every literal to fit `I64` (`lits_fit`). | Goblint has no admissibility predicate; it analyzes whatever CIL produces. | The compiler proofs need a well-formed input to state node ownership and matching results. | Widen the admitted subset, or discharge the conditions during compilation. | Recorded deviation. Some rejections are representational rather than semantic -- a `main` with an explicit `return` is rejected. |
| Library calls | `EA_Special` moves a recognised library call onto `intra` **structurally, at compile time**, from a closed enumeration (`VIMP_Special.thy`). | Goblint keeps a library or unknown call as a `Proc` edge and splits `special` from a real activation per-analysis at transfer time, against an open `LibraryFunctions` table. | A closed enumeration keeps the compiler total and the CFG free of unresolved calls. | A callee designator on the call edge plus an analysis-level `special` hook. | Structural sibling of the `EA_Check` deviation below; the theory itself flags the closed-vs-open difference. |
| `sync` | No counterpart. `dg_spec` has no `sync` field and the identifier occurs nowhere in `src/`. | `Spec.sync` runs after every transfer and at loop heads and thread transitions, and is where `basePriv.ml`'s privatizations publish. | Publication here happens only inside an edge transfer's returned `'dg`. | A `sync` hook on `dg_spec`, driven by the generator at the same points. | **Unrecorded until now, and load-bearing for the D/G reconstruction row above:** that row proposes adding a publish-on-unlock transition example, and there is no hook at which such a transition could fire. |
| `startstate` / `exitstate` / `morphstate` | No `dg_spec` fields. The concrete initial stores are fixed by the language (`init_stores`, globals zero at their kinds); the analysis supplies only their abstraction, as the `init_st` parameter of `dg_pipeline`, with the obligation `ginit_sound` of `dg_analysis` that it covers them. | Analysis-supplied in `Spec`. `base.ml` uses `startstate` to install global initializers; `morphstate` re-bases a `D.t` onto another function's frame at thread entry and for unknown calls. | The entry state is fixed because no instance has needed to vary it. | Three more `dg_spec` fields. | Recorded gap. Nothing in the model can express "the same abstract state, viewed from another frame". |
| Query channel | `query = EvalInt exp`, answered in `int_dom query_lift` (`Analysis_Query.thy`). `dgs_query` is a specification's handler; `ask_with` (`DG_Spec.thy`) and `ask_rec` (`MCP_Spec.thy`) close the recursion with `\<top>` on a query already being asked and a depth bound. Transfers ask (`aeval_ask` in the non-relational transfer, `ord_learn` in the order analysis), and a check is decided by the met answer (`answer_check`, through `mcp_classify`). | `Spec.query` with an extensible `'a Queries.t` GADT and per-query result lattices; `MCP.query'` meets every analysis's answer, answers a cycle with top, and caches per transfer. | One query kind serves the numeric and order analyses. | Further query constructors; a per-transfer cache, which changes only cost. | One query kind, no cache. |
| Global unknown granularity | Under `--program-globals flow-insensitive` every declared global lives in its **own** solver unknown `Analysis_Global x` (`keyed_split_spec`, `DG_Keyed_Split_Spec.thy`): an edge reads the unknowns of the globals its expressions mention and publishes at the unknowns of the globals it may assign, each once per evaluation after side buffering. Under the default flow-sensitive placement program globals stay in the local state and no analysis global is used. The key type is one generic `('v,'c) global_unknown = Analysis_Buffer \| Analysis_Global 'v \| Activation_Seed pp 'c` (`Routed_Call_Programs.thy`). | Goblint's global unknowns are `G of V.t`, one per declared global, with `sideg`/`getg` interleavable many times per transfer. | Matches Goblint's keying for program globals since the keyed-globals change (PR #312). The footprints are `edge_global_reads`, `edge_global_writes` and `call_global_reads` (`CFG_Transfer.thy`); the lemmas that checked them (`Example_Keyed_Global_Footprint`) were removed with the mathematical-integer analysis instances and have no port (`docs/theorem-migration.toml`). | Per-global update rules. | The update rule is still chosen once per run for every global unknown. Each edge reads and publishes through a fixed read-then-publish schedule, although `strategy_tree` could express interleaving. Combined-state components have no globals of their own. |
| Routed key space | `Analysis_Global v` embeds the analogue of Goblint's `Spec.V` into the TD solver's global-key space; `Activation_Seed pp c` addresses the entry state published at a callee activation. | Goblint's main constraint system uses `GVarF (V)` -- `V + Fundec` -- with global values `GVarG(G)(C)`, so reachable contexts are recorded on a **function**-keyed global whose value is a *set* of contexts. It does not key a global by `(node, context)`. (A generic `GVarFC(V)(C)` exists upstream but `SpecSys` does not use it.) | `Activation_Seed` exists because the vendored `TD_side` solver has no `sidel`: the entered state can reach a callee's entry unknown only through a global proxy that the entry equation reads back. The publication itself only joins into the proxy and destabilizes its readers; the callee is demanded by the caller's `QueryL` of `(FunctionResult p, ctx')`, the exit read (see `Solver demand channel`). See the `Function-entry unknown` row. | None without forking the vendored solver (recorded deviation #142 W2). | **`Analysis_Global` is aligned; `Activation_Seed` is deliberately not a Goblint correspondence** and is named to say so. The rule this fixes for later cleanup: `Activation_Seed` is routing/generator machinery and must never appear in analysis semantics -- a `dg_spec` field that constructs one has leaked past the `'v` boundary. |
| Context selector input | `route` receives the call node, caller context, entered frame and call action -- but **not the resolved callee**, although `p` is in scope one line later for `seed`. | `Spec.context man f d` is per-callee. | The resolver and the route were added independently. | Pass the resolved name to `route`. | Invisible today because every instance pins `static_resolve`; it is the second prerequisite, alongside multi-result `enter`, for a state-reading resolver. |
| `__voblint_check` | A dedicated `EA_Check` edge action and `Check_Event` analysis event, classified through the query channel (`answer_check`, `mcp_classify`) as `Check_Proved`/`Check_Refuted`/`Check_Unknown`. The event never refines the state. | Goblint handles `__goblint_check` through `special`: `libraryFunctions.ml` maps it to `Assert { check = true; refine = false }`, which the `assert` analysis checks in its `special` and Base's `special` leaves unrefined. `Events.Assert` exists, but only `abortUnless.ml` emits it, and Base's `event` handles it by refining (`assert_fn man exp true`). So Voblint's event channel mirrors `Spec.event`, while the check itself corresponds to Goblint's non-refining `special` path. Source-checked 2026-09-22 against `5320a6b7` (`libraryFunctions.ml`, `assert.ml`, `base.ml`, `abortUnless.ml`, `events.ml`). | A separate edge keeps the verdict layer independent of the special-call table and gives checks a first-class semantics. | None planned. | Deliberate divergence; it is what makes the check-discharge pipeline stateable. |
| Termination and context bounding | Soundness assumes `solve_dom`. Call-string contexts over a compiled program lie in a finite candidate space (`compiled_call_strings_finite`); entry-state contexts need not. | Goblint uses widening and context lifters to control discovered contexts. | `TD_side` is vendored for partial correctness; proving its termination is separate work. | M3a finite-height Sign termination; M1 plus M3b call-string lifter; general widening requires upstream solver work. | Open, partly upstream-gated. |
| Solver demand channel | `strategy_tree` is `Answer` / `QueryL` / `QueryG` / `Side`; there is no `Demand`. An unknown joins the demanded set only through `dep_L`, i.e. by being **read**. | Goblint's right-hand side receives `demandl : LVar.t -> unit`, which demands an unknown be solved *without* creating a dependency. `constraints.ml`'s spawn path is exactly `sidel (FunctionEntry fd, c) d; demandl (Function fd, c)` -- seed, then demand, never read. | The vendored `TD_side` is taken as-is; W2 weighed forking it for `sidel` alone. | None without forking the vendored solver. A read-and-discard `QueryL` substitutes, at the cost of a dependency edge the callee/creator relationship does not have. | **Not load-bearing today; decisive for any fire-and-forget unknown.** `part_post_solution T x sigma vars` quantifies `sides_of_rhs` only over `u : vars`, so an unknown nothing reads sits outside the soundness statement **and so do its global writes**. Read-and-discard restores coverage but places creator and callee in one SCC, which is where widening placement lives. Extends W2's cost-benefit, which considered only `sidel`. |
| Finding shape | A check row is one node, one boolean expression, one verdict: `classify_checks` (`Check_Report.thy`) yields `pp * 'e * check_result` triples, and the report's `result_check` record adds the check's label (`Analysis_Run.thy`). An arithmetic diagnostic is likewise one node, one obligation and one verdict. No severity, no category. | Goblint's `Message.t` carries tags (category, CWE), a severity, and a `MultiPiece` that is either `Single of Piece.t` or `Group of {group_loc; pieces: Piece.t list}` -- each `Piece` holding **its own** location (`messages.ml`). A race is a group over one memory location with one piece per racing access. | Every check modelled so far is a single-point condition, which the triple states exactly. | Add the `Group` case (today's entry becomes `Single`), then a minimal severity/category enum. | **Structural gap.** No multi-location property is expressible at all; a data race names a memory location plus a set of accesses at different program points, and cannot be encoded in the triple without inventing a fake single-point form. |
| Global read filter (digest) | No read filter. A global read takes the whole value stored at the key. | Goblint parameterises six privatizations over a two-operation `Digest` module type -- `current` and `accounted_for` (`commonPriv.ml`) -- and makes the global's **value** a digest-indexed map (`GMutex = MapBot_LiftTop (Digest) (LD)`). Reading folds that map and skips writes the reader provably cannot observe: its own, a thread not yet started, or a thread already joined. | Single-threaded scope. With one thread the filter only ever fires its self-read case, so it genuinely collapses to key equality -- which is what the removal ledger recorded when the spine was deleted. | Reinstate the two-operation interface (not the removed 653-line kernel) once a `'G` payload exists to key. | **The removal was conditional on scope, not permanent.** The ledger's premise, "there is no relational concrete compatibility to preserve", holds single-threaded and fails at two threads: `accounted_for` consults may-happen-in-parallel and must-joined information rather than collapsing to equality. |
| Branch transfer | The guard transfer `nonrel_branch` (`Nonrelational_Transfer.thy`) is one polarity-parametrized transfer, shared by every non-relational analysis: a forward gate, under which a guard whose forward value contradicts the polarity yields bottom, ahead of backward refinement by `nonrel_refine`, kept at the variables the guard reads. The executed transfer turns a bottom state into `Bot`, no successor (`transfer_lift st_is_bot`). `nonrel_refine` is the generic `bool_refine` (`Bool_Refine.thy`): a disjunction that must hold, or a conjunction that must fail, refines by each operand whose forward value admits the required truth value (`nonrel_feas`) and joins the results, so a side no state satisfies contributes nothing; when neither operand admits it the result is bottom. An atom that leaves one of its variables empty is bottom as a whole (`nonrel_atom`). The order analysis has its own guard transfer (`ord_branch`). | Same two-phase shape, at both levels: `Base.branch` evaluates `eval_rv` forward, raises `Deadcode` on an `ID.to_bool` answer that contradicts the polarity, and calls `invariant` otherwise (`BaseInvariant.invariant` carries a second gate of its own, `if eval_bool exp st = Some (not tv) then contra st`, and `contra` is `raise Deadcode`); inside backward refinement, `inv_exp` for `BinOp (LOr, ...)` under a true target refines each disjunct separately and drops one whose refinement raises `Deadcode` (`\| exception Analyses.Deadcode -> st1`), which is what the gated join reproduces with `bot` in place of the exception. One residual, in Voblint's favour: `inv_bin_int`'s `LAnd` case gives up entirely on a false target, where `bool_refine` still joins two gated refinements. | Under a join, an infeasible disjunct would re-admit its full incoming state, which is why feasibility is checked per operand rather than only for the whole condition (whose abstract value spans both truth values and decides nothing). | None. | **Closed**, source-checked 2026-08-24 against `cac3f81e`. Pinned by the regression corpus: `06-reachability/precision/07-forward_feasibility_branch_gate.vimp` for the whole-condition gate, `02-control-flow/precision/04-infeasible_disjunct_dropped.vimp` for the per-disjunct one. The gate is a precision change only: `nonrel_branch_sound` and `nonrel_refine_sound` state soundness of the guard transfer. |

## Call flow and context selection (source-checked, 2026-07-16)

Goblint models a normal call as **split -> analyze -> combine** over contextual
unknowns, not a concrete push/run/pop. From
[`analyses.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml)
and
[`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml):

1. `enter man lv f args : (D.t * D.t) list` -> pairs `(caller continuation, callee
   entry state)`; the callee entry has the actuals bound to formals. `enter` is
   analysis-defined and may return several pairs.
2. Context is selected from the **post-enter callee state**:
   `List.map (fun (c, callee) -> (c, S.context man f callee, callee)) paths`.
   So `context man f callee_state` reads the callee-entry state, not the caller.
3. The callee entry is published: `sidel (FunctionEntry f, fc) callee_state`; local
   unknowns are indexed `node x context`.
4. `return man (Some e) f` produces the callee return state; the synthetic return
   slot is an analysis representation detail (the generic framework only requires
   `return`, it does not mandate a universal `#ret`).
5. The exit is read for the selected context: `getl (Function f, fc)`.
6. Combination is two phases: `combine_env caller callee_return` (globals / effects,
   no result assignment), then `combine_assign lv callee_return` (only the
   destination write).

### What the formalization implements (this repo)

Read the status column as one of three things: **implemented** (the mechanism
exists and is batch-green), **simplified** (a mechanism exists, but it is
weaker than Goblint's and the difference is load-bearing), or **proxied** (the
observable effect is reproduced through a different encoding, with no claim that
the two compute the same fixpoint).

| Goblint | Formalization | Status |
| --- | --- | --- |
| `enter` -> callee entry with bound formals | `CallEdge dst formals actuals` in the `calls` relation; `call_enter` (`enter_state`, `bind_formals`) on the concrete side, `ls_enter`/`dgs_enter` on the abstract side | implemented |
| several `(caller continuation, callee entry)` pairs from one `enter` | a list of alternatives, folded by the routed call tree; each alternative's context is admitted by the context policy | implemented in the generator and the collecting semantics; the analysis pipeline assumes one alternative (`enter_single`) |
| target set resolved from the abstract state (`tf_proc`, `Queries.EvalFunvar`) | resolved at the call site while solving: `resolve v cc ca (locals d)`, folded by `side_rhs_fold_dg` over the site's targets | implemented (#142 W1); every instance pins `static_resolve`, which answers from `calls g` |
| `context man f callee_state` (post-enter callee state) | `route` applied to the entered frame the generator computes; the relation `call_context_policy` on the concrete side | implemented, **batch-green** |
| local unknown `(node, context)` | `Inl (pp, ctx)` | implemented |
| `sidel (FunctionEntry f, fc) callee_state` | `Side` into the global proxy `Inr (Seed (FunctionEntry f) ctx)`, read back into the local `(FunctionEntry f, ctx)` by `routed_entry_seed_programs` | proxied; recorded deviation (#142 W2). The vendored solver has no `sidel` and will not be forked |
| `getl (Function f, fc)` | routed callee-exit read `Inl (ex, route ...)` in the combine | implemented, batch-green |
| `sidel` before `getl` in `tf_normal_call` | the seed publication is flushed before the exit read at a node where at most one call returns (`buffer_sides`'s `publish_before`, set by `routed_node_rhs_buffered`), at the answer where several calls return | implemented where one call returns (#251); deviation at shared resume nodes, see `Call protocol order` |
| `combine_env` then `combine_assign` | Two separate `dg_spec` fields, `dgs_combine_env` and `dgs_combine_assign` (`DG_Spec.thy`), filled by `dg_spec_of` from a component's `ls_combine_env` and `ls_combine_assign`. On the *concrete* side `combine_collect dst s t = combine_assign dst (conv dst (t rv)) (combine_env glob s t)` stays fixed. | implemented as two analysis-supplied hooks abstractly, composed concretely. The non-relational component gives `ls_combine_env` the global merge (`combine_env is_global` in `nonrel_spec`, `combine_default_st` in `nonrel_exec_spec`) and `ls_combine_assign` the destination write; the order component leaves `ls_combine_env` the identity |

Two corrections worth keeping separate.

**Context is selected from the callee-entry abstract state after parameter
binding**, matching `context man f callee_state`. An earlier model routed on the
caller store, which cannot express argument-sensitive context. See
`docs/history/ROUTE_A7_EXECUTABLE_DG_MIGRATION.md`.

**That entry state is computed once and shared** between context selection and
publication, matching Goblint's use of the same `v` for both `S.context man f v`
and `sidel`. Previously the route entered the frame itself, against a bottom
global, while the publication entered it against the solved global — two `enter`
applications per call edge, one of them fed a value the solver did not hold. The
generator now binds the entered frame once and every route is a formals
projection of the state it is handed. Current domains cannot observe the
difference, because `dg_spec_of` builds `dgs_enter` with `local_enter_transfer`,
which discards the global argument. The `w0_*` lemmas of
`Example_Keyed_Solver_Update_Rule_Regression` used a transfer that does not, and
failed on the old routing; they were removed with the mathematical-integer analysis
instances and have no port (`docs/theorem-migration.toml`).

### Claim discipline

Accurate: *a simplified, machine-checked semantic model of Goblint's
interprocedural context-sensitive architecture.* Not: *the exact implementation.*

Known simplifications (future faithfulness, not blockers): every instance pins
`static_resolve`, so no analysis-driven or indirect call is expressible; the
context selector sees the caller context and entered frame, not a full
manager/query interface and not the resolved callee; `D.t` is a store, not a
product of relational / heap / thread / path-sensitive domains; the analysis
pipeline accepts one `enter` alternative per call (`enter_single`).

Unproved equivalence, distinct from the above: the callee-entry unknown is a
global proxy plus a mirror read, where Goblint has one local unknown. The
encoding expresses the same collecting dependency and the soundness theorems are
stated and proved against it. Whether it reaches the same fixpoint as Goblint's
local-side-effect formulation is **not** claimed and has not been proved. The
scheduling and widening behaviour differ by construction: the proxy carries no
equation, so contributions join there and widening applies one hop later at the
local entry unknown.

## Machine-integer Interval (source-checked, 2026-10-13)

Checked against the local `analyzer` checkout at `0dc12d355`. Paths are relative to
`src/cdomain/value/cdomains/` unless they name `src/analyses/`. The Voblint side is the
Interval and Congruence analyses at machine kinds (`src/Analyses/Interval/`,
`src/Analyses/Congruence/`), both run by the non-relational pipeline in
`src/Analyses/Nonrelational/`. The order relational domain runs over variable
identities in `src/Analyses/Order/`; it has no Goblint counterpart (see Value printing).
Every Voblint behaviour described here is committed on branch `feat/typed-ir`.

**Overflow normalization.** `int/intervalDomain.ml` `norm` (lines 35–70) keeps an
in-range interval. When it overflows, it wraps exactly when `should_wrap ik` holds, the
interval spans at most `max_ik - min_ik`, and the wrapped ends stay ordered; otherwise
it answers `top_of ik`. `should_wrap` (`intDomain0.ml` line 67) is true for unsigned
kinds, and for signed kinds only under `sem.int.signed_overflow = assume_wraparound`.
`cast_to` is `norm ~cast:true` (line 140); `cast` matters only in the `assume_none`
branch, which clamps instead of answering top. `norm_ivl_ik` in `Interval_Kind.thy`
takes the policy (`signed_overflow_policy`, `Assume_Top` by default or
`Assume_Wraparound`) and decides wrapping by `should_wrap`, as Goblint does: a kind that
wraps does so under the same two conditions, signed overflow under `Assume_Top` answers
the kind's range, and a cast and an arithmetic result are normalized alike. Voblint has
no `assume_none`: its concrete semantics wraps every write, so a policy that assumes no
signed overflow would be unsound for it.

**Widening and narrowing.** Without thresholds, `widen` (lines 142–157) moves a growing
bound to the kind's range end, and `narrow` (lines 164–172) replaces only a bound that
sits at the kind's range end, then normalizes. `widen_ivl_ik` moves a growing bound to
the kind's end or past it to the new bound, whichever is further, so a value outside the
kind's range is not lost; `narrow_ivl_ik` replaces the same bounds and does not
normalize. Thresholds are not modelled.

**Guard refinement.** `src/analyses/baseInvariant.ml` refines through a cast
(lines 836–865) only when `VD.is_dynamically_safe_cast` holds, that is, when the operand's
current value fits the target kind. `refine_var` uses the same run-time condition
(`fits_ik`). Through arithmetic, `inv_bin_int` (lines 293–321) inverts `+` and `-` with
the kind's own operations, which in wrapping arithmetic is exact even when the operation
may overflow, and also refines `*` by an odd constant and `/`. `refine_var` inverts only
`+` and `-`: when the mathematical result fits the kind, which it computes with
`raw_aop_ik`, by mathematical subtraction and addition; otherwise with the kind's own
operation (`arith_ik`), at an operand whose kind is the operation's kind. It does not
refine through `*`, `/` or `%`.

**Boolean guards.** The guard refinement (`nonrel_refine`, `Nonrelational_Transfer.thy`) instantiates
the generic `bool_refine` locale (`Bool_Refine.thy`). A conjunction that must hold
narrows by its left operand, then its right, as `inv_exp` narrows `e1` and then `e2`
(`baseInvariant.ml`, lines 744–745 at `0dc12d355`). A disjunction that must hold narrows
by each operand whose forward value admits truth and joins the results, as the `LOr`
case does (lines 724–731). Where neither operand admits it the result is bottom, which
is Goblint's fall-through `Deadcode`. A conjunction that must fail is handled the same
way; Goblint's `LAnd` case gives up there (line 452), so this refines more. The
feasibility of an operand is decided by its forward value, where Goblint catches the
`Deadcode` its refinement raises. The branch then keeps the refinement at the variables
the guard reads, and a variable refined to bottom makes the successor `Bot`
(`transfer_lift st_is_bot`), as `refine_lv` calls `contra` on a bottom value (lines 94
and 108) and `contra` raises `Deadcode`.

**Reduced product.** `int/intDomTuple.ml` `refine` (lines 280–296) applies the
components' refinement functions never, once, or to a fixpoint, and the tuple's
arithmetic first asks the interval component whether an operation may overflow and
passes the answer as `no_ov` to the others (`mapovc`, lines 300–305). `ana.int.refinement`
defaults to `never` (`src/config/options.schema.json`). `join` and `widen` do not refine;
comparisons take the components' common answer (`map2bool` via `same`). The
product `int_tuple` (`src/Analyses/Int/Int_Tuple_Kind.thy`) has the Interval and
Congruence components only. Arithmetic and conversions pass the interval's
no-overflow answer to the congruence as `mapovc` does; a conversion also keeps the
class when the interval fits, where Goblint's `Congruence.cast_to` ignores `no_ov`.
Every arithmetic result, conversion, meet and guard refinement is refined as the mode
says (`it_refine_mode`): never, once, or to a fixpoint, each round refining the
congruence by the interval (`cong_refine_with_ivl`, Goblint's `refine_with_interval`)
and then the interval by the congruence. The mode is part of the analysis
(`Ana_Int refine_mode`), as `ana.int.refinement` is part of Goblint's configuration.
Goblint's `Interval.refine_with_congruence` keeps an end that sits at the kind's limit;
`refine_ivl_with_congruence` rounds every finite end. Widening, narrowing and join are
componentwise without refinement, so the narrowing laws hold; Goblint's `narrow` does
refine (`map2` without `~norefine`, lines 425–426), while its `join` and `widen` do not
(lines 416–423). A comparison takes the
interval's answer and falls back to the congruence's. `Int_Regression.thy` pins
the gain at the fixpoint mode: the step-3 loop that Congruence alone loses to top ends
at exactly `99`.

**Integer interface.** The class `kind_int_domain`
(`src/Analyses/Nonrelational/Nonrelational_Domain.thy`) corresponds to the part of `IntDomain.S`
(`intDomain_intf.ml`) that VIMP's expressions use: `top_ik` is `top_of`, `of_int_ik` is
`of_int`, `cast_ik` is `cast_to ?from_ik` without a `castkind`, `arith_ik` is the
arithmetic at a kind, and `cmp_ik` answers comparisons as `lt`…`ne` do. Comparison and
`meet_ik` take no kind, and `bool_val` builds truth values at `I32` only. `answer_ik`
replaces `to_int`, `minimal`/`maximal` and the exclusion lists by one `answer` record.
`empty_ik` tests emptiness against the kind's range. Absent: `bot_of`, `is_top_of`,
`of_interval`, `of_congruence`, `starting`/`ending`, `neg`, the bit operations and
shifts (VIMP has neither), `invariant` (Goblint's witness output, not guard narrowing),
and `project`. Guard narrowing is `refine_ik`, which corresponds to `inv_bin_int`
in `baseInvariant.ml`, not to `invariant`. Its `!=` case is weaker: Goblint excludes a
known singleton through the exclusion-list components (`baseInvariant.ml`, lines
395–416), while the Interval leaves both operands unchanged (`ivl_refine CNe`).
The interface returns no overflow information: Goblint's `SOverflow` operations return
`overflow_info`, and `check_ov` (`intDomTuple.ml`, lines 70–78) emits a signed-overflow
warning when every overflow-tracking component reports one. Voblint's semantics wraps
signed kinds, and a signed overflow under `Assume_Top` sends the Interval to the kind's
range. Its signed-overflow diagnostic comes from the arithmetic obligations of each
evaluated expression (`arith_obligations`), which the report decides from the activated
analyses' answers (`obligation_classify`, `Run_Report.thy`), not from the domain
operations. `raw_aop_ik` and `fits_ik` stand in for `no_ov` inside `int_tuple`.
Source-checked 2026-10-13 at `0dc12d355`.

**Congruence.** `int/congruenceDomain.ml` wraps a constant on `normalize` and in
`cast_to` (lines 27–45, 168–190); a non-constant class survives a cast only when the
source kind's range lies inside the target's. Unsigned `+`, `-`, `*` on non-constant
classes keep the largest power of two dividing the modulus (`handle_overflow`,
lines 248–262); signed overflow answers top. `norm_cong_ik` in
`src/Analyses/Congruence/Congruence_Kind.thy` keeps a class `c + mℤ` modulo
`gcd m (2^w)` and collapses it to one value when `2^w` divides `m`; this is
`handle_overflow`. `cong_arith_ik` applies it to every kind that wraps under the policy
(`should_wrap`); a signed kind under `Assume_Top` keeps only a difference of two
constants that lies in range and otherwise answers top. A cast from a contained kind
keeps the class, as in Goblint; any other cast normalizes, where Goblint answers top for
a non-constant. Goblint's standalone domain relies on the interval's `no_ov` to keep a
non-power-of-two modulus across arithmetic; the standalone Congruence analysis loses
such a class at the first operation (`odd_step_prog` in `Congruence_Regression.thy`),
and the Int product keeps it (`odd_step_prog` in `Int_Regression.thy`). Comparisons
follow `eq`/`ne`: disjoint classes are unequal. `narrow` is the meet, as in Goblint;
widening is the join. Shifts and bitwise operations are not part of VIMP.

**Queries between analyses.** `base.ml` asks `EvalInt` for every non-constant
integral subexpression it evaluates and replaces the value by the answer
(`eval_rv_ask_evalint`, lines 803–825); it answers `EvalInt` itself through
`eval_rv_no_ask_evalint`, which does not ask the outermost expression back. MCP meets
the answers of all analyses and answers top on a query cycle. `aeval_ask` and `aeval`
in `src/Analyses/Nonrelational/Nonrelational_Domain.thy` follow this, and every
transfer evaluates through the channel it receives. The activated analyses run as one
through `mcp_registry`
(`src/Abstract_Interpreter/Framework/Cooperation/MCP_Registry.thy`), which meets their
answers, and `ask_rec` answers top on a cycle. One difference: on a top answer Goblint uses
`top_of ik`, while `aeval_ask` falls back to its own evaluation, which is sound and at
least as precise. The order component answers `EvalInt` of a comparison between two
variables from its own facts and asks nobody, as `varEq.ml` (line 595) and
`expRelation.ml` (lines 53–70) answer comparisons; it has no Goblint counterpart as an
analysis. `relationAnalysis.apron.ml` answers `EvalInt` from its own state (line 646)
and uses `EvalInt` answers only to convert casts and check overflow
(`sharedFunctions.apron.ml`, lines 110–125). A check is decided by asking the
registry through the channel it closes over itself (`mcp_classify`), as `assert.ml`
(line 21) decides through `Queries.eval_bool`, which asks `EvalInt` of the condition
cast to `_Bool` (`queries.ml`, lines 537–541).

## Boundary examples

These are capability boundaries, not claims that every Goblint configuration
proves every assertion. “Goblint-side” means an analysis instance with the
required domain or cooperating analyses can express and run the scenario. The
formalization-side column states the exact missing layer.

| Scenario | Goblint-side example | Formalization-side boundary | Required closure |
| --- | --- | --- | --- |
| C memory and aliases | `int a[2]; int *p = c ? &a[0] : &a[1]; *p = 0;` A C analysis can model the pointer, array cells, and weak update. | VIMP has scalar stores only. There are no arrays, addresses, dereference, allocation, or alias semantics to state a matching collecting theorem. | `history/ARRAY_SYNTAX_EXTENSION.md` for arrays; the source-language boundary in `history/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` for memory/CIL. |
| Relational numeric invariant | `int x = input(); int y = x; x++; assert(x == y + 1);` A relational numeric domain can retain the relation between `x` and `y`. | The current state is pointwise. Sign/Interval can track each variable but cannot express `x - y = 1`; `input()`/havoc *is* implemented -- `Nondet_Int` (`VIMP_Special.thy`) is an export root and reaches every domain's `special` transfer. | `history/RELATIONAL_DOMAIN_PLAN.md` plus `history/NONDET_HAVOC_MIGRATION.md`. |
| Analysis-specific call behavior | `r = f(p);` where the analysis must preserve a relation between caller state, pointer argument, and returned value. Goblint supplies the call syntax to `enter`, `combine_env`, and `combine_assign`. | VIMP formalizes ordinary actuals and return destinations, and `enter`, `combine_env` and `combine_assign` are analysis-supplied `local_spec` fields; but VIMP has no pointers, so no relation over a pointer argument is expressible. | Gap 3 in `history/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`. |
| Inter-analysis query | A taint transfer asks a value/pointer analysis whether a sink or dereference is feasible before reporting it. | `QueryG` reads this analysis's named global slots only. Questions to other analyses go through the query channel of `local_spec` (row "Multi-analysis manager"); a transfer that suppresses a report on another analysis's answer is not modelled. | Gap 7a in `history/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`; Seidl Slice 8. |
| Origin-sensitive global update | Several loop or call-site origins side-effect the same unknown; a per-origin update policy can widen one contribution without immediately losing the others. | The vendored `TD` solver's own `update_global_warrowing_per_origin` is wired end to end: `Globals_Warrow_Per_Origin` in `run_voblint`, `--globals warrow-per-origin` at the CLI, and code-generated into `Voblint_Generated.ml`. `tests/regression/19-paper-examples/` reproduces FM 2026 Example 2 and Sect. 5.3 on it, with the paper's own contributions. | Closed for the update rule itself. `--program-globals flow-insensitive` lets a declared global exercise it (`19-paper-examples/precision/07-fig1_flow_insensitive_globals.vimp`); choosing the placement per variable, from the source, is the open part -- see `docs/PER_ORIGIN_WIDENING.md`. |
| Recursive context bounding | `int f(int n) { return n ? f(n - 1) : 0; }` analyzed with Context Gas or Loopfree Callstring. | Recursive VIMP behavior is expressible, but the soundness theorems cover only runs whose solve terminated. It cannot certify a dynamically bounded context lifter. | `history/M1_CALLSTRING_CONTEXT_MIGRATION.md` and M3b; M3a separately removes the Sign termination hypothesis. |

### Already expressible here

The contrast is not “C versus nothing.” Current VIMP already formalizes and
certifies scalar assignments, conditionals, loops, procedures with actuals and
optional return destinations, named global side effects, and fixed structural
call/return restoration. It also has semantic context-indexed collecting
soundness. The examples above begin where those capabilities require a richer
source language, a non-pointwise state, an analysis-provided framework hook, or
a termination argument.

## Migration records

The direct typed architecture on `feat/typed-ir` (`history/TYPED_CFG_PLAN.md`, "Stage 7
breakdown") replaced the lowering of declared programs to explicit casts with one
language: surface VIMP elaborated into core VIMP over machine-integer kinds, compiled to
a CFG and analyzed by kind-aware domains. The mathematical-integer analyzer and its
lowering are removed. The Integer width and wraparound row records the result.

Every earlier plan this register tracked
(`ROUTE_A7_EXECUTABLE_DG_MIGRATION.md`, `M1_CALLSTRING_CONTEXT_MIGRATION.md`,
`M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md`,
`CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md`,
`DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION.md`,
`SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md`, `TRACE_BASED_FORK_MIGRATION.md`,
`GHOST_INSTRUMENTATION_MIGRATION.md`, `NONDET_HAVOC_MIGRATION.md`) is archived
under `history/`, and its status line there is the one it had when work stopped.
Where a register row still records a gap, the row names what would close it; the
other open workstream is context bounding (`NEXT_STEPS.md`, "Open: context
bounding").

The three interprocedural rows added above — call entry and return, call-target
resolution, function-entry unknown — are tracked as workstreams on issue #142
rather than as a migration document:

| Workstream | Register rows | State |
| --- | --- | --- |
| W0 shared entry frame | Context input boundary | Closed. The entry state is computed once and shared by context selection and publication. |
| W1 `resolve_targets` | Call-target resolution | Closed. The call site owns resolution: one tree per site, folded over `resolve v cc ca (locals d)`. Pinned to `static_resolve` everywhere, so behaviour is unchanged; `resolve_sound` states what a state-reading resolver must earn. |
| W2 `SideL` | Function-entry unknown, call entry and return | Closed as a recorded decision not to pursue it (2026-08-24). The open questions -- contribution preservation across RHS re-evaluation, widening placement at the target, repeated contributions from one origin, the affected termination and post-solution proofs, whether `buffer_sides` generalizes -- are all downstream of forking the vendored solver, whose proofs the project would then own permanently. The gain is architectural fidelity, not a new theorem. |
| W3 register | All three interprocedural rows | Closed. Each row separates existing behaviour, intended behaviour, and unproved equivalence, and names the residual where one remains. |

## Rules for future alignment work

- State the upstream interface fragment and commit before calling a design
  Goblint-faithful.
- State whether a result is semantic-only, executable-generator, or end-to-end.
- Add a register row or update an existing row whenever a simplification becomes
  load-bearing in a theorem statement.
- Record the rationale as a constraint, not history: proof cost, vendored solver
  interface, source-language scope, or a required concrete semantics.
- Do not call `(node, context)` alignment complete while the executable generator
  cannot derive and seed the selected callee context. (It derives and seeds it
  from the post-enter callee state, and the routed solution carries its
  collecting-soundness certificate.)
- Separate "proxied" from "implemented" in every status. A row that reproduces an
  observable effect through a different encoding must say so and must state
  whether operational equivalence is claimed. Proxy encodings are where a silent
  fidelity claim is cheapest to make and hardest to notice.
- Do not close a fidelity gap with a lemma that characterizes today's domains
  when the point of the gap is to admit domains that violate it. An
  `enter_local ... d g = enter_local ... d bot` independence lemma would have
  been true of every current spec and would have written the restriction into
  the generic interface.

## Superseded inventories

`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` remains useful for the original detailed
design sketches. Its Gap 7 statement that contexts are absent is stale: semantic
context collection and context-indexed unknowns now exist. Read its Gap 7 through
the status in this register and `GOBLINT_ALIGNMENT_TRACKS.md`.
