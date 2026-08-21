# Migration - Seidl 2026 mixed-flow Goblint alignment

Status: **IN PROGRESS**. Phase A (Slices 1-3, structural exposure) and Slice 6
(analysis-specific combine) landed; see the per-slice "Landed" notes below.
Slices 4, 5, 7 and 8 remain.

Seidl, Vojdani, Erhard, Schwarz, "Mixed Flow-Sensitive Static Analysis: Engineering
Modularity", FM 2026, LNCS 16557, pp. 446-470.

This document records the paper notation and maps it to the current Isabelle
formalization. The aim is closer conceptual alignment with Goblint's mixed
flow-sensitive model without losing the current proof spine.

Related local docs:

- `docs/EFFECTFUL_TF_MIGRATION.md`
- `docs/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`
- `docs/TRACE_CONTEXT_ANALYSIS_MIGRATION.md`
- `docs/SEMANTIC_CONTEXT_MIGRATION.md`
- `docs/CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md`

## Paper model

### Side-effecting constraint systems

The paper presents a side-effecting constraint system as:

```text
(L, G, D_X, C)

X = L union G
D_X = (D[x])_[x in X]
E = set of valuations eta with eta[x] in D[x]
```

`L` are local unknowns, usually flow-sensitive program points. `G` are global
unknowns, where side contributions are accumulated flow-insensitively. Each
unknown may have its own domain. A local unknown `[u]` is constrained by one or
more functions:

```text
f : E -> (E x D[u])
```

For a valuation `eta`, `f eta = (eta', d)` returns finitely many global
contributions in `eta'` plus one local contribution `d` for `[u]`. The paper's
constraint shape is:

```text
(eta, eta[u]) >= f eta
```

Interpretation: `eta[u]` must cover the local contribution, and every global
slot must cover the side-effect contribution produced by the same constraint.

### CFG-derived mixed-flow constraints

For a CFG:

```text
N      program points
Act    program actions
E      subset of N x Act x N
```

Every incoming edge `(u, act, v)` induces a constraint for `[v]`:

```text
(eta, eta[v]) >= [[(u, act, v)]] (eta[u]) eta
```

The transfer function has shape:

```text
[[e]] : D[u] -> E -> (E x D[v])
```

It receives the source local value and the whole valuation for further local or
global reads. It returns global side effects plus the successor local value.

### Procedure calls

For a call edge:

```text
e = (u, f(args), v)
start_f, ret_f
enter_f,args : D[u] -> D[start_f]
combine_f    : D[u] -> D[ret_f] -> D[v]
```

The paper's call transfer is:

```text
[[e]] d eta =
  if d = bottom then (empty, bottom)
  else
    let sigma = {[start_f] -> enter_f,args d}
    let d' = combine_f d (eta[ret_f])
    in (sigma, d')
```

Under this formulation, procedure start points are accumulated like global
unknowns. The initial main call uses a dedicated local `[_main]`:

```text
(eta, eta[_main]) >= (sigma_0, eta[ret_main])
```

### Context sensitivity

The paper refines locals by contexts:

```text
[u] becomes [u, c], c in C
```

A non-call edge keeps the same context:

```text
(eta, eta[v, c]) >= [[(e, c)]] (eta[u, c]) eta
```

For calls, the analysis supplies:

```text
context_u,f,args : D[u] -> C -> C
```

The context-sensitive call transfer is:

```text
[[e, c]] d eta =
  if d = bottom then (empty, bottom)
  else
    let c' = context_u,f,args d c
    let sigma = {[start_f, c'] -> enter_f,args d}
    let d' = combine_f d (eta[ret_f, c'])
    in (sigma, d')
```

The initial main constraint reads `eta[ret_main, c0]` and seeds
`[start_main, c0]`.

Typical instances:

- `k`-callstring: `C` is bounded call-site history.
- 1-callstring: `C` is call sites plus `_main`, and `context _ _ = u`.
- partial tabulation: `C` contains abstract start states, and
  `context d _ = enter d`.

### Digests

Digests generalize call contexts from call histories to abstractions of the
reaching execution history, including concurrent events. The paper writes the
digest set as `A`. A digest-refined domain for an unknown `[x]` is:

```text
D[x]^A = A -> D[x]
```

Both local and global unknowns may be refined. Transfer functions operate by
case analysis over digests. Global reads may use a compatibility relation on
digests, so a reader with digest `a` only joins global components whose writer
digest is compatible with `a`.

Example digests in the paper:

- call-string contexts,
- trace partitions by predicates,
- sets of held mutexes,
- mutex types,
- thread identifiers,
- global modification counts,
- single-threaded vs multi-threaded mode `{ST, MT}`.

### Solvers and update rules

The paper separates analysis specification from solving. Solvers for
side-effecting systems include nested fixpoint strategies and the top-down TD
solver with side effects. TD starts at an initial unknown, queries dependencies
on demand, maintains a `called` set to stop infinite descent, tracks
dependencies dynamically, and uses cycles as widening/narrowing candidates.

For global side effects, the paper highlights update rules. An update rule is
invoked when a contribution `d` to a global `g` is triggered. The naive rule
widens the old global value with `d`. A more precise rule stores contributions
per origin local and joins origins afterward, applying widening only per origin.
Further rules may revoke outdated toxic contributions.

### Goblint implementation interface

The paper's simplified Goblint analysis specification contains:

```text
D_L       local domain
Gbar      analysis-specific global names
D_Gbar    global domain
transfer functions for statements
enter     call-entry abstraction
combine   return abstraction
context   optional callee-context function
startcontext
ask/query inter-analysis communication
sideg     side-effect to a named global
```

Multiple activated analyses combine local domains by product. Their global
domains are kept as distinct global namespaces and combined by a sum-like
domain. Transfer functions are applied componentwise to the product local
state. Goblint also supports limited cooperation by query dispatch: `man.ask`
sends a query to all analyses and meets the answer lattice results.

## Current Isabelle mapping

| Paper notation | Current Isabelle artifact | Status |
| --- | --- | --- |
| `L` local unknowns | `pp` or context-indexed `pp x 'c` | Present |
| `G` global unknowns | `'g` in `pp + 'g`; older unit instance remains | Present |
| `X = L union G` | sum type `pp + 'g` | Present |
| valuation `eta : X -> D` | `sigma :: pp + 'g => 'a abs_state` | Present, single payload type |
| per-unknown domains `D[x]` | uniform `'a abs_state` for all locals and globals | Simplified |
| `f : E -> (E x D[u])` | strategy tree with `QueryL`, `QueryG`, `Side`, `Answer` | Present |
| paper eq (1) constraint | `se_constraint_holds` + `part_post_solution_imp_se_constraint_holds`, `se_constraint_holds_imp_etf_full_le_env` | Present (Slice 1) |
| paper eq (2) per-edge tree | `edge_constraint_tree`, `cfg_edge_contributes_to_eq`, `side_acc_eff_least` | Present (Slice 2) |
| local result `d` | `Answer d`, denoted by `traverse_rhs` | Present |
| global side effects `eta'` | `Side g d t`, denoted by `sides_of_rhs` / `all_sides` | Present |
| CFG transfer `[[e]]` | `apply_etf etf a u` and `side_rhs_fold_eff` | Present |
| plain edge transfer | `domain_transfer`, `apply_tf` | Present |
| call `enter` | `etf_enter`; also `tf_enter` in plain transfer record | Present |
| call `combine` | `etf_combine`; unit bridge uses `unit_combine_tree` | Present but structural |
| start-point side seed | `make_side_rhs_tree_eff`, `gseed`, `restrict_global s0` | Present |
| local/global read at a point | `side_env sigma v = sigma (Inl v) sup glob_env sigma` | Present |
| named global read | `side_env_g sigma g v = sigma (Inl v) sup sigma (Inr g)`; `sideg_tree` reads one slot; `side_env_g_le_side_env` | Present (Slice 3) |
| join all globals | `glob_env` | Present |
| context-indexed unknowns | `map_ltree`, `side_cfg_T_eff_ctx`, executable mirrors | Present |
| trace/digest compatibility | `reaching_compat`, `alpha_ctx`, `cfg_collect_ctx` | Present semantically |
| digest soundness contract | `digest_env_sound`, `digest_read_sound` | Present |
| update rules | TD_side default update behavior only | Gap |
| multi-analysis product/sum | no framework-level product/sum of activated analyses | Gap |
| query bus | no `ask`/`query` abstraction | Gap |

## Similarities and differences

| Topic | Paper/Goblint | Isabelle formalization | Difference / migration pressure |
| --- | --- | --- | --- |
| Core system shape | Side-effecting `(L, G, D_X, C)` with local constraints producing global side effects | `strategy_tree` encodes reads, side effects, and answers over `pp + 'g` | Strong match. Use paper notation in docs and theorem names. |
| Domain family | Each unknown `[x]` may have domain `D[x]` | One state type `'a abs_state` is used for all local and global slots | Major simplification. Needed for current TD bridge; limits Goblint fidelity and analysis composition. |
| Local domain vs global domain | Goblint has separate `D` and `G` domains | Globals and locals both store `'a abs_state`; named globals are distinguished by `'g` | Named globals are present, but payload type is unified. |
| Global unknowns | Analysis-defined `GVar.t` | finite `'g`, plus old `unit` bridge | Good alignment for single analysis; finite requirement should be documented as a solver/interface condition. |
| Global read | Transfer can read a selected global via manager | `QueryG g`; `side_env_g`, `side_env_g_le_side_env`; `sideg_tree` reads one slot | Good alignment. `sideg_tree` (Slice 3) is a `man.global`/`man.sideg` instance that reads a single named global via `side_env_g`, not `glob_env`. |
| Global side effect | `man.sideg g d` inside transfer | `Side g d t` inside strategy tree | Good alignment. |
| Plain CFG equation | one constraint per incoming edge | `rhs` and `side_rhs_fold_eff` fold incoming predecessors | Good match. |
| Procedure start points | Treated as globals in paper's call formalization | CFG has `EA_Enter`; seed uses `gseed`; call/return modeled via combine triples | Conceptual mismatch. The current CFG has explicit structural call edges and combine triples; paper treats start-point seed as side effect. |
| Return combine | analysis-specific `combine_f : D[u] -> D[ret_f] -> D[v]` | default `unit_combine_tree` uses locals from caller and globals from callee | Gap for relational domains and Goblint `combine`. |
| Context-sensitive calls | `context d c` computes callee context; read `ret_f,c'` | context-indexing infrastructure exists; executable bridge computes callee context from caller state plus global; eq-(6) combine soundness contract named (`switching_combine_sound`) + discharged for the context-preserving instance | Theorem-facing contract now aligned with eq (6); value-dependent discharge (Slice 4 body) open. See `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md`. |
| Digests | reduced cardinal power `A -> D[x]` for locals and globals; compatible global reads | semantic `cfg_collect_ctx`, `digest_env_sound`; examples exist | Semantic layer present. Solver-level digest-indexed globals remain staged. |
| Update rules | per-global update rule, possibly per origin/revocation | not modeled as a parameter of solver interface | Major solver-alignment gap. |
| Multiple analyses | local product, global sum, componentwise transfer, query system | single analysis/domain stack | Out of thesis scope unless explicitly planned. |
| Solver termination | widening/narrowing and TD cycle handling discussed | soundness assumes `solve_dom`; no general termination proof | Known gap. |

## Key existing lemmas and contracts

These are the current anchors for paper alignment.

| Paper obligation | Isabelle anchor |
| --- | --- |
| paper eq (1) over a strategy tree | `se_constraint_holds`; `part_post_solution_imp_se_constraint_holds`, `se_constraint_holds_imp_etf_full_le_env` |
| paper eq (2) per-edge tree + fold | `edge_constraint_tree`; `side_acc_eff_least`, `cfg_edge_contributes_to_eq`, `cfg_combine_contributes_to_eq` |
| paper eq (7) initialization seed | `entry_local_seed_le_eq`, `entry_global_seed_le_sides` |
| `man.global` / `man.sideg` single-slot transfer | `sideg_tree`; `sideg_assign_sound`, `side_env_g_le_side_env` |
| local result and side effects jointly satisfy constraints | `part_post_solution` from vendored TD side solver, used by `td_cfg_side_solver_eff.part_post_at_cfg` |
| named side effects are bounded by global environment | `all_sides_le_glob_env_sides`, `glob_env_upper`, `glob_env_mono_Inr` |
| unit-global tree reconstructs the pure transfer | `etf_full_unit_edge_tree` |
| unit-global combine reconstructs structural combine | `etf_full_unit_combine_tree` |
| structural call combine is concretely sound | `combine_states_sound` |
| context filtering refines flat traces | `cfg_collect_ctx_subset_flat` |
| context collecting is last-store projection of compatible traces | `cfg_collect_ctx_reaching_compat` |
| context collecting is included in flat collecting | `cfg_collect_ctx_le` |
| digest-indexed analyzer contract | `digest_env_sound` |
| compatible digest read is sound | `digest_read_sound` |
| flat analyzer is a degenerate digest-indexed analyzer | `flat_env_is_digest_sound` |
| mixed-flow trace soundness | `mixed_flow_analysis_sound` |
| TD-backed mixed-flow soundness | `mixed_flow_analysis_optimal` |

## Migration plan

### Slice 0 - terminology and paper notation

Goal: make the paper correspondence obvious to future readers.

Edits:

- Add a short "Seidl 2026 notation" subsection to `src/Analysis/Generic/Solver/README.md`.
- Rename or alias doc-facing terms:
  - local unknowns: `L`,
  - global unknowns: `G`,
  - valuation: `sigma`,
  - side-effecting constraint: `strategy_tree`.
- Cross-link this document from `docs/PROOF_OVERVIEW.md` and `docs/ROADMAP.md`.

Partly landed: paper-notation `text` bridges added to
`Sign_Named_Global_Eff.thy` (`[[e]]` / `man.global` / `man.sideg` / eq (1)
mapping) and `Example_Finite_Sign_Context_Analysis.thy` (`fctx_ec_call` =
paper `context_{u,f,args}`, Example 7). Additive only, no renames.

### Slice 1 - expose the exact side-effecting constraint contract

> **Landed.** `se_constraint_holds` and its bridges live in
> `src/Analysis/Generic/Equations/Constraint_System.thy`:
> `part_post_solution_imp_se_constraint_holds`,
> `part_post_solution_iff_se_constraint_holds` (the post-fixpoint reformulation),
> and `se_constraint_holds_imp_etf_full_le_env` (the `etf_full <= side_env` bound).
> Batch-green on `Voblint_Formalization`.

Goal: state the paper's `(eta, eta[u]) >= f eta` contract directly over
`strategy_tree`.

Add an Isabelle definition in the generic solver layer:

```isabelle
definition se_constraint_holds ::
  "('l, 'g, 'd) strategy_tree => ('l + 'g => 'd) => 'l => bool"
```

Intended shape:

```text
traverse_rhs t sigma <= sigma (Inl u)
sides_of_rhs t sigma (Inr g) <= sigma (Inr g) for all g
```

Key lemmas:

- `part_post_solution_imp_se_constraint_holds`
- `se_constraint_holds_imp_etf_full_le_env`
- unit bridge: `se_constraint_holds` specializes to the old post-fixpoint shape.

This gives the paper equation (1) a named theorem-level target.

### Slice 2 - make CFG equations paper-shaped

> **Landed.** `edge_constraint_tree` and the fold decomposition live in
> `src/Analysis/Generic/Solver/TD_Side_Tree.thy`. The fold
> `side_acc_eff` is characterised as the finite join of the per-edge/per-combine
> contributions (`acc_le_side_acc_eff`, `side_acc_eff_edge_contributes`,
> `side_acc_eff_combine_contributes`, `side_acc_eff_least`). At the CFG level
> `cfg_edge_contributes_to_eq` / `cfg_combine_contributes_to_eq` show every
> incoming edge/combine contributes to the point's equation, and
> `entry_local_seed_le_eq` / `entry_global_seed_le_sides` cover the initialization
> constraint. Batch-green.

Goal: align equation (2) with current per-edge/fold construction.

Add documentation-level and theorem-level wrappers:

```isabelle
definition edge_constraint_tree ::
  "cfg => ('g,'a) effectful_domain_transfer => pp => edge_action => pp
   => (pp,'g,'a abs_state) strategy_tree"
```

The wrapper should reduce to `apply_etf etf act u` for ordinary edges. Then prove:

- every incoming CFG edge contributes to the folded RHS;
- `side_rhs_fold_eff` is the finite join of paper edge constraints;
- the entry seed is the paper initialization constraint.

This is mostly naming and decomposition. It should not alter solver behavior.

### Slice 3 - Goblint-style named globals as first-class examples

> **Landed.** `src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy`
> already carried `named_etf` (two slots `Gpos`/`Gneg`, sound through the real
> side solver via `named_analysis_sound`). Phase A adds the `man.global`/`man.sideg`
> witness that reads a *single* named global: `sideg_tree` (queries only the local
> and one slot `gread`, Sides to one slot `gwrite`), with `traverse_sideg_tree`,
> `sides_sideg_tree`, `etf_full_sideg_tree`, and soundness `sideg_assign_sound`
> stated through `side_env_g`. Two-key routing is witnessed by
> `sideg_pos_neg_writes_only_neg` / `sideg_pos_neg_reads_only_pos`, and the joined
> view bridges via `side_env_g_le_side_env` (`gamma_side_env_g_subset_side_env`).
> Batch-green.

Goal: stop presenting `unit` as the primary story.

Add or promote one example where:

- `'g` has at least two constructors,
- `QueryG g` reads one named global,
- `Side g' d` writes a selected named global,
- soundness uses `side_env_g`, not only `glob_env`.

Proof obligations:

- `side_env_g_le_side_env` when a theorem needs the joined global view.
- named-global transfer soundness lemma that states the manager-style contract:

```text
if local and selected global reads are sound, then the Answer and Side effects
are sound for their selected names.
```

This closes the remaining practical gap between paper `man.global`/`man.sideg`
and the repo examples.

### Slice 4 - paper equation (6) for context-sensitive calls

> **Started (2026-07-01, A1/A2).** `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` lands the
> first concrete piece: `switching_combine_sound`
> (`Example_Finite_Sign_Context_Analysis.thy`) names the theorem-facing soundness
> obligation of equation (6)'s combine; `fixed_combine_satisfies_switching_combine_sound`
> discharges it for the context-preserving instance (`context d c = c`, the certified
> fixed combine); and `fctx_route_call4/7` + `fctx_route_bound_zero/pos` witness that
> the value-dependent selector (`fctx_ec_call` = paper `context_u,f,args`) routes each
> call to the correct finite context with the side contribution bounded by that keyed
> slot. Open: the general equation-(6) discharge for value-dependent `context` (the
> `paper_context_call` locale below), plus an `abs_state` switching combine and the
> return-path re-import argument.

Goal: align the context solver with the paper's call transfer:

```text
c' = context d c
side [start_f,c'] (enter d)
read [ret_f,c']
combine d ret
```

Current infrastructure already supports context-indexed locals and an executable
state-dependent context bridge. The migration should add a clean theorem-facing
locale:

> **Amendment (2026-07-29, issue #66/G1).** `context :: 'a abs_state => 'c => 'c`
> below has no call-site argument, so it cannot express the paper's Example 7
> (`context_u,f,args _ _ = u`) — the same gap `SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`
> names G1. That gap is now fixed at the semantic layer: `CFG_Local_Trace.thy`'s
> `key`/`enterc` take the call-site `pp` (`enterc :: cfg_node => 'c => store => 'c`),
> validated by a computed instance in `Example_Interval_DG_CallString.thy`. This
> slice's locale, if built, should fix the same signature gap here and take
> `context :: pp => 'a abs_state => 'c => 'c`.

```isabelle
locale paper_context_call =
  fixes context :: "pp => 'a abs_state => 'c => 'c"
  fixes enter :: "'a abs_state => 'a abs_state"
  fixes combine :: "'a abs_state => 'a abs_state => 'a abs_state"
```

Key lemmas:

- non-call edges preserve context;
- call edges route the start and return unknowns through the same `c'`;
- the existing `side_cfg_T_eff_ctx` instance satisfies the paper equation (6);
- initialization satisfies equation (7).

This slice should explicitly compare `context_transfer` / `trace_witness_ctx`
with the paper's `context_u,f,args`.

### Slice 5 - digest-indexed globals as reduced cardinal power

Goal: move from semantic digest soundness to solver-level digest slots.

Represent paper `D[x]^A = A -> D[x]` by either:

1. payload lifting: store `'a abs_state` replaced by `'d => 'a abs_state`, or
2. slot splitting: replace a named global `g` by `(g, d)` when the digest set is
   finite and statically known.

Recommendation: start with slot splitting for globals and keep locals
context-indexed as `(pp, d)`. This matches the existing finite `'g` solver
interface and avoids a large rewrite of `abs_state`.

New definitions:

```text
compat_glob_env cmp sigma g reader_digest
cfg_collect_digest_global dg cmp ...
```

Key lemmas:

- compatible global join is below `glob_env`;
- `digest_read_sound` instantiated by a solver environment, not just an
  arbitrary `envd`;
- flat collapse when compatibility is universal;
- ST/MT example from the paper: an `ST` reader excludes `MT` writes.

### Slice 6 - analysis-specific combine

> **Landed.** `unit_combine_tree gs cmb cc ex` takes the combine operation as a
> parameter instead of computing `combine# gs dst` itself, and
> `unit_etf_of_transfer` / `mixed_etf_of_transfer` feed it the transfer record's
> own `combine_env#` (for `etf_combine_env`) and `tf_combine_collect_abs`
> (for `etf_combine_collect`). `in_gamma_unit_combine_tree` is stated against an
> arbitrary combine operation sound for an arbitrary concrete two-input
> operation, so it discharges both roles of Goblint's interface; the
> destination-free `unit_combine_env_tree` and its four lemmas collapsed into
> instances of the general builder. `sound_transferI_for` now takes the merge's
> soundness as an obligation rather than pinning `tf_combine_env` to
> `combine_env_abs`, and `sound_rhs_generator_base` / the `*_transfer` cone and
> monotonicity lemmas carry the combine as a parameter `Fc` with its own
> monotonicity assumption. Sign, Interval and Parity keep `combine_env_abs` and
> so instantiate at `combine# gs`.
> `src/Examples/Sign/Example_Sign_Custom_Combine.thy` is the witness that the
> parameter is free: a Sign instance whose merge joins the caller's view of a
> global into the callee's, proved sound, cone-compatible and monotone through
> the unchanged generic infrastructure, plus disequality witnesses against
> `combine_env_abs` and `combine#`. The executable bridge
> (`sound_rhs_generator_exec`, `part_post_solution_st_to_abs_eff_unit_transfer`)
> still names `combine#` outright: `combine_collect_resolved_for_q` is the
> resolved-store realization of the structural merge, so an analysis with its own
> merge has no code-generated counterpart yet.
>
> **Call metadata and the caller continuation.** The combine operations are
> indexed by a `call_info` record (`ci_dst`, `ci_callee`, `ci_formals`,
> `ci_args`) built by `call_info_of` from the CFG's `CallEdge` and the callee
> name, rather than by a bare destination. `return_calls` / `return_call_list`
> carry that record, so every combine site on the `abs_state` route -- solver
> trees, RHS generator, cone and monotonicity lemmas, executable trees -- sees
> the same call metadata Goblint's `Analyses.Spec` passes to `combine_env` and
> `combine_assign`. Goblint's `fexp`, callee context `fc` and `Queries.ask` have
> no VIMP counterpart and are deliberately absent.
>
> `tf_caller_cont` is the caller half of Goblint's `enter`, which returns a
> *pair*: `tf_enter_pair tf ci sigma = (caller_cont# tf ci sigma, enter# tf ...)`.
> `caller_cont#` over-approximates the pre-call concrete caller store, retaining
> only information intended to remain usable when the call returns; it may forget
> abstract facts invalidated by potential callee effects. The concrete caller
> store itself is unchanged at call entry, so the soundness statement keeps the
> same concrete `s` on both sides; generalizing the concrete side would only be
> warranted once a concrete caller-side transition at call entry is modelled.
>
> The continuation belongs to `enter`, not to combine: `combine_env#` and
> `tf_combine_collect_abs` take the continuation as their first *state* argument
> and never recompute it. Applying `caller_cont#` is the job of the tree builders
> in `unit_etf_of_transfer` / `mixed_etf_of_transfer`, which stand in for `enter`
> at the call-return boundary, and `tf_sound_combine_env_at_call_forD` /
> `tf_sound_combine_collect_at_call_forD` are the bridge lemmas that compose the
> two. It is applied exactly once per call-return path.
>
> The routed D/G family (`Sign_Named_Global_Eff`) fixes its own structural return
> operation, so it takes the same `call_info` but projects `ci_dst ci` into the
> destination-only `combine#`, keeps environment-merge-then-assignment ordering,
> and applies no `caller_cont#` -- the continuation protocol belongs to the
> `abs_state` route.
>
> Threading `call_info` turned out to be an interface change, not a
> solver-architecture rewrite: most `dst` occurrences are plain binders whose
> type is inferred, so the whole migration is roughly 25 edited sites. Large
> downstream cascades (`TD_Side_RHS_Generator`, `Exec_Bridge`) went green with no
> edits of their own once the upstream types changed.

Goal: replace hardwired structural return combine with a Goblint-style
analysis-provided `combine`.

The former `unit_combine_tree` implemented:

```text
locals from caller, globals from callee exit
```

That is sound for product-style Sign/Interval states, but it baked in a
non-Goblint API decision and blocked relational domains.

Assumption discharged by each analysis:

```text
combine_tree_sound:
  caller concrete in gamma caller_abs
  callee concrete in gamma callee_abs
  implies restored concrete in gamma (etf_full combine_tree sigma)
```

The structural merge is recovered as one instance.

This is the most important semantic alignment step for Goblint's `enter` and
`combine` interface.

### Deferred: the relational call-protocol witness

`Rel_Order_Domain.thy`'s `relc` cannot serve as the custom-combine regression.
Its carrier is genuinely relational -- a finite set of pairs `(x, y)` meaning
`x <= y`, with no `vname => 'a` function anywhere -- but its call path is
deliberately maximally imprecise: `dgs_enter_rel` and `dgs_combine_env_rel`
both return `top_relc`, discarding every relation. There is no call-side
invalidation to relocate into a caller continuation, so `relc` keeps
`dgs_caller_cont = (\<lambda>_ d _. d)` and its semantics are left unchanged.

The witness is instead a separate instance over the same carrier shape:

- conservative callee may-write information, keyed by `ci_callee`;
- `caller_cont ci dc g` drops only caller relations mentioning a variable the
  callee may write;
- `combine_env ci dcont de g` meets the surviving caller relations with the
  *caller-visible* callee-exit relations -- not the whole exit set, since the
  callee's own locals and formals do not survive the boundary;
- `combine_assign` stays the second phase.

The regression must exercise both operands, not just the continuation: a
caller fact (`x <= y`, with the callee writing only `z`) and a callee fact
(`g <= h`) must both survive the return, which neither the havoc behaviour nor
a componentwise reconstruction can achieve.

Prefer deriving may-write from the VIMP procedure body. If transitive or
recursive computation would balloon the scope, an explicit conservative
procedure summary is acceptable, documented as the analysis-side stand-in for
Goblint's `Queries.ask` -- which VIMP's `dg_spec` has no counterpart for.

### Next: retire the TD/etf spine

The call/return protocol now lives on the D/G route only. Voblint still
carries a second, independent interprocedural spine -- `TD_Side` with
`domain_transfer`/`effectful_domain_transfer` -- which is not a specification
layer above D/G and not a refinement of it: no proved relation connects the
two, and the exported CLI never reaches it.

The end state is one of each:

```text
transfer interface      dg_spec
call/return protocol    D/G
context routing         D/G
RHS generator family    D/G
executable path         D/G
soundness chain         D/G -> ltr_collect
CLI/codegen path        D/G
```

Removal covers `domain_transfer`/`effectful_domain_transfer`,
`unit_etf_of_transfer`/`mixed_etf_of_transfer`, `side_cfg_T_eff*`,
`make_side_rhs_tree_eff*`, the `_st` TD-side execution path, the
`Exec_Bridge` pieces specific to that spine, and `LTR_TD_Side_Eff_Sound*`.
The strategy-tree monad, the vendored TD solver, `resolved_st_q` and
`ltr_collect` are shared substrate and stay.

The gate is deletion, not deprecation: no compatibility shadow spine and no
internal wrapper that keeps both architectures alive. A temporary public API
alias is the only acceptable exception.

### Slice 7 - update-rule abstraction

Goal: model the solver-level hook discussed in paper Section 5.3.

Do not change the vendored solver first. Add an abstract post-processing layer:

```text
origin = local unknown or edge id
contribution table : g -> origin -> value
update_rule old origin new -> table
global_value table g = join over origins
```

Prove:

- naive update refines to current global join;
- per-origin update is sound if every stored contribution is sound;
- per-origin widening is sound when widening is an upper bound;
- revocation is sound only if dependency invalidation removes all consumers
  or re-solves them.

This can start as a separate theory/document because full TD integration is
substantial.

### Slice 8 - multi-analysis product/sum and query bus

Goal: align with Goblint framework structure.

This is out of thesis-critical path. If pursued:

- define activated analyses indexed by `'A`;
- local domain as product over analyses;
- global names as dependent sum `(analysis_id, global_name)`;
- componentwise transfer;
- optional query lattice and `ask` contract.

Key risk: dependent domain families are awkward in HOL with the current uniform
`'a abs_state`. A pragmatic first step is a fixed binary product of two analyses.

## Recommended order

1. ~~Slice 0: terminology and cross-links.~~
2. ~~Slice 1: paper constraint contract over strategy trees.~~ **(done)**
3. ~~Slice 2: CFG-edge wrapper and fold decomposition.~~ **(done)**
4. ~~Slice 3: named-global example using `side_env_g`.~~ **(done)**
5. Slice 4: theorem-facing context-call locale.
6. Slice 5: digest-indexed globals by slot splitting.
7. Slice 6: analysis-specific combine.
8. Slice 7: update rules.
9. Slice 8: multi-analysis framework.

Rationale: the first four slices mostly expose structure already present. Slice 5
turns semantic digest contracts into solver-facing precision. Slice 6 changes the
API boundary and should land after the existing side/context stack is easier to
read. Slices 7-8 are solver/framework research extensions.

## TODO - recreate paper examples

These examples should become small Isabelle theories under
`src/Formalization/Examples/` once the required slices exist. Each example should
state both the executable result and the semantic soundness property it witnesses.

| Paper example | What it demonstrates | Current support | Target Isabelle artifact | Difficulty |
| --- | --- | --- | --- | --- |
| Fig. 1 / Example 1: sequential globals `g,h`, values `1`, `-17`, `42` | Basic global-store widening shape: locals flow sensitively, selected globals flow insensitively | CFG, side effects, Sign/Interval domains, named globals mostly exist | `Example_Seidl_Global_Store_Widening.thy`: prove `g <= 42`-style abstract fact for named global slots | Medium |
| Example 2: interval widening loses precision to `[-inf, inf]` | Naive global widening can destroy a useful bound | Interval domain exists; update-rule model does not | Negative/diagnostic example after update-rule abstraction exists | Hard |
| Example 2 refinement: widen per origin | Per-origin contribution tables recover `[-17,42]` | `Origin_Lift` has executable per-origin cells; the side-effect/dependency `part_post_solution` transport remains open | `Example_Seidl_Per_Origin_Update.thy`: compare naive vs per-origin update rule after P11 transport | Hard |
| Example 3: global `h` written once but flow-insensitive analysis infers repeated writes | Flow-insensitive globals lose path/count precision | Trace/digest semantics exists; solver-level digest slots pending | `Example_Seidl_Mod_Count_Digest.thy`: bounded write-count digest proves final `h = 1` | Hard |
| Fig. 2 / Example 4: thread-modular local `y`, shared global `g` | Thread-local state remains flow-sensitive while shared memory is flow-insensitive | No real thread semantics; mixed-flow mechanism exists | Start as sequential simulation of two thread bodies; full thread semantics is stretch | Very hard for full version |
| Fig. 3 / Example 9: `{ST, MT}` digest | Reader in single-threaded mode ignores writes from multi-threaded mode | `cfg_collect_ctx`, `digest_read_sound` exist; solver slots pending | `Example_Seidl_ST_MT_Digest.thy`: compatible read excludes `MT` global writes | Medium-hard |
| Example 7: 1-callstring context sensitivity | Calls from distinct call sites get distinct procedure instances | Context-indexed equation generator exists | `Example_Seidl_One_Callstring.thy`: same procedure called twice, separate contexts prove separate facts | Medium |
| Example 8: partial tabulation by abstract entry state | Callee context is `enter d`, not just call site | Semantic/executable context bridge exists | `Example_Seidl_Partial_Tabulation.thy`: context keyed by abstract start state | Medium-hard |
| Goblint `man.sideg` assignment example | Assignment to selected global emits a named side effect | `Side g d t`, `QueryG g` exist | Promote a named-global transfer example using at least two global names | Easy-medium |
| Goblint `ask/query` cooperation | Analyses exchange information without full product reduction | Not modeled | Deferred framework example after multi-analysis product/sum | Very hard |

### TODO difficulty analysis

| Change | Why it matters | Expected effort | Risk |
| --- | --- | --- | --- |
| Add paper-shaped contracts over `strategy_tree` | Makes equation (1) explicit and reviewable | 1-2 days | Low |
| Add CFG-edge wrapper and fold decomposition | Makes equation (2) explicit | 1-3 days | Low |
| Add named-global example with `side_env_g` | Shows Goblint-like `global`/`sideg` use | 2-4 days | Low-medium |
| Add context-call locale for equation (6) | Makes context-sensitive calls match the paper | 3-6 days | Medium |
| Recreate 1-callstring example | Tests context routing end to end | 3-6 days | Medium |
| Recreate ST/MT digest example by slot splitting | Tests digest-compatible global reads | 1-2 weeks | Medium-high |
| Recreate write-count digest for `h` | Tests bounded modification-count digests | 1-2 weeks | Medium-high |
| Generalize `combine` to analysis-provided trees | Aligns with Goblint `combine`; prerequisite for relational domains | 1-3 weeks | High |
| Model per-origin update rules | Captures paper Section 5.3 precision recovery | 2-4 weeks | High |
| Integrate update rules into TD-side solving | Makes update precision executable, not just semantic | 4+ weeks | Very high |
| Separate local/global payload domains | Matches Goblint `D` vs `G` | 3-5 weeks | Very high |
| Multi-analysis product/sum and query bus | Matches Goblint framework composition | 4-8+ weeks | Very high |
| Full thread-modular semantics | Recreates Fig. 2 faithfully | Open-ended | Very high |

### TODO sequencing for examples

1. Start with the named-global assignment example. It exercises existing
   infrastructure and gives a small proof target.
2. Recreate Example 7 with 1-callstring contexts. This validates the
   context-indexed solver before introducing digest-specific globals.
3. Recreate Fig. 3 / Example 9 using finite digest slot splitting.
4. Recreate Fig. 1 / Example 1 as the baseline global-store widening example.
5. Add write-count digest for Example 3 after digest slots are stable.
6. Add per-origin update rules and revisit Example 2.
7. Treat Fig. 2 as a stretch goal unless a thread semantics is added.

## Open risks

- **Uniform payload type.** The paper permits `D[x]` per unknown; Goblint has
  separate local and global domains. The repo uses one `'a abs_state` payload.
  This keeps the solver bridge simple but limits full fidelity.
- **Finite globals.** `glob_env` relies on finite `'g`. This is acceptable for
  executable instances, but the paper permits potentially infinite unknown sets.
- **Context/source of calls.** The paper treats procedure start points as globals.
  The repo uses explicit interprocedural CFG structure and combine triples. The
  migration should align the theorem shape, not force a worse CFG encoding.
- **Relational domains.** Hardwired `restrict_local`/`restrict_global` loses
  cross-variable relations. Analysis-specific `combine` is required before an
  octagon story can match Goblint.
- **Termination.** The current soundness story assumes `solve_dom`; the paper
  discusses widening/narrowing and TD cycle handling. A termination theorem is a
  separate project.
- **Update-rule precision.** Per-origin update rules can improve precision at
  globals, but revocation interacts with dependency invalidation and should not be
  modeled as a pure lattice join without solver-state invariants.

## Acceptance checklist

- [x] Paper equation (1) has a named Isabelle contract over `strategy_tree`
  (`se_constraint_holds`, Slice 1).
- [x] Paper equation (2) has a named CFG-edge wrapper and fold decomposition lemma
  (`edge_constraint_tree`, `side_acc_eff_least`, Slice 2).
- Paper equations (3), (6), and (7) are stated as theorem-facing call/context
  contracts. (Eq (7) init: `entry_local_seed_le_eq` / `entry_global_seed_le_sides`,
  Slice 2. Eqs (3)/(6) call/context: open, Slice 4.)
- [x] At least one executable example uses named globals beyond `unit`
  (`named_etf`, `sideg_tree`, Slice 3).
- Digest-indexed global reads are backed by solver slots, not only arbitrary
  `envd`.
- Structural combine is an instance of an abstract `combine`, not the only API.
- The docs consistently describe the system as a side-effecting constraint
  system with local unknowns `L`, global unknowns `G`, and valuation `sigma`.
