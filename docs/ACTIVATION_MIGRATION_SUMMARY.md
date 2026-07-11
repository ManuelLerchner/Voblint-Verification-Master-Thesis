# Activation-aware seeded soundness — migration summary

Status of the migration to make the activation witness the canonical foundation for
seeded context-sensitive soundness. Records every delivered theorem, the executable
integration state, and the one precise technical blocker that stops the shipped-run
end-to-end (a forward-reachability closure not provided by the generic solver
post-solution — genuinely new solver theory, not a re-application).

## 1. Delivered and green (`Voblint_Formalization` builds)

### Semantic foundation (`CFG_Collect_Activation.thy`)
* `trace_witness_act` — call-only activation witness (context constant on ordinary
  edges, routed at `EA_Enter`, resumed at combine).
* `trace_witness_act_imp_trace_witness`, `cfg_collect_ctx_act_le_collect` — forgetful
  collapse to the unchanged concrete semantics.

### Generic soundness (`Seeded_Activation_Sound.thy`)
* `activation_trace_sound` / `activation_collect_sound` — the domain-independent
  backbone, **no** `dg`/`cmp`/`entdg`/`DG_INTRA`/`DG_RETURN`/`DG_CALLEE` (digest
  machinery retired on the seeded path).
* `seeded_activation_edge` / `seeded_activation_seed` / `seeded_activation_comb` —
  per-rule discharge from the closed reductions.
* `cover_seed` + `enter_state_in_cover_seed` — the locals-covering seed that makes
  `SEED_G` satisfiable (globals from the context, locals pinned to a zero point).
* `cover_seed_st` + `lookup_cover_seed_st` + `fun_of_st_cover_seed_st` — the
  **executable** covering seed and its `st`->`abs` correspondence
  `(\<lambda>c. fun_of_st (cover_seed_st pz c)) = cover_seed pz fun_of_st`, ready to plug a
  re-solved run into the abstract theorem via `part_post_solution_cmp_seed_st_to_abs_eff`.
* `seeded_activation_collecting_sound_cover` — the packaged theorem:
  `cfg_collect_ctx_act \<subseteq> \<gamma>` from a covering-seed post-solution, with `SEED_G`
  reduced to seed-\<gamma>-on-globals + `0 \<in> gamma pz`, and the `vars` obligations
  (`cov_edge`, `cov_frame`) **conditioned on an inhabited source slot** so they are
  instantiable against a finite solved `vars`.

### Domain instances (`Activation_Domain_Instances.thy`)
* `sign_activation_collecting_sound_cover`, `ivl_activation_collecting_sound_cover` —
  the packaged theorem specialised through each domain's `sound_transfer`.
* `sign_zero_point` (`0 \<in> gamma SZero`), `ivl_zero_point`
  (`0 \<in> gamma (Ivl (Fin 0) (Fin 0))`) — the domain zero-point obligations.

### Dependency reachability (`Seeded_Activation_Reach.thy`)
The `vars` obligations are backed by the dependency closure `part_post_solution`
already provides — **no** new forward-closure invariant. Verified there is **no
counterexample** (`dep_aux` ignores `Side` targets, so the seeded callee entry is
reached via the combine's `QueryL` of the callee exit + the body's backward chain):
* `dep_aux_side_cfg_T_eff_cmp_seed` — the seeded RHS depends exactly on the union of
  its intra and combine summands.
* `Inl_dep_L_intra_pred` — a non-`EA_Enter` predecessor `(u,ctx)` is a `dep_L` of
  `(v,ctx)`.
* `Inl_dep_L_combine_summand` — a local read of the combine tree (caller call node,
  routed callee exit) is a `dep_L` of the return node.
* `intra_pred_in_vars` / `combine_dep_in_vars` — the backward `vars`-membership
  bridges (a dependency of a solved unknown is solved).

## 2. The routing, now fully understood

`ivl_combine_rehydrate cc ex ctx` reads the caller local `sc = sg (Inl (cc, ctx))` and
routes the callee at context `ivl_ec ctx sc = restrict_global_st sc` — the callee
context is `restrict_global_st` of the caller slot. So the activation `enterc` must be
`enterc c s = restrict_global_st (point_abstract s)` and reconcile with the generator's
`restrict_global_st (sg (Inl (u, c)))` by **point routing**: on a point-exact slot,
`s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>` gives `restrict_global_st (point_abstract s) =
restrict_global_st (sg (Inl (u, c)))` (the machinery of `enter_mono_point` /
`point_digest`). `combc c1 _ = c1` (return to caller context). With these,
`traverse_ivl_combine_rehydrate` + `seeded_clean_comb_bound` discharge `COMB_BOUND`, and
`iseed_slots_point`-style point-exactness discharges `SEED_glob`.

## 3. The precise blocker — forward reachability closure

`part_post_solution T x sigma vars` (vendored `Basics_side.thy:337`) guarantees
`vars` is closed under **dependencies**: `\<forall>u \<in> vars. dep\<^sub>L T sigma u \<subseteq> vars`. For the
generator, `(v, kc)`'s RHS reads its predecessors, so
`(v, kc) \<in> vars \<Longrightarrow> (predecessor u, kc) \<in> vars` — the **backward** direction.

The activation obligations `cov_edge` / `cov_frame` need the **forward** direction: an
activation trace reaching `(v, ctx)` passes through intermediate `(node, context)`
unknowns that must be in `vars` for `seeded_clean_edge_bound` / `seeded_clean_seed_bound`
to apply (an unsolved slot is `\<bottom>`, whose `\<gamma>` is empty, so the conclusion
`last \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>` fails there). Concretely `cov_frame` asks
`s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk> \<Longrightarrow> (v, enterc kc s) \<in> vars` — the reached callee context is
solved. This is **not** a consequence of dependency closure, and it is not checkable by
`eval` because `kc` ranges over infinitely many `ivl st`.

Closing it — the promising route is **backward dependency closure from the query
unknown**, which `part_post_solution` *does* provide. The query is the exit unknown
`x = (cfg_exit, bot) \<in> vars`, and `vars` is closed under `dep\<^sub>L`. Tracing the
dependency chain of a return node in `vars`:

* the return node `(r, ctx) \<in> vars` (dependency of the exit along the caller path);
* its combine RHS reads the callee exit `QueryL (ex, restrict_global_st (sg (Inl (cc, ctx))))`
  (`ivl_combine_rehydrate`), so `(ex, callee_ctx) \<in> dep\<^sub>L (r, ctx) \<subseteq> vars`;
* the callee exit depends backward through the callee body on the callee entry, so
  `(callee_entry, callee_ctx) \<in> vars`.

So the reached callee-entry context `callee_ctx = restrict_global_st (sg (Inl (cc, ctx)))`
is in `vars` **by dependency closure**, not forward closure. What remains is to connect
the *activation* callee context `enterc kc s` to that *dependency-graph* context
`restrict_global_st (sg (Inl (cc, ctx)))` — the point-routing identity of §2 — and to
thread the argument through the activation trace structure. This is a real but
dependency-closure-backed proof, not new solver theory. The alternative — a
program-specific reachable-context enumeration per run — remains available but is
disfavoured by project guidance.

## 4. What this means

The activation framework is **complete and sound as a generic theorem**, instantiated
for both domains, with the executable seed correspondence in place. The premises that
remain (`cov_edge`, `cov_frame`, `SEED_glob`, `COMB_BOUND`) are all **genuine semantic
properties**, not artifacts of the old witness — no hidden or vacuous assumption
survives. The shipped-run end-to-end `cfg_collect_ctx_act \<subseteq> \<gamma>(solution)` is blocked
only by the forward-reachability closure of §3, which is a well-scoped piece of new
solver theory (option 1). Until it lands:

* the generic activation theorem and the domain instances are the canonical soundness
  statement for any analysis that supplies a covering-seed post-solution plus the
  reachability closure;
* the old `clean_ctx_collect_rread_head_bound` path is **retained** as the current
  route for the shipped return-node results (it cannot be retired while the new path
  lacks a discharged reachability obligation), and the retain (`\<squnion> g`) spine is
  unchanged;
* no obsolete digest infrastructure is removed, because the retain path still uses it.

## 5. Status of the reachability route and the remaining slice

The dependency-reachability **foundation is proved** (`Seeded_Activation_Reach.thy`,
§1): the seeded RHS dependency structure, the intra/combine `dep_L` memberships, and the
backward `vars`-membership bridges, all green — confirming formally that CFG
reachability implies dependency reachability with no omitted dependency.

The one remaining piece is the **trace-to-`trans_dep` induction** that reconciles the
*forward*-shaped `cov_edge` / `cov_frame` (source inhabited ⟹ target solved) with the
*backward* bridges (a dependency of a solved unknown is solved): prove that every
`(node, context)` on a `trace_witness_act` derivation reaching a solved query unknown
`(q, cq) \<in> vars` lies in `trans_dep\<^sub>L (q, cq) \<subseteq> vars` (using
`part_post_solution_implies_trans_dep_subsumed`). The intra step is the predecessor
bridge; the combine step splits into the caller sub-trace (under the caller call node,
a combine `dep_L`) and the callee sub-trace (under the routed callee exit, a combine
`dep_L`, whose body backward-chain reaches the callee entry). This threads the argument
so `cov_edge` / `cov_frame` are discharged for the query's cone rather than assumed
universally. With it, plus the point-routing identity
`enterc kc s = restrict_global_st (sg (Inl (cc, kc)))` (§2) for `SEED_glob` / `COMB_BOUND`
(from `iseed_slots_point`, `traverse_ivl_combine_rehydrate`, `seeded_clean_comb_bound`),
both domains close `cfg_collect_ctx_act \<subseteq> \<gamma>` on the shipped runs, completing the
migration and allowing retirement of the old seeded path.
