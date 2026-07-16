# ROUTE_A7 executable D/G migration — monovariant → polyvariant, in place

Status: **in progress.** One generic executable D/G generator, parameterized by the
context domain; monovariant analysis recovered as the `unit` instantiation. No
parallel generator or theorem family. Tracks the "full staged migration" directive.

The **semantic** cross-context collecting soundness already exists
(`sound_dg_spec.dg_collect_ctx_sound`, `DG_Route_Soundness.thy`, over
`cfg_collect_ctx`). This migration builds the **executable** half: a generator whose
solver post-solution discharges that theorem's eight obligations per reachable
context.

---

## Stage 1 — solver-soundness gate (DONE, executable proof)

Question: can a `Side` (write-effect) target key be **computed at runtime** from a
preceding `QueryL`/`QueryG` result, and does the verified `TD_side` solver still
materialize and subsume it?

Definitional evidence:

- `Basics_side.sides_of_rhs (Side y d t) sigma = (let m = sides_of_rhs t sigma in
  m(Inr y := m (Inr y) \<squnion> d))`, and `sides_of_rhs (QueryL y g) sigma =
  sides_of_rhs (g (sigma (Inl y))) sigma`. The side key `y` is evaluated **through**
  the continuations at `sigma` — a dynamically-chosen target is captured.
- `part_post_solution T x sigma vars` requires `sides_of_rhs (T u) sigma \<le> sigma`
  for all `u \<in> vars`, evaluated at `sigma`; no assumption that side targets are
  syntactically fixed.
- `dep_aux (Side y d t) = dep_aux t` (write target absent from read deps) is fine:
  the write is enforced by the `sides_of_rhs \<le> sigma` conjunct and, inside the
  solver, by the unstable-global store `rho ug_state`.
- `TD_side_upd_rule.partial_post_solution` (the solver-correctness theorem) is
  generic over arbitrary `T :: eqsT`; gated only on `solve_dom` (termination),
  checked per-example by `solve_c \<noteq> None` (`by eval`).

Executable probe (I/R REPL, `ivl` values, real warrowing solver
`TD_side_warrowing_apinis_Interp_solve`):

- `probeT`: `QueryL 1 (\<lambda>d. Side (if d = [3,3] then 9 else 7) d (Answer d))`,
  local `1 = [3,3]`. Result: `sigma (Inr 9) = [3,3]` (chosen slot materialized),
  `sigma (Inr 7) = \<bottom>` (unchosen untouched); `solve_c \<noteq> None`.
- `routeT` (full routing roundtrip): two callers side-effect **distinct
  dynamically-chosen** seed slots (`103`, `110`) from two argument values; two
  callee-entry unknowns read their seed via `QueryG`; a combine pulls both callee
  exits transitively. Result kept the two contexts **fully separate**:
  entry/exit ctx3 = `[3,3]`, entry/exit ctx10 = `[10,10]`, combine = `[3,10]`,
  seed `103 = [3,3]`, seed `110 = [10,10]`.

Conclusion: gate PASSES on all five properties (dynamic target from query; covered by
`part_post_solution`; deps need not list the target; every chosen slot
discovered/materialized; correctness theorem target-shape-agnostic). The seed-slot
routing separates contexts on the real solver.

---

## Architecture

`Side` targets **globals only** (`Side 'g 'd t`, `'g` = the `Inr` key). A callee
entry is a local unknown `Inl (entry, ctx)`, so cross-context entry seeding flows
through a **per-`(entry_pp, callee_ctx)` global seed slot**. That is what the dormant
`gkey` / `frame_seed` / `is_frame_entry` hooks anticipated.

Reuse: `context_domain` locale (`Context_Domain.thy`) supplies
`start_context / prep / ctx_sel / entdg / cmp` and the composite
`route cc ctx a = ctx_sel cc ctx (prep cc a)`. Context model for the flagship: the
**entry-store digest** (already verified via `cfg_collect_ctx`); `twice` routes on
argument values, not a global, so the `fctx` obstruction
(`ROUTE_A7_DECISION_A_vs_C.md`) does not apply.

### One generic generator, three routing hooks

Generalize `side_cfg_T_eff_cmp_seed_dg` (already `'c`-generic in its unknown space
`pp \<times> 'c`, global keys `'k`) so that enter handling is hook-driven:

- `pred_sel :: cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list` — predecessor selector for
  the intra fold.
- `enter_pub :: 'c \<Rightarrow> (pp \<times> edge_action) list \<Rightarrow> tree list` — caller-side
  publication trees for a node's **outgoing** enters (`enter_successor_list`,
  landed in `CFG_Def.thy`). Each tree:
  `QueryL (u,c) (\<lambda>d. Side (seed_key entry (route u c d)) (enter_step d) (Answer bot))`.
- `seed_read :: pp \<Rightarrow> 'c \<Rightarrow> tree` — at a frame-entry node, `QueryG (seed_key v c)`
  read of the incoming seed (generalizes the constant `frame_seed`).

Combines need **no** generator change: the existing `cmb` hook is fully abstract;
the polyvariant instance supplies a routing combine tree
`QueryL (cc,c) (\<lambda>dc. QueryL (ex, route cc c dc) (\<lambda>de. ... combine ...))`.

### Instantiations (recover both analyses from the ONE generator)

| hook | `unit` (monovariant) | polyvariant (entry-store ctx) |
|---|---|---|
| `pred_sel` | `predecessor_list` (enters merge as same-ctx predecessors) | `non_enter_predecessor_list` |
| `enter_pub` | `\<lambda>_ _. []` (no publication) | routed `Side` to `seed_key` |
| `seed_read` | `\<lambda>_ _. Answer bot` | `QueryG (seed_key v c)` |
| `cmb` | `dg_cmb` (same-ctx cc/ex read) | routing combine tree |
| `gkey` / `'k` | `(\<lambda>_. ())`, `'k = unit` | real-global + `seed_key` slots |
| `route` | `\<lambda>_ _ _. ()` | `context_domain.route` |

`unit` reproduces the current `dg_gen` byte-for-byte (empty publication list, `bot`
seed, `predecessor_list` intra fold), so monovariant soundness and the
`Exec_DG_Bridge` transport need no reproof; they are the `'c = unit` instance.

---

## Obligation mapping (Stage 6)

The solver post-solution `sigma` over `pp \<times> 'c + 'k` feeds
`sound_dg_spec.dg_collect_ctx_sound` with
`M = dg_gamma_c sigma ctx`, `rd = dg_D_c sigma ctx`, `rt = route`, `entdg`/`cmp`/`dg`
from the context domain:

- ENTRY / PROC_ENTRY / EDGE — per-context postfix (`dg_postfix_c`) at each reachable
  `ctx`, from `step_sound` + coverage (as in the monovariant
  `dg_post_solution_collect_sound`).
- COMB — the routing combine tree makes the callee-exit read land at
  `route cl ctx (dg_D_c sigma ctx cl)`; discharged from `combine_sound`.
- ENTER_MONO — domain obligation `cmp (entdg s) (route cl ctx (dg_D_c sigma ctx cl))`
  for `s \<in> M (cl, ctx)`; discharged per instance (interval: entry-store digest
  monotone under `enter_step` abstraction).
- DG_INTRA / DG_RETURN / DG_CALLEE — trace-digest laws of the entry-store context
  domain (already available for the semantic entry-store route).

---

## Staged edit list

1. **Gate** — DONE (above).
2. **`CFG_Def.thy`** — `enter_successor_list` + `set_enter_successor_list` /
   `_action` / `_edge`. **LANDED (green).**
3. **`DG_Framework.thy`** — generalized `side_cfg_T_eff_cmp_seed_dg`: prepended
   `pred_sel :: cfg \<Rightarrow> pp \<Rightarrow> (pp \<times> edge_action) list`, replaced
   `frame_seed :: 'c \<Rightarrow> 'd` with `extra :: 'c \<Rightarrow> pp \<Rightarrow> tree list`
   appended to the fold list, and dropped the `is_frame_entry`/`frame_seed` acc0
   term (\<open>bot\<close> for all callers). Both new behaviours — the frame-entry seed
   **read** (`QueryG (seed_key v c)`) and the caller-side `EA_Enter`
   **publication** (routed `Side` to `seed_key`) — are `extra` members: folded
   Answers add \<open>bot\<close> locals, their `Side` effects accumulate via
   `sides_of_rhs_seqcomp`. Unfold lemma `eq_side_cfg_T_eff_cmp_seed_dg` re-proved
   with the new list shape (`... @ extra ctx v`). **LANDED (green).**
4. **`DG_Soundness.thy`** — `dg_gen` is now the `unit` instantiation
   (`pred_sel = predecessor_list`, `extra = (\<lambda>_ _. [])`); `@ []` and the dropped
   `bot` frame term reduce under `simp`, so `eq_dg_gen` / `dg_post_solution_*`
   unchanged. **LANDED (green).**
5. **`Exec_DG_Bridge.thy` / `Mixed_Sign_Interval.thy`** — `dg_gen_of` and
   `mixed_si_generator` re-expressed as the same `unit` instantiation; commute /
   `part_post_solution` transport proofs survive (`@ []` reduction). **LANDED
   (green).** Transport is still typed at `(v, ())`; generalizing the transport to
   `(v, c)` is Stage 5b, ahead.
6. **Regression** — `Example_Interval_DG_Flagship` (loop, `unit`),
   `Interval_DG`, and the monovariant `Example_Interval_DG_IP_Flagship` all stay
   green as `unit` instances of the generalized generator. **VERIFIED (green in
   I/Q).**

### Stage 7 design probe (DONE, disposable I/R computation)

A local copy of the landed generator (`side_poly_gen`, byte-identical body) was
instantiated on `twice_cfg` with concrete interval poly hooks and solved with the
real `TD_side_warrowing_apinis_Interp_solve`:

- context `'c = ivl` = value of `p` at callee entry; `gk = GlobAt ivl | Seed pp ivl`
  (explicit real-global vs seed-slot separation);
- `pred_sel = non_enter_predecessor_list`; `gkey = GlobAt`;
- `extra ctx v` = (frame-entry `QueryG (Seed v ctx)` seed read) ++
  (per outgoing enter: `QueryL (v,ctx) (\<lambda>d. Side (Seed w (route d a)) (entered d a) ...)`);
- `cmb ctx dst cl ex` recomputes `route` from `cl`'s *own* enter edge, then reads the
  callee exit at `Inl (ex, route ...)` — same route as publication, so the combine
  reads the matching callee context.

Result (solver-computed, exact):

```text
call 1 (ctx = [3,3]):   p = [3,3]    #ret = [6,6]
call 2 (ctx = [10,10]): p = [10,10]  #ret = [20,20]
caller:                 x = [6,6]    y = [20,20]
```

Seed slots: `Seed 0 [3,3] -> p=[3,3]`, `Seed 0 [10,10] -> p=[10,10]`. Coverage:
`(0,[3,3])`, `(0,[10,10]) \<in> vars`; `(0, mctx) \<notin> vars` --- the callee is
materialized once per routed context and never under the main context. Termination:
`solve_c \<noteq> None`. All five probe questions pass; the design is validated on the
verified solver before committing definitions.

Note (risk: context-key finiteness): `'c = ivl` value-key is finite and stable for
`twice` (two constant args, no recursion). The committed generic interface must expose
a canonicalizing/finite routing function; do not assume arbitrary interval states are
safe keys for recursive/widening-heavy programs.

### Stage 7 executable instance — COMMITTED, batch-green

`src/Formalization/Examples/Executable/Interval/Core/Example_Interval_DG_Ctx_Flagship.thy`
(in `Voblint_Formalization` ROOT). The routed context hooks on the **landed**
generalized generator:

- `gk = GlobAt ivl | Seed pp ivl` (explicit real-global vs seed-slot separation);
- `route_ivl d a = lookup_st (entered_ivl d a) ''p''`,
  `entered_ivl d a = snd (dg_spec_step Spoly a d bot)`;
- `extra_ivl g ctx v` = frame-entry `QueryG (Seed v ctx)` read ++ per outgoing enter
  `QueryL (v,ctx) (\<lambda>d. Side (Seed w (route ...)) (entered ...) ...)`;
- `cmb_ivl g ctx dst cc ex` reads the callee exit at `route` recomputed from `cc`'s
  own enter edge (matching-context return);
- `twice_ctx_eqs = side_cfg_T_eff_cmp_seed_dg non_enter_predecessor_list GlobAt
  (cmb_ivl twice_cfg) (extra_ivl twice_cfg) twice_cfg Spoly bot cinit ...`.

Certified `by eval` on `TD_side_warrowing_apinis_Interp_solve`: `twice_ctx_terminates`,
`contexts_distinct`, `ctx_call1_val = [3,3]`, `ctx_call2_val = [10,10]`,
`call1/2_p_at_entry`, `call1/2_ret_at_exit` (`[6,6]` / `[20,20]`), `x_computed = [6,6]`,
`y_computed = [20,20]`, `seed_call1/2`, `callee_covered_call1/2`,
`callee_not_under_main`. **This is the polyvariant executable analysis: done.** The
soundness certificate is not yet attached.

### Architectural finding — the context interface must be generalized (enter-action-aware)

Tracing the soundness endpoint (`Seeded_Activation_Sound.activation_collect_sound`,
the 5-obligation domain-independent backbone over `cfg_collect_ctx_act`) surfaced a
genuine boundary, not a mechanical gap:

- The activation router is `enterc :: 'c \<Rightarrow> store \<Rightarrow> 'c`, and the `enter` rule of
  `trace_witness_act` routes to `enterc c (last tau)` --- the **caller store**, before
  formals are bound, with **no access to the enter action's argument expressions**.
- Every existing instantiation routes `enterc kc s = restrict_global (\<lambda>x. decode (s x))`
  (`Seed_EnterMono_Lift`) --- on caller-store **globals**. The entire existing
  activation/context machinery models **global-based** (Goblint-base-style) context.
- `twice` routes on the **argument** (entered value of formal `p`). Its two calls come
  from `main` to the same callee with constant args `N 3` / `N 10`; the distinguishing
  information is the call site's argument expression, not the caller store. A
  caller-store router cannot separate them. Argument-sensitive context is **not
  expressible** against the current activation semantics.

Minimal fix (no signature change): route `enterc` on the **entered store** `s'`
instead of the caller store `last tau`. The `enter` rule already binds
`edge_step (EA_Enter xs es) (last tau) = Some s'`, so change `enterc c (last tau)` to
`enterc c s'`. This is:

- **more Goblint-faithful** --- Goblint's `context f (enter man ...)` reads the callee
  entry state, which is `s'`, not the caller store;
- **backward-compatible** --- for the existing global routers
  `enterc c s = restrict_global (\<lambda>x. decode (s x))`, globals are preserved by
  `enter_state`/`bind_formals` (formals are local), so `enterc c s' = enterc c (last tau)`;
- **sufficient for argument context** --- `s'` holds the bound formals, so
  `enterc c s' = <value of the formal>` becomes expressible.

Scope (atomic across these; the `enter` rule change breaks the backbone until all
migrated, so it lands as one green batch, not file-by-file):

- `CFG_Collect_Activation.thy` (core) --- `trace_witness_act.enter`
  (`enterc c (last tau)` -> `enterc c s'`), `act_enter_routes_ctx`, the recursion example;
- `Seeded_Activation_Sound` --- SEED_G / the `enter` induction case / `seeded_activation_seed`
  / the packaged theorems (`enterc c s` -> `enterc c s'`);
- `Activation_Witness_From` (`twf`) --- route on `enter_state (last tau)`;
- `Seeded_Activation_Reach`, `Activation_Domain_Instances` --- follow;
- existing global-context proofs need the one-line bridge
  `enterc c s' = enterc c (last tau)` (globals preserved) where they assert the old shape.

The `unit`-context and global-context analyses remain instances. This is the one core
generalization the interval argument-context slice needs before the soundness
certificate attaches. It is staged as its own migration.

### Goblint alignment (claim discipline)

The call architecture now mirrors Goblint's `enter -> context -> analyze -> combine`
structure, with the key alignment correct: **context is selected from the callee-entry
abstract state after parameter binding** (`enterc c s'` on the entered store `s'`,
matching `context man f callee_state`). The combine already has Goblint's two-phase
split: `combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)`,
where `combine_states <s|t>` is `combine_env` (caller locals + callee globals) and
`combine_assign dst` is the destination assignment. The seed slot `Inr (Seed entry ctx)`
matches `sidel (FunctionEntry f, fc)`; the routed callee-exit read matches
`getl (Function f, fc)`.

Accurate claim: *a simplified, machine-checked semantic model of Goblint's
interprocedural context-sensitive architecture* --- not the exact implementation.
Known simplifications (future faithfulness, not blockers): `enter` is a single
language-level formal-binding transfer, not an analysis-controlled `(D.t * D.t) list`
(no multi-path split / nondeterminism); the context selector sees the caller context
and entered store, not a full manager/query interface; `D.t` is a store, not a product
of relational / heap / thread / path-sensitive domains.

### Soundness target — CORRECTED after tracing the trace semantics

The earlier plan aimed the routed solution at plain `cfg_collect_ctx` via
`dg_collect_ctx_sound`. That is the **wrong target**: `trace_witness`'s `edge` rule
covers enter edges (`CFG_Collect_Trace.thy:79,92`), so `dg_collect_ctx_sound`'s
same-context `EDGE` / `DG_INTRA` obligations fire on enters. For a routed solution the
callee entry under the *caller's* context is `bot`, so those obligations are
genuinely false against plain `cfg_collect_ctx` — no digest choice satisfies all eight
(whole-trace-entry digest breaks `EDGE`; activation-entry digest breaks `DG_INTRA`).

The correct target is the **activation-indexed** collecting `trace_witness_act`
(`CFG_Collect_Activation.thy`):

- `intra` rule carries `\<not> is_enter_action a` --- the same-context edge obligation
  **excludes enters**;
- `enter` rule routes the context: the callee entry sits at `enterc c (last tau)`;
- `combine` resumes the caller context.

This matches the seed-routing executable solution exactly. Reuse path:

- **ENTER_MONO** --- `point_digest` locale (`Seed_EnterMono_Lift.thy`): interpret with
  `decode = (\<lambda>v. Ivl (Fin v) (Fin v))`, `is_point`, prove the one `point_exact`
  precision fact for intervals. Handles constant-argument (point) routing with
  `cmp = (=)`; the `is_point` premise is where non-constant arguments would (correctly)
  fail --- reviewer risk #4, resolved precisely, not weakened.
- **DG_INTRA / DG_RETURN / DG_CALLEE / activation witness** --- `Seeded_Activation_Sound`
  / `Activation_Witness_From` over `trace_witness_act`.
- **route = rt consistency (reviewer #2/#6)** --- `enterc` in the activation witness and
  the combine's routed read must be the same function; prove the equality lemma
  `callee_ctx_used_by_combine = callee_ctx_published_by_enter`.
- **Coverage (reviewer #3/#7)** --- prove the coverage property required by the
  collecting-soundness theorem itself, not only the contexts observed by `eval`. The
  exact phrasing is left open (generated equations / reachable unknowns / solved
  variables); do not prescribe a specific `(v,c) \<in> vars` shape up front.

### Remaining (ahead)

7b. **Lift the interval context hooks into the interval DG instance.** The hooks are
   currently example-local. The generic implementation **must not mention program
   variables at all** --- it depends only on the existing `context_domain` interface
   (or its generalized successor). The projection / point abstraction
   (`decode`/`is_point`/`proj_var`) is part of the `twice` example's context-selection
   configuration, not the generic instance. `twice` is merely one instantiation.
8. **Transport to `(v, c)`.** Generalize the `Exec_DG_Bridge` commute /
   `part_post_solution` transport from `(v, ())` to `(v, c)`; `unit` recovered by
   instantiating the context domain with `unit`.
9. **Soundness wiring.** Connect the solver post-solution to the activation-indexed
   collecting soundness (`trace_witness_act` + `Seeded_Activation_Sound`), reusing
   `point_digest` for ENTER_MONO. Context-keyed collecting endpoint on the interval
   instance.
10. **Context-sensitive `twice` flagship certificate.** The exact eval values are
    already established; attach the collecting-soundness certificate and lift through
    `compiled_source_simulation`.

### One-implementation discipline

Every generalization **replaces** the previous implementation. After each migration
step, delete obsolete monovariant-only definitions instead of keeping compatibility
layers, unless a layer is temporarily required to keep the build green (then remove it
once callers are migrated). The end state has one `dg_postfix`-family definition
parameterized by context, not `dg_postfix` / `dg_postfix_c` / `dg_postfix_poly`
siblings.

### ENTER_MONO discipline

Do not weaken or replace `ENTER_MONO`. Reuse the existing entry-store /
context-domain theory (`point_digest`). If the executable route needs a stronger
abstraction, **generalize the context interface** rather than introducing
interval-specific (or program-specific) assumptions.

### Ordering invariant

Finish one complete interval vertical slice --- generator, transport, post-solution,
activation-indexed collecting soundness, source lift --- before generalizing the
remaining instances (Sign, Mixed).

### Target architecture

```text
    semantic context collecting
            |
    activation-indexed collecting soundness   (trace_witness_act)
            |
    dg_collect_ctx_sound / context-keyed endpoint
            |
    dg_postfix_c   (context-parameterized post-fixpoint)
            |
    verified executable solver   (part_post_solution over (pp x c))
            |
    one generalized DG generator   (side_cfg_T_eff_cmp_seed_dg)
```

The unit-context analysis is obtained **solely** by instantiating the context domain
with `unit` --- no separate monovariant generator, bridge, or theorem family.

### Batch gate

Interactive (I/Q) green on every touched file is not completion. A full
`isabelle build Voblint_Formalization` is the gate and must be shown green before any
stage is called done.

---

## Phase 1 landed: generic executable bridge (batch-green, 2026-07-16)

`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy` now carries the transport at the
generic generator `side_cfg_T_eff_cmp_seed_dg` over unknowns `pp x 'c` with arbitrary
global-key type `'k`. There is **one** transport family; the monovariant bridge is
its `unit` specialization.

Delivered:

* `dg_tree_st_commute sigma t_st t_abs` --- the reusable per-tree transport contract
  (traverse + side-effect map + static dependencies commute through `fun_of_dg_st`).
  The opaque `cmb`/`extra` trees --- where a dynamic `Side` target computed inside a
  `QueryL`/`QueryG` continuation lives --- enter through this relation as bundled
  hypotheses; the bridge never assumes side targets are syntactically fixed.
* Generalized wrapped-edge / wrapped-combine commutation helpers (`gk`/`lk` instead
  of `unit`): off-key sides collapse to `bot` via `sides_map_gtree_off`.
* `seed_dg_list_commute`, `eq_seed_dg_commute`, `sides_seed_dg_commute`,
  `dep_seed_dg_eq` --- eq / side / dependency commutation for the generic generator,
  parameterized by `pred_sel`, `gkey`, context `'c`, `cmb`, `extra`.
* `part_post_solution_seed_dg_st_to_abs` --- the generic post-solution transport:
  a partial post-solution of the executable context-indexed system maps to one of the
  abstract system over the same unknown set. `Hstep` covers the intra edges; `Hcmb` /
  `Hextra` carry the routed combine and enter-seed trees.
* `part_post_solution_dg_st_to_abs` --- unchanged name/signature, now derived as the
  `unit`-context corollary (`gkey = lambda _. ()`, `extra = lambda _ _. []`,
  `pred_sel = predecessor_list`, `Hcmb` discharged by `dg_tree_st_commute_dg_cmb_of`).

The internal-only unit commute lemmas (`eq_dg_gen_of_commute`,
`sides_dg_gen_of_commute`, `dep_dg_gen_of_eq`) were removed --- the unit transport is
now a one-line corollary of the generic theorem, not a re-proof.

Trap hit and fixed: the context variable named `c` resolved to the imported constant
`state.c` (Dijkstra `c` clobbering), silently pinning the generic theorems to a single
context. Renamed to `ctx` throughout the generic lemmas.

`isabelle build Voblint_Formalization` green: the loop / monovariant IP flagships
(`Example_Interval_DG_Flagship`, `Example_Interval_DG_IP_Flagship`, `Exec_Sign_DG_Run`)
and the context flagship (`Example_Interval_DG_Ctx_Flagship`) all build unchanged.

The generic transport is exactly the endpoint the interval slice needs: applied to the
`twice` generator it leaves `Hcmb` (callee-exit read under the routed context) and
`Hextra` (enter-seed publication) as the open obligations --- these are the named
route-consistency lemma of Phase 3.

---

## Phase 3 landed: route consistency + abstract transport (batch-green, 2026-07-16)

`src/Formalization/Examples/Executable/Interval/Core/Example_Interval_DG_Ctx_Sound.thy`
discharges the two instance-specific obligations the Phase 1 bridge exposes for the
routed `twice` generator, and transports `twice_ctx_sol` to an abstract
context-indexed post-solution.

Single route-consistency core (not three independently unfolded routing expressions):

* `entered_commute`: `fun_of_st (entered_ivl s a) = entered_abs (fun_of_st s) a` --- the
  post-enter callee state commutes with the refinement morphism (`ivl_Hstep` read on
  the returned local component).
* `route_commute`: `route_abs (fun_of_st s) a = route_ivl s a` --- because both routes
  project the same variable and `fun_of_st = lookup_st`, the abstract and executable
  routes agree *as values*, so the `Side`/unknown keys they compute are literally
  equal. This is the one lemma that makes enter publication, the combine callee-exit
  lookup, and (through the activation backbone) the context selection coincide.

Discharged from that core:

* `dg_tree_st_commute_frame_read`, `dg_tree_st_commute_enter_pub`,
  `dg_tree_st_commute_cmb` --- per-tree transport for the frame-entry seed read, the
  routed enter publication, and the destination-aware combine. Generic over program
  point, caller context, and enter action (no `twice` call sites named).
* `hextra_commute` (list_all2 assembly) and `dg_tree_st_commute_cmb` are exactly the
  bundled `Hextra` / `Hcmb` hypotheses of `part_post_solution_seed_dg_st_to_abs`.
* `twice_ctx_pp_abs`: the abstract context-indexed post-solution
  `fun_of_dg_st o snd twice_ctx_sol` over the same unknown set, via the generic bridge
  with `Hstep = ivl_Hstep`.

No new bridge or routing API family: the abstract hooks `entered_abs` / `route_abs` /
`cmb_abs` / `extra_abs` are the plain `ivl abs_state` mirrors of the executable ones.

Traps hit and fixed (constant capture, same class as `state.c`): the valuation named
`sigma` was captured by a `TD_side` selector (renamed to `env`); several
`\<^const>` antiquotations were written on *fact* names (`ivl_Hstep`, `route_commute`,
`entered_commute`, `part_post_solution_seed_dg_st_to_abs`) and rejected as undefined
constants (changed to informal cartouches).

Remaining in the interval slice (Phase 2/4): instantiate `activation_collect_sound`
with `twice_ctx_pp_abs` and discharge EDGE / SEED_G / COMB and the coverage/entry
obligations, yielding the activation-indexed collecting-soundness certificate and the
source lift.

---

## Phase 4 in progress: ENTRY_G proven, PROC_ENTRY_G demonstrably false (2026-07-16)

`Example_Interval_DG_Ctx_Collect.thy` (WIP, NOT in ROOT) instantiates the generic
`activation_collect_sound` at the routed interval solution:

* `sg = ivl_ctx_sg`: `locals(sigma(Inl(v,c))) ⊔ globs(sigma(Inr(GlobAt c)))`;
* `enterc c s' = ivl_decode (s' ''p'')`, `combc = fst`, `seedc = bot`.

Reusable elimination landed (single unfold of `part_post_solution`, shared by
EDGE/SEED_G/COMB): `pp_eq_bound` (`eq ≤ sigma(Inl _)`) and `pp_sides_bound`
(`sides_of_rhs ≤ sigma`).

**ENTRY_G proven** (`side_acc_dg_ge` + entry accumulator ≥ s0d + `cinit ⊆ gamma(s0d)`).

**PROC_ENTRY_G is demonstrably false** for `twice_cfg` — concrete eval witnesses in the
theory (`proc_entry_edge_fires`, `proc_entry_callee_bot_p`):

* `cfg_entry twice_cfg = 4` is `main`'s entry, and `main`'s first statement is a call:
  `(4, EA_Enter [''p''] [N 3], 0) ∈ edges`. So the activation semantics' `proc_entry`
  rule fires, seeding the callee entry `0` at the **root** context `seedc = bot`.
* The polyvariant solver routes node `0` to `[3,3]` / `[10,10]` and leaves `(0, bot)`
  unpopulated: `locals(sigma(Inl(0,bot))) ''p'' = ⊥` (empty gamma).
* A concrete entered store (`p := 3`) lies in `edge_collect (EA_Enter ...) cinit_stores`
  but not in the empty `gamma(ivl_ctx_sg(Inl(0,bot)))`. Obligation false.

Root cause: `main`'s entry node coincides with the source of its first call edge. In the
**monovariant** IP flagship this is harmless — the single context `()` unifies the
`proc_entry` seed and the `enter` route, and `(0,())` is covered. In the **polyvariant**
setting the two disagree: `proc_entry` wants `(0, seedc=bot)`, `enter` wants
`(0, enterc bot s' = [3,3])`. `seedc` is forced to `bot` by ENTRY_G on `main`, so it
cannot also be the argument context.

Recommended fix (does NOT touch generator / route / context model / semantic endpoint):
prepend a `nop` (or any non-call statement) to `main` so `cfg_entry` is not itself the
source of an enter edge. Then `proc_entry`'s premise `(cfg_entry g, EA_Enter …, v) ∈
edges g` is unsatisfiable → PROC_ENTRY_G vacuous; the two calls fire only via the `enter`
rule and route correctly to `[3,3]` / `[10,10]`. Cost: recompile `twice_cfg` and re-eval
the flagship value lemmas (node renumbering) — mechanical, but it changes the flagship
example, so it is a user-facing decision. Awaiting direction before implementing.

---

## Phase 4: PROC_ENTRY_G root-vs-callee bug FIXED at the endpoint (batch-green, 2026-07-16)

The false PROC_ENTRY_G obligation was traced to a stale-context bug in the activation
collecting semantics, **not** a defect of the routed solver or the example. Fixed at the
endpoint (no CFG padding, `twice` unchanged):

Determination — `proc_entry` **must be routed, then is redundant with ENTRY_G + SEED_G**:

* The `proc_entry` *rule* (`CFG_Collect_Activation.thy`) is retained — it is the only
  rule producing a **callee-relative** trace `[s]` (head = entered store), which the
  `combine` rule requires (`enter`-rule traces carry the caller prefix, head != entered
  store).
* Its **context was a stale bug**: it seeded the callee at `seedc` when the routing
  discipline says `enterc seedc s`. Changed the rule's conclusion context
  `seedc` -> `enterc seedc s`, making it consistent with the `enter` rule.
* With the context routed, the `proc_entry` induction case in `activation_trace_sound`
  discharges from ENTRY_G + SEED_G (extract `s0 in S` with
  `edge_step (EA_Enter …) s0 = Some s`; ENTRY_G on `s0`; SEED_G to `enterc seedc s`).
  So **PROC_ENTRY_G was removed** as a separate obligation from `activation_trace_sound`,
  `activation_collect_sound`, `seeded_activation_collecting_sound`, and
  `seeded_activation_collecting_sound_cover`. The domain-instance aliases
  (`ivl_/sign_activation_collecting_sound_cover`) inherit the narrowed signature.

Invariant now holds: the root graph entry is seeded under `seedc`; every callee entry
reached by `EA_Enter` (including a call at `cfg_entry`) is seeded under
`enterc caller_ctx entered_store`; no callee is required under the root context merely
because the enter edge originates at `cfg_entry`. `(0, bot)` remains absent (regression
witness `callee_entry_bot_unpopulated` in the WIP theory).

Full `isabelle build Voblint_Formalization` green: the semantics + backbone change caused
**zero regressions** across the rebuilt Voblint_CFG -> Analysis -> Formalization chain.

Phase-4 status: ENTRY_G proven; the endpoint now exposes exactly EDGE / SEED_G / COMB
(the WIP theory `Example_Interval_DG_Ctx_Collect.thy`, not in ROOT, carries these three
`sorry`). Next: discharge EDGE (step_sound + intra pp bound), SEED_G (point_digest +
route consistency + seed publication), COMB (combine_sound + cmb pp bound), then the
source lift.
