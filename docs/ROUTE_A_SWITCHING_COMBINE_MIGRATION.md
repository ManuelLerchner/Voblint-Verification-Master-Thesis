# Route A: value-dependent (switching) combine soundness — Phase A1–A7

> **Status (2026-07-02):** A1–A6 done. **A5 done** — the contract *is* satisfiable
> for `abs_switching_combine`; the earlier "blocked" analysis was a misdiagnosis
> (see the A5 section). `abs_switching_combine_satisfies_switching_combine_sound`
> (`Exec_Cmp_Bridge.thy`) discharges it, batch-green on `Voblint_Analysis` /
> `Voblint_Formalization`. **A7 remaining, and rescoped (2026-07-02)** — *not* a
> compose. Eval refutes the roadmap's original plan: the single-context flat cover
> (`side_cfg_T_eff_cmp_collect_sound_eq`, which concludes about the flat
> `cfg_collect`) is **false for every context** on `fctx` — main runs at `GOther`,
> `f`'s body at `GZero`/`GPos`, so no single `ctx` covers all edge targets. That
> theorem is inapplicable, and its inapplicability is what keeps it sound (one
> context slot does not over-approximate the flat collecting at a callee point).
> The correct target is **per-context** collecting via `cfg_collect_ctx dg cmp g S v
> ctx` (`CFG_Collect_Trace.thy`); the flat thesis is recovered only by joining the
> finite `sign_gctx` slices. A7 therefore needs a new per-context kernel soundness
> theorem (A7.1) plus a `context_transfer` instance for the sign digest (A7.2), then
> the `fctx` instantiation (A7.3). See the A7 section for the sub-milestones.
>
> A1 (mismatch documented) and A2 (contract extracted + named + discharged for the
> certified fixed combine + concrete example obligations proved). A3 (abstract
> switching combine + `fun_of_st` bridge). A4 (kernel generalized to consume the
> contract): the `switching_combine_sound` contract lives in the kernel;
> `side_cfg_T_eff_cmp_collect_sound_gen` takes it as a hypothesis and
> `side_cfg_T_eff_cmp_collect_sound` is a corollary via
> `fixed_combine_satisfies_switching_combine_sound`, so all existing callers are
> unchanged.

> **Architecture cleanup landed (2026-07-02).** The Goblint-shaped `context_domain`
> locale is in the tree and the kernel routes callee reads through it
> (`CONTEXT_DOMAIN_ARCHITECTURE.md`), batch-green — a pure refactoring, no precision
> change.
>
> **Next route — corrected, then re-corrected (2026-07-02).** An earlier note picked
> the **D/G/C boundary** as primary (route `ctx_sel` over the local read
> `D_read sigma (cc,ctx) = sigma (Inl (cc,ctx))`, not the joined `side_env_cmp`), on
> the Goblint model that context reads a pre-publication flow-sensitive `D`. **The Fix
> A eval probe refutes this** (see the "Fix A refuted" section): in the `Inl`/`Inr`
> framework the retain transfer re-injects the flow-insensitive `Inr` slot at every
> non-writing edge, so `D_read` at a call node is polluted (`SNonNeg`) like
> `side_env_cmp`. **The intra-edge value-refined `cstep` route is re-promoted to
> primary; the D/G/C boundary is demoted.** The `fctx` `ENTER_MONO` obstruction is
> unconditional — it holds for the local read too. Next target: the hybrid `ctxupd`
> soundness kernel (`cstep` intra updates + call-time `ctx_sel`/`route`). See
> `OPEN_PROBLEMS.md` P11 and `CONTEXT_DOMAIN_ARCHITECTURE.md` §"Phase 4".

Preparatory slice for certifying the *precise* executable context-sensitive runs
(`fctx_eqs`, `kgen_eqs`) against the abstract soundness kernel. Companion to
`KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md` (which certified the *fixed*-combine keyed
generator) and the Path-B plan in `SEMANTIC_CONTEXT_MIGRATION.md`.

## A1 — The mismatch

The certified kernel `side_cfg_T_eff_cmp_collect_sound`
(`src/Analysis/Generic/Solver/TD_Side_Eff_Cmp_Gen.thy`) proves the collecting bound

```
cfg_collect g S v0 <= [| side_env_cmp gcmp sigma (v0, ctx) |]
```

**only** for the context-*fixed* combine

```
lambda c cc ex. map_gtree (lambda _. gkey c)
                  (map_ltree (lambda w. (w, c)) (etf_combine etf cc ex))
```

— the callee context equals the caller context (`gkey c`), locals reindex with the
same `c`. Its soundness proof requires `sigma` to be a post-fixpoint of *that* system
(the `pp` premise pattern-matches the fixed combine literally).

The precise executable witnesses use a value-**dependent** *switching* combine:

| witness | file | combine | key |
| --- | --- | --- | --- |
| `fctx_eqs` | `Example_Finite_Sign_Context_Analysis.thy` | `unit_combine_tree_cmp_ctx_st fctx_ec_call` | finite `sign_gctx` |
| `kgen_eqs` | `Exec_Sign_Cmp_Keyed_Gen_Run.thy` | `kgen_combine_st` | `sign st` (infinite) |

The switching combine `Side`s callee globals to a **different** slot
`callee_ctx = ec cc ctx caller` (call site 4 -> `GZero`, site 7 -> `GPos`) and reads
the return from `(ex, callee_ctx)`. A solution of the switching system is therefore
**not** a post-fixpoint of the fixed system: the fixed system's equation at
`(entry_f, GNonNeg)` demands a combine contribution the switching run deliberately
routed into `(entry_f, GZero)` / `(entry_f, GPos)`.

Consequence: `fctx_solution` / `kgen_solution` — even transported `st -> abs_state` —
cannot instantiate `fctx_keyed_sound_if_post_fixpoint` /
`kgen_keyed_generator_sound_if_post_fixpoint`. (`kgen` is additionally blocked: its
key `sign st` is not `finite`, which those theorems require.)

And the two are entangled: the fixed combine the kernel *does* certify is
precision-trivial (with `gkey = id` and no switching, every call inherits the
caller's single context, collapsing to monovariant). The runs worth certifying are
exactly the ones the kernel does not cover. That is the real Route-A gap.

## A2 — The contract

The combine enters `side_cfg_T_eff_cmp_collect_sound` at exactly **one** place — the
combine branch of the `post_fixpoint_sound_at_eff` obligation
(`TD_Side_Eff_Cmp_Gen.thy` ~L583–586):

```isabelle
fix c ex ret assume cm: "(c, ex, ret) : combines g"
show "etf_full (etf_combine etf c ex) (pull_gk gkey ctx sigma)
        <= side_env (pull_gk gkey ctx sigma) ret"
  by (rule side_cfg_T_eff_cmp_combine_le[OF pp cover_comb[OF cm] cm finC])
```

That inequality **is** the obligation any combine must supply. Named
`switching_combine_sound` (in `Example_Finite_Sign_Context_Analysis.thy`, to keep the
blast radius to one theory during A1/A2; migrates into the kernel session when A3
starts):

```isabelle
definition switching_combine_sound ::
  "('c => 'g::finite) => ('c => pp => pp => (pp * 'c, 'g, 'a abs_state) strategy_tree)
   => cfg => (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   => 'a abs_state => 'a abs_state => 'a abs_state => bool"
where
  "switching_combine_sound gkey cmb g etf fresh_frame bot0 s0 ==
     (ALL (sigma :: pp * 'c + 'g => 'a abs_state) x vars ctx cc ex ret.
        part_post_solution (side_cfg_T_eff_cmp gkey cmb g etf fresh_frame bot0 s0) x sigma vars
        --> (ret, ctx) : vars
        --> (cc, ex, ret) : combines g
        --> etf_full (etf_combine etf cc ex) (pull_gk gkey ctx sigma)
              <= side_env (pull_gk gkey ctx sigma) ret)"
```

The `etf_combine etf cc ex` on the left is the **semantic** combine (fixed by the
collecting semantics, independent of the generator combine `cmb`). `cmb` influences
only which `sigma` satisfies the `part_post_solution` premise. So the contract reads:
"whatever generator combine produced `sigma`, the read at `(ret, ctx)` still
over-approximates the semantic combine's effect." For the fixed combine this holds
because its tree literally embeds `etf_combine etf cc ex` at slot `(ret, ctx)`. For a
switching combine it holds only if the return path re-imports the switched slot back
into `(ret, ctx)` — which is exactly what A3 must prove.

### Contract is well-shaped: the certified fixed combine satisfies it

```isabelle
lemma fixed_combine_satisfies_switching_combine_sound:
  assumes "finite (combines g)"
  shows "switching_combine_sound gkey
           (lambda c cc ex. map_gtree (lambda _. gkey c)
              (map_ltree (lambda w. (w, c)) (etf_combine etf cc ex)))
           g etf fresh_frame bot0 s0"
  unfolding switching_combine_sound_def
  using side_cfg_T_eff_cmp_combine_le[OF _ _ _ assms] by blast
```

Proven (`by blast` off the existing kernel lemma). This confirms the contract shape
is the one the generalized theorem will consume, and that it is non-vacuous.

### Concrete example obligations discharged (`fctx`)

Task-3 evidence that the switching route *does* satisfy the contract's intent on the
precise finite run — machine-checked, no `sorry`:

**Routing** (solver-state-independent — `fctx_call_state` overwrites `G` before the
call):

```isabelle
lemma fctx_route_call4: "fctx_ec_call 4 ctx (fctx_call_state 4 s) = GZero"   (* by simp *)
lemma fctx_route_call7: "fctx_ec_call 7 ctx (fctx_call_state 7 s) = GPos"    (* by simp *)
```

**Side contribution bounded by the routed keyed slot** (the surviving global `G` the
combine emits lands within the destination slot of the generated solution):

```isabelle
lemma fctx_route_bound_zero: "SZero <= lookup_st (snd fctx_solution (Inr GZero)) ''G''"  (* by eval *)
lemma fctx_route_bound_pos:  "SPos  <= lookup_st (snd fctx_solution (Inr GPos)) ''G''"   (* by eval *)
```

Together: each call site routes to the correct finite context, and the routed side
contribution is bounded by that context's keyed slot. This is the concrete
instantiation of the contract's obligation for the two combines of `fctx_prog`.

## A3 — The abstract switching combine

Landed in `src/Analysis/Generic/Solver/Exec_Cmp_Bridge.thy` (Analysis session,
downstream of the kernel — the correct layer for A5/A7 to build on). Four items:

**The abstract object** the contract quantifies over — a genuine `abs_state` tree,
keyed globals (`gkey = id`, so `'g = 'c`), honest abstract `prep`/`ec` (no
`st_of_abs` executable-inverse hack, so it is sound for arbitrary abstract `sigma`):

```isabelle
definition abs_switching_combine ::
  "(pp => 'a abs_state => 'a abs_state) => (pp => 'c => 'a abs_state => 'c)
   => pp => pp => 'c
   => (pp * 'c, 'c, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
where
  "abs_switching_combine prep ec cc ex ctx =
     QueryL (cc, ctx) (%sc. QueryG ctx (%g.
       let caller = prep cc (sc | g); callee_ctx = ec cc ctx caller in
       Side callee_ctx (restrict_global caller)
         (QueryL (ex, callee_ctx) (%se.
           let res = restrict_local caller | restrict_global se in
           Side callee_ctx (restrict_global res)
             (Answer (restrict_local res))))))"
```

**The executable sibling** `switching_combine_st` (same shape over `'a st`), which
`unit_combine_tree_cmp_ctx_st fctx_ec_call` is the `prep = fctx_call_state`
instance of. Chosen shape = the **fctx** combine (return `Side` targets
`callee_ctx`); the `kgen` combine differs (return `Side` targets caller `ctx`,
re-joins `g`) and stays a demonstrator per blocker 4.

**`side_rg`**: `side_rg_switching_combine_st` — every `Side` value is
`restrict_global_st`-shaped (`by simp`).

**The `fun_of_st` bridge** (the "relates to it by `fun_of_st`" exit), under the two
per-instance commutation hypotheses `fun_of_st (prep_st cc s) = prep_abs cc
(fun_of_st s)` and `ec_st cc ctx s = ec_abs cc ctx (fun_of_st s)`:

```isabelle
lemma traverse_switching_combine_st_fun_of_st: ...
  "fun_of_st (traverse_rhs (switching_combine_st prep_st ec_st cc ex ctx) sigma_st)
   = traverse_rhs (abs_switching_combine prep_abs ec_abs cc ex ctx)
       (%k. fun_of_st (sigma_st k))"
lemma sides_switching_combine_st_fun_of_st: ...   (* same, for sides_of_rhs *)
```

The commutation hypotheses are exactly the sign-instance obligations A6 discharges;
`dep_aux` bridge is deferred to A6 (post-solution transport) where it is consumed.

## A4 — The kernel consumes the contract

Landed in `src/Analysis/Generic/Solver/TD_Side_Eff_Cmp_Gen.thy`. The contract def
`switching_combine_sound` and `fixed_combine_satisfies_switching_combine_sound`
**migrated out of the example into the kernel** (blast radius was scoped to the
example only during A1/A2). The generalization is mechanical because the three
branch lemmas (`side_cfg_T_eff_cmp_edge_le`, `_enter_le`,
`s0_le_side_env_cmp_entry`) were *already* generic over the combine builder `cmb` —
only the top theorem hardcoded the fixed combine.

- `side_cfg_T_eff_cmp_collect_sound_gen` — the generalized theorem: takes
  `comb_sound: switching_combine_sound gkey cmb g etf fresh_frame bot0 s0` as a
  hypothesis and a `pp` premise over the generic `cmb`; the combine branch (was
  `by (rule side_cfg_T_eff_cmp_combine_le ...)`) now reads
  `using comb_sound ... unfolding switching_combine_sound_def by blast`. Every
  other branch replays verbatim.
- `side_cfg_T_eff_cmp_collect_sound` — kept as a **corollary** with the *identical
  original statement* (hardcoded fixed combine), proved from `_gen` by discharging
  `comb_sound` via `fixed_combine_satisfies_switching_combine_sound[OF finC]`. So
  its only consumer, the `..._eq` corollary, and all external callers
  (`Exec_Sign_Cmp_Keyed_Gen_Run`, the example) are untouched.

Proof note: the corollary is a structured `proof (rule ..._gen) show ... qed`, not
`[OF ...]` — the fixed combine `\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) ...` is
higher-order-ambiguous as an `OF` argument (the inner `gkey` can be abstracted or
literal → "OF: multiple unifiers"). Goal-directed `rule` picks a unifier and
sidesteps it.

## A6 — `st -> abs_state` post-solution transport (done)

Landed in `src/Analysis/Generic/Solver/Exec_Cmp_Bridge.thy`, batch-green. The
executable keyed generator `side_cfg_T_eff_cmp_st` maps, under `fun_of_st`, to a
post-solution of its abstract image `side_cfg_T_eff_cmp`. Mirrors the ctx-bridge
transport (`part_post_solution_ctx_seeded_st_to_abs_eff`) but over keyed globals
(the `map_gtree (\<lambda>_. gkey c)` intra wrapper).

- Generic `map_gtree` companions of the `map_ltree` transport helpers:
  `sides_map_gtree_unit_gen`, `sides_map_gtree_off_gen`, `dep_aux_map_gtree`,
  `traverse_/dep_map_gtree_st_fun_of_st`. Traverse and dep are clean `map_sum`
  pullbacks; sides needs the constant-relabel unit lemmas.
- A `context` parametric in the edge transfers (three edge bridges) and the combine
  builders `cmb_st`/`cmb_abs` (three combine bridges) derives the keyed-intra
  bridges, the fold bridges (reusing the imported `side_rhs_fold_ctx_st_*`), and the
  `eq`/`sides`/`dep` bridges for `side_cfg_T_eff_cmp_st`, then
  `part_post_solution_cmp_st_to_abs_eff` — the standard three-obligation replay.
- `part_post_solution_cmp_switching_st_to_abs_eff_unit_transfer` — the switching
  instance: unit-transfer edge + honest abstract `prep`/`ec`; combine bridges are
  A3's `traverse_/sides_/dep_switching_combine_st_fun_of_st` (the `dep` one was the
  A3-deferred bridge, added here). `gkey :: 'c \<Rightarrow> 'c` (the switching combine's
  globals are contexts, so `'g = 'c`).

Proof notes: the entry `Side (gkey c) (restrict_global s0)` wrapper leaves a
`fun_of_st \<bottom> = (\<lambda>_. \<bottom>)` residue from the `fresh_frame` branch — fold it with
`bot_fun_def[symmetric]`. The combine-bridge `have`s use `using prep ec by (rule
..._fun_of_st)` (goal-first), not `[OF prep ec]` — the `prep`/`ec` premises are
higher-order-ambiguous as `OF` arguments (same trap as A4).

## A5 — done: the contract holds for `abs_switching_combine`

> **Resolved 2026-07-02.** `ROUTE_A5_HANDOFF.md` §0 has the full correction. Proof:
> `abs_switching_combine_satisfies_switching_combine_sound` +
> `abs_switching_combine_le` in `Exec_Cmp_Bridge.thy`.

`switching_combine_sound gkey (\<lambda>c cc ex. abs_switching_combine prep ec cc ex c) ...`
is discharged under three per-instance hypotheses — the semantic combine is
`unit_combine_tree` (the sign/mixed unit-global shape), `prep` preserves locals
(`restrict_local s \<le> restrict_local (prep cc s)`; `fctx_call_state` overwrites only
globals), and `gkey = id`. The contract definition additionally now carries the
`inl_slot_globals_bot_ctx \<sigma>` invariant the kernel already supplies; the final
collecting-soundness conclusion is unchanged.

**Why the "blocked" argument below was wrong.** It claimed `etf_full (etf_combine
etf cc ex) (pull_gk gkey ctx \<sigma>)` contains a callee-written global `G` while the
contract's RHS does not. It does not: `unit_combine_tree` reads the callee exit only
through `restrict_global se` with `se = \<sigma>(Inl (ex, ctx))` a *local* slot, whose
globals `inl_slot_globals_bot` forces to `\<bottom>`; and `G` lives at `\<sigma>(Inr
callee_ctx)`, which `pull_gk gkey ctx` never reads. So the callee-context switch is
*invisible* to the contract read, not an obstruction to it. The original analysis
conflated "`G` written somewhere in `\<sigma>`" with "`G` appears in `etf_full` against the
switching `\<sigma>`".

*The original (refuted) obstruction argument, retained as the record of what it
missed:*

`switching_combine_sound gkey abs_switching_combine ...` **cannot be discharged** for
the A3 object as defined. Confirmed at the contract level, not just suspected:

The contract's right side is `side_env (pull_gk gkey ctx \<sigma>) ret`, which — because
`pull_gk` collapses the keyed environment to the *single* slot `gkey ctx` —
equals `\<sigma>(Inl (ret, ctx)) \<squnion> \<sigma>(Inr (gkey ctx))`. So the only global slot the
contract sees is `gkey ctx` (`= ctx` at `gkey = id`).

But `abs_switching_combine` sides the callee's returned globals (`restrict_global
res`) to slot **`callee_ctx = ec cc ctx caller`**, and keeps only `restrict_local
caller` in its `Answer`. Neither the local answer at `(ret, ctx)` nor the global
slot at `ctx` ever receives the callee globals — they land at `callee_ctx \<noteq> ctx`.

Concrete counterexample shape: a global `G` written only inside the callee. Then
`etf_full (etf_combine etf cc ex) env` (semantic combine, LHS) contains `G`'s value,
but both `\<sigma>(Inl (ret, ctx))` and `\<sigma>(Inr ctx)` are unconstrained by it — the
switching equation routed `G` to `\<sigma>(Inr callee_ctx)`. LHS can exceed RHS. This is
exactly the A1 mismatch, now confirmed to survive at the contract level.

### The obstruction is the callee-exit *context*, not just the global routing

The concrete semantic combine is `unit_combine_tree cc ex`
(`TD_Side_CFG.thy`):

```
unit_combine_tree cc ex =
  QueryL cc (\<lambda>sc. QueryL ex (\<lambda>se. QueryG () (\<lambda>g.
    let res = restrict_local (sc \<squnion> g) \<squnion> restrict_global (se \<squnion> g) in
    Side () (restrict_global res) (Answer (restrict_local res)))))
```

Read against `pull_gk gkey ctx \<sigma>`, it reads the callee exit `se = \<sigma>(Inl (ex, ctx))`
— **at the caller context `ctx`** — and `etf_full` of it is
`restrict_local (\<sigma>(Inl (cc,ctx)) \<squnion> \<sigma>(Inr ctx)) \<squnion> restrict_global (\<sigma>(Inl (ex,ctx)) \<squnion> \<sigma>(Inr ctx))`.

`abs_switching_combine` reads the callee exit `se = \<sigma>(Inl (ex, callee_ctx))` — **at
the callee context `callee_ctx`**. That is the entire precision gain of the
switching combine. But it means the two combines read the callee-exit slot at
*different contexts*. A return-path re-import into the caller's slots
(`\<sigma>(Inl (ret,ctx))`, `\<sigma>(Inr ctx)`) writes the value read at `callee_ctx`; the
contract needs the value read at `ctx`. They coincide only when
`callee_ctx = ctx` — the monovariant collapse.

So the re-import is necessary but **not sufficient**: it repairs where the callee
globals are written, not the context they are read from. The mismatch lives in the
certified collecting-soundness statement, whose contract pins the callee exit to
`ctx` via `pull_gk`.

### Ways forward

1. **Re-target the collecting contract to `callee_ctx`.** Change
   `switching_combine_sound` (and the kernel proof consuming it) so the callee exit
   is read at the callee context. This re-opens the certified collecting-soundness
   theorem (A4 / the `*_edge_le`, `*_enter_le` kernel lemmas all read via
   `pull_gk … ctx`) and must re-establish that `cfg_collect`, which is context-
   uniform, is still over-approximated when the callee is read at a *different*
   context. Large, and its truth is not obvious (it is the actual content of
   context-sensitive soundness).
2. **Path-B warrowing** (`SEMANTIC_CONTEXT_MIGRATION.md` S1/S2) — the roadmap's
   designated route for value-dependent context selection. The recommended path:
   the join back-end genuinely does not model reading the callee at its own context.

The earlier "re-import redesign" framing (add one `Side (gkey ctx)`) addresses only
the global-write routing and does **not** close A5 on its own; it is retained above
as a prerequisite, not a solution.

## Paper alignment (Seidl 2026, equation 6)

This slice is the first concrete landing of **Slice 4** of
`SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` ("paper equation (6) for
context-sensitive calls"). Seidl 2026's context-sensitive call transfer is

```text
[[e, c]] d eta =
  let c'    = context_u,f,args d c
      sigma = {[start_f, c'] -> enter_f,args d}
      d'    = combine_f d (eta[ret_f, c'])
  in (sigma, d')
```

Correspondence to the artifacts here:

| Paper (eq. 6) | Repo |
| --- | --- |
| `context_u,f,args d c` | `fctx_ec_call` / `kgen_ec` (value-dependent context selector) |
| `Side [start_f, c']` | switching combine's `Side callee_ctx (restrict_global caller)` |
| read `eta[ret_f, c']` | `QueryL (ex, callee_ctx)` in the switching combine |
| `context d c = c` (context-preserving) | the certified **fixed** combine |
| `context _ _ = u` (1-callstring), `context d _ = enter d` (tabulation) | the **switching** combine (Route A target) |

So `switching_combine_sound` is the theorem-facing **soundness obligation of the
combine in equation (6)**, and `fixed_combine_satisfies_switching_combine_sound` is
the degenerate `context d c = c` instance. A3 = discharge equation (6)'s combine for
the value-dependent `context`, i.e. the general Slice-4 obligation ("call edges route
start and return through the same `c'`"). The `paper_context_call` locale sketched in
Slice 4 is the natural home for the generalized contract; `switching_combine_sound`
is its combine assumption.

## Which kernel lemma consumes the contract next

`side_cfg_T_eff_cmp_collect_sound` (`TD_Side_Eff_Cmp_Gen.thy` L542). A3 replaces the
combine branch (L583–586) — currently `by (rule side_cfg_T_eff_cmp_combine_le ...)`
— with a use of a `switching_combine_sound gkey cmb g etf fresh_frame bot0 s0`
hypothesis specialized to the outer `sigma x vars ctx`. Everything else in the proof
(the enter/non-enter edge split, the entry seed, `side_env_pull_gk_eq_cmp`) is
combine-agnostic and replays verbatim. The fixed-combine corollary
`side_cfg_T_eff_cmp_collect_sound_eq` then discharges the new hypothesis via
`fixed_combine_satisfies_switching_combine_sound`, so all current callers keep
working unchanged.

## Remaining blockers for full Route A

1. **No abstract switching combine.** `unit_combine_tree_cmp_ctx_st` /
   `kgen_combine_st` exist only over `'a st`. To *state* `switching_combine_sound`
   for the precise runs one needs an `abs_state` version of the switching combine
   (mirroring the `_st` -> abstract relationship the fixed combine already has).
2. **Discharging the contract for the switching combine (the real proof).** Requires
   the return-path argument: the switched slot `(ex, callee_ctx)` is re-imported into
   `(ret, ctx)` so the `(ret, ctx)` read still dominates `etf_combine etf cc ex`.
   This is where `mono_sides` breaks (semantic routing is value-dependent) — the
   monotone back-end may still be sound here (soundness != optimality), but the
   argument is genuinely new, not a replay of `side_cfg_T_eff_cmp_combine_le`.
3. **`st -> abs_state` post-solution transport.** To certify the *executable*
   `fctx_solution` (not merely an abstract post-fixpoint), a lemma transporting a
   `part_post_solution` of the `_st` system to one of its `fun_of_st`-image abstract
   system is still needed. Orthogonal to (2); reusable under either route.
4. **`kgen` infinite key.** `kgen`'s `sign st` key is not `finite`; the generic keyed
   read theorem requires `'ctx::finite`. `kgen` stays a demonstrator; the certifiable
   precise run is the finite-context `fctx`.

## Route A roadmap (phases)

A1/A2 done. Remaining phases, with dependencies and exit criteria. Framed as the
body of SEIDL Slice 4 (equation 6) — the `paper_context_call` locale is the intended
home for A4/A5.

```
A1 done ─▶ A2 done ─▶ A3 done ─┬─▶ A5 done ─┐
                    A4 done ───┘             ├─▶ A7.1 done ─▶ A7.2 done ─▶ A7.3 blocked ─▶ A7.4 (cc-aware ec)
                    A6 done ──────────────────┘
```

**A7.3 blocked (2026-07-02).** The A7.1 kernel cannot cover `fctx` at its call sites.
Both calls (`cc = 4`, `cc = 7`) live in the *same* caller context `GOther`, whose shared
global slot joins the two activations, so the read of `G` at either call site is
`SNonNeg = SZero ⊔ SPos` (eval: `fctx_caller_read_G_imprecise`). The kernel's `ENTER_MONO`
demands one routed context `ec ctx read` that `(=)`-matches the enter digest of every
store in `γ(read)`; but `γ(SNonNeg)` contains `G = 0` (digest `GZero`) and `G = 1`
(digest `GPos`), so no value works. The site distinction fctx encodes via `fctx_call_state`
(pins `G` before routing, keyed on `cc`) is invisible to the kernel's `ec :: 'c ⇒ 'a
abs_state ⇒ 'c` (no `cc`, raw read). → A7.4.

| Phase | Goal | Depends | Size | Exit criterion |
| --- | --- | --- | --- | --- |
| **A3 (done)** | Abstract switching combine: an `abs_state` mirror of `unit_combine_tree_cmp_ctx_st` (currently `_st`-only), so `switching_combine_sound` can be *stated* for the precise runs. | A2 | S–M | ✅ `abs_switching_combine` defined; `side_rg_switching_combine_st` proven; `traverse_`/`sides_switching_combine_st_fun_of_st` relate the `_st` version by `fun_of_st`. In `Exec_Cmp_Bridge.thy`. |
| **A4 (done)** | Generalize the kernel: `side_cfg_T_eff_cmp_collect_sound` takes `switching_combine_sound` as a hypothesis in place of the hardcoded fixed combine. Re-derive the original theorem as a corollary via `fixed_combine_satisfies_switching_combine_sound` so all current callers are unaffected. | A2 | M | ✅ `side_cfg_T_eff_cmp_collect_sound_gen` (hypothesis form) + `side_cfg_T_eff_cmp_collect_sound` (corollary, identical statement); contract migrated into the kernel; example duplicate removed. In `TD_Side_Eff_Cmp_Gen.thy`. |
| **A5 (done)** | Discharge the contract for the switching combine. No re-import needed: the semantic combine reads the callee exit only through `restrict_global` of a local slot (⊥ by `inl_slot_globals_bot`), and the callee globals at `callee_ctx` are unread by `pull_gk gkey ctx`, so the callee-context switch is invisible to the contract read. | A3, A4 | S–M | ✅ `abs_switching_combine_satisfies_switching_combine_sound` + `abs_switching_combine_le` (`Exec_Cmp_Bridge.thy`); contract carries `inl_slot_globals_bot_ctx` (kernel-supplied), conclusion unchanged. Batch-green. |
| **A6 (done)** | `st -> abs_state` post-solution transport: a `part_post_solution` of the `_st` system maps to one of its `fun_of_st`-image abstract system. Reusable, orthogonal to A5. | A2 | M | ✅ `part_post_solution_cmp_st_to_abs_eff` (generic) + `part_post_solution_cmp_switching_st_to_abs_eff_unit_transfer` (switching instance). In `Exec_Cmp_Bridge.thy`, batch-green. |
| **A7.1 (done)** | Per-context kernel soundness: lift the keyed semantic soundness from the trace level to the context-sliced collecting set `cfg_collect_ctx dg cmp g S v ctx` (`CFG_Collect_Trace.thy`), read through `side_env_cmp gcmp`. The hard content pre-existed in `TD_Side_Eff_Cmp_Sound.thy` (the keyed trace backbone `post_fixpoint_sound_at_ctx_semantic_cmp_final`: trace-witness induction, value-dependent combine soundness via `combine_states_sound`, local/global split `combine_read_cmp_le`); A7.1 added the `cfg_collect_ctx` wrapper. Generic — no `fctx`, no sign digest. | A4 | S | ✅ `side_cfg_T_eff_cmp_collect_ctx_sound_semantic` in `TD_Side_Eff_Cmp_Sound.thy`, no `sorry`, batch-green on `Voblint_Formalization`. Obligations named (seed `ENTRY`/`PROC_ENTRY`; step `EDGE`; comb `LOCAL_POST`+`CMP_SOUND`; digest `DG_INTRA`/`DG_RETURN`/`DG_CALLEE`/`ENTER_MONO`); A7.2-instantiable. |
| **A7.2 (partial)** | Digest-propagation primitives for the sign context. **Landed:** `head_digest` (a digest reading only the current activation's head store) discharges `DG_INTRA`/`DG_RETURN`/`DG_CALLEE` generically (head stable under intra append + return concat; `enter_state` preserves globals ⟹ `entdg = f ∘ enter_state`) — program- and domain-independent, in `TD_Side_Eff_Cmp_Sound.thy`, batch-green. **Deferred to A7.3:** the sign-`G` `digest_of` and the value-dependent `ENTER_MONO`, which is *not* generic with `cmp = (=)` — it needs context exactness (`read`'s `G` precise, not `STop`), a precision side-condition `fctx` supplies via `fctx_call_state` (pins `G` before routing). | A7.1 | M | ✅ `head_digest` + `head_digest_DG_INTRA`/`_DG_RETURN`/`_DG_CALLEE`. ENTER_MONO reclassified → A7.3. |
| **A7.3 (blocked)** | Instantiate A7.1 for `fctx_solution`. **Step-1 eval (`derived-context invariant`) refuted it:** both call sites share caller context `GOther` with `G = SNonNeg`, so `ENTER_MONO` cannot hold with `cmp = (=)` (see the blocked note above). `CMP_SOUND` is fixable by a cc-aware `ec`, but `ENTER_MONO` reads the polluted caller abstraction *upstream* of `ec`. | A7.1, A7.2 | M | ❌ Counterexample recorded: `fctx_caller_read_G_imprecise` + `sign_zero_pos_join` (`Example_Finite_Sign_Context_Analysis.thy`, eval, green). |
| **A7.4** | Refine the **caller** context so the read of `G` at the call site is exact (the ENTER_MONO blocker is the imprecise caller read, *upstream* of `ec` — a cc-aware `ec` alone was ruled out because it only fixes the return read). **Root cause (eval):** `G` is a global, so its value lives only in the flow-insensitive per-context global slot `Inr GOther = SNonNeg` (local slot `SBot`); the single main context joins both `G:=0` and `G:=1` phases. **Option B (restructure into per-phase procedures `h0`/`h1`) verified DEAD:** eval of the restructured program routes `f` to contexts `{GZero, GNonNeg}`, not `{GZero, GPos}` — main's flow-insensitive global slot joins the two callee returns and Sides the polluted `SNonNeg` back down into `h1` at entry, so the pollution relocates but persists. The entry procedure unavoidably joins all global phases and propagates the join into every callee. Remaining routes: **A** = value-refined generator (context updates on intra edges = current global sign) — faithful, keeps `cmp=(=)`, but a new context model touching `side_cfg_T_eff_cmp_st` + digest + A6; **C** = pivot to the proven Stack B `semantic_entry_store_ctx_analysis_sound` (entry-store context, `cmp=⊆`, unit globals) — sound today, drops the keyed `cmp=(=)` design. | A7.3 | A: L / C: S | Chosen route batch-green; `fctx`-class witness sound end-to-end. |

Sequencing note: A4 and A6 were independent of A5 and landed first. A5 turned out
to be a proof, not a redesign — the join back-end *does* support it, because the
contract read never consults the switched callee context. **A7 is *not* the compose
the roadmap first assumed.** The predicted cross-context global-flow gap is real: by
`eval` on `fctx_solution`, the single-context flat cover (`(w, ctx) \<in> vars` for a
fixed `ctx`, over all edges) is **`False` for every `ctx \<in> {GZero, GPos, GNonNeg,
GOther}`**, so `side_cfg_T_eff_cmp_collect_sound_eq` — which concludes about the flat
`cfg_collect` — cannot be instantiated for the multi-context `fctx`. The *some*-context
cover (`\<exists>ctx. (w, ctx) \<in> vars`, over edges / combines / entry) is `True`, so the
per-context target is the honest one. A7 splits into A7.1 (per-context kernel theorem
over `cfg_collect_ctx`), A7.2 (sign `context_transfer` instance), A7.3 (`fctx`
instantiation + finite-slice join). The Path-B warrowing route
(`SEMANTIC_CONTEXT_MIGRATION.md`) remains unneeded.

## Corrected next route (2026-07-02): the D/G/C boundary

> **Superseded by the Fix A eval probe (2026-07-02, see the "Fix A refuted" section
> below).** The D/G/C boundary route proposed here — route `ctx_sel` over the local
> read `D_read sigma (cc,ctx) = sigma (Inl (cc,ctx))` — is **refuted by eval**. In
> this `Inl`/`Inr` framework the local slot is *not* a pre-publication flow-sensitive
> `D`: the retain edge transfer re-injects the joined flow-insensitive `Inr` slot at
> every non-writing edge, so `D_read` at a call node is polluted (`SNonNeg`) exactly
> like `side_env_cmp`. **The intra-edge `step_ctx` / value-refined (`cstep`) route is
> re-promoted to primary; the D/G/C boundary is demoted.** The prose below is kept as
> historical rationale.

The upstream-Goblint correction (`ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md`) changes
which route is primary. Goblint does **not** update contexts on ordinary CFG edges —
`Spec.context` reads the flow-sensitive local `D.t` state, and C-globals may stay in
`D` flow-sensitively at a call until `sync`/`sideg` publishes them to the separate
`G.t` side store. So context selection consumes *pre-publication `D`*, never the
joined global slot.

**~~Primary next route~~ — D/G/C boundary (refuted, see "Fix A refuted" below).**
State `ctx_sel` over the local read
`D_read sigma (cc,ctx) = sigma (Inl (cc,ctx))`, not the joined
`side_env_cmp gcmp sigma (cl, ctx)`. Concretely this restates the kernel's
`ENTER_MONO` / `CMP_SOUND` obligations over `D_read` (design study §7-§8):

```text
s in gamma (enter_d cc (D_read sigma (cc,ctx)))
  ==> cmp (entdg s) (ctx_sel cc ctx (enter_d cc (D_read sigma (cc,ctx))))
```

The current `context_domain` locale is forward-compatible: its field
`ctx_sel :: pp => 'c => 'a abs_state => 'c` is already the design study's recommended
shape; only what the kernel *feeds* it changes (plus future `publish`/`read_global`
fields for the publication discipline). This is new soundness content, so it is the
next research milestone — **out of scope** for the architecture cleanup that just
landed.

**~~Demoted to fallback~~ — re-promoted to primary: intra-edge `step_ctx` /
value-refined (`cstep`) context.** The Fix A probe (below) shows this is not merely
an "explicitly-different experiment" — in the `Inl`/`Inr` framework it is the only
route that makes the observation exact, because the flow-insensitive `Inr` slot is
the pollution source and only context refinement makes each `Inr` slot hold a single
write. See `OPEN_PROBLEMS.md` P11 (prototype `side_cfg_T_eff_cmp_ctxupd_st`,
eval-backed).

### Fix A refuted (2026-07-02) — the local read is polluted too

The D/G/C boundary route above assumed a *pre-publication flow-sensitive `D`* whose
local read is exact at a call. **This framework does not provide one.** Eval on the
real side solver (monovariant unit-context retain generator, REPL-local, no theory
or kernel changed):

- Retain local slots are exact only *immediately after* the write (`SZero` after
  `G:=0`, `SPos` after `G:=1`).
- The next `EA_Nop` re-injects the joined `Inr` global slot — confirmed directly:
  retain's `EA_Nop` transfer with `local = SZero`, `Inr () = SPos` outputs
  `SNonNeg`. Re-joining `Inr` every edge is what makes retain *sound*, so it cannot
  be removed. The call node sits one `EA_Nop` past the assignment, so
  `D_read`/`route_read_cmp` there is `SNonNeg` — polluted like `side_env_cmp`.
- **Flat** (`main: G:=0; f(); G:=1; f()`): call nodes 4/7 read local `G = SNonNeg`.
- **Nested** (`main -> f -> g`, `main:G:=0;f()`, `f:G:=1;g()`, `g:GH:=G`): call node
  7 (main->f, expected `SZero`) and call node 4 (f->g, expected `SPos`) both read
  `SNonNeg`.

So the `fctx` `ENTER_MONO` failure is **not** conditional on the joined read: it
holds for the local `D_read` too. Goblint's `D`-holds-globals-until-`sync`
flow-sensitivity is not modelled by the current `Inl`/`Inr` split, where retain
publishes-into-and-reads-back `Inr` at every edge. **Therefore Fix B / `cstep` is
required.**

**Next research target — the hybrid soundness kernel for `ctxupd`.** Intra-activation
context updates via `cstep` combined with call-time routing via `ctx_sel` / `route`
(neither existing kernel does both — the generic kernel routes calls but forbids
intra context change via `DG_INTRA`; `context_transfer` threads intra context but
resets callees to `seed_ctx`). Kernel design only; not yet implemented.

## Acceptance (this slice)

- `Example_Finite_Sign_Context_Analysis.thy`: I/Q file diagnostics 0 errors / 0
  warnings, no `sorry`; ASCII gate clean.
- Kernel untouched (`side_cfg_T_eff_cmp_collect_sound` unchanged, per the A1/A2 remit).
- Batch: `isabelle build ... Voblint_Formalization`.

## See also

- `CONTEXT_DOMAIN_ARCHITECTURE.md` — the landed Goblint-shaped `context_domain`
  locale: interface, old-vs-new architecture, locale dependency graph, Goblint `Spec`
  mapping, and the Phase 4 validation (mechanical vs semantic vs real-research
  changes). The kernel now routes callee reads through `route = ctx_sel o prep`.

- `ROUTE_A7_DECISION_A_vs_C.md` — the A (value-refined keyed) vs C (proven semantic
  entry-store) decision note; A7 is paused pending a thesis-goal call between them.

- `ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` — design review of a Goblint-style
  `context_domain` locale. Verdict: adopt the interface (fixes the kernel/generator
  contract mismatch, unifies keyed and Stack B routes), but it does not unblock Route A
  — the obstruction is the flow-insensitive global slot, not the context interface.

- `KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md` — the certified fixed-combine keyed
  generator (framed enter) this builds on.
- `SEMANTIC_CONTEXT_MIGRATION.md` — S1/S2 Path-B warrowing route for value-dependent
  entry-state contexts (the general form of blocker 2).
- `GLOBAL_CONTEXT_REDESIGN.md` — the fresh-frame / keyed-slot design.
- `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` — Slice 4 (paper equation 6); this
  slice is its first concrete landing.
