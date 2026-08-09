# DG threefold-monotonicity: Step 3 handoff

Status: Steps 1–6 landed and batch-verified. Issue #45 is closed. This
document records the completed investigation and its restart point for any
follow-up work — see `docs/CALLSTRING_PRECISION_INVESTIGATION.md` section
9.6 for the full investigation history.

**Primary source, confirmed against the PDF directly (not secondhand):**
Tilscher, Graß, Seidl, *"Verifying a Solver for Mixed Flow-Sensitive
Analyses"* — this is the paper `vendor/td-verification/TD_side.thy`
implements. Definition 7 (Threefold Monotonicity, p.16) is exactly
`is_mono_eq`/`mono_sides`/`mono_deps`/`threefold_mono`. Definition 8
(Inconsistent Evaluation, p.16-17) and the proposed `abort` mechanism are
exactly `TD_side_opt`'s `abort` flag. **Theorem 2 (Optimality, p.17)
states, verbatim: "Let the considered equation system T be threefold
monotonic. If a call `solve x` of `TD^abort_side` (without widening and
narrowing) terminates, the returned result (σ, stabl) is the least partial
post-solution."** The "without widening and narrowing" qualifier is the
paper's own scope, not an artifact of our reading of the vendored source —
it is restated in the paper's Conclusion (section 8), which lists formal
termination guarantees under widening/narrowing as future work. This is
the authoritative confirmation of the blocker below: the paper itself does
not claim optimality for the widening/warrowing solver.

## What is landed

`side_cfg_T_eff_keyed_seed_dg` (`DG_Framework.thy`) is the heterogeneous
seeded keyed generator every context-sensitive/call-string DG analysis uses
(`nest_1_routed`, `nest_2_routed`, `twice_cs_routed`, ...). Before this work
it had no generic monotonicity pipeline; every instance would have had to
hand-prove `is_mono_eq`/`mono_sides`/`mono_deps` from scratch.

Landed in `src/Core/Solver/Context/DG/DG_Framework.thy`:

- `side_rhs_fold_dg_mono`, `_sides_mono`, `_static_deps` — fold-level
  lemmas, structural induction over the tree list via
  `seqcomp_mono`/`static_deps_seqcomp` (`Strategy_Tree_Monad.thy`).
- `side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen`, `_mono_sides_gen`,
  `_mono_deps_gen` — discharge `TD_side_mono`'s three preconditions for an
  *arbitrary* `side_cfg_T_eff_keyed_seed_dg` instance, from a per-tree
  contract on the `pred_sel`/`cmb`/`extra` hooks (intra/comb/extra
  monotonicity + static deps).
- `side_cfg_T_eff_keyed_seed_dg_threefold_mono` — bundles the three into
  `TD_Side_Eff_Pipeline.thy`'s `threefold_mono`.

Mirrors `td_cfg_side_solver_eff_gen` (`TD_Side_Eff_Pipeline.thy`), the
existing reduction for the flat (non-context) generator. No new proof
technique beyond what that pipeline used.

Verification: I/Q clean (0 errors, 0 warnings), no `sorry`. Batch build
`isabelle build -v -j12 -o threads=12 -N -d ~/afp/thys -d
vendor/td-verification -D . Voblint_Examples` finished green (`Finished
Voblint_Analysis`, `Finished Voblint_Formalization`, `Finished
Voblint_Examples`, all exit 0).

## Corrected theoretical picture

**`threefold_mono` is a precondition, not a precision result.** It makes
the TD solver's ordering/optimality reasoning *available* for a
`side_cfg_T_eff_keyed_seed_dg` instance. It proves nothing about any
computed answer, and no analysis becomes more precise by this lemma
landing. This was an explicit correction mid-session — an earlier framing
implied broader precision impact than is actually true.

**The "inconsistent evaluation" / TDabort concern is already resolved
upstream, not an open gap for us.** The general fixpoint-iteration paper
narrative (naive monotone equation systems with side effects can still lose
optimality if a query for the same unknown returns different values within
one evaluation, because of an interleaved `Side` publication) does not
apply to our situation as an *additional proof obligation*. Checked
directly against the vendored solver:

- `vendor/td-verification/TD_side.thy:3152` defines `TD_side_opt`, the
  *optimized* (caching) solver, parameterized by an `abort :: bool` flag.
  The `abort` mechanism (definitions around lines 54, 340-375) is precisely
  the safety net for the interleaved-query scenario: when `abort` is true,
  a query that would revisit a non-stable unknown aborts that evaluation
  instead of returning a possibly-inconsistent cached value.
- `vendor/td-verification/TD_side.thy:4277` defines `TD_side_mono =
  TD_side_opt True T`, i.e. the abort-enabled optimized solver, plus
  exactly the three threefold obligations (`mono_eq`, `mono_sides`,
  `mono_deps`) as `assumes`. **No fourth "consistency" assumption is
  needed** — abort is fixed `True` in the locale itself.
- `vendor/td-verification/TD_side.thy:5284` proves `least_partial_post_solution`
  inside `TD_side_mono`. This theorem is already fully proved in the
  vendored (trusted, out-of-scope-for-us) library.
- Our own interface already targets this exact locale:
  `src/Analysis/Generic/Solver/Core/TD_Side_Eff_Interface.thy:35`,
  `interpretation side: TD_side_mono cfg_pkg_eff`, inside locale
  `td_cfg_side_solver_eff` (lines 20-57), whose *only* assumptions are the
  three threefold facts (lines 24-26). `part_post_at`
  (line 54-57) gets `least_partial_post_solution` for free from that
  interpretation.

So for the flat generator, the chain is already: threefold_mono (proved
per-instance) -> `TD_side_mono` interpretation (mechanical) ->
`least_partial_post_solution` (free, vendored). There is no separate
abort/consistency proof step anywhere in this project's scope — the FM 2026
authors already discharged it once, generically, in the vendored file.

**Open question — RESOLVED, and it is a blocker.** Checked directly:
`nest_2_sol` (`Example_Interval_DG_CallString_K2.thy:29`) is defined via
`TD_side_warrowing_apinis_Interp_solve`, and its only proved property
(`nest_2_solve_dom`, lines 142-154) is `TD_side_warrowing_apinis_Interp.partial_post_solution`
— soundness only. `TD_side_warrowing_apinis_Interp` is a
`global_interpretation` of `TD_side_upd_rule`
(`vendor/td-verification/TD_side_upd_rule.thy:2421`), and
`TD_side_upd_rule` itself interprets `TD_side_opt False T`
(`TD_side_upd_rule.thy:26`) — **`abort = False`**, the opposite of
`TD_side_mono`'s `TD_side_opt True T`. `TD_side_upd_rule.thy` has its own
`query`/`iterate`/`repeat`/`eval` recursion built around a warrowing
operator (`\<nabla>\<Delta>`, line 50 — widening for globals, warrowing for locals) and
proves only `partial_post_solution` (line 1787) plus a `solve`/`solve_c`
code-equation equivalence (`term_equivalence`/`value_equivalence`, lines
2362-2382). **There is no least/optimal-fixpoint theorem anywhere in
`TD_side_upd_rule.thy`.** This is not a proof gap to fill — for a widening
solver, "computes the least fixpoint" is not generally true (widening
trades precision for termination on infinite-height lattices, e.g.
Interval), so the theorem plausibly does not hold for this solver at all.

**Consequence:** all four existing `routed_context` interpretations
(`twice_routed`, `twice_cs_routed`, `nest_1_routed`, `nest_2_routed`) live
under `src/Examples/Interval/` — Interval is the only domain instantiating
`routed_context` today, and Interval's infinite height means its call-string
examples run through the warrowing solver, not `TD_side_mono`. Discharging
`threefold_mono` for `nest_2_eqs`'s hooks (Steps 1+2's target) is real,
correct, general infrastructure, but it connects to `least_partial_post_solution`
only for a `TD_side_mono` (`abort=True`, non-widening) solve path — and
**no such path exists for any current call-string example**. Finishing
Step 3 exactly as originally scoped would produce a `least_partial_post_solution`
fact for `nest_2_eqs` that nothing in the codebase actually calls `solve`
through, i.e. a theorem about an equation system, disconnected from the
concrete executable result the precision claim needs to talk about.

## Step 3 needs a scoping decision before any proof work

The original plan (discharge threefold_mono at `nest_2_eqs`, get
`least_partial_post_solution` for free) is sound as an isolated Isabelle
exercise but, per the blocker above, would not connect to Interval's actual
solve path. Options, not yet decided:

- **(A) Retarget to a non-widening domain.** Build a call-string
  `routed_context` interpretation over a finite/ACC domain (Sign is the
  natural candidate — already used elsewhere in the project, listed ahead
  of Interval in `CLAUDE.md`'s domain order) where the ordinary `TD_side_mono`
  solve path applies without widening. Then Step 3 as originally scoped
  (instantiate the Step 1+2 pipeline, discharge nine obligations, get
  `least_partial_post_solution`, then a k=2-vs-k=1 precision theorem) is
  directly buildable. Cost: a new Sign call-string example
  (`nest_1`/`nest_2`-equivalent), likely smaller than solving (B) below, but
  scope creep beyond "finish the Interval story."
- **(B) Extend the vendored precision theory to the warrowing solver.**
  Investigate whether any precision guarantee survives widening for
  `TD_side_upd_rule` — realistically not "least fixpoint" but something
  weaker (e.g. widening-relative or `narrowed_le`-style bound). This is new
  mathematics, not just new Isabelle; it may be false as stated, and is out
  of scope for "vendored, trusted, do not touch" per this project's
  boundary around `vendor/td-verification`.
- **(C) Narrow the precision goal to the semantic/soundness layer already
  proved.** Accept that "the widening-executed Interval result is provably
  optimal" is not obtainable with the current vendored solver, and instead
  state the achievable claim: the underlying k=2 equation system is
  well-behaved (`threefold_mono`, Steps 1+2 — already true, general,
  reusable), and `project_sigma`/`post_solution_of_seeded`-style projection
  facts (already landed) are the ceiling of what's provable about the
  *executed* Interval result without new solver theory.

**Decision (2026-07-31): Option A.** Confirmed against the primary source
(Tilscher/Graß/Seidl, Theorem 2, p.17 — optimality holds only "without
widening and narrowing") — Option B is chasing a claim the paper's own
authors do not make, so Option A is the only path to a real precision
theorem with the current vendored solver.

## Option A real scope, per a follow-up codebase audit (2026-07-31)

A dedicated read-only audit of `Routed_Context.thy`,
`Example_Interval_DG_CallString_K1.thy`, `Sign_DG.thy`, `Sign_Lattice.thy`,
`Example_Mixed_Flow_Sign.thy`, and every caller of
`side_cfg_T_eff_keyed_seed_dg` across `src/` found the real shape of Option
A is larger than "add a Sign call-string example." Concretely:

- **No file anywhere solves `side_cfg_T_eff_keyed_seed_dg` via
  `TD_side_mono`.** Every existing call-string/context-sensitive example
  (`Example_Interval_DG_CallString_K1/K2.thy`,
  `Example_Interval_DG_Ctx_Flagship.thy`, `Example_Interval_DG_Ctx_Sound.thy`,
  `Call_String_Solver_Refinement.thy`) solves through
  `TD_side_warrowing_apinis_Interp_solve` (widening). `TD_side_mono` is only
  ever interpreted for the *flat* generator (`td_cfg_side_solver_eff`,
  `TD_Side_Eff_Interface.thy:20-57`). Steps 1+2 (`DG_Framework.thy`) landed
  the conditional monotonicity lemmas but no wrapper locale that actually
  interprets `TD_side_mono` for `side_cfg_T_eff_keyed_seed_dg`. **This piece
  is domain-agnostic** — it doesn't need Sign or Interval, just the generic
  generator — and is the natural next concrete step regardless of which
  domain ends up hosting the precision theorem.
- **`Sign_DG.thy` has no context/`dg_spec` combine-enter machinery at all** —
  only the flat, context-*insensitive* `unit_dg_spec sign_tf` (used by
  `Example_Mixed_Flow_Sign.thy`, itself flat, no call-string). Everything
  Interval's call-string examples use for Sign's role (`Spoly`'s
  `unit_dg_spec_st ivl_tf_st ivl_enter_st`, the `ivl_Hstep`/`ivl_Henter`/
  `ivl_Hcomb` executable-vs-abstract commuting lemmas, `cinit_ivl_st`) has
  no Sign counterpart yet. Building one is new domain engineering (transfer
  - enter functions for Sign in both executable and abstract form, plus
  their soundness/commuting proofs), comparable in size to what already
  exists for Interval — not a small addition.
- **`routed_context`'s own interpretation obligations are substantial**:
  `finC`, `seed_key_ne_gk0`, `route_enterc_agree`, `call_fwd`, `comb_fwd`,
  `call_enter_store_agree`, on top of the underlying `dg_ctx_activation`
  obligations. Interval's existing interpretation of these is itself a
  large proof; a Sign version repeats that scale of work, not a
  refactor of it.
- **Sign is not typeclass-`finite` or ACC-proved** — only "operationally
  terminates" (`Example_Mixed_Flow_Sign.thy` assumes `solve_dom` as a
  hypothesis rather than deriving it; Interval's call-string examples prove
  termination `by eval` on a concrete instance). This is not a blocker —
  `TD_side_mono`'s `least_partial_post_solution` is conditional on
  `solve_dom` regardless of domain — but it means "Sign avoids widening" is
  true and sufficient, not because Sign is formally finite in Isabelle's
  sense, just because nothing in its solve path needs a widening operator.

**Revised staging, smallest reusable piece first:**

1. **Domain-agnostic**: build a `side_cfg_T_eff_keyed_seed_dg` analogue of
   `td_cfg_side_solver_eff` (`TD_Side_Eff_Interface.thy:20-57`) — a locale
   taking the three Step 1+2 `..._gen` lemma shapes as assumptions and
   interpreting `TD_side_mono` for the keyed-seed generator, producing a
   `least_partial_post_solution`/`part_post_at`-style fact generically. No
   domain choice needed yet; this is reusable no matter which analysis ends
   up hosting the actual precision theorem.
2. **Sign domain engineering**: build Sign's context `dg_spec` (transfer +
   enter functions in executable and abstract form, soundness/commuting
   lemmas), mirroring `Spoly`/`ivl_tf_st`/`ivl_enter_st`/`ivl_Hstep` et al.
   This is the largest single piece.
3. **Sign `routed_context` interpretation**: discharge `finC`,
   `seed_key_ne_gk0`, `route_enterc_agree`, `call_fwd`, `comb_fwd`,
   `call_enter_store_agree` for Sign's `cs_route`, mirroring Interval's
   existing interpretation.
4. **Nine primitive obligations**: instantiate Stage 1's wrapper at Sign's
   concrete hooks (mirrors the original Step 3 plan, now for Sign).
5. **The actual precision theorem**: k=2-vs-k=1 as a genuine ordering
   claim, not yet scoped mathematically — `project_sigma`/
   `post_solution_of_seeded` only state "projects to a valid post-solution,"
   not an inequality; this needs new argument structure on top of
   `least_partial_post_solution`.
6. Batch-verify the whole chain.

Stage 1 is the only piece that's both small and unconditionally useful —
recommended starting point, deferring commitment to the Sign domain-
engineering scale (stages 2-3) until Stage 1 lands and the picture is
re-assessed.

No lemma should be written for Step 3 until one of these is chosen — the
choice determines which files change and what the target theorem statement
even is.

## What Step 3 does *not* by itself deliver

Discharging `TD_side_mono` for `nest_2_eqs` gives `least_partial_post_solution`
for the k=2 system alone. It does **not** by itself give the k=2-vs-k=1
precision theorem (`solution(k=2) <= solution(k=1)`). That still needs a
refinement/projection argument connecting the k=2 least solution to the k=1
system — likely building on `project_sigma`
(`Call_String_Solver_Refinement.thy`) and `post_solution_of_seeded`
(`Context_Refinement.thy`), neither of which currently states or proves an
ordering claim, only a "projects to a valid post-solution" claim. That
theorem is genuinely new work, not yet scoped in detail.

## Update (2026-07-31): decision made, Stage 1 landed, Stage 2 collapsed

The blocker above was resolved by decision, not by extending the vendored
solver: retarget to Sign (finite lattice, no widening needed), confirmed
against the primary source (Tilscher/Graß/Seidl, Theorem 2, p.17 — see
above) as the only domain where a real optimality theorem is reachable with
the current vendored `TD_side_mono`.

**Stage 1 — landed, I/Q-clean (batch pending until the final gate, per
explicit instruction not to batch-build until the end of this effort).**
`src/Core/Solver/Context/DG/DG_Framework.thy`, new locale
`td_cfg_side_solver_dg` (inserted after
`side_cfg_T_eff_keyed_seed_dg_threefold_mono`, before the closing
homogeneous-interfaces text): mirrors `td_cfg_side_solver_eff`
(`TD_Side_Eff_Interface.thy:20-57`) but for the keyed-seed DG generator.
Fixes the same nine hooks as `side_cfg_T_eff_keyed_seed_dg`, takes the nine
primitive obligations (the `..._gen` lemmas' preconditions) as `assumes`,
defines `cfg_pkg_dg`, proves `cfg_pkg_dg_threefold_mono`, interprets
`TD_side_mono cfg_pkg_dg`, and exposes `stabl_at`/`nu_at`/`part_post_at`/
`least_part_post_at` exactly like the flat interface does. Two proof
patterns worth knowing for anyone extending this file:

- The type variables `'d`/`'h` in the locale's `fixes` must carry their
  `bounded_semilattice_sup_bot` sort constraint at their *first* textual
  occurrence in the `fixes` list (on `route`'s and `cmb`'s types
  respectively), not on `S`'s type later — Isabelle elaborates each
  `fixes`/`and`-clause's type independently enough that a later
  constraint on an already-used-unconstrained variable is rejected as
  "inconsistent with default type."
- Composing `side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen[OF intra_mono
  comb_mono extra_mono]` (and the sides/deps analogues) directly fails with
  "OF: multiple unifiers" — the lemma's `pred_sel`/`g`/etc. are all
  schematic, so `?pred_sel ?g v` is a genuine (non-pattern) higher-order
  unification against the OF'd facts, before the surrounding `rule` ever
  sees the concrete goal. Fixed by `apply (rule
  side_cfg_T_eff_keyed_seed_dg_is_mono_eq_gen)` first (unifies the
  lemma's *conclusion* against the already-unfolded, fully concrete goal —
  ordinary first-order matching, no ambiguity), which turns the three
  premises into fully concrete subgoals, each closed by a plain `apply
  (rule intra_mono)` etc.

**Stage 2 — collapsed, nothing to build.** `unit_dg_spec sign_tf`
(`DG_Framework.thy:311`, takes any `'a::sound_domain domain_transfer`) is
already Sign's abstract context `dg_spec`, since `sign_tf :: sign
domain_transfer` (`Sign_Transfer.thy:84`) already exists and `Sign_DG.thy`
already proves it sound (`sound_dg_spec_unit[OF sign_is_sound_transfer]`).
Interval's K1/K2 build a *separate* executable (`ivl st`) layer
(`ivl_tf_st`/`ivl_enter_st` + `ivl_Hstep`/`ivl_Henter`/`ivl_Hcomb` commuting
lemmas, ~150 lines) purely to support code generation and `by eval`
termination/coverage proofs against the (unrelated, abort=False) warrowing
solver — not needed here.

**Stage 3 — in progress, and Interval's mechanics do not transfer.**
Traced `routed_context`'s full dependency chain: it extends
`dg_ctx_activation`, whose key precondition
(`DG_Ctx_Activation.thy:32`, `pp`) is literally `part_post_solution
(side_cfg_T_eff_keyed_seed_dg ...) x0 sigma vars` — exactly what Stage 1's
`part_post_at`/`least_part_post_at` produces once Stage 4's nine
obligations are discharged for a concrete instance. Both `routed_context`
and `dg_ctx_activation` operate purely at the abstract level (`S ::
('a::sound_domain abs_state, 'a abs_state) dg_spec`) — confirmed no
executable form is structurally required by these locales themselves.

However: **`TD_side_opt`/`TD_side_mono`'s `solve` has no `[code]` setup
anywhere in `vendor/td-verification/TD_side.thy`** (confirmed by direct
grep — zero hits for `[code]`/`code_pred`/`export_code`). It is a partial
recursive definition (`function (domintros)`) with no code equations.
Interval's `by eval` coverage/termination proofs
(`nest_1_terminates`, `entry_covered_1`, `nest_fwd_closed_1`, etc., ~150
more lines) all run through `TD_side_warrowing_apinis_Interp_solve`'s
*separate*, independently-executable recursive definitions in
`TD_side_upd_rule.thy` (the abort=False path) — that executability was
purpose-built there and does not extend to `TD_side_opt`/`TD_side_mono`.
Building an executable refinement of `TD_side_mono` ourselves would be a
significant undertaking in its own right and oversteps the "vendored,
trusted, do not touch" boundary around `vendor/td-verification`.

**Decided route:** skip running any solver. Hand-construct the witness
`sigma :: pp × context + gk ⇒ (sign abs_state, sign abs_state) dg_state`
and `vars :: (pp × context) set` directly for a small, fully finite nest-
shaped Sign program (finite CFG × finite call-strings, both hand-
enumerable without execution), then prove `part_post_solution`'s clauses
and `dg_ctx_activation`/`routed_context`'s ten obligations (`finE`,
`sg_cov`, `sg_uncov`, `fwd`, `finC`, `seed_key_ne_gk0`,
`route_enterc_agree`, `call_fwd`, `comb_fwd`, `call_enter_store_agree`) by
direct Isar/`simp` reasoning over Sign's seven-element lattice — the same
"hand-built witness" style `Context_Refinement.thy`'s
`projected_part_post_solution`/`post_solution_of_seeded` already use, not
solver-derived coverage. This drops Interval's ~250-line executable-vs-
abstract bridging section entirely (moot once nothing is executed), so
despite being a mechanically different route than Interval's file, it is
not obviously larger — likely smaller — but it is still a substantial,
multi-obligation proof-engineering task for a genuinely new concrete
example, not a mechanical port.

**Program shape (per explicit instruction, do not redesign):** mirror
Interval's `nest_program` exactly — `main` calls `f` at two sites, `f`
calls `g` at one site inside its own body, so `g`'s single call site is
identical for both `f`-activations (1-call-string cannot separate them,
2-call-string can). Unlike Interval's `f(3)`/`f(10)` (both positive, no
sign-domain separation would be visible), the Sign version needs one
positive and one non-positive argument, e.g. `f(3)`/`f(-10)`, so k=1
merges `g`'s parameter to `Top` (imprecise: `Pos ⊔ Neg`) while k=2 keeps
`g`'s two call-string-separated activations at `Pos` and `Neg`
respectively — confirm VIMP's concrete arithmetic-expression syntax
supports a negative literal (or use `0 - 10`) before hard-coding this.

## Final update: Stages 3-5 landed, by a different route than planned

Everything from "Decided route: skip running any solver. Hand-construct the
witness..." above (the hand-witnessed-`sigma` plan) was **superseded, not
executed**. The actual route taken is simpler and stronger, and the
reasoning above about why is worth recording since it corrects a real
mistake in this document's own analysis.

**The correction.** This document's Stage 3 section concluded that because
`TD_side_opt`/`TD_side_mono` (the `abort=True` locale) has no `[code]`
setup, the only way forward was to hand-type `sigma`/`vars` by hand and
prove `part_post_solution` clause-by-clause. That conclusion does not
follow. `part_post_solution` (`Basics_side.thy:337`) is a **pointwise
predicate on a witness** — `dep_L T sigma u <= vars`, `eq T u sigma <=
sigma (Inl u)`, `sides_of_rhs (T u) sigma <= sigma`, for each `u : vars` —
it has nothing to do with monotonicity, `TD_side_mono`, or `TD_side_opt`
at all. Monotonicity (`threefold_mono`, Stage 1's whole point) is only
needed to *derive a witness's existence* generically from an equation
system, via `TD_side_mono`'s `least_partial_post_solution` theorem. If a
witness is obtained some other way — including by actually running a
*different*, already-executable solver — `part_post_solution` still needs
proving, but proving it does not route through `TD_side_mono` at all.

**What actually unlocks Sign, and what the earlier framing missed:**
`TD_side_upd_rule` (`TD_side_upd_rule.thy:18`) — the *executable* solver
family Interval's call-string examples already use — is not tied to
warrowing. It is parameterized by an *update rule*, and the vendored file
interprets it three ways (`Solver_Menu.thy`): `TD_side_always_join_Interp`
(plain join, exact, no widening), `TD_side_per_origin_Interp`, and
`TD_side_warrowing_apinis_Interp` (widening, what Interval uses). Sign is a
finite lattice (`Sign_Lattice.thy`, 7 elements, ACC trivially), so the
*plain join* instantiation terminates on any loop-free program and reaches
the **exact** least fixpoint — no widening step ever fires. Termination is
one `eval`-checked fact
(`TD_side_always_join_Interp_solve_c ... != None`), and
`Solver_Menu.thy`'s `part_post_solution_of_solve_c` turns that single fact
directly into `part_post_solution`, with no monotonicity argument anywhere
in the chain. This is the same "does the solver actually run" question the
Stage 3 section above worried about — it has a positive answer, just not
through the locale the earlier analysis was looking at.

Concretely, this means: **Sign's call-string examples now mirror
Interval's file-for-file** (`Example_Sign_DG_CallString_K1/K2.thy` follow
`Example_Interval_DG_CallString_K1/K2.thy`'s structure exactly), with two
substitutions — `TD_side_always_join_Interp_solve` instead of
`TD_side_warrowing_apinis_Interp_solve`, and Sign's executable transfer
mirror (`Sign_Exec.thy`'s `sign_tf_st`/`sign_enter_st`, already existing,
no new domain engineering needed — Stage 2's original "collapsed, nothing
to build" conclusion undersold this: Sign already had *both* the abstract
`unit_dg_spec sign_tf` *and* the full executable `st`-level mirror before
this session started). The Stage 1 generic `threefold_mono`/`TD_side_mono`
infrastructure landed in `DG_Framework.thy` remains correct, valuable,
general infrastructure for issue #45 (a `side_cfg_T_eff_keyed_seed_dg`
instance now has a reusable path to `least_partial_post_solution` if a
future analysis needs the *existence* argument rather than a computed
witness) — it is simply not on the critical path to this example.

**Result, Stage 5 (the actual precision theorem), stated and proved by
`eval` + `less_sign_def`:**

```
g's entry parameter, k=1 (one merged context [Statement 2]):        STop
g's entry parameter, k=2, context [Statement 2, Statement 5] (f 3):  SPos
g's entry parameter, k=2, context [Statement 2, Statement 6] (f -10): SNeg
```

`sign_k2_strictly_more_precise_than_k1_at_g`
(`Example_Sign_DG_CallString_K2.thy`) proves both `SPos < STop` and
`SNeg < STop` for the actual computed values — a genuine strict-order
precision witness, not a projection/refinement argument (contrast
`Call_String_Solver_Refinement.thy`'s `project_sigma_part_post_solution`,
which only shows a projected value is *a* valid post-solution, not that it
is strictly more precise than anything).

**Connection to the paper (Tilscher/Graß/Seidl, Theorem 2, p.17):** the
paper's optimality theorem is scoped to solver runs "without widening and
narrowing." The always-join solve on Sign satisfies that scope by
construction (Sign has no widening operator invoked in this update rule at
all), so the computed result sits inside the paper's own optimality
envelope, informally — this project did not re-derive or invoke
`TD_side_mono`'s formal optimality theorem for this instance (that would
require the Stage 1 infrastructure plus a fresh `least_partial_post_solution`
argument, not done here), but the paper's own scoping condition is exactly
why Sign, not Interval, was the domain that could host a *computed*
precision witness at all: Interval's call-string examples run only through
the warrowing update rule, which is precisely the case the paper excludes
from its optimality guarantee. The Sign example is this project's
concrete demonstration of *why* that scoping condition in the paper
matters for context-sensitivity: on a domain where it is satisfiable, call-
string refinement (k=1 to k=2) has a directly computable, verified effect
on precision; the paper proves the solver-side half of that story (the
computed result is trustworthy), and this example supplies the
analysis-side half (a concrete case where refining context actually
changes the computed result, and by how much).

Tool note for future sessions: `rtk rg` was found to silently truncate/
mangle long Isabelle identifiers in its returned output during this
session (e.g. `unit_dg_Hstep` rendered as `n`, `part_post_solution_seed_dg_st_to_abs`
rendered as `part_n`) — confirmed by cross-checking against plain `rg` and
I/Q's own parser (`command_found` field). Do not trust `rtk rg` output for
exact identifier names; use the `Read` tool or I/Q directly.

## Task list at handoff

- `#14` (Stage 1: `td_cfg_side_solver_dg` wrapper) — completed, I/Q-clean.
- `#15` (batch-verify #45 pipeline) — completed (this was the earlier,
  separate Steps 1+2 verification; batch-green).
- `#16` (Stage 2: Sign `dg_spec`) — completed (collapsed to reuse, see
  above; no new file).
- `#17` (Stage 3: Sign `routed_context` interpretation) — completed.
- `#18` (Stage 4: nine primitive obligations for the Sign instance) —
  completed.
- `#19` (Stage 5: k=2-vs-k=1 precision theorem) — completed.
- `#20` (Stage 6: final batch verify) — completed; the full build is green.

## Explicit scope note

All six stages now have a green batch build behind them. The concrete list
of obligations from `DG_Ctx_Activation.thy:31-39` and
`Routed_Context.thy:99-121` remains the reference for any follow-up
generalization.
