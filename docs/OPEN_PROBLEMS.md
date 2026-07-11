# Open problems and handoffs

Catalogue of repo-level problems with stable file:line refs (P1–P10). For *new
work and extensions*, see `docs/ROADMAP.md` + [GitHub Project 8](https://github.com/users/ManuelLerchner/projects/8).

Source of truth for live sorries:

```bash
rg -n '^\s*sorry' src/ | rg -v '\.thy~'
```

Related: `docs/HOL_IMP_COMPARISON.md`, `docs/PROOF_PHASES.md`, `docs/PROOF_OVERVIEW.md`.

---

## Bridges in the soundness chain

```
cfg_collect_trace (trace spec at each pp)
       |
       |  alpha_last projection (CFG_Collect_Trace)
       v
cfg_collect (state spec at each pp)
       |
       |  unified_post_fixpoint_sound (Analysis_Sound / B3)
       v
gamma_state (env v)  <-----  side_analyse_eff output (B4)
       ^
       |  [P1 side_cfg_solve_dom_eff per pp]
       |
   TD_side solver (per-pp root at v, interprocedural)
```

| Bridge | Statement | Where | Status |
| --- | --- | --- | --- |
| B3 | `is_post_fixpoint env ==> ∀v. cfg_collect g S v ⊆ gamma_state (env v)` | `Analysis_Sound.thy` (`unified_post_fixpoint_sound`) | done |
| B4 | per-pp `side_analyse_eff` sound w.r.t. `cfg_collect` at queried `v` | `TD_Side_Eff_Soundness.thy` (`side_analyse_eff_collect_sound_exit_pruned_gen`) | done (modulo P1 as hyp) |
| B5 | ~~`td_cfg_in_reach`~~ — removed (Fix B, 2026-06-01) | was `Pipeline.thy` (classical spine) | **done** (historical; classical spine retired) |
| B6 | `comp_fun_idem (ac_join cfg)` | classical spine | **done** (historical; classical spine retired) |
| B7 | `side_cfg_solve_dom_eff g etf bot s0 gseed v` for each queried `v` | `Sign_Side_Soundness.thy` assumptions | open (P1) |

**Operational link:** `cfg_runs_to pi ps c s t` is definitional exit `cfg_collect`
at `cfg_exit (compile_prog …)` (`CFG_Collect_Runs.thy`).

Optional / removed from main path:

| Item | Status |
| --- | --- |
| `Direct_Equations.thy` | **deleted** — was alternate AST path (P10 abandoned) |
| `TD_Total.thy` | **deleted** — was orphan totality track (P6) |
| Classical intra spine (`Pipeline.thy`, `TD_Soundness.thy`, etc.) | **extracted** to `voblint-formalization-classical` |

`trace_analysis_sound` / `reaching_global_read_sound` carry **P1** (`side_cfg_solve_dom_eff`) as the only solver hypothesis.

---

## Problem catalogue

| ID | Problem | Files | Why it blocks | Needed for |
| --- | --- | --- | --- | --- |
| P1 | `side_cfg_solve_dom_eff` assumed | `Sign_Side_Soundness.thy` | "If TD side terminates, result is sound" | Cleaner main theorem; total correctness |
| P2 | ~~`td_cfg_in_reach`~~ | was classical `Pipeline.thy` | **done** 2026-06-01 — Fix B; classical spine retired | (historical) |
| P3 | `comp_fun_idem (ac_join cfg)` | classical `Pipeline.thy` | **done** 2026-05-27 (`join_state_comp_fun_idem`); classical spine retired | (historical) |
| P4 | Interval domain | not in current tree | Second numeric domain | Wider thesis scope |
| P5 | `pp = nat` vs TD `finite UNIV` | `CFG_Def.thy`, vendored TD | Termination locale type finiteness | Generic termination claim |
| P6 | TD total correctness | was `TD_Total.thy` | **file removed**; reopen if totality returns | Total correctness |
| P7 | Widening soundness | not in current tree | Feeds termination track | Interval + widening |
| P8 | `quick_and_dirty` in `ROOT` | `ROOT` | **done** — removed | — |
| P9 | Executable end-to-end limited | `Example_Side_Proc_Global.thy` | Concrete solve_dom witness needed | In-Isabelle execution |
| P10 | `Direct_Equations` | was `Equations/Direct_Equations.thy` | **deleted** — CFG path is the only route | — |
| P11 | Per-origin widening on a digest system | `Example_Interval_Mode_Digest.thy`, vendor `Update_rules.thy:143`; **executability solved:** `Generic/Solver/Exec/Origin_Lift.thy` | The vendored `warrowing_per_origin` rule does not code-generate (`Interrupt_Breakdown`). `Origin_Lift` sidesteps it: it lifts the value domain to `('o,'d) origin_st` (per-origin cells, `collapse` on read) and runs the *ordinary* warrowing solver, whose pointwise widening is per-origin — this **does** `eval`. Soundness reduction proved for the local RHS (`traverse_lift_tree`, `collapse_eq_origin_lift`); the `sides_of_rhs`/`dep_L` half of the `part_post_solution` transport is the remaining mechanization | Finish the `part_post_solution` transport so per-origin widening is a proven-sound solver feature |
| P12 | Finite upper bounds on recursive/loop **globals** | `Example_Interval_Recursion_Digest.thy`, `Example_Interval_Recursion_Origin.thy`; domain `Interval_Domain.thy` | **Diagnosis corrected (2026-07-08).** The old story (collapse-on-read re-merges the recursive cell) was not the primary barrier. Mechanized findings: (1) the missing widening **bot-law** was the dominant loss — `⊥` is the empty interval, so an unguarded widen-from-`⊥` topped every global on its *first* write (`G := 5`, no loop, gave `[-inf,+inf]`); the bot-law (now in `Interval_Domain.thy`) fixes the **lower** bound, so recursion `G = [0,+inf]` for both monovariant and per-origin (`rec_warrowing_widens_to_top`, `rec_per_origin_matches_monovariant`, `by eval`). (2) The **upper** bound is still lost because `G` is a **flow-insensitive global side slot**: the guard refines the read but not the write-back, so `[0,+inf]` is a genuine fixpoint. (3) Per-origin widening is **orthogonal** — origin cells top identically; it helps only if the side semantics becomes flow/context-sensitive. (4) Interval narrowing is **real** (fill an infinite bound from the guard-refined value), enabled in the domain: it recovers *locals* (`[0,20]` under every update rule) but not the global, and the full build is green with it on. It did **not** cause the `rec_digest` breakdown — that is the bot-law keeping `G` precise so the value-keyed digest churns a bucket per depth, which happens with narrowing on or off; that solve is stated non-evaluationally. A gas-bounded narrowing solver (`update_global_bounded_narrowing`) was probed and, even with real narrowing, still yields `[0,+inf]` on the global | Finite bounds on globals need context/origin-sensitive **reads** of the slot (a side-semantics change) — not per-origin widening, not a stronger value-domain narrowing |

---

## Per-problem notes

### P1 — solver termination assumption

`trace_analysis_sound`, `reaching_global_read_sound`, and `side_sign_analysis_sound`
ultimately require:

```isabelle
assumes side_solve_dom:
  "side_cfg_solve_dom_eff (compile_prog pi ps main) sign_etf bot s0 ()
     (cfg_exit (compile_prog pi ps main))"
```

This is `TD_side.solve_dom destab_opt True (side_cfg_T_eff …) v`, i.e. termination
of the side-effecting per-pp solve. Monotonicity of `side_cfg_T_eff` is proved
(in `TD_Side_Eff_Bounds.thy` + `TD_Side_Eff_Soundness.thy`), so P1 is gated on
well-foundedness of the TD side worklist over a finite pp set.

P1 is gated on P5 for a generic termination proof.

**P2 (closed 2026-06-01):** Fix B — per-pp `td_analyse`, `td_analyse_collect_sound_at`
via `td_env_at_path_step_le`; `td_cfg_in_reach` removed from all theorems. See finding below (historical).

### P2 finding (2026-05-27) — structural inconsistency

`td_cfg_in_reach` is the hypothesis

```isabelle
\<And>v::pp. v \<in> reach T sigma (cfg_entry g)
```

where `T = make_rhs_tree (to_cfg c) tf join bot s0` and
`sigma = TD_plain_Interp_solve T (cfg_entry g)`.

#### Why it is false

- `reach T sigma x` (`vendor/td-verification/Basics.thy:278`) is the set
  of unknowns transitively queried while computing `eq T x sigma`.
  Inductively: `x \<in> reach T sigma x`; if `y \<in> reach T sigma x` and
  `z \<in> dep T sigma y` then `z \<in> reach T sigma x`.
- `dep T sigma y = dep_aux sigma (T y)` (`Basics.thy:212`) is the set of
  `Query` targets in the strategy tree at `y`.
- `make_rhs_tree g tf join bot s0 v` (`src/Solver/TD_CFG_Core.thy:62`)
  builds the forward dataflow equation: `Query` nodes target
  `predecessor_list g v`.
- Therefore `dep T sigma v` = CFG predecessors of `v`, and
  `reach T sigma entry` = `{entry}` ∪ predecessors-of-entry ∪ ... .
- `to_cfg` constructions give entry no predecessors, so

  ```
  reach T sigma (cfg_entry g) = {cfg_entry g}
  ```

The assumption then claims `\<forall>v. v = cfg_entry g`. False for any
program with more than one program point.

#### Concrete example

Take `c = ''x'' ::= N 5`. The compiled CFG `to_cfg c` has two pp's:
`cfg_entry g = 0`, `cfg_exit g = 1`, with a single Assign edge
`(0, x:=5, 1)`. Then:

- `predecessor_list g 0 = []` (entry has no predecessors).
- `dep T sigma 0 = {}`, so `reach T sigma 0 = {0}`.
- `td_cfg_in_reach` at `v = 1` requires `1 \<in> {0}`. False.

Instantiating `voblint_sign_sound` on this `c` is impossible: discharging
`td_cfg_in_reach` would require proving false.

The proofs go through only because the hypothesis is left abstract — no
example actually discharges it. The soundness chain holds *vacuously* on
a false premise.

#### Where it bites in the proof

`td_env_post_fixpoint` (`src/Solver/TD_Interface.thy:38-58`) closes the
post-fixpoint goal at arbitrary `v` via

```
part_solutionD[OF psol v_reach]
```

`psol : part_solution cfg_T entry sigma (reach cfg_T sigma entry)`
gives the equation only on `reach`. `v_reach : v \<in> reach ...` is the
P2 assumption that bridges to "for all `v`". Without P2 actually true,
this step is unjustified at non-entry `v`.

#### Possible fixes

**A. Solve at exit, prove backwards-reachability as CFG side condition.**

- Change `td_solve_dom T (cfg_exit g)` and `... \<in> reach T sigma (cfg_exit g)`.
- New lemma: every pp on an entry→exit path is in
  `reach T sigma exit` (equivalent to "backwards-reachable from exit").
- Provable from `to_cfg` structure by induction on the program.
- **Breaks for non-terminating programs.** `nonterm_prog`,
  `incr_loop_prog` have no entry→exit path; exit is reachable in
  neither the CFG nor `reach`. Loop-body pp's would need a separate
  solve point.

**B. Per-pp solve (cleanest).**

- Redefine

  ```isabelle
  td_analyse c tf join bot s0 v
    \<equiv> lookup_bot (Interp_solve (make_rhs_tree ...) v) v
  ```

  One solve per query. Each solve fills the queried node's transitive
  predecessors.
- The reach hypothesis becomes `v \<in> reach T sigma_v v`, which is
  `reach.base` — **trivially true**.
- The solve-termination hypothesis becomes per-pp: `\<forall>v. solve_dom T v`.
  Slightly stronger than the single `solve_dom T entry` we have now,
  but in line with how TD is actually used.
- Pipeline theorems quantify per-pp termination, no architectural
  inversion.
- Cost: more solver invocations at run time. Acceptable for a
  formalization — Voblint's real worklist solver covers everything in
  one pass; this is a proof artifact.

**C. Invert the equation system (rejected).**

- Make `make_rhs_tree` query *successors* (`successor_list g v`) instead
  of predecessors. Then `reach T sigma entry` covers everything
  forward-reachable from entry.
- But the resulting equation is a backwards predicate transformer, not
  the forward dataflow equation. Sign/interval analyses are forward;
  this changes their meaning.
- Off-table for the existing domain track.

**D. Macro-solve over a covering root set.**

- Compute a set `R \<subseteq> pp` whose backward-reach covers every pp,
  call TD once per root, merge.
- Effectively Fix B with the solve set chosen up front. More machinery,
  same trade-off.

**Recommendation.** Fix B. Cleanest mathematically (`reach.base`
discharges the hypothesis, no CFG-side connectivity proof needed),
covers terminating and non-terminating examples uniformly, no
architectural inversion. Cost is a minor refactor of `td_analyse` and
the pipeline statement shape (per-pp solve termination instead of
single-point), not weeks of work.

**Track B overlap.** B3 (side-effecting TD) already reshapes the
`strategy_tree` signature (`Side`/`QueryL`/`QueryG`). If B3 proceeds,
fold P2 into the B3 refactor rather than fix it standalone first.

#### Status

**Closed 2026-06-01** — Fix B implemented ([#8](https://github.com/ManuelLerchner/voblint-formalization/issues/8)):
`TD_Interface.thy`, `TD_Soundness.thy`, `Pipeline.thy`, `Constraint_System_Sound.thy`
(`post_fixpoint_sound_at`). Historical analysis above kept for thesis / meeting notes.

### P5 — type-level finiteness

See previous table (routes a/b/c). Partial-correctness thesis may keep P1 explicit.

### P4 / P7 — interval domain

Sign end-to-end proved (`side_sign_analysis_sound`; carries P1 only). Interval
domain not in current tree — was in classical spine (sibling repo). Adding it
requires only a `sound_transfer` interpretation for interval transfer functions;
no architectural changes needed.

### P6 — TD total correctness

`TD_Total.thy` removed from the tree. Reintroduce only if P5 is resolved and totality is in scope.

### P8 — session hygiene

Split core vs stretch sessions when sorry-free core is policy.

### P10 — Direct_Equations

**Abandoned.** File deleted; `Voblint_Formalization` imports CFG route only.

### P11 — Switching fctx: caller-context exactness for ENTER_MONO

**Resolved at prototype level by a value-refined (bounded intra-edge) context.
No call-boundary scheme works; a deterministic per-edge context update does. The
cheaper local-read alternative (Fix A) is refuted by eval — see the "Fix A probe"
subsection below; `cstep` context refinement is required *within the fixed
context-keyed global*.**

**Superseding direction (2026-07-02): re-key the writer, not the context.** The
`cstep` conclusion holds only while the global key is the context (one flow-insensitive
slot per context, joined at write time). Re-keying global writes by **definition site**
and reading through a **reaching-definition digest** recovers the same exactness with
contexts kept call-only — the paper-faithful route. Generalized to a digest interface
(`writer_key` / `reader_digest` / `compatible`), with reaching definitions as the first
instance. See `DIGEST_INDEXED_READER_MIGRATION.md` and the "Writer re-keying" subsection
below. `cstep` demoted to fallback.

The value-dependent (switching) route in
`src/Formalization/Examples/Example_Finite_Sign_Context_Analysis.thy` cannot
discharge `ENTER_MONO` (`Voblint_Analysis.TD_Side_Eff_Cmp_Sound`). `ENTER_MONO`
quantifies over the observation concretisation `gamma (side_env_cmp sigma (cl,
ctx))` and needs it exact on the digest variable `G`. It is not, and no
call-boundary context scheme can fix it — machine-checked in the file's
"Investigation" subsection:

- `fctx_call4_only_GOther` / `fctx_call8_only_GOther`: both call nodes 4 and 8
  live under the single caller context `GOther` (they are interior points of one
  `main` activation; context changes only at call boundaries).
- `fctx_GOther_slot_joins_G`: the keyed slot `Inr GOther` joins `main`'s `G := 0`
  and `G := 1` to `SNonNeg` (globals are flow-insensitive per context).
- `fctx_caller_read_G_imprecise` / `_imprecise8`: `side_env_cmp` adds that global
  summand, pinning the observation of `G` at both call nodes to `SNonNeg`.

Retain sharpens only the routing read `route_read_cmp` (the local slot), not the
global summand `side_env_cmp` adds. Every candidate call-boundary scheme
(call-site-refined, call-string, entry-store) leaves `main` under one context, so
`Inr (that context)` joins both writes. The needed `G = 0` at 4 vs `G = 1` at 8
distinction is flow-sensitivity *within* one activation — expressible only by an
intra-edge context update, outside the call-only protocol.

**Prototype resolution (same file, "Prototype: value-refined caller contexts"
section).** A *bounded* intra-edge context update fixes it — not an arbitrary
`step_ctx`. `side_cfg_T_eff_cmp_ctxupd_st` threads a context transition
`fctx_ctx_step` that is the identity on every edge except the two `G`-assignments:
`G := 0` switches `GOther → GZero`, `G := 1` switches `GZero → GPos`. Determinism
matters — the transition must map only the *real* predecessor context and dump any
other into a never-demanded sink; a constant `_ → GZero`/`GPos` makes the demand
solver materialise spurious context copies that re-run the pinning combine and
pollute the keyed slot (diagnosed and fixed during the prototype). Machine-checked
by eval on the real side solver: `fctxu_call4_GZero` (call 4 under `GZero`, not
`GOther`), `fctxu_call8_GPos`, `fctxu_caller_read_G4_exact` / `_G8_exact` (the
observation read of `G` is now `SZero` / `SPos`, exact — so `ENTER_MONO` becomes
provable), `fctxu_fGZero_GH_zero` / `fctxu_fGPos_GH_pos` (`f`@`GZero` gives
`GH = SZero`, `f`@`GPos` gives `SPos`). Dependencies stay static and the RHS
monotone. Still a prototype: soundness of the context-updating generator is not
yet proved, and it is deliberately not generalised beyond this example.

#### Fix A probe (2026-07-02) — narrowing `ENTER_MONO` to `route_read_cmp` is insufficient

Before committing to the `cstep` soundness kernel, the cheaper alternative was
tested: keep the context monovariant and route callee context from the precise
*local* read `route_read_cmp sigma (cl,ctx) = sigma (Inl (cl,ctx))` (the D/G/C
boundary of `ROUTE_A_SWITCHING_COMBINE_MIGRATION.md`), restating `ENTER_MONO` over
that local read instead of the joined `side_env_cmp`. **Refuted by eval** on the
real side solver (monovariant unit-context retain generator, REPL-local, no theory
or kernel changed):

- **Retain local slots are exact only *immediately after* the write.** After
  `G := 0` the local slot is `SZero`; after `G := 1` it is `SPos`.
- **The next `EA_Nop` re-injects the joined `Inr` global slot.** Confirmed
  directly: the retain edge transfer of `EA_Nop` with `local = SZero`,
  `Inr () = SPos` outputs `SZero join SPos = SNonNeg`. Re-joining `Inr` at every
  edge is what makes retain *sound* (the local copy of a global must
  over-approximate other activations' side effects), so it cannot be removed.
- The compiler always places the call node one `EA_Nop` past the assignment, so
  `route_read_cmp` at the call node is `SNonNeg` — **polluted exactly like
  `side_env_cmp`**.
- **Flat probe** (`main: G:=0; f(); G:=1; f()`): call nodes 4/7 both read local
  `G = SNonNeg` (write nodes 3/6 read `SZero`/`SPos`).
- **Nested probe** (`main -> f -> g`, `main:G:=0;f()`, `f:G:=1;g()`,
  `g:GH:=G`): call node 7 (main->f, expected `SZero`) reads `SNonNeg`; call node 4
  (f->g, expected `SPos`) reads `SNonNeg`. Write nodes 6/3 read `SZero`/`SPos`.

Even with a `prep` pin making the *route* single-valued, `ENTER_MONO` still
quantifies the enter store over the polluted observation, so a single routed
context cannot match the varying concrete enter digest. The pollution is
structural: globals live in the per-context flow-insensitive `Inr` slot, and while
that slot joins multiple writes it is `SNonNeg`, and **every** read (local `Inl` or
observation `side_env_cmp`) sees it. The only way to make it exact is to refine the
context so each `Inr` slot holds a single write.

**Conclusion.** In the current `Inl`/`Inr` (local / flow-insensitive-global)
framework, **Fix B / `cstep` context refinement is required** — it is not merely a
precision demonstration. Fix A is closed as insufficient. Next research target: the
**hybrid soundness kernel** for `side_cfg_T_eff_cmp_ctxupd_st` — intra-activation
context updates via `cstep` combined with call-time routing via `ctx_sel` / `route`
(neither existing kernel does both). Kernel not yet implemented.

#### Fix A' probe (2026-07-02) — routing from the local slot alone is subsumed by Fix A

The narrower variant was also tested: change the switching combine to select context
from the local routing state only — `routing = prep cc sc`, `callee_ctx = ec cc ctx
routing` — dropping the `sc join g` join, on the hypothesis that the combine's
`join g` (the flow-insensitive global slot) was the routing pollution source. Keep
global side publication, callee-exit observation, and `side_env_cmp` for soundness.
Implemented example-local (`aprime_combine`, `prep = id`, publication/return on the
full `sc join g`) and run on both programs, retain transfer:

- **Publish transfer** gives `sc = bot` — globals are erased from the local slot, so
  routing from `sc` alone carries no `G` information (routes everything to the seed
  context). This is what real `fctx` uses; there all routing is done by the `prep`
  pin, not the local read.
- **Retain transfer** gives `sc = SNonNeg` at every call site (the retain edge
  transfer re-injects `Inr` at each `EA_Nop`, exactly as in the Fix A probe).
- Therefore `ctx_sel (sc)` cannot distinguish the two call sites: route@4 and
  route@7 both compute `GNonNeg` (flat); route@7 and route@4 both `GNonNeg` (nested
  `main -> f -> g`). `(4,GZero)` / `(7,GPos)` are never reached; the callee collapses
  into one `GNonNeg` slot (`GH = SNonNeg`). All four target checks fail.

The `sc join g` was never the pollution source — `sc` is already polluted upstream by
the edge transfer, so dropping `join g` removes only a redundant second join of the
same `Inr`. **Keeping the `prep` pin** (`fctx_call_state`, which hard-codes `G` per
call site) makes routing exact, but that is artificial — it encodes the answer — and
with the pin Fix A' is identical to the current combine, so the caller observation
stays `SNonNeg` and `ENTER_MONO` is unfixed.

**Fix A' is subsumed by Fix A and fails for the same reason:** the `Inl`/`Inr`
framework offers no clean pre-publication local read to route from. **Proceed only
with the `ctxupd` / `cstep` soundness kernel** — *within the fixed context-keyed
global*; see the writer-re-keying correction below.

#### Writer re-keying (2026-07-02) — the `cstep` conclusion was scoped to a context-keyed global

The Fix A/A' probes and the `cstep` conclusion all assumed `'g = ctx`: one global slot
per context. Under that assumption the two writes `G := 0` / `G := 1` are joined into
`Inr GOther` **at publication** (`fctx_GOther_slot_joins_G` → `SNonNeg`), and no reader
can recover them — so context refinement (`cstep`) is the only lever. Revisiting the
writer key removes that assumption:

- **Re-key writers by definition site** (`'g = def_site`): `G := 0 ↦ Inr d1 = SZero`,
  `G := 1 ↦ Inr d3 = SPos` — separate slots, no join at write time.
- **Read through a reaching-definition digest** `reader_digest v ctx = RD(G, v, ctx)`
  with proper kill/gen: `RD(node 4) = {d1}` (reads `SZero`), `RD(node 7) = {d3}` (reads
  `SPos`; `G := 1` *kills* `d1`). The two call nodes are **distinct program points** in
  one `main` activation, so a flow-sensitive `reader_digest` separates them under one
  call-only context — no `cstep`, no context move.

The earlier "the distinction is flow-sensitivity within one activation, expressible only
by an intra-edge context update" is corrected: it is expressible by a flow-sensitive
reader digest over def-site-keyed writers, which is what Goblint/the paper do. Interproc
soundness needs RD kill/gen across calls (a callee `must_write` kills+gens at the return
site); naive intra RD is unsound for callee-modified globals (`main{G:=0;f();GH:=G},
f{G:=1}` → intra reads `SZero`, concrete `1`). REPL-local this session: the `obs_digest`
COMB split, its `CMP_SOUND` reduction to a compatibility inclusion, and the flat/nested/
callee-writes inclusions are validated (`digest_reader_split_sketch.thy`); nothing
committed, no theory changed.

**Status.** Generalized to a digest interface (kernel proved once over `writer_key` /
`reader_digest` / `compatible`; RD is the first instance; mod-count / thread-mode /
locksets are further instances). Full design, obligations, and migration sequence in
`DIGEST_INDEXED_READER_MIGRATION.md`. `cstep` kept as a fallback for precision no digest
can express.

**Update (2026-07-10) — seeded-clean bridge, transport enabler landed.** The R_read
seeded-clean spine (Goblint-faithful enter/context/combine, `M2_DGC_RREAD_BOUNDARY_MIGRATION.md`
§13–16) sidesteps this problem's `Obs`-read obstruction by concluding at the local
slot. Its solver-to-kernel bridge now has all structural pieces closed, batch-green:
`part_post_solution_cmp_seed_st_to_abs_eff` (`Exec_Cmp_Bridge`, the `st`→`abs`
transport of the run's post-solution), `seeded_clean_edge_bound` (`EDGE_BOUND` from any
post-solution), `seeded_clean_seed_bound` (the order half of `ENTRY`/`PROC_ENTRY`:
`frame_seed ctx ≤ sg (Inl (v, ctx))` at every reached frame-entry), plus the already-
generic `rehydrate_caller_continuation_sound` (COMB) and head-digest `DG_*`. The
last obligation — `ENTER_MONO` over `route_read_cmp` — is now **discharged as a
theorem** (`Exec_Sign_Seed_EnterMono.thy`, batch-green isolated, no `sorry`;
`M2_DGC_RREAD_BOUNDARY_MIGRATION.md` §17). It factors into a domain-generic lift
`enter_mono_proj_lift` (per-projection γ-exactness ⟹ the routing equation, reusable at
any `sound_domain`), the sign lemma `point_sign_gamma_exact`, and the run-specific
**point-routing** premise `seed_slots_point` (the seeded-clean generator keeps each
call-site routing slot γ-exact). `seed_enter_mono_call_sites` is the resulting routing
equation at the two call sites — the value-keyed split proved, where the Obs read merged
them (`non_point_sign_splits` formalises the Obs failure). Point-routing is the genuinely-
required extra invariant, unprovable from soundness alone but established here by the
Goblint-faithful seed + clean transfer. With it, all obligations of
`clean_ctx_collect_rread` are met on the seeded-clean spine.

**Update (2026-07-11b) — entry-side reductions closed; residual is a trace-digest gap.**
`Seeded_Clean_Ctx_Collect.thy` closes every per-obligation reduction of the seeded-clean
kernel generically: `seeded_clean_edge_bound` (non-enter `EDGE_BOUND`, hoisted from Sign),
`seeded_clean_seed_bound` (seed order-half of `ENTRY`/`PROC_ENTRY`), `seeded_clean_comb_bound`
(`COMB`), and `point_digest.enter_mono_kernel` — the **ENTER_MONO connection** from the
point-routing equation, so `ENTER_MONO` is no longer a raw premise. The final
`cfg_collect_ctx ⊆ γ` is blocked by one genuine gap: the seeded generator seeds callee
entries at the *callee* context, but every `hd`-based trace digest gives a callee-entry-
reaching trace the *caller* context (it is reached via the `edge` rule on `EA_Enter`), so the
enter-edge `EDGE_BOUND` reduces to `tf_enter(caller) = ⊥` (false). The retain spine avoids
this by using the transfer at enter; the clean spine replaces it with the seed. Needs a
context-switching R_read trace digest (activation-separated collecting semantics) — a
structural change, not a lemma. Detail: `M2_DGC_RREAD_BOUNDARY_MIGRATION.md` §22.

**Update (2026-07-11) — `COMB` reduced to an abstract bound.** The return combine is no
longer a raw semantic premise on the clean R_read spine. `combine_abs_bound_sound` +
`clean_{cfg,ctx}_collect_rread_bound` / `…_head_bound` (`Clean_RRead_Sound.thy`) replace
the `<s|t> ∈ ⟦sg (Inl ret)⟧` premise with the order-theoretic
`⟨caller|callee⟩ ≤ sg (Inl ret)` — the R_read analogue of the retain spine's
`combine_read_cmp_le`. Interval instantiates all three (`Exec_Ivl_Cmp_Seed_Sound.thy`),
matching `ivl_combine_rehydrate`'s `combine_abs_st` return. The recursive interval
example now applies the vendored generic post-fixpoint (`rdiv_rehyd_post_fixpoint`) and
reads `EDGE_BOUND`/`COMB_BOUND`/seed bound uniformly off it (`rdiv_rehyd_rhs_dominated`,
`rdiv_rehyd_main_return_sound`). Full detail: `M2_DGC_RREAD_BOUNDARY_MIGRATION.md` §21.
The one remaining step — the seeded-context routing + `st`→`abs` transport for interval
(built for Sign, §16–18) — is deliberately left as marked-incomplete generic closure.

**Update (2026-07-11c) — activation semantics closes the trace-digest gap; surfaces a
seed-locals obstruction.** The 2026-07-11b trace-digest gap is resolved structurally:
`CFG_Collect_Activation.thy` adds the call-only activation witness `trace_witness_act`
(context constant on ordinary edges, routed at `EA_Enter`, resumed at combine; forgets to
`trace_witness`), and `Seeded_Activation_Sound.thy` proves the generic
`seeded_activation_collecting_sound` — `cfg_collect_ctx_act ⊆ γ` from a seeded
post-solution + `ENTRY_G`/`PROC_ENTRY_G`/`SEED_G`/`COMB_BOUND`, with `EDGE`/`COMB`
discharged off the closed reductions and `SEED_G` reduced by `seeded_activation_seed` to
the covering invariant `enter_state s ∈ ⟦frame_seed (enterc kc s)⟧`. Instantiating it for
the *shipped* Sign/Interval runs is **blocked by a genuine domain gap**: the globals-only
seed `restrict_global` leaves callee-entry locals at `⊥`, so (since `gamma_state` is total
and `gamma_ivl ⊥ = {}`) the callee-entry slot concretises to `{}` and `SEED_G` is
unsatisfiable — the activation witness *removes the vacuity* by which the old
`head_digest` path hid this at callee entries. Needs a locals-covering seed
(`restrict_global c ⊔ zero_locals`) + re-solve — small but genuinely new domain theory.
Detail: `ACTIVATION_SEED_LOCALS_OBSTRUCTION.md`; design basis:
`ACTIVATION_SEMANTICS_MODEL_DECISION.md`.

**Update (2026-07-11d) — covering seed + executable seed correspondence landed; residual
is a dependency-closure reachability wiring.** `cover_seed` closes the locals gap
generically (`enter_state s ∈ ⟦cover_seed pz fs kc⟧` from globals-\<gamma> + `0 ∈ γ pz`);
`seeded_activation_collecting_sound_cover` packages it. The executable
`cover_seed_st` + `fun_of_st_cover_seed_st` give the `st`→`abs` seed correspondence, and
the `vars` obligations (`cov_edge`/`cov_frame`) are conditioned on an inhabited source so
they are instantiable. Sign and Interval instances proved. The shipped-run end-to-end
`cfg_collect_ctx_act ⊆ γ` is blocked only by connecting the activation callee context
`enterc kc s` to the generator's `restrict_global_st (sg (Inl (cc, kc)))` (point routing)
and discharging the reached callee context from backward dependency closure of the query
unknown (`part_post_solution` gives `dep_L`-closure; the return node's combine reads the
callee exit, whose body deps reach the callee entry) — a dependency-closure-backed proof,
not new solver theory. Full status + next slice: `ACTIVATION_MIGRATION_SUMMARY.md`;
canonical-foundation rationale: `ACTIVATION_CANONICAL_FOUNDATION.md`.

**Update (2026-07-11e) — recursive-return obstruction is a witness-calculus limitation.**
Dependency reachability holds (no counterexample: `dep_aux` ignores `Side` targets, so the
seeded callee entry is reached through the combine's `QueryL` of the callee exit;
`Seeded_Activation_Reach.thy` proves the backward `dep_L` bridges
`intra_pred_in_vars` / `combine_dep_in_vars` and the enter-edge
`callee_entry_dep_L_empty`). The remaining failure is the shape of the seeded witness
interface: `trace_witness_act_hd_initial` proves every activation-trace head lies in
`S ∪ enter_state ` S`, while a recursive callee activation is available as a suffix headed
by `enter_state (last tau)` from the caller execution.

`Activation_Witness_From.thy` repairs the witness layer with `twf`, a from-node witness
whose start rule seeds any store at any program point. The lemma
`twf_combine_reuses_callee_suffix` states the needed reuse principle explicitly: combine
can consume a callee suffix witness beginning at the frame entry, headed by the
caller-derived entry store. The returning fragment `twfr` supports the query-anchored
theorem `twfr_sound_seeded`, which derives the required `cov_edge` / `cov_frame`
obligations from the backward dependency contract and reuses the existing seeded edge,
seed, combine, and cover-seed facts.

The active architecture therefore keeps `trace_witness`, `trace_witness_act`,
`cfg_collect`, CFG definitions, and solver interfaces fixed. The activation-indexed
store-set collecting experiment has been removed from the active session graph. Design
note: `docs/WITNESS_CALCULUS_REPAIR.md`.

**Update (2026-07-11f) — generic reachability tasks closed; residual is one executable
transport bridge.** The three generic deliverables the dependency-reachability goal asks
for are proved and I/Q-clean:

* **Unified dependency-reachability theorem (task 1).** `act_reach` (`Seeded_Activation_Reach.thy`)
  folds the intra and combine activation dependency steps into one relation;
  `act_reach_in_vars` proves every unknown reachable from a solved query is solved, by one
  induction discharging each step from `part_post_solution`'s backward `dep_L` closure — no
  forward-closure invariant. The `enter` case is covered by combine-then-body composition
  (`combine_reaches_frame_in_vars`), since `dep_aux` drops `Side` targets so the callee
  entry is reached backward through the exit.
* **Routing equality via point-exactness (task 3).** `point_route_eq` (`Seed_EnterMono_Lift.thy`,
  in the `point_digest` locale) lifts `enter_mono_point` to the global region:
  `restrict_global (\<lambda>x. decode (s x)) = restrict_global (sg (Inl (cl, ctx)))` on a
  point-exact inhabited caller slot — the concrete callee-context routing equals the
  abstract-slot routing.
* **`cov_edge` / `cov_frame` derived (task 4).** `cov_edge_from_query` / `cov_frame_from_query`
  expose the two run-level `vars` obligations as derivations from `(query) \<in> vars` plus
  dependency closure, not assumptions. `twfr_sound_seeded` threads them along the witness.

The remaining piece (tasks 5–6, the shipped `rdiv` interval run as a direct
`cfg_collect_ctx_act \<subseteq> \<gamma>` / `twfr_sound_seeded` instance) is blocked only by the
executable→abstract transport gap of `WITNESS_CALCULUS_REPAIR.md` §Remaining:
`ivl_combine_rehydrate` computes the callee context from the executable caller slot
(`ivl st`), while the abstract theorem works over `fun_of_st` images, and the context key
cannot be reconstructed from the abstract value alone. This is a concrete transport lemma,
not missing generic theory.

**Update (2026-07-11g) — enter reachability made first-class; ENTER_MONO/SEED_glob wired
generically.** Two further generic closures, I/Q-clean:

* **Enter as a first-class `act_reach` chain (task 2).** `act_reach_intra_rtrancl` lifts an
  `intra_pred_rel` rtrancl to `act_reach` intra steps at a fixed context; `act_reach_enter`
  packages the enter obligation as *one* `act_reach` derivation (return node → combine step
  to the routed callee exit → intra body chain to the callee entry) rather than an external
  chaining of bridge lemmas. The three activation rules are now covered by a single
  reachability relation with an explicit enter consequence.
* **SEED_glob reduced to point-exactness (`seed_glob_from_point_route`, `point_digest`).**
  With the pointwise-decode global routing `enterc kc s = restrict_global (\<lambda>x. decode (s x))`,
  the seed obligation `s xx \<in> gamma (enterc kc s xx)` follows from caller-store soundness
  plus point-exactness of the caller slot's globals (via `point_route_eq`). This wires the
  routing equation to the kernel obligation — the first of the two "genuinely missing generic
  results" flagged in `Example_Interval_Recursion_Rehydrate.thy` (the ENTER_MONO
  kernel-connection), now closed with no program-specialised proof.

What is left for the shipped-run instance is genuinely a **run contract**, not missing
generic theory: (a) the ENTRY / PROC_ENTRY \<gamma>-cover (`s \<in> S \<Longrightarrow> s \<in> \<lbrakk>seed at entry\<rbrakk>`),
which depends on the run's initial-state set and its seed — the analogue of Sign's
`seed_clean_sound_on_prog2`, supplied per run; and (b) the `ivl st`→abstract match of the
concrete `enterc` to the generator's `ivl_combine_rehydrate_abs` routing key, plus
eval-checked point-exactness of the reached slots and `(query) \<in> vars`.

**Update (2026-07-11h) — the `rdiv` run contract is being discharged in
`Example_Rdiv_Twfr_Sound.thy` (keys stay `ivl st`, no `fun_of_st` inverse).** Landed and
I/Q-clean:

* `rdiv_enterc kc s = ivl_abs_route_st (\<lambda>x. ivl_of_int (s x))` — the witness routing keeps
  the entered store's globals and abstracts them to an ∗executable∗ `ivl st` key.
* `rdiv_route_correspondence` — on an inhabited point-exact caller slot this equals
  `ivl_abs_route_st (rdiv_sg (Inl (cl, kc)))`, the ∗same∗ key the generator's
  `ivl_combine_rehydrate_abs` reads (proved from `point_ivl_gamma_exact`, no `fun_of_st`
  inverse, no key reconstruction from abstract values).
* `dep_aux_ivl_combine_rehydrate_abs` — the combine tree depends exactly on the caller call
  node and the routed callee exit.
* `rdiv_q_edge` / `rdiv_q_caller` / `rdiv_q_callee` — three `twfr_sound_seeded` `q_*`
  obligations discharged from `rdiv_rehyd_cover_abs_post_fixpoint` via the generic
  `q_edge_from_pp` / `combine_edge_dep_in_vars`, no manual context enumeration.
* `rdiv_comb_bound` — COMB_BOUND from `seeded_clean_comb_bound` +
  `traverse_ivl_combine_rehydrate_abs` + the routing correspondence.

Remaining to close the end-to-end `twfr_sound_seeded` instance: SEED_glob (the
`fun_of_st ∘ st_of_abs` transport of the routed-key seed content), `q_frame` (the callee
body's `intra_pred_rel` chain to the frame entry), the point-exactness contract
(inhabited caller slot ⟹ point on globals, one `eval` over the finite solved slots),
`(cfg_exit rdiv_cfg, bot) \<in> vars` (`eval`), a concrete `twfr` witness reaching node 11
with `G = [3,3]`, and the final over-approximation theorem. The generic scaffolding and
the routing bridge are complete; what remains is the run-specific assembly.

**Update (2026-07-11i) — the full-slot `twfr_sound_seeded` conclusion is VACUOUS for
seeded-clean runs; the non-vacuous soundness is per-coordinate.** Discovered while wiring
the `rdiv` instance. Verified by `eval` + definitions:

* The concrete store universe is `vname \<Rightarrow> int` over ALL names; `is_global x`
  holds for infinitely many (`x = [] \<or> hd x = CHR ''G''`), and
  `gamma_state \<sigma> = {s. \<forall>x. s x \<in> gamma (\<sigma> x)}` quantifies over every one.
* At the shipped run's return node 11 (main context `bot`) the local slot has
  `G = [3,3]` but any UNMENTIONED global (e.g. `''GG''`) sits at
  `Ivl PlusInf MinInf = \<bottom>`, whose `gamma_ivl` is `{}` (`gamma_ivl_bot`). The
  rehydrating combine takes globals from the callee exit, whose local slot never touched
  `GG`, so `GG` stays `\<bottom>`. Hence `\<lbrakk>sg (Inl (11, bot))\<rbrakk> = {}`.
* Therefore `twfr_sound_seeded`'s conclusion `last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>`
  has an EMPTY right side here, and its premise `hd tr \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk>`
  is likewise unsatisfiable (entry `Inl` slot is empty too — globals live in the `Inr`
  slot in the R_read architecture, not in `Inl`). A "successful" instantiation would be
  the vacuous empty collecting set the autoformalization audit forbids.
* This is ARCHITECTURAL, not specific to `rdiv`: the whole activation / twfr full-
  `gamma_state` spine (`seeded_activation_collecting_sound`, `activation_trace_sound`) is
  vacuous on any run seeded by `restrict_global` (unmentioned globals `\<bottom>`). No
  combined concretization reading globals from `Inr` exists.
* The codebase's own non-vacuous headline (`reaching_global_read_sound`) already reads
  PER-VARIABLE: `(last tr) x \<in> gamma (env v x)`. The honest non-vacuous `rdiv`
  deliverable is the same shape at the twfr level, projected to `G`:
  `(last tr) ''G'' \<in> gamma_ivl (sg (Inl (11, bot)) ''G'') = gamma_ivl [3,3]`, with
  `3 \<in> [3,3]` — non-vacuous, shipped run unchanged. A fully generic per-coordinate
  twfr theorem does not close (intra transfers couple coordinates); the `G`-coordinate
  closes for `rdiv` because every `rdiv` edge's `G`-output reads only `G`.

**Update (2026-07-11j) — Phase 1 closed: per-coordinate `rdiv` soundness + explicit
witness, full batch-green.**  `Example_Rdiv_Twfr_Sound.thy` now carries the end-to-end,
non-vacuous result (shipped run unchanged, keys stay `ivl st`, no `fun_of_st` inverse):

* `rdiv_slot_11_full_gamma_empty` — the full-store slot at node 11 is `{}` (unmentioned
  global `''GG''` at bot); the mechanised proof that a full-slot conclusion would be vacuous.
* `rdiv_analysis_G_sound_at_main_cont` — `3 : gamma (rdiv_sg (Inl (11, bot)) ''G'')`
  (`= gamma_ivl [3,3]`), the per-coordinate soundness.
* An explicit `twfr` witness of the shipped `rdiv_cfg`, built bottom-up: `wit_f3` (base,
  else branch), `wit_frec` (generic recursive level, `combine` at `(3,7,4)`),
  `wit_f0`/`wit_f1`/`wit_f2` chained, `wit_main` (top call spliced at `(10,7,11)`).  Stores
  are `gk k = (%_. 0)(''G'' := k)`; `enter_state (gk k) = gk k` and `<gk a|gk b> = gk b`.
* `rdiv_twfr_witness_reaches_main_cont` — the witness reaches node 11 (ctx bot) with
  `last tr ''G'' = 3`, and is non-empty.
* `rdiv_witness_G_over_approximated` — the end-to-end theorem: a concrete `twfr` run reaches
  node 11 whose terminal `G` lies in the analysis slot `[3,3]`.  Non-vacuous by the witness.

The full-slot `twfr_sound_seeded` instantiation (its `q_frame` / `SEED_glob` /
point-exactness premises) was left undischarged deliberately: it is provably vacuous here, so
discharging it would produce the empty collecting set the audit forbids.  The generic
`twfr_sound_seeded` `SEED_glob` premise was still tightened (conditioned on `(u,kc) : vars`)
as a standalone improvement.

**Update (2026-07-12) — twfr migration complete; canonical spine.**  The `rdiv` proof was
refactored into reusable infrastructure and every shipped executable seeded example moved
onto the witness spine:

* `Twfr_Reach_Read.thy` — the generic `twfr_reach_read` reach-and-read combinator plus the
  domain-agnostic single-global concrete store family `gk` and its `edge_step` lemmas.
* `Ivl_Twfr_Common.thy` — the run-independent interval seeded-clean dischargers
  (`ivl_enterc`, `ivl_route_correspondence`, `dep_aux_ivl_combine_rehydrate_abs`,
  `ivl_q_caller`, `ivl_q_callee`, `ivl_comb_bound`), generic in the graph + post-fixpoint.
* Migrated examples with concrete witness + per-coordinate soundness: `iseed`
  (`iseed_wit_{lo,hi}_sound`), `dseed` (`dseed_wit_{lo,hi}_sound`), `rhyd`
  (`rhyd_wit_readback_sound`, a witness across a return combine), sign `seed_enter`
  (`seed_wit_sound`).  `rdiv` now routes its end-to-end theorem through `twfr_reach_read`
  and drops the dead premise-discharge cluster.

No Sign-specific dischargers were needed: a callee-exit query crosses no return combine, so
`Twfr_Reach_Read` + the `gk` kit suffice across Sign and Interval.  Migration summary table
and the canonical-path statement live in `docs/WITNESS_CALCULUS_REPAIR.md`.

---

## Where to start

**Session plan:** `docs/NEXT_STEPS.md`.

1. `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`
2. `docs/PROOF_OVERVIEW.md` — current theorem names
3. `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` — `trace_analysis_sound`, `reaching_global_read_sound`
4. `src/Analysis/Domains/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`
5. Open TD hyp: P1 (`side_cfg_solve_dom_eff`) only
6. MCP-first workflow: `AGENTS.md`
