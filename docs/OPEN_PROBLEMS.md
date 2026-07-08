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
| P12 | Per-depth call contexts for recursion | `Example_Interval_Recursion_Digest.thy`, `Example_Interval_Recursion_Origin.thy` | The value-digest generator keys global *writes* by the write-point digest, but a recursive self-*call* is not split per depth, so the digest solve climbs `G` unbounded and breaks down under `by eval`. `Example_Interval_Recursion_Origin` tests per-origin widening instead: it terminates and `eval`s, but `G` still widens to top (`rec_per_origin_matches_monovariant`) — the transfer **reads** `collapse_origins`, re-merging the recursive edge's own climbing cell, so the monotone self-loop survives the origin split. Precision needs origin-separated *reads* (a relational, per-origin transfer), not just widening | A discipline that keeps recursion-depth reads separated, recovering full precision executably |

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

- `fctx_call4_only_GOther` / `fctx_call7_only_GOther`: both call nodes 4 and 7
  live under the single caller context `GOther` (they are interior points of one
  `main` activation; context changes only at call boundaries).
- `fctx_GOther_slot_joins_G`: the keyed slot `Inr GOther` joins `main`'s `G := 0`
  and `G := 1` to `SNonNeg` (globals are flow-insensitive per context).
- `fctx_caller_read_G_imprecise` / `_imprecise7`: `side_env_cmp` adds that global
  summand, pinning the observation of `G` at both call nodes to `SNonNeg`.

Retain sharpens only the routing read `route_read_cmp` (the local slot), not the
global summand `side_env_cmp` adds. Every candidate call-boundary scheme
(call-site-refined, call-string, entry-store) leaves `main` under one context, so
`Inr (that context)` joins both writes. The needed `G = 0` at 4 vs `G = 1` at 7
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
`GOther`), `fctxu_call7_GPos`, `fctxu_caller_read_G4_exact` / `_G7_exact` (the
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

---

## Where to start

**Session plan:** `docs/NEXT_STEPS.md`.

1. `rg -n '^\s*sorry' src/ | rg -v '\.thy~'`
2. `docs/PROOF_OVERVIEW.md` — current theorem names
3. `src/Formalization/Pipeline/Trace_Analysis_Sound.thy` — `trace_analysis_sound`, `reaching_global_read_sound`
4. `src/Analysis/Domains/Sign_Side_Soundness.thy` — `side_sign_analysis_sound`
5. Open TD hyp: P1 (`side_cfg_solve_dom_eff`) only
6. MCP-first workflow: `AGENTS.md`
