# Procedures / Function Calls — Extension Plan

Scoped extension of the verified pipeline to interprocedural analysis (function
calls), triggered by Seidl's scope question ("warum keine Prozeduren, warum keine
Seiten-Effekte?"). Goal: a **thesis-scoped** but non-trivial interprocedural
analysis — not state-of-the-art context-sensitivity, but real interprocedural
information flow with simplifying assumptions on `enter`/`combine`.

KB companion: `~/git/voblint-formalization-kb/wiki/research/procedures-extension-feasibility.md`.

> **⚠️ Read §9 first — it supersedes §1–§8 for the thesis scope.** Working the proofs
> through (§9) showed the monovariant, flow-sensitive-globals scope needs **plain
> `TD_plain` + a binary `combine` edge**, *not* the side-effecting `TD_side` solver.
> The genuinely-new proof is **`L-sound'` / `is_post_fixpoint_ip`** (§9.x), **not**
> `post_fixpoint_sound_side`. §1–§8 (the `TD_side`/`Side`/`post_fixpoint_sound_side`
> route, incl. the §6 core-lemma table and SO1 note) remain accurate only for the
> **future flow-insensitive-globals / context-sensitive axis**. For the recommended
> path, go straight to §9.

---

## 1. What "enter/exit" should actually be

The right target is the **`enter` / `combine` pair**, not "enter/exit":

- `enter`  : call-site state → callee-entry state (project/bind on the call edge).
- `combine`: (caller pre-call state, callee summary) → return-site state (restore
  caller-private data, absorb callee effects on the return edge).

These are exactly Voblint's `enter`/`combine` callbacks (`constraints.ml`,
`FromSpec` functor) and the Sharir–Pnueli functional-summary transfer pair. "exit"
is just the callee's exit program point — it is not a transfer function. So:
**target = `enter`/`combine`, with the callee exit unknown as the summary carrier.**

---

## 2. Why a plain (read-only) CFG extension is not enough

The combine is intrinsically **binary**: it needs the caller's pre-call state *and*
the callee's exit summary. The current constraint system (`Constraint_System.thy`,
`rhs`) is **unary per edge** — each predecessor edge reads exactly one source node:

```
rhs g tf join bot s0 env v = join_over { apply_tf a (env u) | (u,a,v) ∈ edges g } (+ s0 at entry)
```

Three ways to deliver the second operand to `combine`:

| Route | Mechanism | Verdict |
|---|---|---|
| Two ordinary CFG edges into the return site (locals from call site, globals from callee exit) | predecessor join reconstructs the product | **Fails.** Join needs ⊥-padding on the don't-care half → γ collapses to ∅; ⊤-padding → join gives ⊤. The pointwise *join* cannot reconstruct a (locals × globals) product. Would need a *meet*, which `rhs` does not do. |
| New binary edge action `EA_Combine` reading two sources | extend `edge_action`, `apply_tf`, `rhs`; re-prove `rhs_mono` + `post_fixpoint_sound` | Possible but invasive: breaks the uniform unary `rhs` and every lemma built on it. |
| **Callee summary as a global unknown; return site queries it** | side-effecting constraint system (`Basics_side`): return-site RHS issues `QueryL` (caller pre-call) then `QueryG` (callee summary) then `combine` | **Recommended.** The two-source problem dissolves: the combine is *unary in the CFG* (reads its call-site predecessor) and pulls the summary via a global query. This is precisely the framework the vendor already verified. |

The side-effecting route is also what makes the analysis **non-trivial** (Seidl's
real point): each call site *contributes* (`Side`) the entered state to the
callee's entry summary global, so the callee is analysed once over the **join of
all calling contexts** — context-insensitive interprocedural merge with widening
on the global summaries. With a single (unified) store and no side-effects, a call
is provably equivalent to inlining (non-recursive) or to `SKIP` (recursive) — exactly
the "mainstream" case Seidl flagged.

---

## 3. Solver finding (corrects the KB note)

| Solver | Imports | Side-effecting? | Final correctness |
|---|---|---|---|
| `TD_plain.thy` | `Basics` | no | post-fixpoint on `reach` |
| `TD_plain_s.thy` | `Basics` | **no** (stable-set optimization only) | `partial_correctness`: `part_solution T x σ (reach T σ x)` |
| `TD_side.thy` | `Basics_side` | **yes** | `theorem partial_solution` (line ~1939), via `eq_equal_sides_subsumed` |

The earlier feasibility note called `TD_plain_s` a "plain-TD variant with side
effects" — **wrong**. The side-effecting solver is `TD_side.thy`. The bridge for
procedures must target `TD_side`, not `TD_plain_s`.

`TD_side` interface to build on (`Basics_side.thy`):

- Bipartite unknowns `'x + 'g`: `Inl x` = locals (flow-sensitive program points),
  `Inr g` = globals (flow-insensitive sinks).
- `strategy_tree = Answer 'd | QueryL 'x f | QueryG 'g f | Side 'g 'd t`.
- `traverse_rhs` computes a node's local value (ignores `Side`); `sides_of_rhs`
  accumulates the per-global join of `Side` contributions.
- `part_solution T x σ vars` ≡ for all `u ∈ vars`:
  `eq T u σ = σ (Inl u)` (exact local fixpoint) **and** `sides_of_rhs (T u) σ ≤ σ`
  (every global contribution subsumed).

That two-part condition *is* the side-effecting post-fixpoint the pipeline bridge
must consume. **The solver is already verified — the thesis re-proves nothing here.**

---

## 4. Simplifying assumptions (what makes it thesis-scoped)

| # | Assumption | Effect | SOTA gap |
|---|---|---|---|
| S1 | **No parameters, no return values.** Communication only through globals. | `enter`/`combine` reduce to projections (keep globals / restore locals). Kills parameter-aliasing soundness. | SOTA passes params + returns. |
| S2 | **Monovariant (context-insensitive).** One entry + one exit summary per procedure. | Interprocedural merge = a single join over call sites. No context machinery. | SOTA: call-strings / functional / Context Gas (P4). |
| S3 | **Recursion allowed — handled by the TD fixpoint for free.** | No special-casing; recursion = a cycle through the summary globals. Narrative win. | none (this is a feature, not a gap). |
| S4 | **Local/global variable split.** Globals cross call boundaries; locals are caller-private and untouched by callees. | Makes the analysis non-trivial (callee affects caller via globals); matches FM 2026 §2 and Voblint. | none. |

S1+S2 are the scope cuts. S3+S4 are kept precisely so the result is not the trivial
inlining case. Net target: **monovariant, global-effect-only, recursion-tolerant
interprocedural analysis** over the verified side-effecting solver.

---

## 5. Layered plan (de-risked)

### Stage A — unified store, plain TD (guaranteed deliverable, ~2 weeks)

Procedures with a single global store, `enter = combine = id`, return edge = `EA_Nop`.
Whole-program interprocedural CFG; **`Constraint_System.thy` and
`post_fixpoint_sound` unchanged** — only a bigger CFG. Sound but boring (= inlining).
Ships as the safety net and as the worked example that "procedures compile to a CFG".

### Stage B — monovariant global-effect via `TD_side` (the real target, ~6–8 weeks)

S1–S4. Callee entry/exit summaries are globals; call edge `Side`s the entered globals
to the entry summary; return site queries the exit summary and combines. This is the
stage that answers Seidl. The new bridge `post_fixpoint_sound_side` is the hard part.

### Stage C — parameters / context-sensitivity (future work, out of thesis scope)

Param binding + return values (drop S1); call-string or Context-Gas context-sensitivity
(drop S2; cite P4). Acknowledge explicitly; do not attempt within the thesis timeline.

---

## 6. Core lemmas to prove

Mapped onto the existing chain. **R** = reuse as-is, **R'** = restate over the
extended object (mechanical), **N** = genuinely new proof.

### Semantics layer

| ID | Statement | Kind | Notes |
|---|---|---|---|
| SE1 | `com` + `Call pname`; `program = pname ⇒ com option`; store split locals⊎globals | R' | extend `IMP2_Syntax.thy` |
| SE2 | program-relative `small_step` with call stack; `PCall`/`PReturn` rules realise `enter`/`combine` | R' | re-prove `small_step_deterministic` + the `star_*` inversion lemmas (`IMP2_SmallStep.thy`) |
| SE3 | interprocedural collecting semantics (reachable-state set over the whole-program CFG) | R' | extend `cfg_collect` / `cfg_collect_paths` |
| **SE4** | **monovariant merge soundness**: the single callee-entry summary (join over all call sites) over-approximates every individual calling context | **N** | the heart of interprocedural soundness; the one genuinely new semantic argument |

### CFG / constraint layer

| ID | Statement | Kind | Notes |
|---|---|---|---|
| CE1 | `compile_prog :: program ⇒ cfg` wiring `enter`/`combine`/`Side` edges; freshness, finiteness, entry≠exit over the whole program | R' | generalise `compile_*` family (`IMP2_to_CFG.thy`); finiteness needs *finitely many procedures* |
| CE2 | side-effecting RHS builder `make_rhs_tree_side` emitting `QueryL`/`QueryG`/`Side` | R' | new `Constraint_System_Side.thy`; mirror `apply_tf`/`rhs` |
| CE3 | **`rhs_side_mono`** — monotonicity of the side-effecting RHS | R' → N | analogue of `rhs_mono`; harder because of `Side`/`QueryG`, but structurally parallel |
| **CE4** | **`post_fixpoint_sound_side`** — `part_solution`/`eq_equal_sides_subsumed` ⟹ over-approximation of the interprocedural collecting semantics | **N** | THE big new bridge; subsumes local-edge soundness (as today) + `enter`/`combine`/`Side` soundness. ~2–3× `post_fixpoint_sound`. |

### Solver layer

| ID | Statement | Kind | Notes |
|---|---|---|---|
| SO1 | `make_rhs_tree_side` well-formed; `TD_side.solve_dom` ⟹ `part_solution` instantiates CE4's premise | R' | mirror of `td_analyse_collect_sound_at`; solver itself already verified |

**P2 fold-in (do not copy the `cfg_entry`-rooted shape).** *(Bipartite-`'x+'g` /
`make_rhs_tree_side` form below applies to the `TD_side` future axis. For the §9
plain-TD route, the same P2 fix lands on `make_rhs_tree_ip` / `td_analyse_ip` — see
§9.)* The current pipeline's
`td_cfg_in_reach` premise is *false* (see "P2 finding" in `OPEN_PROBLEMS.md`): the
forward RHS rooted at `cfg_entry` reaches only the entry. SO1 must adopt **Fix B
(per-pp solve)** — `td_analyse_side c … v ≡ lookup_bot (Interp_solve_side (make_rhs_tree_side …) v) v`
— so the local in-reach premise is `reach.base` (trivially `v ∈ reach … v`). Note
the in-reach obligation widens over the bipartite `'x + 'g` unknown set: **global
summary unknowns are populated by `Side`, not by CFG predecessor edges**, so their
coverage is a *data-dependency* fact threaded through CE4, not a CFG side condition.
Budget this into CE4; SO1's "solver already verified" covers the solver, not the
pipeline's discharge of in-reach.

### Pipeline / domain layer

| ID | Statement | Kind | Notes |
|---|---|---|---|
| PD1 | `enter`/`combine` transfer soundness for sign + interval (analogue of `domain_transfer_sound`) | R' | small under S1: enter = project-to-globals, combine = (caller locals, callee globals) |
| PD2 | top-level `pipeline_sound_prog` assembling CE4 + SO1 + PD1 | R' | mirror of `pipeline_invariant_sound` / `pipeline_sound_path` |

**Genuinely new mathematics: SE4 and CE4.** Everything else is structural re-proof
over a bigger object or direct reuse. CE3 sits in between (parallel to `rhs_mono`
but with the side-effecting tree).

---

## 7. Concrete file changes

New:

```
src/IMP2/Program.thy                 -- program = pname ⇒ com option; well-formedness
src/Equations/Constraint_System_Side.thy        -- side-effecting RHS + rhs_side_mono (CE2, CE3)
src/Equations/Constraint_System_Side_Sound.thy   -- post_fixpoint_sound_side (CE4)
src/Solver/TD_Side_Interface.thy     -- bridge to vendor TD_side.solve_dom (SO1)
src/Pipeline/Pipeline_Side.thy       -- pipeline_sound_prog (PD2)
```

Changed:

```
src/IMP2/IMP2_Syntax.thy     -- + Call pname; type pname; local/global vname tagging  (SE1)
src/IMP2/IMP2_SmallStep.thy  -- program-relative step + call stack; re-prove inversions (SE2)
src/CFG/IMP2_to_CFG.thy      -- compile_prog; whole-program freshness/finiteness        (CE1)
src/CFG/Collecting/*         -- interprocedural collecting semantics                    (SE3, SE4)
src/Domains/{Sign,Interval}_Domain.thy -- enter/combine instances                       (PD1)
```

Unchanged (key reuse): `TD_plain.thy` path stays for Stage A; `TD_side.thy` vendor
solver consumed as-is for Stage B.

---

## 8. Risks

- **CE4 is the schedule risk.** If `post_fixpoint_sound_side` over-runs, Stage A is
  the fallback deliverable (real, sound, shippable; just not the impressive answer).
- **Store split (S4) touches every existing tf-soundness lemma** unless globals are
  modelled as a disjoint `vname` subset that the existing pointwise `'a abs_state =
  vname ⇒ 'a` already covers — preferred, keeps `domain_transfer_sound` reusable.
- **NASA FM 2026 overlap.** Stage B's solver layer is the Tilscher–Graß–Schwarz–Seidl
  artifact. Coordinate scope/attribution with Alex before committing (see KB
  `meetings/2026-06-01-meeting4-prep` §6).

---

## 9. Exact lemmas, hand-proofs, and examples

This section pins down the Stage B mathematics precisely enough to start writing
`.thy` files, with informal correctness arguments for every non-trivial claim.

**Design refinement up front (important).** Working the proofs through shows that
the *monovariant, flow-sensitive-globals* scope (S1–S4) does **not** need the
side-effecting solver. It needs exactly one new ingredient over the current plain
pipeline: a **binary `combine` edge**. The merge at procedure entry is just an
ordinary predecessor join; recursion is just a cycle the plain TD fixpoint already
handles. `TD_side`/`Side` becomes necessary only when globals are made
*flow-insensitive sinks* (written from anywhere, à la Voblint) or when contexts are
created dynamically (context-sensitivity). See §9.7. The plan below is therefore
stated for the **plain-TD + binary-combine** route, which is strictly lower-risk
than the `post_fixpoint_sound_side` route in §6 and keeps the verified `TD_plain`.

### 9.1 Precise semantic model

Fix a program partition `is_global :: vname ⇒ bool` (globals `G`, locals `L`,
disjoint, `L ∪ G = vname`). A program is `π :: pname ⇀ com` with `finite (dom π)`;
`com` gains `Call pname`.

```isabelle
definition enter :: "store ⇒ store" where
  "enter s = (λx. if is_global x then s x else 0)"          (* globals pass in; locals reset *)

definition combine :: "store ⇒ store ⇒ store" where
  "combine s t = (λx. if is_global x then t x else s x)"     (* callee globals; caller locals *)
```

Big-step, program-relative (`enter`/`combine` are the only call-boundary logic):

```
              π p = Some body      π ⊢ ⟨body, enter s⟩ ⇓ t
(PCall)       ─────────────────────────────────────────────
                       π ⊢ ⟨Call p, s⟩ ⇓ combine s t
```

plus the usual SKIP/Assign/Seq/If/While rules threading `π`. Recursion needs no
explicit stack: the caller state `s` is captured in the `PCall` premise and reused
by `combine` in its conclusion, so each activation restores its own locals. The
inductive definition is well-founded on derivation height.

**Why this is exactly S1–S4.** No parameters/returns (S1): the only data crossing
the boundary is the global slice (`enter` keeps `G`, `combine` returns `G`).
Locals caller-private (S4): `combine` takes `L` from the caller's pre-call `s`, so
whatever the callee did to the shared `L` cells is discarded. Globals are
flow-sensitive *inside* a body (threaded normally) and only summarised at the
boundary — that is the monovariant cut (S2). Recursion (S3) is free.

### 9.2 Interprocedural collecting semantics

Whole-program CFG `G_π`: each body compiled once to its sub-CFG (entry `en_p`,
exit `ex_p`); a call site is a node `c` with return node `r`; wiring is

- one **enter edge** `(c, EA_Enter, en_p)` per call site, and
- one **combine triple** `(c, ex_p, r) ∈ combines G_π` per call site.

Collecting environment `C :: node ⇒ store set` is `lfp F` where `F C v` is the
union of:

```
  {s0}                                  if v = main_entry            (* seed *)
  edge_collect a (C u)                  for each intra/enter edge (u,a,v)
  { combine s t | s ∈ C c, t ∈ C ex }   for each (c, ex, v) ∈ combines
```

with `edge_collect EA_Enter X = enter ` X` (image of `enter`). Monotone ⇒ `lfp`
exists. Note `C r` pairs **any** `s ∈ C c` with **any** `t ∈ C ex` — including
mismatched caller/return pairs. That deliberate over-approximation *is*
monovariance (see Example 3).

### 9.3 Constraint encoding (abstract)

```isabelle
definition enter_abs :: "'a abs_state ⇒ 'a abs_state" where
  "enter_abs σ = (λx. if is_global x then σ x else ⊤)"      (* locals unknown ⇒ ⊤ *)

definition combine_abs :: "'a abs_state ⇒ 'a abs_state ⇒ 'a abs_state" where
  "combine_abs σc σe = (λx. if is_global x then σe x else σc x)"
```

`edge_action` gains `EA_Enter` with `apply_tf tf EA_Enter σ = enter_abs σ`
(the callee identity is the edge *target*, not a payload). The generalized RHS:

```isabelle
rhs_ip g tf join bot s0 env v =
  abs_join_set join bot (
        { apply_tf tf a (env u) | (u,a,v) ∈ edges g }                 (* intra + enter *)
      ∪ { combine_abs (env c) (env e) | (c,e,v) ∈ combines g }        (* combine into v *)
      ∪ (if v = cfg_entry g then {s0} else {}) )

is_post_fixpoint_ip g tf join bot s0 env  ≡  (∀v. rhs_ip g tf join bot s0 env v ≤ env v)
```

The merge at `en_p` is automatic: `en_p`'s only predecessors are the enter edges
`(c, EA_Enter, en_p)`, so `rhs_ip … en_p = ⨆_c enter_abs (env c)`. No `Side`.

### 9.4 The exact lemma list

| ID | Statement | Reuses |
|---|---|---|
| **L-enter** | `s ∈ γ_state σ ⟹ enter s ∈ γ_state (enter_abs σ)` | pointwise γ |
| **L-comb** | `s ∈ γ_state σc ⟹ t ∈ γ_state σe ⟹ combine s t ∈ γ_state (combine_abs σc σe)` | pointwise γ |
| **L-enter-mono** / **L-comb-mono** | `enter_abs`, `combine_abs` monotone (combine in both args) | trivial |
| **L-mono'** | `rhs_ip` monotone in `env` (extends `rhs_mono`) | `rhs_mono` + above |
| **L-edge≤rhs** | each combine contribution `≤ rhs_ip … v` (extends `apply_tf_le_rhs`) | `apply_tf_le_rhs` |
| **L-sound'** (**CE4**) | `finite` + `is_post_fixpoint_ip` + `S ≤ γ s0` + tf/enter/combine soundness ⟹ `∀v. C v ≤ γ_state (env v)` | `post_fixpoint_sound` |
| **L-adeq** (**SE4**) | balanced operational reachability ⊆ `C` (`π ⊢ ⟨_,s⟩ ⇓ t` ⟹ `t ∈ C(exit)`) | `cfg_collect_paths` adequacy |
| **L-fin** | `finite (edges G_π) ∧ finite (combines G_π)` | `compile_finite`, `compile_add_offset` |
| **L-td'** | per-pp solve rooted at `v` ⟹ soundness at `v` (see §9.8 — **not** a global `is_post_fixpoint_ip`) | **done** — `td_analyse_collect_sound_at` (Fix B, 2026-06-01) |

Only **L-sound'** and **L-adeq** carry real proof weight; the rest are mechanical
or direct extensions. `make_rhs_tree_ip` emits a plain multi-`Query` tree for
combine nodes — `QueryL c (λdc. QueryL e (λde. Answer (combine_abs dc de)))` — so
**the solver stays `TD_plain`**; only the tree builder changes.

### 9.5 Hand-proofs

**L-comb (combine soundness).** Let `s ∈ γ_state σc`, `t ∈ γ_state σe`, fix `x`.
γ_state is pointwise: `s ∈ γ_state σ ⟺ ∀y. s y ∈ γ (σ y)`.
▸ If `x` global: `combine s t x = t x ∈ γ (σe x) = γ (combine_abs σc σe x)`.
▸ If `x` local: `combine s t x = s x ∈ γ (σc x) = γ (combine_abs σc σe x)`.
So `combine s t ∈ γ_state (combine_abs σc σe)`. ∎ (L-enter is the same shape; on
locals the obligation is `enter s x = 0 ∈ γ ⊤`, true.)

**L-sound' (abstract soundness, CE4).** Identical strategy to `post_fixpoint_sound`:
show `γ_state ∘ env` is an `F`-pre-fixpoint, then `lfp_lowerbound` gives
`C = lfp F ≤ γ_state ∘ env`. Per node `v`, `F (γ_state∘env) v` is a union; each
piece must sit inside `γ_state (env v)`:
▸ *seed*: `{s0} ⊆ γ_state (env main_entry)` since `S ≤ γ s0 ≤ γ_state (env entry)`
  (entry post-fixpoint, as in `s0_le_rhs_entry`).
▸ *intra/enter edge* `(u,a,v)`: `edge_collect a (γ_state (env u)) ⊆
  γ_state (apply_tf a (env u))` (per-edge soundness; the `EA_Enter` case is L-enter)
  `⊆ γ_state (env v)` because `apply_tf a (env u) ≤ rhs_ip … v ≤ env v` (L-edge≤rhs +
  post-fixpoint + `γ_state` monotone).
▸ *combine* `(c,e,v)`: for `s ∈ γ_state(env c)`, `t ∈ γ_state(env e)`,
  `combine s t ∈ γ_state (combine_abs (env c)(env e))` (L-comb)
  `⊆ γ_state (env v)` since `combine_abs (env c)(env e) ≤ rhs_ip … v ≤ env v`.
Union of pieces each `⊆ γ_state(env v)` ⇒ `F(γ_state∘env) v ⊆ γ_state(env v)`. ∎
The combine case is the *only* structural novelty over the current proof, and it is
the binary mirror of the existing unary edge case.

**L-adeq (operational adequacy, SE4).** Induction on the height of `π ⊢ ⟨c,s⟩ ⇓ t`.
The only non-routine case is `PCall` on `Call p` at call node with caller state `s`:
▸ by the prefix reasoning (IH up to the call) `s ∈ C(call_node c)`;
▸ `enter s ∈ enter ` (C c) = edge_collect EA_Enter (C c) ⊆ C(en_p)` by `F`'s enter
  clause — the merge absorbs this caller, however many others contribute;
▸ the callee sub-derivation `π ⊢ ⟨body, enter s⟩ ⇓ t` has smaller height; apply the
  *intraprocedural* adequacy of the body's sub-CFG seeded at `C(en_p)` (the present
  repo's `cfg_collect_paths` argument, reused verbatim on the sub-CFG) to get
  `t ∈ C(ex_p)`;
▸ then `combine s t ∈ {combine s' t' | s'∈C c, t'∈C ex_p} ⊆ C(r)` by `F`'s combine
  clause, using `s ∈ C c` and `t ∈ C ex_p`.
So the post-call state lands in `C(r)`. ∎
**Crux:** soundness survives the monovariant merge precisely because the *matched*
pair `(s,t)` from one activation is a *member* of the all-pairs set the analysis
keeps — over-approximation never drops the real pair. Recursion is unproblematic:
the induction is on derivation height, not on call depth.

### 9.6 Worked examples

**Example 1 — non-recursive, global effect, locals preserved.**
```
global g;   proc inc() { g := g + 1; }
main() { local x;  x := 5;  inc();  inc(); }
```
Sign analysis. At the two call nodes `c1,c2`: `x = +`, and `g` whatever sign holds.
`en_inc = enter_abs(env c1) ⊔ enter_abs(env c2)` keeps the global `g`, sets local
`x` to ⊤. Body: `g := g+1`. At each return, `combine_abs` takes `g` from `ex_inc`
and `x` from the call node ⇒ `x` stays `+` across both calls (locals never leaked
into the callee). Demonstrates `combine = caller-locals ⊕ callee-globals` and that
the call is *not* a `SKIP`: `g` genuinely changes.

**Example 2 — recursion (inlining is impossible).**
```
global n, r;   proc fac() { if (n > 0) { r := r*n; n := n-1; fac(); } }
main() { n := 4; r := 1; fac(); }
```
Interval analysis with widening. The call graph has a self-loop `fac → fac`, so the
whole-program CFG has a cycle `en_fac → (body) → c_rec → en_fac` and a combine
`(c_rec, ex_fac, r_rec)`. There is **no** finite inlining. The TD fixpoint iterates:
`en_fac` starts as the merge of the initial enter (`n=[4,4]`) and the recursive
enter; after the guard `n>0` and `n := n-1` the recursive contribution lowers the
bound, the merge climbs, widening sends `n` to `[-∞,4]`, the guard `n>0` refines the
in-body value to `[1,4]`. Converges to a sound summary with **no** call-depth bound —
exactly the "Fixpunkt über alle Summaries" claim. The verified `TD_plain` computes
this; the only assumption is the existing `solve_dom` (termination/descent), unchanged.

**Example 3 — monovariant precision loss (soundness ≠ precision).**
```
global g;   proc id() { }                       (* no-op on g *)
main() { local b; if (b) { g := 1; id(); A: } else { g := -1; id(); B: } }
```
Sign analysis. Call nodes carry `g=+` (then-branch) and `g=-` (else-branch). Both
enter edges feed the *one* shared `en_id`, so `en_id` sees `g = + ⊔ - = ⊤`, and
`ex_id` carries `g=⊤`. At `A:` and `B:`, `combine_abs` takes `g` from the shared
`ex_id` ⇒ both see `g=⊤`, even though the matched truth is `g=+` at `A` and `g=-` at
`B`. Inlining (or context-sensitivity) would keep them apart. This is the
all-pairs over-approximation of §9.2 made visible — sound (L-sound'/L-adeq still
hold), just imprecise. It is the honest content of "kontext-insensitiv, sonst
werden die Beweise extrem schwierig".

### 9.7 Plain-TD vs. `TD_side` — what each scope actually needs

| Scope | Merge mechanism | Combine mechanism | Solver |
|---|---|---|---|
| **This plan (S1–S4): monovariant, flow-sensitive globals** | predecessor join at `en_p` over `EA_Enter` edges | **binary combine edge** `(c,ex,r)` | **`TD_plain`** (multi-`Query` tree; verified, unchanged) |
| Flow-**insensitive** globals (true sinks, written anywhere — Voblint-style) | `Side g d` accumulation into a global unknown | `QueryG` of the global summary | **`TD_side`** (`Basics_side`) |
| Context-**sensitive** (call-strings / functional / Context Gas) | per-context entry unknowns created on the fly | per-context return query | `TD_side` + context lifter (P4) |

So §6's `post_fixpoint_sound_side` / `TD_side` route is **not** required for the
thesis-scoped target — it is the *next* axis (flow-insensitive globals or
context-sensitivity), and should be presented as future work alongside Stage C.
The recommended thesis path is therefore: **Stage A** (smoke-test, unified store) →
**Stage B via plain TD + binary combine** (L-sound' + L-adeq are the two real
proofs) → defer `TD_side` to the flow-insensitive/context-sensitive extension.

This also retires the §8 risk "CE4 = `post_fixpoint_sound_side`": the binary-combine
`L-sound'` is a direct extension of the existing `post_fixpoint_sound` (one extra
union case), not a bridge to a new solver's `eq_equal_sides_subsumed` invariant.

### 9.8 Interaction with P2 (the `reach` root) — per-pp solve is mandatory

The proof repo's P2 finding (`docs/OPEN_PROBLEMS.md`, commit `87027e9`) changes the
shape of L-td', and procedures make the point sharper.

**The finding.** `make_rhs_tree` is *forward* dataflow: each node's RHS `Query`s its
CFG **predecessors**, so `dep T σ v` = predecessors of `v` and
`reach T σ x` = the **backward cone** of `x` (all CFG-ancestors). Hence
`reach T σ (cfg_entry) = {cfg_entry}` (entry has no ancestors), and the old
pipeline hypothesis `∀v. v ∈ reach(entry)` is **structurally false** for any
multi-pp program — not a missing lemma.

**Why exit-rooting (the tempting "Fix A") is wrong.** Rooting the solve at `cfg_exit`
gives `reach = ` backward cone of exit = nodes that *forward-reach* exit. For a
**diverging** program the loop body never reaches exit, so it falls outside the cone
— exit-rooting reproduces the vacuity for exactly the divergence examples
(`nonterm_prog`, `incr_loop_prog`) the small-step migration was built to handle.

**Fix B (per-pp solve) — adopted.** Root the solve at the queried node `v`. Then
`v ∈ reach T σ_v v` by `reach.base`, trivially, with no CFG-connectivity proof;
soundness at `v` localizes to `v`'s backward cone (the only nodes whose equations
feed `cfg_collect` at `v`). Cost: a per-pp termination hypothesis (`solve_dom`
rooted at `v`) instead of one global one. So L-td' is per-pp, and L-sound' is
consumed in **localized** form (post-fixpoint on `reach(v)` ⟹ soundness at `v`),
never as a global `∀v` post-fixpoint.

**Procedures interaction.**
- The new `dep` edges are: a return node `r` queries `{call c, callee-exit ex_p}`;
  `en_p` queries **all** its call sites. Backward cones become interprocedural and,
  under recursion, cyclic. Under per-pp solve this needs no new argument:
  `v ∈ reach(v)` holds regardless, and soundness at `v` needs the post-fixpoint only
  on `v`'s (interprocedural) backward cone, which the per-`v` solve provides.
- Procedures make exit-rooting **doubly** wrong: diverging recursion (Example 2)
  never returns to `main`'s exit, so it is outside exit's backward cone — the same
  vacuity as diverging loops. **Per-pp is the single uniform mechanism for both
  loop- and recursion-divergence.**
- The per-`v` `solve_dom` over a recursive (cyclic) backward cone is discharged by
  the same termination/widening story as P1/P5 — recursion adds no new solver
  obligation beyond what loops already require.

**Net effect on the lemma set.** L-enter, L-comb, L-adeq, and the structural combine
case of L-sound' are untouched. Only L-td' (and how L-sound' is *consumed*) takes
the per-pp shape — and that is shared verbatim with the single-procedure pipeline's
P2 resolution. Procedures inherit the P2 fix; they do not enlarge it.

---

## See also

- KB: `wiki/research/procedures-extension-feasibility.md` — approaches A/B/C, effort
- KB: `wiki/research/seidl-scope-feedback.md` — verbatim email + L0–L4 ladder
- `docs/ROADMAP.md` — domain stretch (octagon) is the *orthogonal* axis; procedures
  is the interprocedural axis. They are independent scope choices.
- Vendor: `vendor/td-verification/{TD_side,Basics_side}.thy` — verified side-effecting solver
- P1 Apinis–Seidl–Vojdani APLAS 2012; P2 Seidl–Apinis–Vojdani 2014; P4 Context Gas STTT 2025
