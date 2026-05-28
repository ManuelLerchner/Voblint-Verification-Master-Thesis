# Procedures / Function Calls — Extension Plan

Scoped extension of the verified pipeline to interprocedural analysis (function
calls), triggered by Seidl's scope question ("warum keine Prozeduren, warum keine
Seiten-Effekte?"). Goal: a **thesis-scoped** but non-trivial interprocedural
analysis — not state-of-the-art context-sensitivity, but real interprocedural
information flow with simplifying assumptions on `enter`/`combine`.

KB companion: `~/git/goblint-formalization-kb/wiki/research/procedures-extension-feasibility.md`.

---

## 1. What "enter/exit" should actually be

The right target is the **`enter` / `combine` pair**, not "enter/exit":

- `enter`  : call-site state → callee-entry state (project/bind on the call edge).
- `combine`: (caller pre-call state, callee summary) → return-site state (restore
  caller-private data, absorb callee effects on the return edge).

These are exactly Goblint's `enter`/`combine` callbacks (`constraints.ml`,
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
| S4 | **Local/global variable split.** Globals cross call boundaries; locals are caller-private and untouched by callees. | Makes the analysis non-trivial (callee affects caller via globals); matches FM 2026 §2 and Goblint. | none. |

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
| SO1 | `make_rhs_tree_side` well-formed; `TD_side.solve_dom` ⟹ `part_solution` instantiates CE4's premise | R' | mirror of `td_analyse_post_fixpoint`; solver itself already verified |

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

## See also

- KB: `wiki/research/procedures-extension-feasibility.md` — approaches A/B/C, effort
- KB: `wiki/research/seidl-scope-feedback.md` — verbatim email + L0–L4 ladder
- `docs/ROADMAP.md` — domain stretch (octagon) is the *orthogonal* axis; procedures
  is the interprocedural axis. They are independent scope choices.
- Vendor: `vendor/td-verification/{TD_side,Basics_side}.thy` — verified side-effecting solver
- P1 Apinis–Seidl–Vojdani APLAS 2012; P2 Seidl–Apinis–Vojdani 2014; P4 Context Gas STTT 2025
