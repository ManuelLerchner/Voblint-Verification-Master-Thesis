# A7 decision note: Goblint D/G/C route (A) vs semantic entry-store context (C)

Route A (keyed `cmp=(=)` finite context) is blocked at the `fctx` witness by an
architectural fact, not a missing lemma:

```text
flow-insensitive global slots
+ routing based on a global (G)
= the caller read of G is polluted before any context split
```

Proven, eval-backed (`Example_Finite_Sign_Context_Analysis.thy`,
`ROUTE_A_SWITCHING_COMBINE_MIGRATION.md`):

- The `ENTER_MONO` obligation reads the caller's abstract state, *upstream* of the
  routing function `ec`. A cc-aware `ec` fixes only the return read (CMP_SOUND).
- `G` is a global; its value lives solely in the flow-insensitive per-context global
  slot. Any procedure holding both `G:=0` and `G:=1` phases sees `G = SNonNeg`, whose
  `gamma` admits `G=0` (digest `GZero`) and `G=1` (digest `GPos`). No single routed
  context `(=)`-matches both.
- Coarsening to `subseteq` routes to `GNonNeg`, a slot the solver never populates.
- Restructuring into per-phase procedures relocates the pollution to `main` (verified:
  `f` lands in `{GZero, GNonNeg}`).

Escaping this needs a Goblint-style **routing state before information loss**
(A) or a **different, already-sound context model** (C). They answer different
research questions; pick by thesis goal.

Upstream Goblint correction (2026-07-02): Goblint does not update contexts on
normal edges. `Spec.context` receives a `D.t` local abstract state; in `base`,
that state may still contain globals flow-sensitively before they are published
to the separate `G.t` side store. That Base fact is evidence, not the general
invariant. The architectural invariant is weaker and cleaner: `context()` must
observe whatever information the analysis uses for routing before that
information is joined away. Therefore the primary A route is no longer
`step_ctx`/intra-edge context updates. The primary A route is a `D/G/C`
interface boundary: context selection reads a pre-loss routing state, while
global side slots remain separate.

## The two routes

| | **A — Goblint D/G/C keyed generator** | **C — semantic entry-store context** |
| --- | --- | --- |
| Idea | Context selection at calls reads a routing state before the relevant information is published, widened, or joined away. Published globals live separately in `G` side slots. | Reuse the proven `semantic_entry_store_ctx_analysis_sound`: context = entry-store abstraction, unit global pot. |
| Comparison | `cmp = (=)`, precise per-call keyed globals | `cmp = (subseteq)`, unit globals |
| Status | Not built. New context model. | Sound in the repo today (`TD_Side_Eff_Ctx_Sound.thy`, batch-sealed). |
| Kernel A7.1 | Untouched | Not used (different theorem) |
| Touches | `Context_Domain.thy`, keyed combine/generator boundary, `ENTER_MONO`/`CMP_SOUND` statements, fctx witness representation of the routing information before it is lost | A witness program + instantiation of an existing theorem |
| Effort / risk | Medium-large / medium-high; less invasive than normal-edge `step_ctx`, but requires a clean `D` vs `G` boundary | Small / low |
| Research question | "Can Goblint's D/G/C context interface be certified with exact `(=)` context matching?" | "Can a value-dependent (entry-state) context-sensitive analysis be certified sound at all?" — already answered yes |

## What each buys the thesis

**A** is the only route that certifies the *Goblint-shaped D/G/C context
interface* with exact context matching. If the thesis claim is specifically "we
verify Goblint's context mechanism," A is the faithful path. The old
normal-edge `step_ctx` variant is now a fallback experiment, not the Goblint
alignment story.

**C** already exists and is sound. It certifies value-dependent context-sensitivity via
entry-store contexts and a `subseteq` digest with a single global pot. If the thesis
claim is "we verify a sound, value-dependent context-sensitive interprocedural
analysis," C discharges it now; A would be a precision refinement, not a soundness
prerequisite.

The obstruction proof itself is a third, zero-additional-cost contribution: it
characterizes exactly *why* a finite keyed `(=)` context cannot cover global-derived
routing without flow-sensitive contexts. That is a genuine negative result and can
stand in the thesis regardless of A vs C.

## Decision framing (not yet decided)

- Thesis needs **Goblint D/G/C context alignment** verified → **A**, budget a large slice.
- Thesis needs **sound value-dependent context-sensitivity** verified → **C** (done),
  keep A as stated future work, ship the obstruction proof as the boundary result.
- Undecided → default to **C + obstruction proof** now; A stays a scoped, optional
  extension. C is stable and reversible; A is not cheap to unwind.

Recommendation: unless the thesis explicitly commits to Goblint `D/G/C`
alignment, take **C** and publish the obstruction result as the precise reason
side-slot-based keyed `(=)` context selection fails. Revisit A only if a chapter
depends on matching Goblint's `Spec.context` boundary.
