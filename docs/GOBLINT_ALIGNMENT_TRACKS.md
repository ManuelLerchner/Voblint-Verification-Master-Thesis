# Goblint-alignment remaining tracks — comparison and priority

Index for the three remaining Goblint context-alignment migration plans. The
`(node, context)` unknown mechanism itself is **already modeled and verified**
(semantic entry-state contexts, `context_domain` locale, computed keyed/retain
runs — see `docs/NEXT_STEPS.md` "Context-sensitivity status"). These three tracks
are the remaining breadth/fidelity/termination work, none a soundness
prerequisite for the current pipeline.

| Track | Plan | One line |
| --- | --- | --- |
| **M1** | `M1_CALLSTRING_CONTEXT_MIGRATION.md` | Computed k-call-string contexts on the monotone solver |
| **M2** | `M2_DGC_RREAD_BOUNDARY_MIGRATION.md` | `R_read` pre-loss routing; dissolve the `fctx` obstruction |
| **M3** | `M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md` | Sign termination (M3a) + context lifters (M3b) + widening termination (M3c, future) |

## Cross-track comparison

| Axis | M1 call-strings | M2 R_read / D-G | M3a Sign term. | M3b lifter |
| --- | --- | --- | --- | --- |
| **Implementation effort** | Medium — new locale + indexed system + witness | Medium-large — read split, invariant relax, publish fields | **Low** — one domain, height argument | Medium — wrapper + finiteness (needs M1) |
| **Proof effort** | Medium — mono preconditions + combine over-approx (R3) | **High** — cross-proc global soundness (O1), invariant cascade (O2), collecting rework (O3) | Low — well-founded ascent | Medium — finite-image + sound instance |
| **Research risk** | **Low** — syntactic, value-independent, monotone | **High** — selective publication can regress soundness | **Low** — standard finite-height | Medium — gas/collapse ∩ `mono_sides` |
| **Expected payoff** | New optimal-back-end computed context; textbook precision witness | Removes the one construction-imposed precision loss; certifies `(=)` global-derived splits | Unconditional Sign soundness (drops P1 for one domain) | Recursion terminates under a dynamic bound |
| **Faithfulness to Goblint** | High for the call-string `C.t`; a subset of Goblint's richer default context | **Highest** — certifies the `D/G/C` `Spec.context` boundary Goblint actually uses | Medium — matches finite-height termination argument | High — models a real Goblint lifter |

## Priority order (technical value + Goblint alignment only)

Deliberately ignores thesis schedule and time budget. Ranked by alignment payoff
weighted against research risk and dependency depth.

1. **M2 — `R_read` / D-G boundary.** *Highest technical and alignment value.* It
   certifies the exact `Spec.context` boundary Goblint relies on and removes the
   only precision loss we impose by construction, not by the abstraction. It is
   the deepest fidelity result available. Its high research risk is front-loaded
   into a single go/no-go obligation (cross-procedure global soundness under
   selective publication, M2 Stage 1) on a minimal `fctx` fragment — so the risk
   is *bounded and testable early*, not diffuse. On pure technical merit it
   outranks the others despite being the hardest.

2. **M3a — Sign termination.** *Best value-to-cost.* Low effort, low risk, and it
   converts conditional soundness into an unconditional theorem for a whole
   domain by discharging the `solve_dom` hypothesis. Independent of everything;
   strengthens the core result directly. Ranked above M1 because closing a
   standing soundness assumption is worth more than adding a second context
   scheme.

3. **M1 — computed k-call-strings.** *Solid, self-contained breadth.* Adds the
   most recognizable Goblint context as a computed, optimal-back-end instance with
   low research risk. Ranks below M2/M3a because it broadens rather than deepens —
   the context mechanism is already certified; M1 adds one more scheme alongside
   the semantic one. It is the natural prerequisite for M3b.

4. **M3b — context-bounding lifter.** *Faithful but dependent.* Models a real
   Goblint lifter and makes recursion terminate under a dynamic bound, but it
   needs M1 first and its payoff is incremental over the static `'c::finite`
   bound. Do it after M1.

5. **M3c — general widening termination.** *Future / upstream.* Requires a
   `td-verification` change; out of local scope. Lowest local priority.

**Dependency graph:**

```
M2  (independent, highest value)
M3a (independent, best value-to-cost)
M1  (independent) ──► M3b (needs a call-string context)
M3c (upstream-gated, future)
```

M2 and M3a can proceed in parallel with each other and with M1. The only ordering
constraint among the value-bearing tracks is M1 → M3b.

## See also

- `docs/NEXT_STEPS.md` — "Context-sensitivity status" (what is already done)
- `docs/DGC_ALIGNMENT_ANALYSIS.md` — the M2 obstruction audit (§6 layered change)
- `docs/ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` — corrected call-only Goblint model
- `docs/TRACE_BASED_FORK_MIGRATION.md` — M1 fork detail (A1–A5, R1–R6)
- `docs/GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` — Gap inventory (Gap 6 = M3; Gap 7
  context-sensitivity is **partially stale** — the semantic-context half landed
  since 2026-06-17; only computed call-strings (M1) remain of that gap)
