# docs/ index

Map of this directory. Grouped by lifecycle so a reader can tell **current** from
**history** at a glance. Buckets are driven by each doc's own `Status:` header —
open a doc to see its detail. Nothing here is moved or renamed; this is the key.

> Migration/handoff docs are kept in place (cross-referenced from `CLAUDE.md`, the
> source READMEs, and each other). A **Completed** doc is a historical record of a
> change that has already landed in the code — read it for provenance, not for the
> current state. For the current state, start with the navigation set.

---

## Start here — navigation & live status

| Doc | What |
| --- | --- |
| `ROADMAP.md` | Live backlog (mirrors GitHub Project 8) |
| `NEXT_STEPS.md` | Short-horizon work plan |
| `OPEN_PROBLEMS.md` | Open items + explicit hypotheses (P1 …) |
| `PROOF_OVERVIEW.md` | Big-picture soundness chain |
| `PROOF_PHASES.md` | Phases, exit criteria, sorry inventory |
| `NON_GOALS.md` | What the project deliberately does not do |
| `GLOSSARY.md` | Project terms with `file:line` |
| `THESIS_SCOPE_MEMO.md` | Thesis scope decision |
| `TRACK_PLAN.md` | Track-level plan |
| `PROOF_CLEANUP_OPPORTUNITIES.md` | Cleanup / generalization menu (this migration) |
| `ISABELLE_AGENT_NOTES.md` | Isabelle / MCP traps |

## Reference & design (enduring, no lifecycle status)

`HOL_IMP_COMPARISON.md` · `IMP_SYNTAX_NIPKOW_EXTENSION.md` · `cfg-representation.md` ·
`DIGEST_TWO_FAMILIES.md` (design rationale; Family A / RD retired `92739cf`, mode-only in-tree) · `DIGEST_IN_FIXPOINT_DESIGN.md` ·
`CONTEXT_DOMAIN_ARCHITECTURE.md` · `DGC_ALIGNMENT_ANALYSIS.md` ·
`ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md` · `ROUTE_A7_DECISION_A_vs_C.md` ·
`ROUTE_A_SWITCHING_COMBINE_MIGRATION.md` · `AFP_IMP2_REUSE_DECISION.md` ·
`PROCEDURES_EXTENSION_PLAN.md` · `GraphViz-improvements.md` ·
`VALUE_CARRIED_DIGEST_STATUS.md`

## Active / in progress

| Doc | Status |
| --- | --- |
| `DGCV_LAYER_MIGRATION.md` | IN PROGRESS — D/G/C/V native layer: N1 carrier generalization + N2 Sign-on-DG convergence DELIVERED; homogeneous-tower retirement pending |
| `DG_KEYED_CONTEXT_FEASIBILITY.md` | DELIVERED (slice) — keyed/context soundness on the DG spine: reader lemma + per-context theorem + Sign probe; conditional GO for full port |
| `DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION.md` | IN PROGRESS — superset-reader class closed |
| `DIGEST_INDEXED_READER_MIGRATION.md` | **RETIRED** — the RD family it describes was removed (`92739cf`); historical |
| `CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` | IN PROGRESS |
| `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` | IN PROGRESS (Phase A landed) |
| `DOMAIN_INTERFACE_MINIMIZATION.md` | historical plan — superseded by the type-class/domain split now reflected in source READMEs |
| `TRACE_CONTEXT_ANALYSIS_MIGRATION.md` | Track B done; Track A open |
| `TRACE_CONTEXT_BRIDGE_MIGRATION.md` | Partially done |
| `P1_TOTAL_CORRECTNESS_ROUTE.md` | Open (GitHub #14) |
| `SEIDL_TRACE_MIGRATION_HANDOFF.md` · `M3_5_INTERPROC_TRACE_HANDOFF.md` · `UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` | Handoffs |

## Planned / proposed (not started)

`AFP_IMP2_FORWARD_SIM_MIGRATION.md` · `ARRAY_SYNTAX_EXTENSION.md` ·
`GHOST_INSTRUMENTATION_MIGRATION.md` · `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` ·
`NONDET_HAVOC_MIGRATION.md` · `RELATIONAL_DOMAIN_PLAN.md` ·
`TRACE_BASED_FORK_MIGRATION.md` · `TRACE_VALUED_DOMAIN_MIGRATION.md` ·
`VALUE_CARRIED_DIGEST_MIGRATION.md` · `SEMANTIC_CONTEXT_MIGRATION.md`

## Completed — historical records (change already landed)

Read for provenance; the code is the current truth. Status is each doc's own.

`AFP_IMP2_REBASE_MIGRATION.md` · `BACKWARD_ANALYSIS_PLAN.md` ·
`CLASSICAL_SPINE_RETIREMENT.md` · `CONTEXT_GRAPHVIZ_DEBUG_RENDERER.md` ·
`DOMAIN_TYPECLASS_MIGRATION.md` · `EFFECTFUL_TF_MIGRATION.md` ·
`EXECUTABLE_CONTEXT_MIGRATION.md` · `EXECUTABLE_DOMAIN_MIGRATION.md` ·
`EXIT_ROOTED_SOLVE_MIGRATION.md` (superseded) · `GLOBAL_CONTEXT_REDESIGN.md` ·
`IMP2_PRETTY_NOTATION_MIGRATION.md` · `INTERVAL_REINTRODUCTION_PLAN.md` ·
`IP_COLLECTING_CANONICAL_MIGRATION.md` · `IP_NAMING_DROP_MIGRATION.md` ·
`IP_ONLY_CONSOLIDATION.md` · `KEYED_CONTEXT_CONSOLIDATION.md` ·
`DG_KEYED_CONTEXT_MIGRATION.md` ·
`KEYED_CONTEXT_ENTER_FRAMED_MIGRATION.md` · `LOCAL_EDGE_TREE_MIGRATION.md` ·
`NAMED_GLOBAL_RUNNABLE_HANDOFF.md` · `ROUTE_A5_HANDOFF.md` ·
`SESSION_DAG_MIGRATION.md` · `SIDE_ENTRY_GLOBALS_SEEDING.md` ·
`TD_SIDE_ONLY_MIGRATION.md`
