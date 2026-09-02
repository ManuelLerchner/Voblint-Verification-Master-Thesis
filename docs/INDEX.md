# Documentation index

The source theories are authoritative for definitions and theorem statements.
These documents describe the supported architecture and its verification.

## Architecture

- [Procedure-aware CFG architecture](PROCEDURE_AWARE_CFG_ARCHITECTURE.md) — source
  contract, compiler, activation-local semantics, equations, D/G routing, and
  solver integration.
- [Proof overview](PROOF_OVERVIEW.md) — end-to-end soundness chain.
- [Check-discharge architecture](CHECK_ARCHITECTURE.md) — how a compiled check
  becomes a GraphViz-rendered proof status and a semantic soundness guarantee,
  and how a contextual `analysis_result` feeds checks, collapsed GraphViz, and
  expanded GraphViz from one canonical table.
- [CLI](CLI_DESIGN.md) — `voblint`'s flags, architecture, and trust boundary.
- [Per-origin widening](PER_ORIGIN_WIDENING.md) — what the solver's per-origin
  update rules recover, on which unknowns, and where they make no difference.
- [Glossary](GLOSSARY.md) — current terms and defining layers.
- [Non-goals](NON_GOALS.md) — claims deliberately outside the framework.
- [Goblint alignment register](GOBLINT_ALIGNMENT_REGISTER.md) — the living
  record of where the formalization differs from upstream Goblint, why each
  difference exists, and what would close it.
- [Verification chain and trust boundary](VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md)
  — what is proved, what is generated, and what is handwritten.

## Work and verification

- [Export-surface audit](EXPORT_SURFACE_AUDIT.md) — what the formalization
  defines that the exported OCaml never reaches, which of it is legacy, and
  where definitions and proofs can be unified.
- [Cleanup migration plan](CLEANUP_MIGRATION_PLAN.md) — the phased execution
  sequence for that audit.
- [Core refactor plan](CORE_REFACTOR_PLAN.md) — the four-phase split of
  `Voblint_Framework` along Goblint's library boundaries, with the measured
  import evidence and a per-step status table.
- [Roadmap](ROADMAP.md) — stable extension directions and completion criteria.
- [Next work](NEXT_STEPS.md) — near-term technical directions.
- [Open problems](OPEN_PROBLEMS.md) — research and engineering boundaries.
- [Proof verification gates](PROOF_PHASES.md) — checks required for each proof
  layer and for the repository.

## Isabelle development

- [Isabelle agent notes](ISABELLE_AGENT_NOTES.md) — document-aware editing,
  diagnostics, proof-state inspection, and batch verification.

Migration logs, superseded designs, and deleted component descriptions live in
[`history/`](history/README.md). They are kept for provenance and are not
maintained against the current tree.
