# Voblint formalization (`src/`)

Isabelle/HOL session **Voblint_Formalization**: sound static analysis from IMP2 source
through CFG collecting semantics, abstract equations, and the vendored **TD** solver
(`vendor/td-verification`, session `TD`) to pipeline soundness theorems.

**Top level:** the interprocedural / unified / side spine — `Trace_IP_Analysis_Sound`,
`TD_IP_Soundness`, `Sign_IP_Soundness`, `Sign_Side_Soundness`, `Analysis_Sound`. The
intra-procedural (classical) spine was extracted to the sibling repo
`voblint-formalization-classical` (see `docs/CLASSICAL_SPINE_RETIREMENT.md`).

**Pipeline (left to right):**

```
IMP2 → CFG (+ Collecting) → Equations → Solver (TD) → Pipeline → Examples
         Domains ─────────────────────────────┘
```

| Folder | README | Role |
| --- | --- | --- |
| [`IMP2/`](IMP2/) | [README](IMP2/README.md) | Source language syntax and small-step semantics |
| [`CFG/`](CFG/) | [README](CFG/README.md) | Control-flow graphs, compilation, paths |
| [`CFG/Collecting/`](CFG/Collecting/) | [README](CFG/Collecting/README.md) | Collecting semantics (`cfg_collect`, `runs_to`) |
| [`Domains/`](Domains/) | [README](Domains/README.md) | Abstract domains (sign, interval, shared locale) |
| [`Equations/`](Equations/) | [README](Equations/README.md) | CFG → equation system + fixpoint soundness |
| [`Solver/`](Solver/) | [README](Solver/README.md) | TD solver bridge (`TD_CFG_Core`, plain + widen/WN interfaces) |
| [`Pipeline/`](Pipeline/) | [README](Pipeline/README.md) | End-to-end soundness (invariant + path + exit) |
| [`Examples/`](Examples/) | [README](Examples/README.md) | Executable checks and demonstrations |

Also at CFG root: `CFG_GraphViz.thy` (Graphviz tooling, imported from top theory).

Plans and sorry inventory: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
