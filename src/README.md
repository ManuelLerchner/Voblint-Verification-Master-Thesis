# Voblint formalization (`src/`)

Isabelle/HOL sessions **Voblint_IMP2**, **Voblint_CFG**, **Voblint_Analysis**,
**Voblint_Formalization**: sound static analysis from IMP2 source with procedures
through interprocedural CFG collecting semantics, abstract equations, and the
vendored **TD side** solver (`vendor/td-verification`, session `TD`) to pipeline
soundness theorems.

**Top level:** the interprocedural / side-effecting spine — `Trace_IP_Analysis_Sound`,
`TD_Side_Eff_Soundness`, `Sign_Side_Soundness`, `Analysis_Sound`. The
intra-procedural (classical) spine was extracted to the sibling repo
`voblint-formalization-classical` (see `docs/CLASSICAL_SPINE_RETIREMENT.md`).

**Pipeline (left to right):**

```
IMP2 (+ Proc + Globals) → CFG (+ IP Collecting) → Equations → Solver (TD side) → Pipeline → Examples
                    Domains ────────────────────────────────┘
```

| Folder | README | Role |
| --- | --- | --- |
| [`IMP2/`](IMP2/) | [README](IMP2/README.md) | Source language syntax, procedures, globals/locals split, small-step semantics |
| [`CFG/`](CFG/) | [README](CFG/README.md) | Control-flow graphs, interprocedural compilation, paths |
| [`CFG/Collecting/`](CFG/Collecting/) | [README](CFG/Collecting/README.md) | IP collecting semantics (`cfg_collect`), trace collecting, unified locale |
| [`Analysis/Domains/`](Analysis/Domains/) | [README](Analysis/Domains/README.md) | Abstract domains (sign, shared locale) |
| [`Analysis/Equations/`](Analysis/Equations/) | [README](Analysis/Equations/README.md) | CFG → IP equation system + fixpoint soundness |
| [`Analysis/Solver/`](Analysis/Solver/) | [README](Analysis/Solver/README.md) | TD side solver bridge (`TD_Side_IP_Tree (tree construction only)`, `TD_Side_Eff_*`, soundness) |
| [`Formalization/Pipeline/`](Formalization/Pipeline/) | [README](Formalization/Pipeline/README.md) | End-to-end soundness (`trace_ip_analysis_sound`, `reaching_global_read_sound`) |
| [`Formalization/Examples/`](Formalization/Examples/) | [README](Formalization/Examples/README.md) | Concrete demonstrations and precision examples |

Also at CFG root: `CFG_GraphViz.thy` (Graphviz tooling), `CFG_Prune.thy` (reachability pruning).

Plans and sorry inventory: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
