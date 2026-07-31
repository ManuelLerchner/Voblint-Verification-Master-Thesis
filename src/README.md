# Voblint formalization (`src/`)

Isabelle/HOL sessions **Voblint_VIMP**, **Voblint_CFG**, **Voblint_Core**,
**Voblint_Analysis**, **Voblint_Formalization**: sound static analysis from VIMP source with procedures
through interprocedural CFG collecting semantics, abstract equations, and the
vendored **TD side** solver (`vendor/td-verification`, session `TD`) to pipeline
soundness theorems.

**Top level:** the interprocedural / side-effecting spine —
`Mixed_Flow_Sound`, `TD_Side_Eff_Soundness`, `Sign_Side_Soundness`,
`Analysis_Sound`, plus the native D/G interface (`DG_Soundness`, `Sign_DG`,
`Interval_DG`, `Mixed_Sign_Interval`) and its executable transport
(`Exec_DG_Bridge`). An intra-procedural (classical) formulation is developed
in the sibling repo `voblint-formalization-classical`.

**Pipeline (left to right):**

```
VIMP (+ Proc + Globals) → CFG (+ IP Collecting) → Equations → Solver (TD side) → Pipeline → Examples
                    Domains ────────────────────────────────┘
```

| Folder | README | Role |
| --- | --- | --- |
| [`VIMP/`](VIMP/) | [README](VIMP/README.md) | Source language syntax, procedures, globals/locals split, small-step semantics |
| [`CFG/`](CFG/) | [README](CFG/README.md) | Control-flow graphs, interprocedural compilation, paths |
| [`CFG/Collecting/`](CFG/Collecting/) | [README](CFG/Collecting/README.md) | IP collecting semantics (`cfg_collect`), trace collecting, run-to-exit projection |
| [`Core/Domain/`](Core/Domain/) | [README](Core/Domain/README.md) | Abstract-domain classes and executable state representation |
| [`Core/Equations/`](Core/Equations/) | [README](Core/Equations/README.md) | CFG -> IP equation system + fixpoint soundness |
| [`Core/Solver/`](Core/Solver/) | [README](Core/Solver/README.md) | TD side solver bridge (`TD_Side/`, `Strategy_Tree/`, `Context/`, `Exec/`) |
| [`Analysis/Instances/`](Analysis/Instances/) | [README](Analysis/Instances/README.md) | Concrete domains and native effectful transfer records (`sign_etf`, `ivl_etf`) |
| [`Formalization/Pipeline/`](Formalization/Pipeline/) | [README](Formalization/Pipeline/README.md) | End-to-end soundness and mixed-flow optimality (`trace_analysis_sound`, `mixed_flow_analysis_optimal`) |
| [`Examples/`](Examples/) | [README](Examples/README.md) | Concrete demonstrations and precision examples |

Also at CFG root: `CFG_GraphViz.thy` (Graphviz tooling), `CFG_Prune.thy` (reachability pruning).

Plans and sorry inventory: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
