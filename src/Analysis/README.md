# Voblint_Analysis session

Concrete domain instances over the abstract `Voblint_Core` framework. Each
domain threads its type through type-class declarations, locale interpretation,
the executable bridge, and end-to-end soundness.

**Session graph position:** `Voblint_Core` -> `Voblint_Analysis` -> `Voblint_Formalization`.
Downstream consumers are in `src/Formalization/Pipeline/` and `src/Examples/`.

## Sub-folders

| Folder | Content |
| --- | --- |
| `Instances/Sign/` | Seven-element sign lattice, executable bridge, end-to-end soundness |
| `Instances/Interval/` | Interval domain (`ivl`), executable bridge, soundness |
| `Instances/Parity/` | Parity domain, executable bridge |
| `Instances/Mixed/` | Heterogeneous D/G instance with Sign local facts and one Interval shared fact |
| `Instances/NamedGlobalSign/` | Named-global sign analysis (side-effecting, mixed-flow) |
| `Instances/Tooling/` | GraphViz output for CFG/analysis visualisation |

## ROOT

`src/Analysis/ROOT` registers the source directories needed by Isabelle's flat
theory namespace.
