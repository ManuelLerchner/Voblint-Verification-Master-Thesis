# Voblint_Analysis session

Concrete domain instances over the abstract `Voblint_Core` framework. Each
domain threads its type through type-class declarations, locale interpretation,
the executable bridge, and end-to-end soundness.

**Session graph position:** `Voblint_Core` -> `Voblint_Analysis` -> `Voblint_Soundness`.
Downstream consumers are in `src/Formalization/Pipeline/` and `src/Examples/`.

## Sub-folders

| Folder | Content |
| --- | --- |
| `Instances/Sign/` | Seven-element sign lattice, executable bridge, end-to-end soundness |
| `Instances/Interval/` | Interval domain (`ivl`), executable bridge, soundness |
| `Instances/Congruence/` | Normalized congruence domain with executable lattice, arithmetic, backward filtering, and `sound_domain` |
| `Instances/Parity/` | Parity domain, executable bridge |
| `Instances/Product/` | Composite Sign/Interval/Parity/Congruence facts, verified progressive and structural-fixpoint refinement, and heterogeneous D/G instances |
| `Instances/Relational/` | Order carriers that are not pointwise abstract states |
| `Instances/Tooling/` | GraphViz output for CFG/analysis visualisation |

## ROOT

`src/Analysis/ROOT` registers the source directories needed by Isabelle's flat
theory namespace.
