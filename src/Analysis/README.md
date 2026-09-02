# Voblint_Analysis session

Concrete domain instances over the `Voblint_Framework` framework and its `Voblint_Exec` carrier. Each
domain threads its type through type-class declarations, locale interpretation,
the executable bridge, and end-to-end soundness.

**Session graph position:** `Voblint_Exec` -> `Voblint_Analysis` -> `Voblint_Soundness`.
Downstream consumers are in `src/Formalization/Pipeline/` and `src/Examples/`.

## Sub-folders

| Folder | Content |
| --- | --- |
| `Common/` | Base-level reuse locales every domain interprets: the expression-evaluation induction (`Abstract_Arithmetic`), special-call dispatch (`Special_Ops`), the executable branch/enter construction (`Numeric_Ops`), executable backward filtering (`Exec_Backward`), and what a solved table publishes -- state and check report, generic in the domain (`Analysis_Surface`) |
| `Context/` | Routing policies over a compiled program: bounded call strings (`Call_String_Routed_Context`, `Call_String_Context_Finite`) and entry-state contexts (`Entry_State_Routed_Context`) |
| `Instances/Sign/` | Seven-element sign lattice, executable bridge, end-to-end soundness |
| `Instances/Interval/` | Interval domain (`ivl`), executable bridge, soundness |
| `Components/Congruence/` (a domain component, not a runnable analysis: no `_Sound`/`_Analyses` of its own, consumed by `Instances/Int`) | Normalized congruence domain with executable lattice, arithmetic, backward filtering, and `sound_domain` |
| `Instances/Parity/` | Parity domain, executable bridge |
| `Instances/Int/` | The `int_dom` analysis family: a reduced product of Sign, Interval, Parity and Congruence, with verified progressive and structural-fixpoint refinement. Named for the domain it analyses, not for the product construction -- multi-analysis composition in the Goblint sense does not exist here yet, and that vocabulary is deliberately left free |
| `Instances/Relational/` | Order carriers that are not pointwise abstract states |
| `Reporting/` | GraphViz output for CFG/analysis visualisation. Generic construction of a graph from an analysis result; the CLI-facing formatting lives in `Voblint_CLI.State_Report_GraphViz` |

## ROOT

`src/Analysis/ROOT` registers the source directories needed by Isabelle's flat
theory namespace.
