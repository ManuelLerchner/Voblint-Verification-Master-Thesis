# Concrete analysis instances

Each domain supplies its carrier, order, concretization, transfer functions,
executable representation, and the soundness obligations needed by the generic
equation and D/G layers.

| Folder | Role |
| --- | --- |
| `Sign/` | Seven-element Sign lattice, transfers, executable maps, and D/G registration |
| `Interval/` | Interval lattice, backward guards, widening, executable maps, and D/G registration |
| `Congruence/` | Normalized congruence carrier, executable lattice and arithmetic, backward filtering, warrowing, and `sound_domain` |
| `Parity/` | Parity lattice, transfers, executable maps, and D/G registration |
| `Mixed/` | Composite Sign/Interval/Parity/Congruence arithmetic, backward filtering, refinement, componentwise widening/narrowing, mode-registered `domain_transfer` bundles, and their abstract (non-executable) D/G registration; heterogeneous D/G instances; relational domains |
| `Tooling/` | CFG and analysis GraphViz renderers |

Executable runs and concrete precision witnesses live in `src/Examples/`.

## Assembly map

Every domain is assembled from the same roles, and the file names alone do not
say which role a file plays -- `Interval_Analyses`, `Interval_Solver_Analyses`
and `Interval_Exec_Sound` are three different questions. This table is the
key; read a column downward to see one domain built up, or a row across to
compare the same role between domains. A blank cell means the domain does not
need that role, not that it is missing.

| Role | Sign | Interval | Parity | Int |
| --- | --- | --- | --- | --- |
| carrier, order, joins | `Sign_Lattice` | `Interval_Lattice`, `Interval_Bounds` | `Parity_Domain` | `Int_Domain` |
| abstract arithmetic | `Sign_Arithmetic` | `Interval_Arithmetic` | | `Int_Arithmetic` |
| backward guard filters | `Sign_Backward` | `Interval_Backward` | | `Int_Backward` |
| widening and narrowing | | `Interval_Warrowing` | | `Int_Warrowing` |
| `Min`/`Max` special calls | `Sign_Special` | `Interval_Special` | `Parity_Special` | |
| numeric queries | `Sign_Numeric_Queries` | `Interval_Numeric_Queries` | `Parity_Numeric_Queries` | |
| edge/entry/combine transfers | `Sign_Transfer` | `Interval_Transfer` | `Parity_Transfer` | `Int_Transfer` |
| `abstract_domain` registration | `Sign_Domain` | `Interval_Domain` | `Parity_Domain` | `Int_Domain` |
| executable transfer mirror | `Sign_Exec` | `Ivl_Exec` | `Parity_Exec` | `Int_Exec` |
| the `dg_spec` and its concretization, before any context | `Sign_Sound` | `Interval_Sound` | `Parity_Sound` | `Int_Sound` |
| production endpoint: solve an arbitrary program, executably, with soundness | `Voblint_CLI.Sign_Entry` | `Interval_Exec_Sound` | `Voblint_CLI.Parity_Entry` | `Int_Exec_Sound` |
| second derivation of the same equations through the routed spine directly | `Sign_Analyses` | `Interval_Analyses` | `Parity_Analyses` | `Int_Analyses` |
| the same equations under a different solver configuration | | `Interval_Solver_Analyses` | | `Int_Solver_Analyses` |
| check classifier | `Sign_Classify` | `Interval_Classify` | `Parity_Classify` | `Int_Classify` |
| result tables and check reports off one solved run | `Sign_Checks` | `Interval_Checks` | `Parity_Checks` | `Int_Checks` |
| point abstraction | | `Interval_Point_Digest` | | |
| component refinement | | | | `Int_Refinement` |

Two rows are easy to confuse. *Second derivation* reaches the same
`unit_routed_eqs` system a second way -- through
`Voblint_Framework.Routed_Context`'s generic locales rather than through the
packaged registration a production run uses -- so that the generic route stays
exercised and the two answers are known to agree. *Different solver
configuration* keeps the equations fixed and changes only the update rule.
Neither is what the CLI dispatches to; that is the production-endpoint row.

## Adding a domain

1. Define the carrier order, joins, bottom, concretization, and widening needed
   by `sound_domain` and `abstract_domain`.
2. Define edge, entry, and combine transfers and discharge their concrete
   soundness obligations.
3. Provide the executable `st` operations and prove they commute with the
   function-state operations.
4. Instantiate `sound_dg_spec_core` directly or register a diagonal unit D/G
   analysis.
5. Add an executable example that checks solver success and states a concrete
   precision fact.

The generic solver and collecting proofs remain independent of the concrete
domain.
