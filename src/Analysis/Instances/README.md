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
| `NamedGlobalSign/` | Sign analysis with named shared-state routing |
| `Mixed/` | Composite Sign/Interval/Parity/Congruence arithmetic, backward filtering, refinement, componentwise widening/narrowing, mode-registered `domain_transfer` bundles, and their abstract (non-executable) D/G registration; heterogeneous D/G instances; relational domains |
| `Tooling/` | CFG and analysis GraphViz renderers |

Executable runs and concrete precision witnesses live in `src/Examples/`.

## Adding a domain

1. Define the carrier order, joins, bottom, concretization, and widening needed
   by `sound_domain` and `abstract_domain`.
2. Define edge, entry, and combine transfers and discharge their concrete
   soundness obligations.
3. Provide the executable `st` operations and prove they commute with the
   function-state operations.
4. Instantiate `sound_dg_spec` directly or register a diagonal unit D/G
   analysis.
5. Add an executable example that checks solver success and states a concrete
   precision fact.

The generic solver and collecting proofs remain independent of the concrete
domain.
