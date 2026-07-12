# Voblint_Analysis session

Two-layer structure:

```
Generic/     — abstract framework (locales, constraint systems, solver bridge)
Instances/   — concrete domain instantiations (Sign, Interval, NamedGlobalSign, Tooling)
```

`Generic/` has no domain-specific content; it defines the shared interfaces every
instance consumes.  `Instances/` threads each domain through four layers: type-class
declarations, locale interpretation, executable bridge, and end-to-end soundness.

**Session graph position:** `Voblint_CFG` → `Voblint_Analysis` → `Voblint_Formalization`.
Downstream consumers are in `src/Formalization/Pipeline/` and `src/Formalization/Examples/`.

## Sub-folders

| Folder | Content |
| --- | --- |
| `Generic/Domain/` | `sound_domain` / `abstract_domain` locales; `'a st` state type |
| `Generic/Equations/` | Constraint-system definition + post-fixpoint soundness |
| `Generic/Solver/` | TD side-effecting solver bridge; effectful strategy trees |
| `Instances/Sign/` | 7-element sign lattice, executable bridge, end-to-end soundness |
| `Instances/Interval/` | Interval domain (`ivl`), executable bridge, soundness |
| `Instances/NamedGlobalSign/` | Named-global sign analysis (side-effecting, mixed-flow) |
| `Instances/Tooling/` | GraphViz output for CFG/analysis visualisation |

## ROOT

`src/Analysis/ROOT` registers all nine `directories` entries so Isabelle's
theory-name uniqueness requirement is satisfied across the flat theory namespace.
Theory headers (`theory Sign_Domain …`) are unchanged from before the folder migration.
