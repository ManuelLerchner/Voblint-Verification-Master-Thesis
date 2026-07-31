# Voblint_Core session

The abstract framework: domains, constraint systems, and the TD solver bridge.
Has no domain-specific content; it defines the shared interfaces every concrete
domain instance (`src/Analysis/Instances/`) consumes.

**Session graph position:** `Voblint_CFG` -> `Voblint_Core` -> `Voblint_Analysis`
-> `Voblint_Formalization`. Downstream consumers are in `src/Analysis/Instances/`,
`src/Formalization/Pipeline/`, and `src/Examples/`.

## Sub-folders

| Folder | Content |
| --- | --- |
| `Domain/` | `sound_domain` / `abstract_domain` locales; `'a st` state type |
| `Equations/` | Constraint-system definition + post-fixpoint soundness |
| `Solver/` | TD side-effecting solver bridge; effectful strategy trees |

`Solver/README.md` documents its own four-way split (`TD_Side/`, `Strategy_Tree/`,
`Context/`, `Exec/`).

## ROOT

`src/Core/ROOT` registers the source directories needed by Isabelle's flat
theory namespace.
