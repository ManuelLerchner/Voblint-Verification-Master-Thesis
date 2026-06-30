# Generic abstract-domain interface

Shared locale definitions and state representation consumed by every concrete domain.
No domain-specific content lives here.

**Theories**

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | `sound_domain`, `abstract_domain` (+ `widen`), `gamma_state`, join/fold lemmas |
| `Exec_St.thy` | `'a st` quotient type (two-region rep), `lookup_st`, `update_st`, order/sup/widening instances |

**Key concepts**

`sound_domain` packages the lattice + concretisation (`gamma`) + monotonicity contract.
`abstract_domain` extends it with a widening operator.
`gamma_state` lifts `gamma` pointwise to `'a abs_state = vname ⇒ 'a`.
`'a st` is the executable association-list representation; `fun_of_st` witnesses simulation.

**Downstream:** Every concrete domain in `Instances/` interprets `abstract_domain` and
extends `sound_domain` with a transfer function to instantiate `Equations/Constraint_System`.
