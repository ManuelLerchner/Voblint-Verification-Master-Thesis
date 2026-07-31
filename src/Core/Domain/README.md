# Generic abstract-domain interface

Shared locale definitions and state representation consumed by every concrete domain.
No domain-specific content lives here.

**Theories**

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | `sound_domain`, `abstract_domain` (+ `widen`), `gamma_state`, join/fold lemmas, `backward_domain` (generic `afilter`/`bfilter`) |
| `Split_State.thy` | `('l, 'g) split_state` local/global pair, `merge_state`/`split_state` isomorphism to `'a abs_state` at `'l = 'g`, and `gamma_split` |
| `Exec_St.thy` | `'a st` quotient type (two-region rep), `lookup_st`, `update_st`, order/sup/widening instances |
| `Exec_Backward.thy` | Extends `backward_domain` with the generic `'a st` mirror `afilter_st`/`bfilter_st` and their commutation with `afilter`/`bfilter` through `fun_of_st` |

**Key concepts**

`sound_domain` packages the lattice + concretisation (`gamma`) + monotonicity contract.
`abstract_domain` extends it with a widening operator.
`gamma_state` lifts `gamma` pointwise to `'a abs_state = vname ⇒ 'a`.
`'a st` is the executable association-list representation; `fun_of_st` witnesses simulation.
`backward_domain` (in `Abstract_Domain.thy`) proves `afilter`/`bfilter` sound once, generically,
for any domain supplying `meet`, `aval_abs`, and the `inv_*` operators. `Exec_Backward.thy`
reopens that locale to add the executable `'a st` mirror and its commutation proof, also once.
A concrete domain's own `backward_domain` interpretation (e.g. `Sign_Backward`,
`Interval_Backward`) names both halves via its `defines` clause -- no per-domain induction.

**Downstream:** Every concrete domain in `Instances/` interprets `abstract_domain` and
extends `sound_domain` with a transfer function to instantiate `Equations/Constraint_System`.
