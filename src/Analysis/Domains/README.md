# Abstract domains

**Main contribution:** Shared abstract-domain interface (`sound_domain` /
`abstract_domain` locales, `'a abs_state`, `gamma_state`) and concrete domains
(sign) with per-edge transfer soundness lemmas.

**Theories**

| File                         | Role                                                                                                                           |
| ---------------------------- | ------------------------------------------------------------------------------------------------------------------------------ |
| `Abstract_Domain.thy`        | `sound_domain`, `abstract_domain` (+ `widen`), `gamma_state`, join/fold lemmas, `join_state_comp_fun_idem`                     |
| `Sign_Domain.thy`            | Sign lattice (`SNeg`, `SZero`, `SPos`, `STop`, `SBot`), `gamma_sign`, `sign_tf`, `interpretation sign_domain: abstract_domain` |
| `Sign_Side_IP_Soundness.thy` | `side_ip_sign_analysis_sound` — sign domain end-to-end via `side_analyse_ip`                                                   |

**Layering:** `Sign_Domain` imports `Constraint_System` (for the `'a domain_transfer`
type) and `IMP2_Expr` (for `aval` / `bval` in transfer proofs).
`Sign_Side_IP_Soundness` imports `Sign_Domain` and `TD_Side_IP_Soundness`.

**Key concepts:** `gamma` / `gamma_state`, `bot`, join (⊔); per-action soundness lemmas
(`sound_transfer` locale in `TD_Side_IP_Soundness.thy`). The `sound_transfer` locale
unifies transfer soundness with solver soundness.

**Downstream:** `Analysis/Equations/Constraint_System.thy` builds `rhs`/`rhs_ip`;
`Formalization/Pipeline/Trace_IP_Analysis_Sound.thy` — `trace_ip_analysis_sound`.

**Stretch goal:** Interval domain (was in classical spine; fits `sound_transfer` locale without architectural changes); Octagon domain (see `docs/ROADMAP.md`).
