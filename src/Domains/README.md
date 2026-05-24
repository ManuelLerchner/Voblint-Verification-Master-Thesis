# Abstract domains

**Main contribution:** Shared abstract-domain interface (`sound_domain` /
`abstract_domain` locales, `'a abs_state`, `gamma_state`) and concrete domains
(sign, interval) with per-edge transfer soundness lemmas.

**Theories**

| File | Role |
| --- | --- |
| `Abstract_Domain.thy` | `sound_domain`, `abstract_domain` (+ `widen`), `gamma_state`, join/fold lemmas |
| `Sign_Domain.thy` | Sign lattice, `sign_tf`, `interpretation sign_domain: abstract_domain` |
| `Interval_Domain.thy` | Interval lattice, `ivl_tf`, widening (`widen_ivl`), interval transfers |

**Layering:** `Sign_Domain` and `Interval_Domain` import `Constraint_System` (for the
`'a domain_transfer` type used by `sign_tf` / `ivl_tf`). The `domain_transfer` record
is defined in `Equations/Constraint_System.thy`.

**Key concepts:** `gamma` / `gamma_state`, `bot`, join (⊔); per-action soundness lemmas
(e.g. assign/assume). The bundle `domain_transfer_sound` is defined in
`Pipeline/Pipeline.thy`; analysis configs `sign_analysis_config` / `ivl_analysis_config`
live there too.

**Downstream:** `Equations/Constraint_System.thy` builds `rhs`; `Pipeline/Pipeline.thy`
— `sign_pipeline_sound`, `ivl_pipeline_sound`.

**Stretch goal:** Octagon domain (not yet in tree).
