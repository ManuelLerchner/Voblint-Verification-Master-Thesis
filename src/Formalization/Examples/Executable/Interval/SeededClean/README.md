# Examples / Executable / Interval / SeededClean

Interval executable witnesses for the context-sliced (seeded-clean) and
DG-native keyed disciplines.

| File | Role | What |
| --- | --- | --- |
| `Exec_Ivl_Cmp_Seed_Sound.thy` | seeded-clean R_read spine | interval instantiates the generic seeded-clean R_read soundness (`apply_etf_ivl_etf_clean`, `Clean_RRead_Sound`) |
| `Exec_Ivl_Cmp_Seed_Enter.thy` | DG seeded-enter witness | native DG seeded-enter run on the interval program (`seed_wit_sound`) |
| `Exec_Ivl_Cmp_Keyed_DG_Run.thy` | DG keyed witness | DG-native keyed-slot separation over interval contexts |

For the full executable D/G run — source through certified computed result — see
`../Core/Example_Interval_DG_Flagship.thy`.
