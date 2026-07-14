# Read

Global-read and digest-refinement infrastructure.

| File | Role |
| --- | --- |
| `Global_Cmp_Read.thy` | context-filtered global read |
| `Context_Domain.thy` | context domain and routing base |
| `Digest_Global_Read.thy` | digest-refined global read kernel |
| `Clean_RRead_Sound.thy` | clean read-side soundness |

## `Read/Support/`

Generic digest and keyed-context bridge scaffolding.

| File | Role |
| --- | --- |
| `TD_Side_Eff_Cmp_Sound.thy` | cmp combine layer and soundness |
| `TD_Side_Eff_Cmp_Pull.thy` | cmp pullback discharge |
| `TD_Side_Eff_Cmp_Gen.thy` | keyed generator bridge |
| `Value_Digest_Reader.thy` | generic value-projected reader |
