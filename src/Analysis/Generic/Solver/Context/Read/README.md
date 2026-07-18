# Read

Keyed-global generator scaffolding for the side-effecting solver. The relational
digest/compatibility read layer was retired (see
`docs/DIGEST_SPINE_REMOVAL_PLAN.md`); the retained analyses read their own
per-context slot directly on the DG spine (`DG/`), so no separate read-interface
model remains here.

Generic keyed-context bridge scaffolding:

| File | Role |
| --- | --- |
| `TD_Side_Eff_Ctx_Shared.thy` | shared context-pull helpers |
| `TD_Side_Eff_Keyed_Gen.thy` | functional keyed-global generator (routes global writes by context) |
