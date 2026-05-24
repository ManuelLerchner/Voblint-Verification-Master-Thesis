# IMP2

**Main contribution:** The source language layer — IMP2 syntax (native `com` datatype;
HOL-IMP leaf wraps for shared `aexp`/`bexp` forms) and small-step operational semantics,
linked later to CFG collecting semantics via `runs_to`.

**Theories**

| File | Role |
| --- | --- |
| `IMP2_Syntax.thy` | `com`, `aexp`, `bexp` datatypes; countability instances |
| `IMP2_SmallStep.thy` | `aval`, `bval`, `small_step`, `small_steps` (`→*`), determinism |
| `HOL_IMP_Countable.thy` | Countability for wrapped HOL-IMP `AExp` / `BExp` types |

**Key concepts:** small-step `(c, s) → (c', s')`; terminating runs `(c, s) →* (SKIP, t)`;
`code_pred small_step` in `IMP2_SmallStep.thy`.

**Downstream:** `CFG/IMP2_to_CFG.thy` compiles commands to CFGs;
[`CFG/Collecting/`](../CFG/Collecting/) proves `runs_to_iff_small_step` in `CFG_Runs_To_Bridge.thy`.
