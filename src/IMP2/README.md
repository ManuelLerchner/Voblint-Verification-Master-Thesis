# IMP2

**Main contribution:** The source language layer — IMP2 with parameterless procedures
and a locals/globals split. Provides the `com` datatype, frame-stack small-step
semantics, and a bridge to AFP IMP2 for the thesis reference anchor.

**Theories**

| File                    | Role                                                                                                               |
| ----------------------- | ------------------------------------------------------------------------------------------------------------------ |
| `IMP2_Syntax.thy`       | Base `com` (SKIP, Assign, Seq, If, While), `aexp`, `bexp` datatypes; countability instances; HOL-IMP leaf wraps    |
| `IMP2_Expr.thy`         | `aval`, `bval` — expression evaluation only; leaf cases delegate to HOL-IMP `AExp` / `BExp`                        |
| `HOL_IMP_Countable.thy` | Countability for wrapped HOL-IMP `AExp` / `BExp` types                                                             |
| `IMP2_Globals.thy`      | `combine_states <s\|t>`, `enter_state`, `is_global`; `pname` type synonym                                          |
| `IMP2_Proc.thy`         | Extended `com` with Scope / Call / Restore; `proc_table`; `pstep` (frame-stack small-step, `→ₚ`), `psteps` (`→ₚ*`) |
| `IMP2_Bridge.thy`       | One-way bridge: our `com` / `store` → AFP `IMP2` (expression embedding + scalar-array state embedding)             |
| `IMP2_VCG_Example.thy`  | Example showing IMP2's own VCG and our analyzer agreeing on one program                                            |

**Key concepts:**

- `com` in `IMP2_Proc.thy` — SKIP, Assign, Seq, If, While, Scope, Call, Restore.
- `proc_table = pname ⇒ com option`; `frame = store`.
- `pstep pi (c, s, frs) (c', s', frs')` — frame-stack small-step; `Restore` pops frame and restores locals via `combine_states`.
- `is_global x` — variable `x` is global iff it is empty or starts with `'G'`.
- `combine_states s t = <s|t>` — locals from `s`, globals from `t`.
- `enter_state s` — globals from `s`, locals reset to 0.

**Downstream:** `CFG/IMP2_Proc_to_CFG.thy` compiles `com` programs with a `proc_table` to
interprocedural CFGs; `CFG/Collecting/CFG_Collect_Runs.thy` defines `cfg_runs_to`.
