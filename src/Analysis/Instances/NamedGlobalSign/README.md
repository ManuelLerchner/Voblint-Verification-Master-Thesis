# Named-global sign — mixed-flow, side-effecting

A genuinely effectful sign transfer over named globals. Executable + sound
through the solver on the constant route (edge contributions to `Gpos`, combine
contributions to `Gneg`): both named slots are populated and the routing is
monotone, so the TD_side preconditions discharge.

| File | Role |
| --- | --- |
| `Sign_Named_Global_Eff.thy` | named-global effectful sign transfer; constant-route soundness through the side solver |
