# Named-global sign — mixed-flow, side-effecting

A genuinely effectful sign transfer over named globals. Executable + sound
through the solver on the constant-route; the conditional-flag route is a
**documented boundary**: `flag_etf_mono_sides_unprovable` (`oops`) shows it is
provably not `mono_sides`, hence not solver-drivable. Work in progress — see the
`NamedGlobalSign/` row in `Instances/README.md`.

| File | Role |
| --- | --- |
| `Sign_Named_Global_Eff.thy` | named-global effectful sign transfer; constant-route soundness + the flag-route boundary |
