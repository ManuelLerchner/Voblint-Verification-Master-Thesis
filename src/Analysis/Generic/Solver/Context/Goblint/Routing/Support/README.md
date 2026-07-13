# Routing support

Proof scaffolding for the Goblint routing story.

This folder packages reusable bridge lemmas that connect the routing contract to
collecting semantics and activation witnesses. It does not model a separate Goblint
interface.

## `Activation/`

| File | Role |
| --- | --- |
| `Activation_Witness_From.thy` | from-node-tracking witness calculus |
| `Seeded_Activation_Sound.thy` | activation collecting soundness |
| `Seeded_Activation_Reach.thy` | activation reachability |
