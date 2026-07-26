# Context-keyed solver helpers

This directory contains the small compatibility layer used by functional
context-keyed side-solver equations.

| File | Role |
| --- | --- |
| `TD_Side_Eff_Ctx_Shared.thy` | Context pullback and shared helper lemmas |
| `TD_Side_Eff_Keyed_Gen.thy` | Functional keyed-global generator |

The generic D/G framework is the public modular-analysis interface. New
analyses should use it unless they specifically require the functional keyed
generator.
