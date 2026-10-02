# Examples / Interval

Interval-domain witnesses: flagship D/G runs and procedure-call soundness
spines. Context-sensitive D/G examples with entry-state contexts live in `Ctx/`;
call-string contexts are witnessed on Sign (`../Sign/CallString/`).

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Flagship.thy` | canonical spine | interval analysis of a counting loop, executed and certified on the D/G spine |
| `Example_Interval_DG_IP_Flagship.thy` | canonical spine | interprocedural: `twice` compiled and analyzed end to end through `FunctionEntry`/`FunctionResult` |
| `Interval_Regression.thy` | regression | build-checked assertions moved out of core: interval rendering, the check classifier on bounded and precision states, and the boundary witnesses of the numeric queries |

Analysis results on concrete programs (guard refinement, loop bounds, call
strings, per-context values) are pinned by the VIMP regression corpus under
`tests/regression/`, which runs the generated analyzer in seconds.

Role vocabulary: repository `README.md`.

## `Ctx/` — context routed by entered value

`twice` analyzed context-sensitively, each call site's context the entry value
of formal `p`, by the production entry-state analysis
(`Voblint_Analysis_Interval.Interval_Analyses`). Import chain:
`Ctx_Flagship` -> `Ctx_Collect` -> `Source_Ctx`.

| File | Role | What |
| --- | --- | --- |
| `Example_Interval_DG_Ctx_Flagship.thy` | canonical spine | the production entry-state analysis run on `twice`; each call site's context is the entry value of formal `p` |
| `Example_Interval_DG_Ctx_Collect.thy` | canonical spine | activation-indexed collecting soundness: `twice` as a named instance of `entry_state_activation_collect_sound` |
| `Example_Interval_Source_Ctx.thy` | canonical spine | the `twice` program called twice under distinct contexts — interprocedural, repeated-call, context-sensitive; not recursive |

### `Ctx/` — the entry-state family

`rc_program` is the entry-state coverage witness: one call whose argument is
unconstrained, so the routed context is `Top` itself — one context covering
every draw, rather than a family of contexts diverging over them. Import
chain: `EntryState_Base` -> `EntryState_Ctx` -> `EntryState_Collect`.

| File | Role | What |
| --- | --- | --- |

## `CallString/` — context routed by call site

Context routed by call site instead of entered value; `K1`/`K2` parameterize
the call-string bound `k`.

| File | Role | What |
| --- | --- | --- |
