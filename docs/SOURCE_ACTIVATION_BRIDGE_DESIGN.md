# Source-to-activation bridge — historical design record

Status: SUPERSEDED. No code changed by this record.

This document originally claimed that the second return of the `twice` example was empty.
That claim was mechanically refuted: `cfg_collect_ctx_act … twice_cfg … 7 bot ≠ {}`, with
the expected `y = 20`. The old witness reaches that result through a re-rooted
whole-program callee execution, so its defect is compositionality rather than vacuity.

The canonical source-bridge target is now
[`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md):

```text
pstep → cstep → valid_ltr → cfg_collect_ctx_act → analysis
```

The source proof is a decomposition of the concrete runtime stack into nested local activation
traces. It does not widen `trace_witness_act`, introduce a parallel set collecting semantics,
or restore `twf/twfr`.

