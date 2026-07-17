# Local activation trace semantics — historical design record

Status: SUPERSEDED. No code changed by this record.

This draft made the essential move from context-threaded witnesses to concrete local
activation traces. Its proposed `Call` ancestry, faithful `edge_step` entry, and
stack-oriented source bridge are retained.

It is not the adopted endpoint because it introduced a sibling `local_ctx_collect` and
sibling soundness theorem, and its two-constructor trace could express only caller-restoring
returns. The final design keeps one activation-sensitive API:

```text
valid_ltr → cfg_collect_ctx_act → Activation_Backbone → DG_Ctx_Activation
```

A concrete `Resume caller callee path` constructor retains enough return evidence for general
`combc`. See
[`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md).

