# Origin-parameterised witness calculus — historical design record

Status: SUPERSEDED. No code changed by this record.

This design identified two durable requirements:

- a callee must be born from its concrete caller rather than an arbitrary start;
- call entry must use `edge_step (EA_Enter …)` and retain `bind_formals`.

It put abstract contexts inside the foundational witness, so it is not the adopted design.
The canonical replacement is
[`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md).
There, concrete `Call` and `Resume` ancestry supplies frame identity and return evidence;
`enterc` and `combc` are computed only by a projection over the concrete trace.

The old `twf/twfr` relations remain deleted. Their useful frame-origin insight is absorbed by
`valid_ltr`; their parameter-binding loss is not reintroduced.

