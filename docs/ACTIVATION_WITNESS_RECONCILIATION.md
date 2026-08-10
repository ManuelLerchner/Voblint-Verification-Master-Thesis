# Activation witness reconciliation — historical evidence

Status: historical analysis. No `.thy` files changed by this record. The adopted architectural
decision is [`ACTIVATION_LOCAL_TRACE_CONVERGENCE.md`](ACTIVATION_LOCAL_TRACE_CONVERGENCE.md).

## Mechanical correction

The claim that the second `twice` return was vacuous was false. In a live Isabelle I/R
session, the following was proved:

```text
cfg_collect_ctx_act … twice_cfg … 5 bot ≠ {}
cfg_collect_ctx_act … twice_cfg … 7 bot ≠ {}
```

The node-7 witness yields the genuine result `y = 20`. The old relation obtains its callee
through an independently re-rooted whole-program run whose head is the bound entry store
`p = 10`. Thus the old activation theorem is not refuted and its `twice` result is not
vacuous.

## What this established

The defect is representational and compositional:

```text
source runtime frame
    ≠
independently re-rooted global callee witness
```

A source execution cannot be mapped homomorphically to the old `combine` premise. Flat
repeated calls may be inhabited through re-rooting; this does not provide the stack-faithful
basis needed for a recursive source bridge.

The deleted `twf/twfr` calculus supplied the opposite capability — frame-origin composition
— but used `enter_state` rather than `edge_step` and therefore lost formal-parameter
binding. Neither old relation is the endpoint.

## Consequence

The reconciliation initially suggested an origin-parameterised witness. Subsequent review
improved that proposal: a concrete activation-local trace tree is clearer and keeps abstract
contexts out of the foundational semantics. `valid_ltr` absorbs the useful properties:

- concrete caller-created callee entries;
- `edge_step` / `bind_formals` faithfulness;
- structural nested and recursive returns;
- context as a projection rather than trace state.

The old `trace_witness_act` remains migration evidence only and is deleted after the
canonical local-trace backbone and source bridge are proved.
