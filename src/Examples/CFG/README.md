# Examples / CFG

The domain-agnostic compiler witness every domain's flagship reuses. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Int/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Compile_Call_Free.thy` | required support | `no_proc_call`, the syntactic condition for a call-free source, and `compile_prog_calls_empty`, the theorem that such a source compiles to a graph with no call edges; each importer states its own program and reuses the theorem |

The compiler's behaviour on concrete programs (layout, call edges, the
well-formedness gate) is pinned by `tests/regression/` and
`codegen/regression/`.

Role vocabulary: repository `README.md`.
