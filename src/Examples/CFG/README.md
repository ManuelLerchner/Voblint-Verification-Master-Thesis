# Examples / CFG

The domain-agnostic compiler witness every domain's flagship reuses. Nothing here depends on an abstract
domain; compare with `../Sign/`, `../Interval/`, `../Parity/`, `../Int/` for
domain-specific procedure-call spines.

| File | Role | What |
| --- | --- | --- |
| `Example_Compile_Call_Free.thy` | required support | `no_proc_call`, the syntactic condition for a call-free source, and `compile_prog_calls_empty`, the theorem that such a source compiles to a graph with no call edges; each importer states its own program and reuses the theorem |
| `VIMP_Regression.thy` | regression | build-checked assertions on VIMP concrete syntax (statement boundaries, `else if`, operator precedence) and on comparison, `c_div` and `c_mod` semantics over signed operands |
| `Elaborated_Compilation_Regression.thy` | regression | build-checked facts about the elaboration: an erased residual `x = 1` sits at both branch nodes while its annotated form sits at one, identical procedure bodies stay apart, a call from `main` is run through `Return`, `Unwind` and `Restore` with the node `point` names at each step, every annotation agrees with the edge the compiler emits, and nested, looping and calling programs meet `wf_compile_input` |
| `Compile_Regression.thy` | regression | build-checked compiler facts moved out of core: both branches of a conditional return keep their result edge, and a self-call is a call edge into its own entry |

The compiler's behaviour on concrete programs (layout, call edges, the
well-formedness gate) is pinned by `tests/regression/` and
`codegen/regression/`.

Role vocabulary: repository `README.md`.
