# Examples / CFG

Session `Voblint_Examples_CFG`, parented on `Voblint_Compile`: the domain-agnostic
compiler witness and the language regressions. Nothing here depends on an abstract
domain.

| File | Role | What |
| --- | --- | --- |
| `Example_Compile_Call_Free.thy` | required support | `no_proc_call`, the syntactic condition for a call-free source, and `compile_prog_calls_empty`, the theorem that such a source compiles to a graph with no call edges; each importer states its own program and reuses the theorem |
| `VIMP_Regression.thy` | regression | build-checked assertions on VIMP concrete syntax (statement boundaries, `else if`, operator precedence) and on comparison, `c_div` and `c_mod` semantics over signed operands |
| `Compile_Regression.thy` | regression | build-checked compiler facts moved out of core: both branches of a conditional return keep their result edge, and a self-call is a call edge into its own entry |
| `Elaboration_Regression.thy` | regression | elaboration of surface VIMP to core VIMP: kinds, conversions and variable identities |
| `CFG_Regression.thy` | regression | the graph `elab_cfg` builds for elaborated programs |

The compiler's behaviour on concrete programs (layout, call edges, the
well-formedness gate) is pinned by `tests/regression/` and
`codegen/regression/`.

Role vocabulary: repository `README.md`.
