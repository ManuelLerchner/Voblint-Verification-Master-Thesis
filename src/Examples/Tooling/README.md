# Examples / Tooling

Rendering / visualisation demos outside the proof spine.

| File | Role | What |
| --- | --- | --- |
| `Example_Proc_GraphViz.thy` | tooling | interprocedural CFG (`compile_prog`) exported as Graphviz DOT (`plain_dot_of_prog_lit`; two demo programs) |
| `Example_Proc_GraphViz_Recursion.thy` | tooling | recursive-procedure CFG (built on `Example_Compile_Baseline`, see `../CFG/`) exported as Graphviz DOT |

The annotated (domain-parameterised) DOT renderer lives in
`Voblint_Analysis.Analysis_GraphViz`; this folder is the plain structural export.
Role vocabulary: repository `README.md` § Architecture.
