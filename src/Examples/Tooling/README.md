# Examples / Tooling

Rendering / visualisation demos outside the proof spine.

| File | Role | What |
| --- | --- | --- |
| `Example_Proc_GraphViz.thy` | tooling | interprocedural CFG (`compile_prog`) exported as Graphviz DOT (`plain_dot_of_prog_lit`; two demo programs) |
| `Example_Mixed_Sign_Interval_GraphViz.thy` | tooling + witness | mixed Sign/Interval analysis (`Instances/Mixed`) on `x := -1; x := 2`: solver run, `part_post_solution`, expected values (`SPos` exit answer, `[-1, 2]` side invariant), DOT with Sign stores at nodes and the Interval invariant in a separate cluster |

The annotated (domain-parameterised) DOT renderer lives in
`Voblint_Analysis.Analysis_GraphViz`; this folder is the plain structural export.
Role vocabulary: repository `README.md` § Architecture.
