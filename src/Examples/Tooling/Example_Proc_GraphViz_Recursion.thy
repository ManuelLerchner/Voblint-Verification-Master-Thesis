section \<open>Example: recursive interprocedural CFG as Graphviz\<close>

theory Example_Proc_GraphViz_Recursion
  imports
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Analysis.Analysis_GraphViz"
    Example_Compile_Baseline
begin

definition dot_main_name :: pname where
  "dot_main_name = ''main''"

text \<open>
  This example exports the interprocedural CFG of a recursive factorial
  procedure through @{const raw_cfg_dot_lit}.

  Green double circles mark procedure entries.
  Red double circles mark procedure results.
  Purple solid edges enter callees.
  Dashed blue edges resume callers.
\<close>

subsection \<open>DOT output\<close>

text \<open>@{const factorial_program} is the shared recursive-factorial witness from
  @{text Example_Compile_Baseline}, which also provides its compiled
  @{const Example_Compile_Baseline.factorial_cfg} for direct inspection.\<close>

definition factorial_dot :: String.literal where
  "factorial_dot =
     raw_cfg_dot_lit
       (prog_table factorial_program)
       (prog_procs factorial_program)
       dot_main_name
       (prog_main factorial_program)
       no_annotations"

ML_val \<open>
  writeln (@{code factorial_dot})
\<close>

end