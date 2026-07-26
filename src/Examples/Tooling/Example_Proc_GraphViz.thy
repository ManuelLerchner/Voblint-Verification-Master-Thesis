section \<open>Example: interprocedural CFG (compile_prog) as Graphviz\<close>

theory Example_Proc_GraphViz
  imports "Voblint_IMP2.IMP2_Notation" "Voblint_Analysis.Analysis_GraphViz"
begin

definition dot_main_name :: pname where
  "dot_main_name = ''main''"

text \<open>
  Two @{const compile_prog} results are exported through @{const raw_cfg_dot_lit}.
  The first graph has one procedure call.  The second has two procedures selected by
  a conditional in main.

  Green double circles mark procedure entries.  Red double circles mark procedure
  results.  Purple solid edges enter callees; dashed blue edges resume callers.
\<close>

subsection \<open>Single call\<close>

definition proc_p_body :: com where
  "proc_p_body = imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition proc_table_a :: proc_table where
  "proc_table_a = ((\<lambda>_. None)(''p'' := Some (proc_decl_of [] proc_p_body)))"

definition prog_call_p :: com where
  "prog_call_p = imp \<lbrakk> p() \<rbrakk>"

definition procs_a :: "pname list" where
  "procs_a = [''p'']"

subsection \<open>Conditional calls to two procedures\<close>

definition proc_q_body :: com where
  "proc_q_body = imp \<lbrakk> Gy := Gy + 1 \<rbrakk>"

definition proc_table_b :: proc_table where
  "proc_table_b = (proc_table_a(''q'' := Some (proc_decl_of [] proc_q_body)))"

definition prog_if_calls :: com where
  "prog_if_calls = imp \<lbrakk> if (Gx < Gy) { p() } else { q() } \<rbrakk>"

definition procs_b :: "pname list" where
  "procs_b = [''p'', ''q'']"

subsection \<open>DOT output\<close>

subsection \<open>DOT output\<close>

text \<open>
  @{const raw_cfg_dot_lit} compiles the program and renders it through the
  canonical graph model and DOT backend.  The result is a native ML @{text "string"};
  a single @{command ML_val} call with @{text "writeln"} suffices.
\<close>

ML_val \<open>
  writeln (@{code raw_cfg_dot_lit}
             @{code proc_table_a} @{code procs_a} @{code dot_main_name} @{code prog_call_p})
\<close>

ML_val \<open>
  writeln (@{code raw_cfg_dot_lit}
             @{code proc_table_b} @{code procs_b} @{code dot_main_name} @{code prog_if_calls})
\<close>

end
