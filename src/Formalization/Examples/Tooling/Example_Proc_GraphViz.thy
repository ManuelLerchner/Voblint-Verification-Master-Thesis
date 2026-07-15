section \<open>Example: interprocedural CFG (compile_prog) as Graphviz\<close>

theory Example_Proc_GraphViz
  imports "Voblint_IMP2.IMP2_Notation" "Voblint_Analysis.Analysis_GraphViz"
begin

text \<open>
  Two @{const compile_prog} demos exported via @{const plain_dot_of_prog_lit}
  (procedure clusters from @{const compile_prog_regions}).  These are
  structural CFG witnesses only; annotated DOT needs an executable analysis
  result (see the sign executable examples).

  @verbatim\<open>
  Example A (simple):
    proc p { Gx := Gx + 1 }
    main { call p }

  Example B (multi-procedure, conditional calls):
    proc p { Gx := Gx + 1 }
    proc q { Gy := Gy + 1 }
    main {
      if Gx < Gy then call p else call q
    }
  \<close>

  Visual legend (see also docs/GraphViz-improvements.md):
  green double circle = program entry/exit;
  green box = procedure entry (target of @{term EA_Enter});
  red box = procedure exit (middle of a @{term combines} triple);
  purple thick edge = enter; dashed blue = combine.
\<close>

(* -- Example A: single call -------------------------------------- *)

definition proc_p_body :: com where
  "proc_p_body = \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition proc_table_a :: proc_table where
  "proc_table_a = ((\<lambda>_. None)(''p'' := Some (proc_decl_legacy proc_p_body)))"

definition prog_call_p :: com where
  "prog_call_p = Call None ''p'' []"

definition procs_a :: "pname list" where
  "procs_a = [''p'']"

(* -- Example B: two procedures + branch -------------------------- *)

definition proc_q_body :: com where
  "proc_q_body = \<lbrakk> Gy := Gy + 1 \<rbrakk>"

definition proc_table_b :: proc_table where
  "proc_table_b = (proc_table_a(''q'' := Some (proc_decl_legacy proc_q_body)))"

definition prog_if_calls :: com where
  "prog_if_calls = \<lbrakk> if (Gx < Gy) { p() } else { q() } \<rbrakk>"

definition procs_b :: "pname list" where
  "procs_b = [''p'', ''q'']"

(* -- DOT output -------------------------------------------------- *)

subsection \<open>DOT output\<close>

text \<open>
  @{const plain_dot_of_prog_lit} bundles @{const compile_prog},
  @{const compile_prog_regions}, and labeled rendering into one call.
  The result is a native ML @{text "string"} -- a single @{command ML_val}
  with @{text "writeln"} suffices.
\<close>

ML_val \<open>
  writeln (@{code plain_dot_of_prog_lit}
             @{code proc_table_a} @{code procs_a} @{code prog_call_p})
\<close>

ML_val \<open>
  writeln (@{code plain_dot_of_prog_lit}
             @{code proc_table_b} @{code procs_b} @{code prog_if_calls})
\<close>

end
