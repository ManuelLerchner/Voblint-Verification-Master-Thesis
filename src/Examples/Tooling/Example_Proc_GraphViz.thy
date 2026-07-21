section \<open>Example: interprocedural CFG (compile_prog) as Graphviz\<close>

theory Example_Proc_GraphViz
  imports "Voblint_IMP2.IMP2_Notation" "Voblint_Analysis.Analysis_GraphViz"
begin

text \<open>
  Two @{const compile_prog} demos exported via @{const raw_cfg_dot_lit}.
  These are structural CFG witnesses; annotated DOT requires an executable analysis
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
  "proc_p_body = imp \<lbrakk> Gx := Gx + 1 \<rbrakk>"

definition proc_table_a :: proc_table where
  "proc_table_a = ((\<lambda>_. None)(''p'' := Some (proc_decl_of [] proc_p_body None)))"

definition prog_call_p :: com where
  "prog_call_p = Call None ''p'' []"

definition procs_a :: "pname list" where
  "procs_a = [''p'']"

(* -- Example B: two procedures + branch -------------------------- *)

definition proc_q_body :: com where
  "proc_q_body = imp \<lbrakk> Gy := Gy + 1 \<rbrakk>"

definition proc_table_b :: proc_table where
  "proc_table_b = (proc_table_a(''q'' := Some (proc_decl_of [] proc_q_body None)))"

definition prog_if_calls :: com where
  "prog_if_calls = imp \<lbrakk> if (Gx < Gy) { p() } else { q() } \<rbrakk>"

definition procs_b :: "pname list" where
  "procs_b = [''p'', ''q'']"

(* -- DOT output -------------------------------------------------- *)

subsection \<open>DOT output\<close>

text \<open>
  @{const raw_cfg_dot_lit} compiles the program and renders it through the
  canonical graph model and DOT backend.  The result is a native ML @{text "string"};
  a single @{command ML_val} call with @{text "writeln"} suffices.
\<close>

ML_val \<open>
  writeln (@{code raw_cfg_dot_lit}
             @{code proc_table_a} @{code procs_a} @{code prog_call_p})
\<close>

ML_val \<open>
  writeln (@{code raw_cfg_dot_lit}
             @{code proc_table_b} @{code procs_b} @{code prog_if_calls})
\<close>

end
