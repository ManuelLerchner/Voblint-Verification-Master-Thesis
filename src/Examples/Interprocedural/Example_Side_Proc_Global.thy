section \<open>Example: TD\_side Sign Analysis on a Single Global Increment Call\<close>

theory Example_Side_Proc_Global
  imports
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_IMP2.IMP2_Notation"
begin

text \<open>
  Side-effecting interprocedural witness: \<open>inc_pi\<close> with a single call to
  procedure p. Its soundness uses the effectful side TD solver.
\<close>

text \<open>The analyzed program, defined locally so the example is self-contained: a single
  procedure \<open>p\<close> increments the global \<open>Gx\<close>, \<open>main\<close> calls it once.\<close>
definition inc_program :: imp_prog where
  "inc_program = program {
     int Gx;
     void p() { Gx := Gx + 1 }
     void main() { p() }
   }"

definition inc_pi :: proc_table where
  "inc_pi = prog_table inc_program"

(* A non-trivial initial state: every variable -- including the globals --
   starts at STop, not bot.  The entry seeds the initial globals into the
   single global unknown, so soundness holds for an arbitrary s0 (no
   restrict_global s0 = bot precondition). *)
definition side_proc_global_s0 :: "sign abs_state" where
  "side_proc_global_s0 = (\<lambda>_. STop)"

theorem proc_global_side_sign_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> \<lbrakk>side_proc_global_s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)) {s}
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)) sign_etf bot
       side_proc_global_s0 ()
       (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))"
  shows "t \<in> \<lbrakk>side_analyse_eff inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>) sign_etf bot side_proc_global_s0 ()
         (cfg_exit (compile_prog inc_pi [''p''] ''main'' (imp \<lbrakk> p() \<rbrakk>)))\<rbrakk>"
  by (rule side_sign_analysis_sound[OF s_sound collect_exit side_solve_dom])
subsection \<open>Executable sign analysis\<close>

definition inc_procs :: "pname list" where
  "inc_procs = [''p'']"


definition inc_main :: com where
  "inc_main = imp \<lbrakk> p() \<rbrakk>"
definition inc_prog_mnm :: pname where "inc_prog_mnm = ''main''"

definition inc_prog :: imp_prog where
  "inc_prog = imp_prog.make [(''p'', the (inc_pi ''p''))] inc_main"


value "sign_exec_prog ''main'' inc_prog ''Gx''"

lemma inc_gx_nonneg:
  "sign_exec_prog ''main'' inc_prog ''Gx'' = SNonNeg"
  by eval

lemma inc_terminates: "sign_terminates_prog ''main'' inc_prog"
  by (rule sign_terminates_prog_via_solve_c) eval

corollary inc_certified_sound:
  "ltr_collect (prog_cfg ''main'' inc_prog) cinit_stores (cfg_exit (prog_cfg ''main'' inc_prog))
   \<le> \<lbrakk>sign_exec_prog ''main'' inc_prog\<rbrakk>"
  by (rule sign_exec_prog_sound_collecting[OF inc_terminates])

subsection \<open>Annotated CFG visualisation\<close>

text \<open>
  @{const sign_annotated_dot_prog_lit} on the same witness: CFG nodes labelled
  with sign abstract states from @{const sign_exec_raw} (exit @{thm [source] inc_gx_nonneg}).
\<close>


ML_val \<open>
  writeln (@{code sign_annotated_dot_prog_lit} @{code inc_prog_mnm} @{code inc_prog})
\<close>

end



