section \<open>Example: TD\_side Interval Analysis on a Single Global Increment Call\<close>

theory Example_Interval_Side_Proc_Global
  imports "Voblint_Analysis.Interval_Side_Soundness" "Voblint_CFG.CFG_Collect_Runs"
          "Voblint_IMP2.IMP2_Notation"
begin

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

text \<open>
  Interval instance of the side-effecting interprocedural witness: the same
  @{const inc_pi} program (a single call to procedure p incrementing the global
  @{term \<open>''Gx''\<close>}) carried through the @{const side_analyse_eff} solver at the
  interval domain.  Demonstrates the soundness scaffold is domain-generic by
  reusing it on a second, infinite-height numeric domain.
\<close>

text \<open>
  Initial state: every variable -- including the globals -- starts at the full
  interval @{term \<open>Ivl MinInf PlusInf\<close>} (top), the interval analogue of sign top.
\<close>
definition side_proc_global_ivl_s0 :: "ivl abs_state" where
  "side_proc_global_ivl_s0 = (\<lambda>_. Ivl MinInf PlusInf)"

theorem proc_global_side_ivl_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> \<lbrakk>side_proc_global_ivl_s0\<rbrakk>"
  assumes runs: "cfg_runs_to inc_pi [''p''] (Call None ''p'' []) s t"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog inc_pi [''p''] (Call None ''p'' [])) ivl_etf bot
       side_proc_global_ivl_s0 ()
       (cfg_exit (compile_prog inc_pi [''p''] (Call None ''p'' [])))"
  shows "t \<in> \<lbrakk>side_analyse_eff inc_pi [''p''] (Call None ''p'' []) ivl_etf bot side_proc_global_ivl_s0 ()
         (cfg_exit (compile_prog inc_pi [''p''] (Call None ''p'' [])))\<rbrakk>"
proof -
  have collect_exit:
    "t \<in> cfg_collect (compile_prog inc_pi [''p''] (Call None ''p'' [])) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (Call None ''p'' [])))"
    using runs unfolding cfg_runs_to_def
    by metis
  show ?thesis
    by (rule side_ivl_analysis_sound[OF s_sound collect_exit side_solve_dom])
qed

end
