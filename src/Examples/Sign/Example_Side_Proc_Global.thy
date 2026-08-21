section \<open>Example: TD\_side Sign Analysis on a Single Global Increment Call\<close>

theory Example_Side_Proc_Global
  imports
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_VIMP.VIMP_Notation"
    Example_Inc_Proc
begin

text \<open>
  Side-effecting interprocedural witness: \<open>inc_pi\<close> with a single call to
  procedure p. Its soundness uses the effectful side TD solver.
\<close>

(* A non-trivial initial state: every variable -- including the globals --
   starts at STop, not bot.  The entry seeds the initial globals into the
   single global unknown, so soundness holds for an arbitrary s0 (no
   restrict_global s0 = bot precondition). *)
definition side_proc_global_s0 :: "sign abs_state" where
  "side_proc_global_s0 = (\<lambda>_. STop)"

theorem proc_global_side_sign_analysis:
  fixes s t :: store and gs :: "vname \<Rightarrow> bool"
  assumes s_sound: "s \<in> \<lbrakk>side_proc_global_s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect gs (compile_prog inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>)) {s}
       (cfg_exit (compile_prog inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>)))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff gs (compile_prog inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>)) (sign_etf gs) bot
       side_proc_global_s0 ()
       (cfg_exit (compile_prog inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>)))"
  shows "t \<in> gamma_state_lift (side_analyse_eff gs inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>) (sign_etf gs) bot side_proc_global_s0 ()
         (cfg_exit (compile_prog inc_pi [(STR ''p'')] (STR ''main'') (imp \<lbrakk> p() \<rbrakk>))))"
  by (rule side_sign_analysis_sound[OF s_sound collect_exit side_solve_dom])
subsection \<open>Executable sign analysis\<close>

text \<open>Reuses @{const inc_program} (\<open>Example_Inc_Proc\<close>) directly rather than
  reconstructing an equivalent @{typ imp_prog} from @{const inc_pi}.\<close>

abbreviation inc_gs :: "vname \<Rightarrow> bool" where
  "inc_gs \<equiv> declared_global inc_program"

lemma inc_counter_nonneg:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (sign_exec_prog inc_gs (STR ''main'') inc_program) (STR ''counter'') = SNonNeg"
  by eval

lemma inc_terminates: "sign_terminates_prog inc_gs (STR ''main'') inc_program"
  by (rule sign_terminates_prog_via_solve_c) eval

corollary inc_certified_sound:
  "ltr_collect inc_gs (prog_cfg (STR ''main'') inc_program) (cinit_stores inc_gs) (cfg_exit (prog_cfg (STR ''main'') inc_program))
   \<le> gamma_state_lift (sign_exec_prog inc_gs (STR ''main'') inc_program)"
  by (rule sign_exec_prog_sound_collecting[OF refl inc_terminates])

end



