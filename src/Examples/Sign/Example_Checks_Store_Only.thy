section \<open>Example: checks_proven/checks_proven_sound alone, store-only\<close>

theory Example_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_Analysis.Sign_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

text \<open>
  Exercises \<^const>\<open>checks_proven\<close> and \<open>checks_proven_sound\<close> alone, against a
  computed (not hand-built) Sign post-solution, with no ghost or
  trace-projection content: the check condition is a plain \<^typ>\<open>bexp\<close>,
  evaluated by \<^const>\<open>bval\<close> against \<^const>\<open>gamma_state\<close>, anchored to the same
  \<^const>\<open>ltr_collect\<close> soundness every other Sign example already relies on.
  This is G-A1's acceptance case: the check machinery derisked on its own,
  independently of any ghost fact.
\<close>

definition checks_ex_program :: imp_prog where
  "checks_ex_program = program { void main() { y := 5 } }"

text \<open>Non-vacuity, at the source semantics: a concrete run exists, so the
  payoff below is not vacuously true of an unreachable program.\<close>
lemma checks_ex_run:
  fixes s :: store and gs :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
  shows "pcompletes gs \<Pi> (prog_main checks_ex_program) s (s(''y'' := 5))"
  unfolding checks_ex_program_def
  using pcompletes_assign[of gs \<Pi> "''y''" "N 5" s] by simp

lemma checks_ex_exec_y: "sign_exec_prog ''main'' checks_ex_program ''y'' = SPos"
  by eval

lemma checks_ex_solver_terminates: "sign_terminates_prog ''main'' checks_ex_program"
  by (rule sign_terminates_prog_via_solve_c) eval

corollary checks_ex_exit_sound:
  "ltr_collect is_global (prog_cfg ''main'' checks_ex_program) (cinit_stores is_global)
     (cfg_exit (prog_cfg ''main'' checks_ex_program))
   \<le> \<lbrakk>sign_exec_prog ''main'' checks_ex_program\<rbrakk>"
  by (rule sign_exec_prog_sound_collecting[OF checks_ex_solver_terminates])

definition checks_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ex_reach v = ltr_collect is_global (prog_cfg ''main'' checks_ex_program) (cinit_stores is_global) v"

definition checks_ex_checks :: checks where
  "checks_ex_checks v =
     (if v = cfg_exit (prog_cfg ''main'' checks_ex_program)
      then Some (Not (Less (V ''y'') (N 0))) else None)"

lemma checks_ex_checks_proven: "checks_proven checks_ex_checks checks_ex_reach"
proof (rule checks_provenI)
  fix v c s
  assume ck: "checks_ex_checks v = Some c" and mem: "s \<in> checks_ex_reach v"
  from ck have v_exit: "v = cfg_exit (prog_cfg ''main'' checks_ex_program)"
    and c_eq: "c = Not (Less (V ''y'') (N 0))"
    unfolding checks_ex_checks_def by (auto split: if_splits)
  from mem v_exit have "s \<in> ltr_collect is_global (prog_cfg ''main'' checks_ex_program)
      (cinit_stores is_global) (cfg_exit (prog_cfg ''main'' checks_ex_program))"
    unfolding checks_ex_reach_def by simp
  then have s_in: "s \<in> \<lbrakk>sign_exec_prog ''main'' checks_ex_program\<rbrakk>"
    using checks_ex_exit_sound by blast
  then have "s ''y'' \<in> gamma_sign (sign_exec_prog ''main'' checks_ex_program ''y'')"
    using gamma_stateD[OF s_in] by simp
  then have "s ''y'' \<ge> 0" using checks_ex_exec_y by simp
  then show "bval c s" unfolding c_eq by simp
qed

text \<open>The payoff: every concrete store reaching the exit satisfies the
  \<open>y \<ge> 0\<close> assertion, derived through \<open>checks_proven_sound\<close> alone --- no
  ghost projection, no trace-indexed condition type.\<close>

corollary checks_ex_exit_nonneg:
  assumes "t \<in> checks_ex_reach (cfg_exit (prog_cfg ''main'' checks_ex_program))"
  shows "bval (Not (Less (V ''y'') (N 0))) t"
proof -
  have "checks_ex_checks (cfg_exit (prog_cfg ''main'' checks_ex_program))
          = Some (Not (Less (V ''y'') (N 0)))"
    unfolding checks_ex_checks_def by simp
  then show ?thesis using checks_proven_sound[OF checks_ex_checks_proven] assms by blast
qed

end
