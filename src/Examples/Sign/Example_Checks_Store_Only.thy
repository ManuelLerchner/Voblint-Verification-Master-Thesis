section \<open>Example: checks_proven/checks_proven_sound alone, store-only\<close>

theory Example_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_Analysis.Sign_Exec_Sound" "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

text \<open>
  Exercises \<^const>\<open>checks_proven\<close> and \<open>checks_proven_sound\<close> against a computed
  (not hand-built) Sign post-solution, consuming the \<^const>\<open>checks\<close> field a real
  compiler run populates (\<open>collect_checks_prog\<close>, \<open>VIMP_Proc_to_CFG.thy\<close>) directly
  --- two \<open>check(...)\<close> source statements at distinct positions, so a numbering
  mistake in \<open>collect_checks\<close> would show up as a wrong node in the \<open>by eval\<close> step
  below, not merely in the abstract soundness proof. No ghost or trace-projection
  content: the check condition is a plain \<^typ>\<open>bexp\<close>, evaluated by \<^const>\<open>bval\<close>
  against \<^const>\<open>gamma_state\<close>, anchored to the same \<^const>\<open>ltr_collect\<close> soundness
  every other Sign example already relies on.
\<close>

definition checks_ex_program :: imp_prog where
  "checks_ex_program = program {
     void main() {
       y := 5;
       check(0 < y);
       z := 1;
       check(0 < z)
     }
   }"

text \<open>Computed, not asserted: both \<open>check(...)\<close> statements land at the node
  \<^const>\<open>compile\<close> actually assigns them --- \<^term>\<open>Statement 1\<close> right after
  \<open>y := 5\<close>, \<^term>\<open>Statement 3\<close> after \<open>z := 1\<close>. If \<^const>\<open>collect_checks\<close>'s
  counter threading were wrong, this equation would fail, not merely mislabel
  a check.\<close>
lemma checks_ex_checks_eval:
  "checks (prog_cfg ''main'' checks_ex_program) =
     {(Statement 1, Less (N 0) (V ''y'')), (Statement 3, Less (N 0) (V ''z''))}"
  unfolding prog_cfg_def by eval

lemma checks_ex_exec_y: "sign_exec_prog ''main'' checks_ex_program ''y'' = SPos"
  by eval

lemma checks_ex_exec_z: "sign_exec_prog ''main'' checks_ex_program ''z'' = SPos"
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

text \<open>The compiled edges downstream of each check, read off \<^const>\<open>prog_cfg\<close>'s
  own \<open>eval\<close>-computed shape: \<open>Statement 1\<close> (\<open>check(0 < y)\<close>) reaches
  \<open>Statement 2\<close> (\<open>z := 1\<close>) reaches \<open>Statement 3\<close> (\<open>check(0 < z)\<close>) reaches the
  epilogue \<open>Statement 4\<close> reaches \<open>cfg_exit\<close>. Only \<open>z := 1\<close> is a real store
  change, and it never touches \<open>y\<close>, so every store reaching either check is
  also, unchanged in the variable that check names, a store reaching the exit.\<close>
lemma checks_ex_intra_eval:
  "intra (prog_cfg ''main'' checks_ex_program) =
     {(FunctionEntry ''main'', EA_Nop, Statement 0),
      (Statement 0, EA_Assign ''y'' (N 5), Statement 1),
      (Statement 1, EA_Nop, Statement 2),
      (Statement 2, EA_Assign ''z'' (N 1), Statement 3),
      (Statement 3, EA_Nop, Statement 4),
      (Statement 4, EA_Ret None ''main'', FunctionResult ''main'')}"
  unfolding prog_cfg_def by eval

lemma checks_ex_exit_eval: "cfg_exit (prog_cfg ''main'' checks_ex_program) = FunctionResult ''main''"
  unfolding prog_cfg_def by eval

lemma checks_ex_entry_eval: "cfg_entry (prog_cfg ''main'' checks_ex_program) = FunctionEntry ''main''"
  unfolding prog_cfg_def by eval

text \<open>Non-vacuity: \<open>checks_proven\<close> is not merely vacuously true because no store ever reaches
  either check. The all-zero store, admissible as an initial \<^const>\<open>cinit_stores\<close> witness, runs
  the compiled prefix \<open>y := 5\<close> and lands at \<open>Statement 1\<close> --- the first check's own node.\<close>
lemma checks_ex_reach1_nonempty: "checks_ex_reach (Statement 1) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores is_global" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ex_reach (FunctionEntry ''main'')"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect is_global (prog_cfg ''main'' checks_ex_program) (cinit_stores is_global)
            (cfg_entry (prog_cfg ''main'' checks_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ex_reach_def checks_ex_entry_eval .
  qed
  have e0: "(FunctionEntry ''main'', EA_Nop, Statement 0) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "FunctionEntry ''main''" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ex_reach_def by simp
  have e1: "(Statement 0, EA_Assign ''y'' (N 5), Statement 1) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have "(\<lambda>_. 0)(''y'' := 5) \<in> checks_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 0" "EA_Assign ''y'' (N 5)" "Statement 1"
        "(\<lambda>_. 0)(''y'' := 5)"]
    using s1 e1 unfolding checks_ex_reach_def by simp
  then show ?thesis by blast
qed

text \<open>Continuing the same run through \<open>z := 1\<close> reaches \<open>Statement 3\<close> --- the second check's node.\<close>
lemma checks_ex_reach3_nonempty: "checks_ex_reach (Statement 3) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores is_global" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ex_reach (FunctionEntry ''main'')"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect is_global (prog_cfg ''main'' checks_ex_program) (cinit_stores is_global)
            (cfg_entry (prog_cfg ''main'' checks_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ex_reach_def checks_ex_entry_eval .
  qed
  have e0: "(FunctionEntry ''main'', EA_Nop, Statement 0) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "FunctionEntry ''main''" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ex_reach_def by simp
  have e1: "(Statement 0, EA_Assign ''y'' (N 5), Statement 1) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s2: "(\<lambda>_. 0)(''y'' := 5) \<in> checks_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 0" "EA_Assign ''y'' (N 5)" "Statement 1"
        "(\<lambda>_. 0)(''y'' := 5)"]
    using s1 e1 unfolding checks_ex_reach_def by simp
  have e2: "(Statement 1, EA_Nop, Statement 2) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s3: "(\<lambda>_. 0)(''y'' := 5) \<in> checks_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)(''y'' := 5)" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 1" EA_Nop "Statement 2"]
    using s2 e2 unfolding checks_ex_reach_def by simp
  have e3: "(Statement 2, EA_Assign ''z'' (N 1), Statement 3) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have "(\<lambda>_. 0)(''y'' := 5, ''z'' := 1) \<in> checks_ex_reach (Statement 3)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)(''y'' := 5)" is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 2" "EA_Assign ''z'' (N 1)" "Statement 3"
        "(\<lambda>_. 0)(''y'' := 5, ''z'' := 1)"]
    using s3 e3 unfolding checks_ex_reach_def by simp
  then show ?thesis by blast
qed

text \<open>Every store reaching \<open>Statement 3\<close> (the second check) reaches the exit
  unchanged: both intervening edges (\<open>Statement 3\<close>'s own \<^const>\<open>EA_Nop\<close> and the
  epilogue's \<open>EA_Ret None\<close>-shaped return) are the identity on the store.\<close>
lemma checks_ex_reach3_to_exit:
  assumes "s \<in> checks_ex_reach (Statement 3)"
  shows "s \<in> checks_ex_reach (cfg_exit (prog_cfg ''main'' checks_ex_program))"
proof -
  have e1: "(Statement 3, EA_Nop, Statement 4) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "s \<in> checks_ex_reach (Statement 4)"
    using ltr_collect_intra_step[of s is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 3" EA_Nop "Statement 4"]
    using assms e1 unfolding checks_ex_reach_def by simp
  have e2: "(Statement 4, EA_Ret None ''main'', FunctionResult ''main'')
              \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s2: "s \<in> checks_ex_reach (FunctionResult ''main'')"
    using ltr_collect_intra_step[of s is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 4" "EA_Ret None ''main''" "FunctionResult ''main''"]
    using s1 e2 unfolding checks_ex_reach_def by simp
  then show ?thesis using checks_ex_exit_eval by simp
qed

text \<open>Every store reaching \<open>Statement 1\<close> (the first check) also reaches the
  exit, up to the one real store change on the way (\<open>z := 1\<close>) --- which never
  touches \<open>y\<close>, so it does not affect what the first check's condition says.\<close>
lemma checks_ex_reach1_to_exit:
  assumes "s \<in> checks_ex_reach (Statement 1)"
  shows "s(''z'' := 1) \<in> checks_ex_reach (cfg_exit (prog_cfg ''main'' checks_ex_program))"
proof -
  have e1: "(Statement 1, EA_Nop, Statement 2) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "s \<in> checks_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of s is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 1" EA_Nop "Statement 2"]
    using assms e1 unfolding checks_ex_reach_def by simp
  have e2: "(Statement 2, EA_Assign ''z'' (N 1), Statement 3) \<in> intra (prog_cfg ''main'' checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s2: "s(''z'' := 1) \<in> checks_ex_reach (Statement 3)"
    using ltr_collect_intra_step[of s is_global "prog_cfg ''main'' checks_ex_program"
        "cinit_stores is_global" "Statement 2" "EA_Assign ''z'' (N 1)" "Statement 3" "s(''z'' := 1)"]
    using s1 e2 unfolding checks_ex_reach_def by simp
  then show ?thesis using checks_ex_reach3_to_exit by simp
qed

lemma checks_ex_checks_proven: "checks_proven (checks (prog_cfg ''main'' checks_ex_program)) checks_ex_reach"
proof (rule checks_provenI)
  fix v c s
  assume ck: "(v, c) \<in> checks (prog_cfg ''main'' checks_ex_program)" and mem: "s \<in> checks_ex_reach v"
  from ck consider (c1) "v = Statement 1" "c = Less (N 0) (V ''y'')"
    | (c2) "v = Statement 3" "c = Less (N 0) (V ''z'')"
    unfolding checks_ex_checks_eval by auto
  then show "bval c s"
  proof cases
    case c1
    with mem have exit: "s(''z'' := 1) \<in> checks_ex_reach (cfg_exit (prog_cfg ''main'' checks_ex_program))"
      using checks_ex_reach1_to_exit by simp
    have z_in: "s(''z'' := 1) \<in> \<lbrakk>sign_exec_prog ''main'' checks_ex_program\<rbrakk>"
      using exit checks_ex_exit_sound unfolding checks_ex_reach_def by blast
    have "s ''y'' \<in> gamma_sign (sign_exec_prog ''main'' checks_ex_program ''y'')"
      using spec[OF gamma_stateD[OF z_in], of "''y''"] by simp
    then have "0 < s ''y''" using checks_ex_exec_y by simp
    then show ?thesis using c1 by simp
  next
    case c2
    with mem have exit: "s \<in> checks_ex_reach (cfg_exit (prog_cfg ''main'' checks_ex_program))"
      using checks_ex_reach3_to_exit by simp
    have z_in: "s \<in> \<lbrakk>sign_exec_prog ''main'' checks_ex_program\<rbrakk>"
      using exit checks_ex_exit_sound unfolding checks_ex_reach_def by blast
    have "s ''z'' \<in> gamma_sign (sign_exec_prog ''main'' checks_ex_program ''z'')"
      using gamma_stateD[OF z_in] by fastforce
    then have "0 < s ''z''" using checks_ex_exec_z by simp
    then show ?thesis using c2 by simp
  qed
qed

text \<open>The payoff: every concrete store reaching either check satisfies its
  own condition, derived through \<open>checks_proven_sound\<close> alone, consuming the
  compiler's own \<^const>\<open>checks\<close> table --- no ghost projection, no
  trace-indexed condition type, no hand-built check map.\<close>

corollary checks_ex_first_check_holds:
  assumes "t \<in> checks_ex_reach (Statement 1)"
  shows "bval (Less (N 0) (V ''y'')) t"
  using checks_proven_sound[OF checks_ex_checks_proven] assms checks_ex_checks_eval by blast

corollary checks_ex_second_check_holds:
  assumes "t \<in> checks_ex_reach (Statement 3)"
  shows "bval (Less (N 0) (V ''z'')) t"
  using checks_proven_sound[OF checks_ex_checks_proven] assms checks_ex_checks_eval by blast

end
