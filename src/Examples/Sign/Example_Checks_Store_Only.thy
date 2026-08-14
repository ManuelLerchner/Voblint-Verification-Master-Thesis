section \<open>Example: checks_proven/checks_proven_sound alone, store-only\<close>

theory Example_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_Analysis.Sign_Exec_Sound" "Voblint_Analysis.Sign_Checks"
          "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Exercises \<^const>\<open>checks_proven\<close> against a computed (not hand-built) Sign
  post-solution, discharged node-locally through the generic
  \<^theory>\<open>Voblint_Analysis.Sign_Checks\<close> interface rather than by forwarding each
  check node's stores to the procedure exit. The compiled \<^const>\<open>checks\<close> field
  comes from a real compiler run (\<open>collect_checks_prog\<close>, \<open>VIMP_Proc_to_CFG.thy\<close>);
  \<open>y\<close> is overwritten (\<open>y := 0\<close>) between the first and second check, and \<open>z\<close> is
  set by a nondeterministic \<open>random()\<close> read, so the three checks land in each
  of the three possible outcomes: the first is \<^term>\<open>Check_Proved\<close>, the second
  --- checking \<open>0 < y\<close> again after \<open>y := 0\<close> --- is \<^term>\<open>Check_Refuted\<close>, and
  the third --- \<open>z = 1\<close> against an unconstrained \<open>z\<close> --- is \<^term>\<open>Check_Unknown\<close>.
  \<open>sign_exec_prog_sound_collecting_at\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>)
  connects the computed node-indexed environment back to \<^const>\<open>ltr_collect\<close> at
  each check's own node, for any node the solver's query seed can reach ---
  not only the seed itself. No ghost or trace-projection content: the check
  condition is a plain \<^typ>\<open>bexp\<close>.
\<close>

definition checks_ex_program :: imp_prog where
  "checks_ex_program = program {
     void main() {
       y := 5;
       __voblint_check(0 < y);
       y := 0;
       __voblint_check(0 < y);
       z := random();
       __voblint_check(z == 1)
     }
   }"

text \<open>Computed, not asserted: the three \<open>check(...)\<close> statements land at the
  nodes \<^const>\<open>compile\<close> actually assigns them.\<close>
lemma checks_ex_checks_eval:
  "checks (prog_cfg (STR ''main'') checks_ex_program) =
     {(Statement 1, Less (N 0) (V (STR ''y''))),
      (Statement 3, Less (N 0) (V (STR ''y''))),
      (Statement 5, Eq (V (STR ''z'')) (N 1))}"
  unfolding prog_cfg_def by eval

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere.\<close>
abbreviation checks_ex_gs :: "vname \<Rightarrow> bool" where
  "checks_ex_gs \<equiv> declared_global checks_ex_program"

lemma checks_ex_program_declared_global_vars [simp]:
  "declared_global_vars checks_ex_program = []"
  by (simp add: checks_ex_program_def)

lemma checks_ex_solver_terminates: "sign_terminates_prog checks_ex_gs (STR ''main'') checks_ex_program"
  by (rule sign_terminates_prog_via_solve_c) eval

definition checks_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ex_reach v = ltr_collect checks_ex_gs (prog_cfg (STR ''main'') checks_ex_program) (cinit_stores checks_ex_gs) v"

text \<open>The computed Sign environment at an arbitrary node, not fixed to the
  exit: \<^const>\<open>sign_exec_prog_at\<close> queries the same solver result
  \<^const>\<open>sign_exec_prog\<close> reads only at the exit.\<close>
definition checks_ex_env :: "pp \<Rightarrow> sign abs_state" where
  "checks_ex_env v = case_lifted bot (\<lambda>\<sigma>. \<sigma>)
     (sign_exec_prog_at checks_ex_gs (STR ''main'') checks_ex_program v)"

text \<open>The compiled edges, read off \<^const>\<open>prog_cfg\<close>'s own \<open>eval\<close>-computed
  shape: \<open>Statement 1\<close> (\<open>__voblint_check(0 < y)\<close>, proved) reaches \<open>Statement 2\<close> reaches
  \<open>Statement 3\<close> (\<open>y := 0\<close> already ran, so this second \<open>__voblint_check(0 < y)\<close> is
  refuted) reaches \<open>Statement 4\<close> (\<open>z := random()\<close>) reaches \<open>Statement 5\<close>
  (\<open>__voblint_check(z == 1)\<close>, unknown --- \<open>z\<close> is unconstrained) reaches the epilogue
  \<open>Statement 6\<close> reaches \<open>cfg_exit\<close>.\<close>
lemma checks_ex_intra_eval:
  "intra (prog_cfg (STR ''main'') checks_ex_program) =
     {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
      (Statement 0, EA_Assign (STR ''y'') (N 5), Statement 1),
      (Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2),
      (Statement 2, EA_Assign (STR ''y'') (N 0), Statement 3),
      (Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4),
      (Statement 4, EA_Special Nondet_Int (STR ''z''), Statement 5),
      (Statement 5, EA_Check (Eq (V (STR ''z'')) (N 1)), Statement 6),
      (Statement 6, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma checks_ex_exit_eval: "cfg_exit (prog_cfg (STR ''main'') checks_ex_program) = FunctionResult (STR ''main'')"
  unfolding prog_cfg_def by eval

lemma checks_ex_entry_eval: "cfg_entry (prog_cfg (STR ''main'') checks_ex_program) = FunctionEntry (STR ''main'')"
  unfolding prog_cfg_def by eval

text \<open>Structural reachability to the exit, for each check node --- the
  premise \<open>sign_exec_prog_sound_collecting_at\<close> needs to bound
  \<^const>\<open>ltr_collect\<close> at that node against the solver's query seed
  (\<open>cfg_exit\<close>). This is a fact about the CFG's shape, not about any concrete
  store: it does not forward stores.\<close>
lemma checks_ex_statement1_reaches_exit:
  "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 1)
     (cfg_exit (prog_cfg (STR ''main'') checks_ex_program))"
proof -
  have r1: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 1) (Statement 2)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r2: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 2) (Statement 3)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r3: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r4: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 4) (Statement 5)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r5: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 5) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 6) (FunctionResult (STR ''main''))"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  show ?thesis
    unfolding checks_ex_exit_eval
    using r1 r2 r3 r4 r5 r6 cfg_reaches_trans by blast
qed

lemma checks_ex_statement3_reaches_exit:
  "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 3)
     (cfg_exit (prog_cfg (STR ''main'') checks_ex_program))"
proof -
  have r3: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 3) (Statement 4)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r4: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 4) (Statement 5)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r5: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 5) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 6) (FunctionResult (STR ''main''))"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  show ?thesis
    unfolding checks_ex_exit_eval
    using r3 r4 r5 r6 cfg_reaches_trans by blast
qed

lemma checks_ex_statement5_reaches_exit:
  "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 5)
     (cfg_exit (prog_cfg (STR ''main'') checks_ex_program))"
proof -
  have r5: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 5) (Statement 6)"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  have r6: "cfg_reaches (prog_cfg (STR ''main'') checks_ex_program) (Statement 6) (FunctionResult (STR ''main''))"
    by (rule cfg_reaches_intra) (simp add: checks_ex_intra_eval)
  show ?thesis
    unfolding checks_ex_exit_eval
    using r5 r6 cfg_reaches_trans by blast
qed

text \<open>Node-local collecting soundness at each check node, via
  \<open>sign_exec_prog_sound_collecting_at\<close> and the reachability facts above ---
  no store is forwarded to the exit.\<close>
lemma gamma_state_case_lifted:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_state (case_lifted bot (\<lambda>\<sigma>. \<sigma>) x) = gamma_state_lift x"
  by (cases x) (simp_all add: gamma_state_bot)

lemma checks_ex_node_sound_1:
  "checks_ex_reach (Statement 1) \<le> \<lbrakk>checks_ex_env (Statement 1)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def gamma_state_case_lifted
  by (rule sign_exec_prog_sound_collecting_at[OF refl checks_ex_solver_terminates checks_ex_statement1_reaches_exit])

lemma checks_ex_node_sound_3:
  "checks_ex_reach (Statement 3) \<le> \<lbrakk>checks_ex_env (Statement 3)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def gamma_state_case_lifted
  by (rule sign_exec_prog_sound_collecting_at[OF refl checks_ex_solver_terminates checks_ex_statement3_reaches_exit])

lemma checks_ex_node_sound_5:
  "checks_ex_reach (Statement 5) \<le> \<lbrakk>checks_ex_env (Statement 5)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def gamma_state_case_lifted
  by (rule sign_exec_prog_sound_collecting_at[OF refl checks_ex_solver_terminates checks_ex_statement5_reaches_exit])

text \<open>Executable classification at each check's own node --- \<open>y\<close> is \<open>SPos\<close>
  right after \<open>y := 5\<close> at \<open>Statement 1\<close>, \<open>SZero\<close> right after \<open>y := 0\<close> at
  \<open>Statement 3\<close> (so the second \<open>0 < y\<close> is refuted, not merely unproven), and
  \<open>z\<close> is \<open>STop\<close> at \<open>Statement 5\<close> (unconstrained by \<open>random()\<close>).\<close>
lemma checks_ex_classify_1:
  "sign_classify_check (Less (N 0) (V (STR ''y''))) (checks_ex_env (Statement 1)) = Check_Proved"
  unfolding checks_ex_env_def by eval

lemma checks_ex_classify_3:
  "sign_classify_check (Less (N 0) (V (STR ''y''))) (checks_ex_env (Statement 3)) = Check_Refuted"
  unfolding checks_ex_env_def by eval

lemma checks_ex_classify_5:
  "sign_classify_check (Eq (V (STR ''z'')) (N 1)) (checks_ex_env (Statement 5)) = Check_Unknown"
  unfolding checks_ex_env_def by eval

text \<open>The payoff: the proved check's condition genuinely holds at every
  reaching store, and the refuted check's condition genuinely fails at every
  reaching store --- both derived from \<^const>\<open>sign_classify_check\<close> plus
  node-local collecting soundness, with no store forwarded between check
  nodes. The unknown check gets no such corollary, by design.\<close>

corollary checks_ex_first_check_holds:
  assumes "t \<in> checks_ex_reach (Statement 1)"
  shows "bval (Less (N 0) (V (STR ''y''))) t"
proof -
  have "t \<in> \<lbrakk>checks_ex_env (Statement 1)\<rbrakk>" using checks_ex_node_sound_1 assms by blast
  then show ?thesis using sign_classify_check_proved[OF checks_ex_classify_1] by blast
qed

corollary checks_ex_second_check_refuted:
  assumes "t \<in> checks_ex_reach (Statement 3)"
  shows "\<not> bval (Less (N 0) (V (STR ''y''))) t"
proof -
  have "t \<in> \<lbrakk>checks_ex_env (Statement 3)\<rbrakk>" using checks_ex_node_sound_3 assms by blast
  then show ?thesis using sign_classify_check_refuted[OF checks_ex_classify_3] by blast
qed

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Core.Checks\<close> bridge,
  exercised on exactly the checks that are actually true: the compiler's own
  \<^const>\<open>checks\<close> table names all three, but a blanket \<open>checks_proven\<close> over the
  whole table would be a false statement here, since the second check is a
  genuine bug (refuted, not merely unproven). Restricting to the singleton
  \<open>{(Statement 1, Less (N 0) (V (STR ''y'')))}\<close> keeps the bridge theorem meaningful.\<close>

lemma checks_ex_proven_check_discharged:
  "sign_checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_env"
proof (rule sign_checks_provenI)
  fix v :: pp and cnd :: bexp
  assume mem: "(v, cnd) \<in> {(Statement 1, Less (N 0) (V (STR ''y'')))}"
  then have v_eq: "v = Statement 1" and cnd_eq: "cnd = Less (N 0) (V (STR ''y''))" by auto
  show "sign_check_true cnd (checks_ex_env v)"
    unfolding v_eq cnd_eq checks_ex_env_def by eval
qed

lemma checks_ex_proven_check_checks_proven:
  "checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_reach"
proof (rule sign_checks_proven_sound)
  fix v :: pp and cnd :: bexp
  assume "(v, cnd) \<in> {(Statement 1, Less (N 0) (V (STR ''y'')))}"
  then show "checks_ex_reach v \<le> \<lbrakk>checks_ex_env v\<rbrakk>"
    using checks_ex_node_sound_1 by auto
next
  show "sign_checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_env"
    by (rule checks_ex_proven_check_discharged)
qed

text \<open>Non-vacuity: \<open>checks_ex_reach\<close> is not merely vacuously true because no
  store ever reaches these nodes. The all-zero store, admissible as an
  initial \<^const>\<open>cinit_stores\<close> witness, runs the compiled prefix and reaches
  both the first check's own node and, continuing through the rest of the
  chain, the third (unknown) check's own node.\<close>
lemma checks_ex_reach1_nonempty: "checks_ex_reach (Statement 1) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores checks_ex_gs" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ex_reach (FunctionEntry (STR ''main''))"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect checks_ex_gs (prog_cfg (STR ''main'') checks_ex_program) (cinit_stores checks_ex_gs)
            (cfg_entry (prog_cfg (STR ''main'') checks_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ex_reach_def checks_ex_entry_eval .
  qed
  have e0: "(FunctionEntry (STR ''main''), EA_Nop, Statement 0) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "FunctionEntry (STR ''main'')" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ex_reach_def by simp
  have e1: "(Statement 0, EA_Assign (STR ''y'') (N 5), Statement 1) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have "(\<lambda>_. 0)((STR ''y'') := 5) \<in> checks_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 0" "EA_Assign (STR ''y'') (N 5)" "Statement 1"
        "(\<lambda>_. 0)((STR ''y'') := 5)"]
    using s1 e1 unfolding checks_ex_reach_def by simp
  then show ?thesis by blast
qed

lemma checks_ex_reach5_nonempty: "checks_ex_reach (Statement 5) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores checks_ex_gs" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ex_reach (FunctionEntry (STR ''main''))"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect checks_ex_gs (prog_cfg (STR ''main'') checks_ex_program) (cinit_stores checks_ex_gs)
            (cfg_entry (prog_cfg (STR ''main'') checks_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ex_reach_def checks_ex_entry_eval .
  qed
  have e0: "(FunctionEntry (STR ''main''), EA_Nop, Statement 0) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "FunctionEntry (STR ''main'')" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ex_reach_def by simp
  have e1: "(Statement 0, EA_Assign (STR ''y'') (N 5), Statement 1) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s2: "(\<lambda>_. 0)((STR ''y'') := 5) \<in> checks_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 0" "EA_Assign (STR ''y'') (N 5)" "Statement 1"
        "(\<lambda>_. 0)((STR ''y'') := 5)"]
    using s1 e1 unfolding checks_ex_reach_def by simp
  have e2: "(Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s3: "(\<lambda>_. 0)((STR ''y'') := 5) \<in> checks_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''y'') := 5)" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 1" "EA_Check (Less (N 0) (V (STR ''y'')))" "Statement 2"]
    using s2 e2 unfolding checks_ex_reach_def by simp
  have e3: "(Statement 2, EA_Assign (STR ''y'') (N 0), Statement 3) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s4: "(\<lambda>_. 0)((STR ''y'') := 0) \<in> checks_ex_reach (Statement 3)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''y'') := 5)" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 2" "EA_Assign (STR ''y'') (N 0)" "Statement 3"
        "(\<lambda>_. 0)((STR ''y'') := 0)"]
    using s3 e3 unfolding checks_ex_reach_def by simp
  have e4: "(Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have s5: "(\<lambda>_. 0)((STR ''y'') := 0) \<in> checks_ex_reach (Statement 4)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''y'') := 0)" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 3" "EA_Check (Less (N 0) (V (STR ''y'')))" "Statement 4"]
    using s4 e4 unfolding checks_ex_reach_def by simp
  have e5: "(Statement 4, EA_Special Nondet_Int (STR ''z''), Statement 5) \<in> intra (prog_cfg (STR ''main'') checks_ex_program)"
    by (simp add: checks_ex_intra_eval)
  have "(\<lambda>_. 0)((STR ''y'') := 0, (STR ''z'') := 7) \<in> checks_ex_reach (Statement 5)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''y'') := 0)" checks_ex_gs "prog_cfg (STR ''main'') checks_ex_program"
        "cinit_stores checks_ex_gs" "Statement 4" "EA_Special Nondet_Int (STR ''z'')" "Statement 5"
        "(\<lambda>_. 0)((STR ''y'') := 0, (STR ''z'') := 7)"]
    using s5 e5 unfolding checks_ex_reach_def by force
  then show ?thesis by blast
qed

subsection \<open>Whole-program check report\<close>

text \<open>
  The entire report in one shot, computed --- not hand-assembled --- from
  \<^const>\<open>classify_checks\<close> over the compiled \<^const>\<open>intra\<close> edges, in the
  checks' own compiled order: the same three outcomes the per-node lemmas
  above establish individually (\<open>checks_ex_classify_1\<close>/\<open>_3\<close>/\<open>_5\<close>), now
  read off the whole program at once.
\<close>

lemma checks_ex_report_eval:
  "sign_check_report checks_ex_gs (STR ''main'') checks_ex_program =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted),
      (Statement 5, Eq (V (STR ''z'')) (N 1), Check_Unknown)]"
  by eval

text \<open>The wrapper is exactly \<^const>\<open>classify_checks\<close> applied to this
  program's own compiled CFG and computed environment --- no separate
  representation to drift from the per-node facts above.\<close>

lemma checks_ex_report_unfold:
  "sign_check_report checks_ex_gs (STR ''main'') checks_ex_program
     = classify_checks (prog_cfg (STR ''main'') checks_ex_program) checks_ex_env sign_classify_check"
  unfolding sign_check_report_def checks_ex_env_def by simp

text \<open>Agreement with the existing per-node classification: the first report
  entry is derivable directly from \<open>classify_checks_mem_iff\<close> together
  with the compiled \<^const>\<open>EA_Check\<close> edge (\<open>checks_ex_intra_eval\<close>) and
  the already-proven node-local classification (\<open>checks_ex_classify_1\<close>),
  not merely re-derived by \<open>eval\<close>.\<close>

corollary checks_ex_report_agrees_with_node_classification:
  "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved)
     \<in> set (sign_check_report checks_ex_gs (STR ''main'') checks_ex_program)"
  unfolding checks_ex_report_unfold
  using classify_checks_mem_iff[of "prog_cfg (STR ''main'') checks_ex_program"
      "Statement 1" "Less (N 0) (V (STR ''y''))" Check_Proved checks_ex_env sign_classify_check]
  using checks_ex_intra_eval checks_ex_classify_1
  by (auto simp: checks_ex_intra_eval)

text \<open>The textual renderer applied to this program's own report --- rendering
  stays separate from \<^const>\<open>classify_checks\<close> itself, this is just evidence
  it produces the expected lines for a real computed report.\<close>

lemma checks_ex_report_rendered:
  "map string_of_check_report_entry (sign_check_report checks_ex_gs (STR ''main'') checks_ex_program) =
     [''pp1: 0<y  PROVED'', ''pp3: 0<y  REFUTED'', ''pp5: z==1  UNKNOWN'']"
  by eval

subsection \<open>CFG rendering, checks colored by executable classification\<close>

text \<open>
  The compiled CFG is rendered through the same generic
  \<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close> pipeline every other example uses
  (\<^const>\<open>raw_cfg_dot_lit\<close>), not a bespoke renderer, through the same
  check-agnostic \<^type>\<open>graphviz_node_annotation\<close> hook every other annotated
  example uses. There is no manually maintained \<^typ>\<open>pp\<close>-to-\<^typ>\<open>bexp\<close> table:
  \<^const>\<open>check_report_node_annotation\<close> looks each node up directly in the
  computed \<^const>\<open>sign_check_report\<close>, so a change to the program or the
  solver result changes the rendered color automatically.
  \<^term>\<open>Check_Proved\<close> renders dark green, \<^term>\<open>Check_Refuted\<close> red,
  \<^term>\<open>Check_Unknown\<close> grey. The unrelated \<open>FunctionResult (STR ''main'')\<close> exit node
  gets its own neutral-grey annotation through the same hook, so the ordinary
  end-of-procedure node is not visually confused with a refuted check.
\<close>

text \<open>No manually maintained \<^typ>\<open>pp\<close>-to-\<^typ>\<open>bexp\<close> table: the check nodes
  and their conditions are read off \<^const>\<open>sign_check_report\<close>'s own computed
  report through \<^const>\<open>check_report_node_annotation\<close>.\<close>

definition checks_ex_node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "checks_ex_node_annotation v =
     (case check_report_node_annotation
             (sign_check_report checks_ex_gs (STR ''main'') checks_ex_program) v of
        Some ann \<Rightarrow> Some ann
      | None \<Rightarrow>
          if v = FunctionResult (STR ''main'') then
            Some (Node_Annotation ''''
              ''shape=doublecircle,color=gray40,style=filled,fillcolor=lightgray'')
          else None)"

text \<open>Validation that the generic renderer's hook actually carries all three
  computed classifications, not merely that this file's check table intends
  them to.\<close>

lemma checks_ex_annotation_proved:
  "checks_ex_node_annotation (Statement 1) =
     Some (check_result_annotation Check_Proved (Less (N 0) (V (STR ''y''))))"
  unfolding checks_ex_node_annotation_def by eval

lemma checks_ex_annotation_refuted:
  "checks_ex_node_annotation (Statement 3) =
     Some (check_result_annotation Check_Refuted (Less (N 0) (V (STR ''y''))))"
  unfolding checks_ex_node_annotation_def by eval

lemma checks_ex_annotation_unknown:
  "checks_ex_node_annotation (Statement 5) =
     Some (check_result_annotation Check_Unknown (Eq (V (STR ''z'')) (N 1)))"
  unfolding checks_ex_node_annotation_def by eval

definition checks_ex_dot_lit :: String.literal where
  "checks_ex_dot_lit =
     raw_cfg_dot_with_report_lit (prog_table checks_ex_program) (prog_procs checks_ex_program)
       (STR ''main'') (prog_main checks_ex_program) checks_ex_node_annotation
       (sign_check_report checks_ex_gs (STR ''main'') checks_ex_program)"

ML_val \<open>
  writeln (@{code checks_ex_dot_lit})
\<close>

end

