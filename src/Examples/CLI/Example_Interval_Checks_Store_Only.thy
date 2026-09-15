section \<open>Example: checks_proven/checks_provenD alone, store-only, Interval\<close>

theory Example_Interval_Checks_Store_Only
  imports "Voblint_Framework.Checks" "Voblint_Analysis_Interval.Interval_Entry"
          "Voblint_Analysis_Interval.Interval_Checks"
          "Voblint_Analysis_Sign.Sign_Checks"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N

text \<open>
  The Interval analogue of \<open>Example_Checks_Store_Only\<close> (Sign): exercises
  \<^const>\<open>checks_proven\<close> against a computed Interval post-solution, discharged
  node-locally through \<open>Interval_Checks\<close> rather than by forwarding stores to
  the procedure exit. Unlike the Sign example, the checks sit inside a guard
  that bounds \<open>x\<close> on both sides (\<open>0 < x \<and> x < 10\<close>), so Interval's numeric
  bounds --- not just its sign --- narrow the checked variable.
\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so it cannot be
  written inside the \<open>program { ... }\<close> quotation the way other calls can: Pure's inner-syntax
  lexer reserves leading-underscore tokens for translation-internal nonterminals, rejecting any
  user identifier that begins with one.  The call is spliced in directly instead.\<close>
definition checks_ivl_ex_program :: imp_prog where
  "checks_ivl_ex_program = mk_program []
     (Seq (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int [])
          (imp \<lbrakk> if (0 < x && x < 10) {
                   __voblint_check(x < 11);
                   __voblint_check(x < 0);
                   __voblint_check(x == 5);
                 } else {
                   y = 0;
                 } \<rbrakk>))
     []"

text \<open>Computed, not asserted: the three \<open>__voblint_check(...)\<close> statements land
  at the nodes \<^const>\<open>compile\<close> actually assigns them, inside the guarded
  branch.\<close>
lemma checks_ivl_ex_checks_eval:
  "checks (prog_cfg checks_ivl_ex_program) =
     {(Statement 2, Less (V (STR ''x'')) (N 11)),
      (Statement 3, Less (V (STR ''x'')) (N 0)),
      (Statement 4, Eq (V (STR ''x'')) (N 5))}"
  unfolding prog_cfg_def by eval

abbreviation checks_ivl_ex_gs :: "vname \<Rightarrow> bool" where
  "checks_ivl_ex_gs \<equiv> declared_global checks_ivl_ex_program"

lemma checks_ivl_ex_program_declared_global_vars [simp]:
  "declared_global_vars checks_ivl_ex_program = []"
  by (simp add: checks_ivl_ex_program_def)

lemma checks_ivl_ex_calls_eval: "calls (prog_cfg checks_ivl_ex_program) = {}"
  unfolding prog_cfg_def
  by (rule compile_prog_calls_empty)
     (simp_all add: checks_ivl_ex_program_def special_table_def
        special_pname_nondet_int_def main_body_def prog_main_name_def)

lemma checks_ivl_ex_solver_terminates:
  "interval_conf_terminates_prog checks_ivl_ex_gs checks_ivl_ex_program"
  by (rule interval_conf_terminates_prog_via_solve_c) eval

lemma checks_ivl_ex_entry_cov:
  "(cfg_entry (prog_cfg checks_ivl_ex_program), ())
     \<in> fst (interval_conf_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  by eval

lemma checks_ivl_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg checks_ivl_ex_program).
     (u, ()) \<in> fst (interval_conf_sol_prog checks_ivl_ex_gs checks_ivl_ex_program) \<longrightarrow>
     (w, ()) \<in> fst (interval_conf_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  by eval

definition checks_ivl_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ivl_ex_reach v =
     ltr_collect checks_ivl_ex_gs (prog_cfg checks_ivl_ex_program)
       (cinit_stores checks_ivl_ex_gs) v"

text \<open>The computed Interval environment at an arbitrary node, read out of the
  routed-unit solved table \<^const>\<open>analyse_interval_result_join_for\<close> the
  always-join report also reads, with an unreachable node concretizing to \<^term>\<open>bot\<close>.\<close>
definition checks_ivl_ex_env :: "pp \<Rightarrow> ivl abs_state" where
  "checks_ivl_ex_env v =
     (case lookup_context
       (analyse_interval_result_join_for checks_ivl_ex_gs checks_ivl_ex_program) v () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

lemma checks_ivl_ex_intra_eval:
  "intra (prog_cfg checks_ivl_ex_program) =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 0, EA_Special Nondet_Int (STR ''x''), Statement 1),
      (Statement 1,
       EA_Assume (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10))),
       Statement 2),
      (Statement 1,
       EA_AssumeNot (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10))),
       Statement 5),
      (Statement 2, EA_Check (Less (V (STR ''x'')) (N 11)), Statement 3),
      (Statement 3, EA_Check (Less (V (STR ''x'')) (N 0)), Statement 4),
      (Statement 4, EA_Check (Eq (V (STR ''x'')) (N 5)), Statement 6),
      (Statement 5, EA_Assign (STR ''y'') (N 0), Statement 6),
      (Statement 6, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma checks_ivl_ex_entry_eval:
  "cfg_entry (prog_cfg checks_ivl_ex_program) = FunctionEntry (STR ''main'')"
  by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)

lemma checks_ivl_ex_node_sound: "checks_ivl_ex_reach v \<le> \<lbrakk>checks_ivl_ex_env v\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  using checks_ivl_ex_fwd_ok_ball
  by (intro analyse_interval_result_join_node_sound_for checks_ivl_ex_solver_terminates
        checks_ivl_ex_entry_cov)
     (auto simp: checks_ivl_ex_calls_eval)

text \<open>Executable classification at each check's own node --- the guard
  \<open>0 < x \<and> x < 10\<close> narrows \<open>x\<close> to \<open>[1,9]\<close> at \<open>Statement 2\<close>, so \<open>x < 11\<close> is
  proved and \<open>x < 0\<close> is refuted outright; \<open>x = 5\<close> stays unknown since \<open>x\<close>
  ranges over the whole \<open>[1,9]\<close> interval, not just \<open>5\<close>.\<close>
lemma checks_ivl_ex_classify_2:
  "interval_classify_check (Less (V (STR ''x'')) (N 11))
     (checks_ivl_ex_env (Statement 2)) = Check_Proved"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_3:
  "interval_classify_check (Less (V (STR ''x'')) (N 0))
     (checks_ivl_ex_env (Statement 3)) = Check_Refuted"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_4:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5))
     (checks_ivl_ex_env (Statement 4)) = Check_Unknown"
  unfolding checks_ivl_ex_env_def by eval

text \<open>The precision comparison: Sign only ever tracks the sign of \<open>x\<close>, so
  after \<open>0 < x\<close> its best abstraction is \<open>SPos\<close> --- \<open>x < 10\<close> narrows nothing
  further in that lattice, and \<open>SPos\<close> alone cannot prove \<open>x < 11\<close> (a
  \<open>SPos\<close> value like \<open>1000000\<close> is not \<open>< 11\<close>). Interval proves it outright
  because it tracks the upper bound \<open>9\<close> directly, not merely the sign.\<close>
lemma checks_ivl_ex_precision_over_sign:
  "sign_classify_check (Less (V (STR ''x'')) (N 11))
     ((\<lambda>_. STop)((STR ''x'') := SPos)) = Check_Unknown"
  by eval

corollary checks_ivl_ex_first_check_holds:
  assumes "t \<in> checks_ivl_ex_reach (Statement 2)"
  shows "truthy (aval (Less (V (STR ''x'')) (N 11)) t)"
  using assms checks_ivl_ex_node_sound interval_classify_check_proved[OF checks_ivl_ex_classify_2]
  by blast

corollary checks_ivl_ex_second_check_refuted:
  assumes "t \<in> checks_ivl_ex_reach (Statement 3)"
  shows "\<not> truthy (aval (Less (V (STR ''x'')) (N 0)) t)"
  using assms checks_ivl_ex_node_sound interval_classify_check_refuted[OF checks_ivl_ex_classify_3]
  by blast

lemma checks_ivl_ex_proven_check_discharged:
  "interval_checks_proven {(Statement 2, Less (V (STR ''x'')) (N 11))} checks_ivl_ex_env"
proof (rule interval_checks_provenI)
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 2, Less (V (STR ''x'')) (N 11))}"
  then have v_eq: "v = Statement 2" and cnd_eq: "cnd = Less (V (STR ''x'')) (N 11)" by auto
  show "interval_check_query cnd (checks_ivl_ex_env v) = Some True"
    unfolding v_eq cnd_eq checks_ivl_ex_env_def by eval
qed

lemma checks_ivl_ex_proven_check_checks_proven:
  "checks_proven {(Statement 2, Less (V (STR ''x'')) (N 11))} checks_ivl_ex_reach"
  by (rule interval_checks_proven_sound)
     (use checks_ivl_ex_node_sound checks_ivl_ex_proven_check_discharged in auto)

text \<open>Non-vacuity: reading \<open>5\<close> for \<open>x\<close> satisfies the guard, so the all-zero initial store
  reaches the guarded branch holding all three checks.\<close>

lemma checks_ivl_ex_reach2_nonempty: "checks_ivl_ex_reach (Statement 2) \<noteq> {}"
proof -
  note step = ltr_collect_intra_step[where gs = checks_ivl_ex_gs
      and g = "prog_cfg checks_ivl_ex_program" and S = "cinit_stores checks_ivl_ex_gs",
      folded checks_ivl_ex_reach_def]
  have "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (cfg_entry (prog_cfg checks_ivl_ex_program))"
    unfolding checks_ivl_ex_reach_def by (rule ltr_collect_init) (simp add: cinit_stores_def)
  then have "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (Statement 0)"
    by (rule step) (auto simp: checks_ivl_ex_entry_eval checks_ivl_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 5) \<in> checks_ivl_ex_reach (Statement 1)"
    by (rule step) (auto simp: checks_ivl_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 5) \<in> checks_ivl_ex_reach (Statement 2)"
    by (rule step) (auto simp: checks_ivl_ex_intra_eval)
  then show ?thesis by blast
qed

subsection \<open>Whole-program check report\<close>

lemma checks_ivl_ex_report_eval:
  "analyse_interval_report_join_for checks_ivl_ex_gs checks_ivl_ex_program =
     [(Statement 2, Less (V (STR ''x'')) (N 11), Check_Proved),
      (Statement 3, Less (V (STR ''x'')) (N 0), Check_Refuted),
      (Statement 4, Eq (V (STR ''x'')) (N 5), Check_Unknown)]"
  by eval

end
