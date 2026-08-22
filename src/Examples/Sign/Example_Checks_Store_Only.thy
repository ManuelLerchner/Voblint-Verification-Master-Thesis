section \<open>Example: checks_proven/checks_proven_sound alone, store-only\<close>

theory Example_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_CLI.Sign_Entry" "Voblint_Analysis.Sign_Checks"
          "Voblint_Analysis.Analysis_GraphViz" "Voblint_VIMP.VIMP_Notation"
begin

text \<open>
  Exercises \<^const>\<open>checks_proven\<close> against a computed (not hand-built) Sign
  post-solution, discharged node-locally through the generic
  \<^theory>\<open>Voblint_Analysis.Sign_Checks\<close> interface rather than by forwarding each
  check node's stores to the procedure exit. The compiled \<^const>\<open>checks\<close> field
  comes from a real compiler run (\<open>collect_checks_prog\<close>, \<open>VIMP_Proc_to_CFG\<close>);
  \<open>y\<close> is overwritten (\<open>y := 0\<close>) between the first and second check, and \<open>z\<close> is
  set by a nondeterministic \<open>__voblint_nondet_int()\<close> read, so the three checks land in each
  of the three possible outcomes: the first is \<^term>\<open>Check_Proved\<close>, the second
  --- checking \<open>0 < y\<close> again after \<open>y := 0\<close> --- is \<^term>\<open>Check_Refuted\<close>, and
  the third --- \<open>z = 1\<close> against an unconstrained \<open>z\<close> --- is \<^term>\<open>Check_Unknown\<close>.
  \<open>sign_exec_prog_sound_collecting_at\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Exec_Sound\<close>)
  connects the computed node-indexed environment back to \<^const>\<open>ltr_collect\<close> at
  each check's own node, for any node the solver's query seed can reach ---
  not only the seed itself. No ghost or trace-projection content: the check
  condition is a plain \<^typ>\<open>exp\<close>.
\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so it cannot be
  written inside the \<open>program { ... }\<close> quotation the way other calls can: Pure's inner-syntax
  lexer reserves leading-underscore tokens for translation-internal nonterminals, rejecting any
  user identifier that begins with one.  The call is spliced in directly instead.\<close>
definition checks_ex_program :: imp_prog where
  "checks_ex_program = mk_program []
     (Seq (Seq (imp \<lbrakk> y := 5; __voblint_check(0 < y); y := 0; __voblint_check(0 < y) \<rbrakk>)
                (VIMP_Proc.com.Call (Some (STR ''z'')) special_pname_nondet_int []))
          (imp \<lbrakk> __voblint_check(z == 1) \<rbrakk>))
     []"

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

lemma checks_ex_reserved: "reserved_ret_var checks_ex_gs"
  unfolding reserved_ret_var_def checks_ex_program_def by (simp add: ret_var_def)

text \<open>The compiled graph has no call edges: the nondeterministic read compiles
  to an \<^const>\<open>EA_Special\<close> intra edge, not a \<^const>\<open>CallEdge\<close>.\<close>

lemma checks_ex_calls_eval: "calls (prog_cfg prog_main_name checks_ex_program) = {}"
  unfolding prog_cfg_def by eval

text \<open>The routed-unit solve terminates, and its solved key set is closed under
  the compiled graph -- the four coverage facts the D/G node-soundness bridge
  turns on, each computed rather than argued.\<close>

lemma checks_ex_solver_terminates:
  "sctx_terminates_prog checks_ex_gs prog_main_name checks_ex_program"
  by (rule sctx_terminates_prog_via_solve_c) eval

lemma checks_ex_entry_cov:
  "(cfg_entry (prog_cfg prog_main_name checks_ex_program), ())
     \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
  by eval

lemma checks_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg prog_main_name checks_ex_program).
     (u, ()) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program) \<longrightarrow>
     (w, ()) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
  by eval

lemma checks_ex_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
    and "(u, a, w) \<in> intra (prog_cfg prog_main_name checks_ex_program)"
  shows "(w, ctx) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
  using assms checks_ex_fwd_ok_ball by (cases ctx) auto

lemma checks_ex_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name checks_ex_program)"
  shows "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
  using assms by (simp add: checks_ex_calls_eval)

lemma checks_ex_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name checks_ex_program)"
  shows "(k, c1) \<in> fst (sctx_sol_prog checks_ex_gs prog_main_name checks_ex_program)"
  using assms by (simp add: checks_ex_calls_eval)

definition checks_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ex_reach v = ltr_collect checks_ex_gs (prog_cfg (STR ''main'') checks_ex_program) (cinit_stores checks_ex_gs) v"

text \<open>The computed Sign environment at an arbitrary node, read out of the
  routed-unit solved table \<^const>\<open>analyse_sign_result_for\<close> the production
  report also reads -- one solve, queried per node, with an unreachable node
  concretizing to \<^term>\<open>bot\<close>.\<close>
definition checks_ex_env :: "pp \<Rightarrow> sign abs_state" where
  "checks_ex_env v =
     (case lookup_context (analyse_sign_result_for checks_ex_gs checks_ex_program) v () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

text \<open>The compiled edges, read off \<^const>\<open>prog_cfg\<close>'s own \<open>eval\<close>-computed
  shape: \<open>Statement 1\<close> (\<open>__voblint_check(0 < y)\<close>, proved) reaches \<open>Statement 2\<close> reaches
  \<open>Statement 3\<close> (\<open>y := 0\<close> already ran, so this second \<open>__voblint_check(0 < y)\<close> is
  refuted) reaches \<open>Statement 4\<close> (\<open>z := __voblint_nondet_int()\<close>) reaches \<open>Statement 5\<close>
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

text \<open>Node-local collecting soundness at each check node, from the routed D/G
  node-soundness bridge and the four computed coverage facts --- no store is
  forwarded to the exit, and no reachability-to-exit premise is needed: the
  routed bridge turns on solved-key coverage, not on the query seed.\<close>

lemmas checks_ex_node_sound =
  analyse_sign_result_node_sound_for[OF checks_ex_reserved checks_ex_solver_terminates
    checks_ex_entry_cov checks_ex_fwd_ok checks_ex_call_fwd_ok checks_ex_comb_fwd_ok]

lemma checks_ex_node_sound_1:
  "checks_ex_reach (Statement 1) \<le> \<lbrakk>checks_ex_env (Statement 1)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def
  using checks_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

lemma checks_ex_node_sound_3:
  "checks_ex_reach (Statement 3) \<le> \<lbrakk>checks_ex_env (Statement 3)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def
  using checks_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

lemma checks_ex_node_sound_5:
  "checks_ex_reach (Statement 5) \<le> \<lbrakk>checks_ex_env (Statement 5)\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def
  using checks_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

text \<open>Executable classification at each check's own node --- \<open>y\<close> is \<open>SPos\<close>
  right after \<open>y := 5\<close> at \<open>Statement 1\<close>, \<open>SZero\<close> right after \<open>y := 0\<close> at
  \<open>Statement 3\<close> (so the second \<open>0 < y\<close> is refuted, not merely unproven), and
  \<open>z\<close> is \<open>STop\<close> at \<open>Statement 5\<close> (unconstrained by \<open>__voblint_nondet_int()\<close>).\<close>
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
  shows "truthy (aval (Less (N 0) (V (STR ''y''))) t)"
proof -
  have "t \<in> \<lbrakk>checks_ex_env (Statement 1)\<rbrakk>" using checks_ex_node_sound_1 assms by blast
  then show ?thesis using sign_classify_check_proved[OF checks_ex_classify_1] by blast
qed

corollary checks_ex_second_check_refuted:
  assumes "t \<in> checks_ex_reach (Statement 3)"
  shows "\<not> truthy (aval (Less (N 0) (V (STR ''y''))) t)"
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
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 1, Less (N 0) (V (STR ''y'')))}"
  then have v_eq: "v = Statement 1" and cnd_eq: "cnd = Less (N 0) (V (STR ''y''))" by auto
  show "sign_check_true cnd (checks_ex_env v)"
    unfolding v_eq cnd_eq checks_ex_env_def by eval
qed

lemma checks_ex_proven_check_checks_proven:
  "checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_reach"
proof (rule sign_checks_proven_sound)
  fix v :: pp and cnd :: exp
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
  "analyse_sign_report_for checks_ex_gs checks_ex_program =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted),
      (Statement 5, Eq (V (STR ''z'')) (N 1), Check_Unknown)]"
  by eval

text \<open>The wrapper is exactly \<^const>\<open>classify_checks\<close> applied to this
  program's own compiled CFG and computed environment --- no separate
  representation to drift from the per-node facts above.\<close>

lemma checks_ex_report_unfold:
  "analyse_sign_report_for checks_ex_gs checks_ex_program
     = classify_checks (prog_cfg (STR ''main'') checks_ex_program) checks_ex_env sign_classify_check"
  unfolding analyse_sign_report_for_def checks_ex_env_def
  by (simp add: prog_main_name_def)

text \<open>Agreement with the existing per-node classification: the first report
  entry is derivable directly from \<open>classify_checks_mem_iff\<close> together
  with the compiled \<^const>\<open>EA_Check\<close> edge (\<open>checks_ex_intra_eval\<close>) and
  the already-proven node-local classification (\<open>checks_ex_classify_1\<close>),
  not merely re-derived by \<open>eval\<close>.\<close>

corollary checks_ex_report_agrees_with_node_classification:
  "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved)
     \<in> set (analyse_sign_report_for checks_ex_gs checks_ex_program)"
  unfolding checks_ex_report_unfold
  using classify_checks_mem_iff[of "prog_cfg (STR ''main'') checks_ex_program"
      "Statement 1" "Less (N 0) (V (STR ''y''))" Check_Proved checks_ex_env sign_classify_check]
  using checks_ex_intra_eval checks_ex_classify_1
  by (auto simp: checks_ex_intra_eval)

text \<open>The textual renderer applied to this program's own report --- rendering
  stays separate from \<^const>\<open>classify_checks\<close> itself, this is just evidence
  it produces the expected lines for a real computed report.\<close>

lemma checks_ex_report_rendered:
  "map string_of_check_report_entry (analyse_sign_report_for checks_ex_gs checks_ex_program) =
     [''pp1: 0<y  PROVED'', ''pp3: 0<y  REFUTED'', ''pp5: z==1  UNKNOWN'']"
  by eval

subsection \<open>CFG rendering, checks colored by executable classification\<close>

text \<open>
  The compiled CFG is rendered through the same generic
  \<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close> pipeline every other example uses
  (\<^const>\<open>raw_cfg_dot_lit\<close>), not a bespoke renderer, through the same
  check-agnostic \<^type>\<open>graphviz_node_annotation\<close> hook every other annotated
  example uses. There is no manually maintained \<^typ>\<open>pp\<close>-to-\<^typ>\<open>exp\<close> table:
  \<^const>\<open>check_report_node_annotation\<close> looks each node up directly in the
  computed \<^const>\<open>analyse_sign_report_for\<close>, so a change to the program or the
  solver result changes the rendered color automatically.
  \<^term>\<open>Check_Proved\<close> renders dark green, \<^term>\<open>Check_Refuted\<close> red,
  \<^term>\<open>Check_Unknown\<close> grey. The unrelated \<open>FunctionResult (STR ''main'')\<close> exit node
  gets its own neutral-grey annotation through the same hook, so the ordinary
  end-of-procedure node is not visually confused with a refuted check.
\<close>

definition checks_ex_node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "checks_ex_node_annotation v =
     (case check_report_node_annotation
             (analyse_sign_report_for checks_ex_gs checks_ex_program) v of
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
       (analyse_sign_report_for checks_ex_gs checks_ex_program)"

end

