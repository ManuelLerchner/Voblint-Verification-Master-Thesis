section \<open>Example: checks_proven/checks_proven_sound alone, store-only, Interval\<close>

theory Example_Interval_Checks_Store_Only
  imports "Voblint_Core.Checks" "Voblint_CLI.Interval_Entry" "Voblint_Analysis.Interval_Checks"
          "Voblint_Analysis.Sign_Checks" "Voblint_Analysis.Analysis_GraphViz"
          "Voblint_VIMP.VIMP_Notation"
          Example_Compile_Call_Free
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N

text \<open>This file compares Sign and Interval classification on the same
  program, so both are in scope, but both now resolve \<open>prog_cfg\<close> to the same
  shared \<^const>\<open>prog_cfg\<close> (\<^theory>\<open>Voblint_Compile.Compile_Invariants\<close>) --- no
  hiding needed to disambiguate below, unlike when each domain's
  \<open>*_Exec_Sound\<close> theory defined its own local copy.\<close>

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
                   __voblint_check(x == 5)
                 } else {
                   y := 0
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

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere.\<close>
abbreviation checks_ivl_ex_gs :: "vname \<Rightarrow> bool" where
  "checks_ivl_ex_gs \<equiv> declared_global checks_ivl_ex_program"

lemma checks_ivl_ex_program_declared_global_vars [simp]:
  "declared_global_vars checks_ivl_ex_program = []"
  by (simp add: checks_ivl_ex_program_def)

lemma checks_ivl_ex_reserved: "reserved_ret_var checks_ivl_ex_gs"
  unfolding reserved_ret_var_def checks_ivl_ex_program_def by (simp add: ret_var_def)

lemma checks_ivl_ex_calls_eval: "calls (prog_cfg checks_ivl_ex_program) = {}"
  unfolding prog_cfg_def
  by (rule compile_prog_calls_empty)
     (simp_all add: checks_ivl_ex_program_def special_table_def
        special_pname_nondet_int_def main_body_def prog_main_name_def)

text \<open>The routed-unit solve terminates, and its solved key set is closed under
  the compiled graph -- the four coverage facts the D/G node-soundness bridge
  turns on, each computed rather than argued.\<close>

lemma checks_ivl_ex_solver_terminates:
  "ictx_terminates_prog checks_ivl_ex_gs checks_ivl_ex_program"
  by (rule ictx_terminates_prog_via_solve_c) eval

lemma checks_ivl_ex_entry_cov:
  "(cfg_entry (prog_cfg checks_ivl_ex_program), ())
     \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  by eval

lemma checks_ivl_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg checks_ivl_ex_program).
     (u, ()) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program) \<longrightarrow>
     (w, ()) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  by eval

lemma checks_ivl_ex_fwd_ok:
  assumes "(u, ctx) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
    and "(u, a, w) \<in> intra (prog_cfg checks_ivl_ex_program)"
  shows "(w, ctx) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  using assms checks_ivl_ex_fwd_ok_ball by (cases ctx) auto

lemma checks_ivl_ex_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg checks_ivl_ex_program)"
  shows "(FunctionEntry q, ()) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  using assms by (simp add: checks_ivl_ex_calls_eval)

lemma checks_ivl_ex_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg checks_ivl_ex_program)"
  shows "(k, c1) \<in> fst (ictx_sol_prog checks_ivl_ex_gs checks_ivl_ex_program)"
  using assms by (simp add: checks_ivl_ex_calls_eval)

definition checks_ivl_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ivl_ex_reach v = ltr_collect checks_ivl_ex_gs (prog_cfg checks_ivl_ex_program) (cinit_stores checks_ivl_ex_gs) v"

text \<open>The computed Interval environment at an arbitrary node, read out of the
  routed-unit solved table \<^const>\<open>analyse_interval_join_result_for\<close> the
  always-join report also reads -- one solve, queried per node, with an
  unreachable node concretizing to \<^term>\<open>bot\<close>.\<close>
definition checks_ivl_ex_env :: "pp \<Rightarrow> ivl abs_state" where
  "checks_ivl_ex_env v =
     (case lookup_context (analyse_interval_join_result_for checks_ivl_ex_gs checks_ivl_ex_program) v () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

text \<open>The compiled edges, read off \<^const>\<open>prog_cfg\<close>'s own \<open>eval\<close>-computed
  shape: \<open>Statement 1\<close> (\<open>x := __voblint_nondet_int()\<close>'s successor) branches on
  \<open>0 < x \<and> x < 10\<close> to \<open>Statement 2\<close> (the guarded branch, holding all three
  checks) or to \<open>Statement 5\<close> (\<open>y := 0\<close>, the else branch); both rejoin at
  \<open>Statement 6\<close>.\<close>
lemma checks_ivl_ex_intra_eval:
  "intra (prog_cfg checks_ivl_ex_program) =
     {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
      (Statement 0, EA_Special Nondet_Int (STR ''x''), Statement 1),
      (Statement 1, EA_Assume (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10))), Statement 2),
      (Statement 1, EA_AssumeNot (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10))), Statement 5),
      (Statement 2, EA_Check (Less (V (STR ''x'')) (N 11)), Statement 3),
      (Statement 3, EA_Check (Less (V (STR ''x'')) (N 0)), Statement 4),
      (Statement 4, EA_Check (Eq (V (STR ''x'')) (N 5)), Statement 6),
      (Statement 5, EA_Assign (STR ''y'') (N 0), Statement 6),
      (Statement 6, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma checks_ivl_ex_exit_eval: "cfg_exit (prog_cfg checks_ivl_ex_program) = FunctionResult (STR ''main'')"
  by (simp only: prog_cfg_def cfg_exit_compile_prog prog_main_name_def)

lemma checks_ivl_ex_entry_eval: "cfg_entry (prog_cfg checks_ivl_ex_program) = FunctionEntry (STR ''main'')"
  by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)

text \<open>Node-local collecting soundness at each check node, from the routed D/G
  node-soundness bridge and the four computed coverage facts --- no store is
  forwarded to the exit, and no reachability-to-exit premise is needed: the
  routed bridge turns on solved-key coverage, not on the query seed.\<close>

lemmas checks_ivl_ex_node_sound =
  analyse_interval_join_result_node_sound_for[OF checks_ivl_ex_reserved checks_ivl_ex_solver_terminates
    checks_ivl_ex_entry_cov checks_ivl_ex_fwd_ok checks_ivl_ex_call_fwd_ok
    checks_ivl_ex_comb_fwd_ok]

lemma checks_ivl_ex_node_sound_2:
  "checks_ivl_ex_reach (Statement 2) \<le> \<lbrakk>checks_ivl_ex_env (Statement 2)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  using checks_ivl_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

lemma checks_ivl_ex_node_sound_3:
  "checks_ivl_ex_reach (Statement 3) \<le> \<lbrakk>checks_ivl_ex_env (Statement 3)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  using checks_ivl_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

lemma checks_ivl_ex_node_sound_4:
  "checks_ivl_ex_reach (Statement 4) \<le> \<lbrakk>checks_ivl_ex_env (Statement 4)\<rbrakk>"
  unfolding checks_ivl_ex_reach_def checks_ivl_ex_env_def
  using checks_ivl_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

text \<open>Executable classification at each check's own node --- the guard
  \<open>0 < x \<and> x < 10\<close> narrows \<open>x\<close> to \<open>[1,9]\<close> at \<open>Statement 2\<close>, so \<open>x < 11\<close> is
  proved and \<open>x < 0\<close> is refuted outright; \<open>x = 5\<close> stays unknown since \<open>x\<close>
  ranges over the whole \<open>[1,9]\<close> interval, not just \<open>5\<close>.\<close>
lemma checks_ivl_ex_classify_2:
  "interval_classify_check (Less (V (STR ''x'')) (N 11)) (checks_ivl_ex_env (Statement 2)) = Check_Proved"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_3:
  "interval_classify_check (Less (V (STR ''x'')) (N 0)) (checks_ivl_ex_env (Statement 3)) = Check_Refuted"
  unfolding checks_ivl_ex_env_def by eval

lemma checks_ivl_ex_classify_4:
  "interval_classify_check (Eq (V (STR ''x'')) (N 5)) (checks_ivl_ex_env (Statement 4)) = Check_Unknown"
  unfolding checks_ivl_ex_env_def by eval

text \<open>The precision comparison: Sign only ever tracks the sign of \<open>x\<close>, so
  after \<open>0 < x\<close> its best abstraction is \<open>SPos\<close> --- \<open>x < 10\<close> narrows nothing
  further in that lattice, and \<open>SPos\<close> alone cannot prove \<open>x < 11\<close> (a
  \<open>SPos\<close> value like \<open>1000000\<close> is not \<open>< 11\<close>). Interval proves it outright
  because it tracks the upper bound \<open>9\<close> directly, not merely the sign.\<close>
lemma checks_ivl_ex_precision_over_sign:
  "sign_classify_check (Less (V (STR ''x'')) (N 11)) ((\<lambda>_. STop)((STR ''x'') := SPos)) = Check_Unknown"
  by eval

text \<open>The payoff: the proved check's condition genuinely holds at every
  reaching store, and the refuted check's condition genuinely fails at every
  reaching store --- both derived from \<^const>\<open>interval_classify_check\<close> plus
  node-local collecting soundness, with no store forwarded between check
  nodes. The unknown check gets no such corollary, by design.\<close>

corollary checks_ivl_ex_first_check_holds:
  assumes "t \<in> checks_ivl_ex_reach (Statement 2)"
  shows "truthy (aval (Less (V (STR ''x'')) (N 11)) t)"
proof -
  have "t \<in> \<lbrakk>checks_ivl_ex_env (Statement 2)\<rbrakk>" using checks_ivl_ex_node_sound_2 assms by blast
  then show ?thesis using interval_classify_check_proved[OF checks_ivl_ex_classify_2] by blast
qed

corollary checks_ivl_ex_second_check_refuted:
  assumes "t \<in> checks_ivl_ex_reach (Statement 3)"
  shows "\<not> truthy (aval (Less (V (STR ''x'')) (N 0)) t)"
proof -
  have "t \<in> \<lbrakk>checks_ivl_ex_env (Statement 3)\<rbrakk>" using checks_ivl_ex_node_sound_3 assms by blast
  then show ?thesis using interval_classify_check_refuted[OF checks_ivl_ex_classify_3] by blast
qed

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Core.Checks\<close> bridge,
  exercised on exactly the checks that are actually true: the compiler's own
  \<^const>\<open>checks\<close> table names all three, but a blanket \<open>checks_proven\<close> over the
  whole table would be a false statement here, since the second check is a
  genuine bug (refuted, not merely unproven). Restricting to the singleton
  \<open>{(Statement 2, Less (V (STR ''x'')) (N 11))}\<close> keeps the bridge theorem
  meaningful.\<close>

lemma checks_ivl_ex_proven_check_discharged:
  "interval_checks_proven {(Statement 2, Less (V (STR ''x'')) (N 11))} checks_ivl_ex_env"
proof (rule interval_checks_provenI)
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 2, Less (V (STR ''x'')) (N 11))}"
  then have v_eq: "v = Statement 2" and cnd_eq: "cnd = Less (V (STR ''x'')) (N 11)" by auto
  show "interval_check_true cnd (checks_ivl_ex_env v)"
    unfolding v_eq cnd_eq checks_ivl_ex_env_def by eval
qed

lemma checks_ivl_ex_proven_check_checks_proven:
  "checks_proven {(Statement 2, Less (V (STR ''x'')) (N 11))} checks_ivl_ex_reach"
proof (rule interval_checks_proven_sound)
  fix v :: pp and cnd :: exp
  assume "(v, cnd) \<in> {(Statement 2, Less (V (STR ''x'')) (N 11))}"
  then show "checks_ivl_ex_reach v \<le> \<lbrakk>checks_ivl_ex_env v\<rbrakk>"
    using checks_ivl_ex_node_sound_2 by auto
next
  show "interval_checks_proven {(Statement 2, Less (V (STR ''x'')) (N 11))} checks_ivl_ex_env"
    by (rule checks_ivl_ex_proven_check_discharged)
qed

text \<open>Non-vacuity: \<open>checks_ivl_ex_reach\<close> is not merely vacuously true because
  no store ever reaches these nodes. The all-zero store, admissible as an
  initial \<^const>\<open>cinit_stores\<close> witness, runs the compiled prefix, picks
  \<open>x := 5\<close> at the \<open>__voblint_nondet_int()\<close> step (satisfying the guard \<open>0 < x \<and> x < 10\<close>),
  and reaches the guarded branch holding all three checks.\<close>
lemma checks_ivl_ex_reach2_nonempty: "checks_ivl_ex_reach (Statement 2) \<noteq> {}"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores checks_ivl_ex_gs" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (FunctionEntry (STR ''main''))"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect checks_ivl_ex_gs (prog_cfg checks_ivl_ex_program) (cinit_stores checks_ivl_ex_gs)
            (cfg_entry (prog_cfg checks_ivl_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding checks_ivl_ex_reach_def checks_ivl_ex_entry_eval .
  qed
  have e0: "(FunctionEntry (STR ''main''), EA_Nop, Statement 0) \<in> intra (prog_cfg checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> checks_ivl_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ivl_ex_gs "prog_cfg checks_ivl_ex_program"
        "cinit_stores checks_ivl_ex_gs" "FunctionEntry (STR ''main'')" EA_Nop "Statement 0"]
    using s0 e0 unfolding checks_ivl_ex_reach_def by simp
  have e1: "(Statement 0, EA_Special Nondet_Int (STR ''x''), Statement 1) \<in> intra (prog_cfg checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have s2: "(\<lambda>_. 0)((STR ''x'') := 5) \<in> checks_ivl_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" checks_ivl_ex_gs "prog_cfg checks_ivl_ex_program"
        "cinit_stores checks_ivl_ex_gs" "Statement 0" "EA_Special Nondet_Int (STR ''x'')" "Statement 1"
        "(\<lambda>_. 0)((STR ''x'') := 5)"]
    using s1 e1 unfolding checks_ivl_ex_reach_def by force
  have e2: "(Statement 1, EA_Assume (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10))), Statement 2)
              \<in> intra (prog_cfg checks_ivl_ex_program)"
    by (simp add: checks_ivl_ex_intra_eval)
  have "(\<lambda>_. 0)((STR ''x'') := 5) \<in> checks_ivl_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 5)" checks_ivl_ex_gs "prog_cfg checks_ivl_ex_program"
        "cinit_stores checks_ivl_ex_gs" "Statement 1" "EA_Assume (And (Less (N 0) (V (STR ''x''))) (Less (V (STR ''x'')) (N 10)))"
        "Statement 2" "(\<lambda>_. 0)((STR ''x'') := 5)"]
    using s2 e2 unfolding checks_ivl_ex_reach_def by simp
  then show ?thesis by blast
qed

subsection \<open>Whole-program check report\<close>

text \<open>
  The entire report in one shot, computed --- not hand-assembled --- from
  \<^const>\<open>classify_checks\<close> over the compiled \<^const>\<open>intra\<close> edges, in the
  checks' own compiled order: the same three outcomes the per-node lemmas
  above establish individually (\<open>checks_ivl_ex_classify_2\<close>/\<open>_3\<close>/\<open>_4\<close>), now
  read off the whole program at once.
\<close>

lemma checks_ivl_ex_report_eval:
  "analyse_interval_report_for checks_ivl_ex_gs checks_ivl_ex_program =
     [(Statement 2, Less (V (STR ''x'')) (N 11), Check_Proved),
      (Statement 3, Less (V (STR ''x'')) (N 0), Check_Refuted),
      (Statement 4, Eq (V (STR ''x'')) (N 5), Check_Unknown)]"
  by eval

text \<open>The wrapper is exactly \<^const>\<open>classify_checks\<close> applied to this
  program's own compiled CFG and computed environment --- no separate
  representation to drift from the per-node facts above.\<close>

lemma checks_ivl_ex_report_unfold:
  "analyse_interval_report_for checks_ivl_ex_gs checks_ivl_ex_program
     = classify_checks (prog_cfg checks_ivl_ex_program) checks_ivl_ex_env
         interval_classify_check"
  unfolding analyse_interval_report_for_def surface_unfold checks_ivl_ex_env_def
  by (simp add: prog_main_name_def)

text \<open>Agreement with the existing per-node classification: the first report
  entry is derivable directly from \<open>classify_checks_mem_iff\<close> together with
  the compiled \<^const>\<open>EA_Check\<close> edge (\<open>checks_ivl_ex_intra_eval\<close>) and the
  already-proven node-local classification (\<open>checks_ivl_ex_classify_2\<close>), not
  merely re-derived by \<open>eval\<close>.\<close>

corollary checks_ivl_ex_report_agrees_with_node_classification:
  "(Statement 2, Less (V (STR ''x'')) (N 11), Check_Proved)
     \<in> set (analyse_interval_report_for checks_ivl_ex_gs checks_ivl_ex_program)"
  unfolding checks_ivl_ex_report_unfold
  using classify_checks_mem_iff[of "prog_cfg checks_ivl_ex_program"
      "Statement 2" "Less (V (STR ''x'')) (N 11)" Check_Proved checks_ivl_ex_env interval_classify_check]
  using checks_ivl_ex_intra_eval checks_ivl_ex_classify_2
  by (auto simp: checks_ivl_ex_intra_eval)

subsection \<open>CFG rendering, checks colored by executable classification\<close>

text \<open>
  The compiled CFG is rendered through the same generic
  \<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close> pipeline every other example uses,
  through the same \<^const>\<open>check_result_annotation\<close> status-to-style mapping
  \<open>Example_Checks_Store_Only\<close> (Sign) uses --- shared there, not redefined
  here, confirming the mapping is analysis-independent: no Interval-specific
  rendering code was needed. There is no manually maintained \<^typ>\<open>pp\<close>-to-
  \<^typ>\<open>exp\<close> table either: \<^const>\<open>check_report_node_annotation\<close> looks each
  node up directly in the computed \<^const>\<open>analyse_interval_report_for\<close>.
\<close>

definition checks_ivl_ex_node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "checks_ivl_ex_node_annotation v =
     (case check_report_node_annotation
             (analyse_interval_report_for checks_ivl_ex_gs checks_ivl_ex_program) v of
        Some ann \<Rightarrow> Some ann
      | None \<Rightarrow>
          if v = FunctionResult (STR ''main'') then
            Some (Node_Annotation '''' NS_Exit)
          else None)"

text \<open>Validation that the generic renderer's hook actually carries all three
  computed classifications, not merely that this file's check table intends
  them to.\<close>

lemma checks_ivl_ex_annotation_proved:
  "checks_ivl_ex_node_annotation (Statement 2) =
     Some (check_result_annotation Check_Proved (Less (V (STR ''x'')) (N 11)))"
  unfolding checks_ivl_ex_node_annotation_def by eval

lemma checks_ivl_ex_annotation_refuted:
  "checks_ivl_ex_node_annotation (Statement 3) =
     Some (check_result_annotation Check_Refuted (Less (V (STR ''x'')) (N 0)))"
  unfolding checks_ivl_ex_node_annotation_def by eval

lemma checks_ivl_ex_annotation_unknown:
  "checks_ivl_ex_node_annotation (Statement 4) =
     Some (check_result_annotation Check_Unknown (Eq (V (STR ''x'')) (N 5)))"
  unfolding checks_ivl_ex_node_annotation_def by eval

definition checks_ivl_ex_dot_lit :: String.literal where
  "checks_ivl_ex_dot_lit =
     raw_cfg_dot_with_report_lit (prog_table checks_ivl_ex_program) (prog_procs checks_ivl_ex_program)
       checks_ivl_ex_node_annotation
       (analyse_interval_report_for checks_ivl_ex_gs checks_ivl_ex_program)"

end
