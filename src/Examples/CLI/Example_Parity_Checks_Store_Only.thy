section \<open>Example: Parity check-discharge, node-local, store-only\<close>

theory Example_Parity_Checks_Store_Only
  imports "Voblint_Framework.Checks" "Voblint_CLI.Parity_Entry"
          "Voblint_Analysis_Base.Analysis_GraphViz" "Voblint_VIMP.VIMP_Notation"
          "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

text \<open>
  Third-domain worked example, mirroring
  Voblint_Examples_CLI.Example_Checks_Store_Only (Sign) and
  Voblint_Examples_CLI.Example_Interval_Checks_Store_Only, discharged
  node-locally through \<^theory>\<open>Voblint_Analysis_Parity.Parity_Checks\<close> rather than by
  forwarding stores to the procedure exit.

  \<open>x\<close> is read from \<open>__voblint_nondet_int()\<close>, so neither Sign nor Interval learns anything
  about it. \<open>y := x * 2\<close> is \<^emph>\<open>always even\<close>, regardless of \<open>x\<close>'s sign or
  range --- a fact only Parity expresses. \<open>z := y + 1\<close> is then always odd.
  \<open>y\<close> and \<open>z\<close> therefore land in disjoint parity classes no matter what \<open>x\<close>
  or \<open>w\<close> (a second, independent \<open>__voblint_nondet_int()\<close> read) turn out to be: the first
  check, \<open>!(y == z)\<close>, is \<^term>\<open>Check_Proved\<close>; the second, \<open>y == z\<close> again, is
  \<^term>\<open>Check_Refuted\<close>; the third, \<open>y == w\<close> against the unconstrained \<open>w\<close>, is
  \<^term>\<open>Check_Unknown\<close> (Parity has no singleton representation, so it can
  never prove a positive equality).
\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so it cannot be
  written inside the \<open>program { ... }\<close> quotation the way other calls can: Pure's inner-syntax
  lexer reserves leading-underscore tokens for translation-internal nonterminals, rejecting any
  user identifier that begins with one.  Both calls are spliced in directly instead.\<close>
definition parity_ex_program :: imp_prog where
  "parity_ex_program = mk_program []
     (Seq (Seq (Seq
       (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int [])
       (imp \<lbrakk> y := x * 2; z := y + 1;
              __voblint_check(! (y == z)); __voblint_check(y == z) \<rbrakk>))
       (VIMP_Proc.com.Call (Some (STR ''w'')) special_pname_nondet_int []))
       (imp \<lbrakk> __voblint_check(y == w) \<rbrakk>))
     []"

text \<open>Computed, not asserted: the three \<open>__voblint_check(...)\<close> statements
  land at the nodes \<^const>\<open>compile\<close> actually assigns them.\<close>
lemma parity_ex_checks_eval:
  "checks (prog_cfg parity_ex_program) =
     {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z'')))),
      (Statement 4, Eq (V (STR ''y'')) (V (STR ''z''))),
      (Statement 6, Eq (V (STR ''y'')) (V (STR ''w'')))}"
  unfolding prog_cfg_def by eval

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere.\<close>
abbreviation parity_ex_gs :: "vname \<Rightarrow> bool" where
  "parity_ex_gs \<equiv> declared_global parity_ex_program"

lemma parity_ex_program_declared_global_vars [simp]:
  "declared_global_vars parity_ex_program = []"
  by (simp add: parity_ex_program_def)

lemma parity_ex_reserved: "reserved_ret_var parity_ex_gs"
  unfolding reserved_ret_var_def by simp

text \<open>The compiled graph has no call edges: the nondeterministic reads compile
  to \<^const>\<open>EA_Special\<close> intra edges, not \<^const>\<open>CallEdge\<close>s.\<close>

lemma parity_ex_calls_eval: "calls (prog_cfg parity_ex_program) = {}"
  unfolding prog_cfg_def
  by (rule compile_prog_calls_empty)
     (simp_all add: parity_ex_program_def special_table_def
        special_pname_nondet_int_def main_body_def prog_main_name_def)

text \<open>The routed-unit solve terminates, and its solved key set is closed under
  the compiled graph -- the four coverage facts the D/G node-soundness bridge
  turns on, each computed rather than argued.\<close>

lemma parity_ex_solver_terminates:
  "pctx_terminates_prog parity_ex_gs parity_ex_program"
  by (rule pctx_terminates_prog_via_solve_c) eval

lemma parity_ex_entry_cov:
  "(cfg_entry (prog_cfg parity_ex_program), ())
     \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
  by eval

lemma parity_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg parity_ex_program).
     (u, ()) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program) \<longrightarrow>
     (w, ()) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
  by eval

lemma parity_ex_fwd_ok:
  assumes "(u, ctx) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
    and "(u, a, w) \<in> intra (prog_cfg parity_ex_program)"
  shows "(w, ctx) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
  using assms parity_ex_fwd_ok_ball by (cases ctx) auto

lemma parity_ex_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg parity_ex_program)"
  shows "(FunctionEntry q, ()) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
  using assms by (simp add: parity_ex_calls_eval)

lemma parity_ex_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg parity_ex_program)"
  shows "(k, c1) \<in> fst (pctx_sol_prog parity_ex_gs parity_ex_program)"
  using assms by (simp add: parity_ex_calls_eval)

definition parity_ex_reach :: "pp \<Rightarrow> store set" where
  "parity_ex_reach v = ltr_collect parity_ex_gs (prog_cfg parity_ex_program) (cinit_stores parity_ex_gs) v"

text \<open>The computed Parity environment at an arbitrary node, read out of the
  routed-unit solved table \<^const>\<open>analyse_parity_result_for\<close> the production
  report also reads -- one solve, queried per node, with an unreachable node
  concretizing to \<^term>\<open>bot\<close>.\<close>
definition parity_ex_env :: "pp \<Rightarrow> parity abs_state" where
  "parity_ex_env v =
     (case lookup_context (analyse_parity_result_for parity_ex_gs parity_ex_program) v () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

text \<open>The compiled edges, read off \<^const>\<open>prog_cfg\<close>'s own \<open>eval\<close>-computed
  shape: \<open>Statement 0\<close> (\<open>x := __voblint_nondet_int()\<close>) reaches \<open>Statement 1\<close>
  (\<open>y := x * 2\<close>, always even) reaches \<open>Statement 2\<close> (\<open>z := y + 1\<close>, always
  odd) reaches \<open>Statement 3\<close> (\<open>__voblint_check(!(y == z))\<close>, proved) reaches
  \<open>Statement 4\<close> (\<open>__voblint_check(y == z)\<close>, refuted) reaches \<open>Statement 5\<close>
  (\<open>w := __voblint_nondet_int()\<close>) reaches \<open>Statement 6\<close> (\<open>__voblint_check(y == w)\<close>,
  unknown) reaches the epilogue \<open>Statement 7\<close> reaches \<open>cfg_exit\<close>.\<close>
lemma parity_ex_intra_eval:
  "intra (prog_cfg parity_ex_program) =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 0, EA_Special Nondet_Int (STR ''x''), Statement 1),
      (Statement 1, EA_Assign (STR ''y'') (Times (V (STR ''x'')) (N 2)), Statement 2),
      (Statement 2, EA_Assign (STR ''z'') (Plus (V (STR ''y'')) (N 1)), Statement 3),
      (Statement 3, EA_Check (Not (Eq (V (STR ''y'')) (V (STR ''z'')))), Statement 4),
      (Statement 4, EA_Check (Eq (V (STR ''y'')) (V (STR ''z''))), Statement 5),
      (Statement 5, EA_Special Nondet_Int (STR ''w''), Statement 6),
      (Statement 6, EA_Check (Eq (V (STR ''y'')) (V (STR ''w''))), Statement 7),
      (Statement 7, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma parity_ex_exit_eval: "cfg_exit (prog_cfg parity_ex_program) = FunctionResult (STR ''main'')"
  unfolding prog_cfg_def by (simp add: cfg_exit_compile_prog prog_main_name_def)

lemma parity_ex_entry_eval: "cfg_entry (prog_cfg parity_ex_program) = FunctionEntry (STR ''main'')"
  unfolding prog_cfg_def by (simp add: cfg_entry_compile_prog prog_main_name_def)

text \<open>Node-local collecting soundness at each check node, from the routed D/G
  node-soundness bridge and the four computed coverage facts --- no store is
  forwarded to the exit, and no reachability-to-exit premise is needed: the
  routed bridge turns on solved-key coverage, not on the query seed.\<close>

lemmas parity_ex_node_sound =
  analyse_parity_result_node_sound_for[OF parity_ex_reserved parity_ex_solver_terminates
    parity_ex_entry_cov parity_ex_fwd_ok parity_ex_call_fwd_ok parity_ex_comb_fwd_ok]

lemma parity_ex_node_sound_3:
  "parity_ex_reach (Statement 3) \<le> \<lbrakk>parity_ex_env (Statement 3)\<rbrakk>"
  unfolding parity_ex_reach_def parity_ex_env_def
  using parity_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: lifted.splits)

lemma parity_ex_node_sound_4:
  "parity_ex_reach (Statement 4) \<le> \<lbrakk>parity_ex_env (Statement 4)\<rbrakk>"
  unfolding parity_ex_reach_def parity_ex_env_def
  using parity_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: lifted.splits)

lemma parity_ex_node_sound_6:
  "parity_ex_reach (Statement 6) \<le> \<lbrakk>parity_ex_env (Statement 6)\<rbrakk>"
  unfolding parity_ex_reach_def parity_ex_env_def
  using parity_ex_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: lifted.splits)

text \<open>Executable classification at each check's own node --- \<open>y\<close> is \<open>PEven\<close>
  and \<open>z\<close> is \<open>POdd\<close> at both \<open>Statement 3\<close> and \<open>Statement 4\<close> (checks do not
  change the store), and \<open>w\<close> is \<open>PTop\<close> at \<open>Statement 6\<close> (unconstrained by
  \<open>__voblint_nondet_int()\<close>).\<close>
lemma parity_ex_classify_3:
  "parity_classify_check (Not (Eq (V (STR ''y'')) (V (STR ''z'')))) (parity_ex_env (Statement 3)) = Check_Proved"
  unfolding parity_ex_env_def by eval

lemma parity_ex_classify_4:
  "parity_classify_check (Eq (V (STR ''y'')) (V (STR ''z''))) (parity_ex_env (Statement 4)) = Check_Refuted"
  unfolding parity_ex_env_def by eval

lemma parity_ex_classify_6:
  "parity_classify_check (Eq (V (STR ''y'')) (V (STR ''w''))) (parity_ex_env (Statement 6)) = Check_Unknown"
  unfolding parity_ex_env_def by eval

text \<open>The payoff: the proved check's condition genuinely holds at every
  reaching store, and the refuted check's condition genuinely fails at every
  reaching store --- both derived from \<^const>\<open>parity_classify_check\<close> plus
  node-local collecting soundness, with no store forwarded between check
  nodes.\<close>

corollary parity_ex_first_check_holds:
  assumes "t \<in> parity_ex_reach (Statement 3)"
  shows "truthy (aval (Not (Eq (V (STR ''y'')) (V (STR ''z'')))) t)"
proof -
  have "t \<in> \<lbrakk>parity_ex_env (Statement 3)\<rbrakk>" using parity_ex_node_sound_3 assms by blast
  then show ?thesis using parity_classify_check_proved[OF parity_ex_classify_3] by blast
qed

corollary parity_ex_second_check_refuted:
  assumes "t \<in> parity_ex_reach (Statement 4)"
  shows "\<not> truthy (aval (Eq (V (STR ''y'')) (V (STR ''z''))) t)"
proof -
  have "t \<in> \<lbrakk>parity_ex_env (Statement 4)\<rbrakk>" using parity_ex_node_sound_4 assms by blast
  then show ?thesis using parity_classify_check_refuted[OF parity_ex_classify_4] by blast
qed

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Framework.Checks\<close> bridge,
  exercised on exactly the check that is actually true: the compiler's own
  \<^const>\<open>checks\<close> table names all three, but a blanket \<open>checks_proven\<close> over the
  whole table would be a false statement here, since the second check is
  genuinely refuted.\<close>

lemma parity_ex_proven_check_discharged:
  "parity_checks_proven {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))} parity_ex_env"
proof (rule parity_checks_provenI)
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))}"
  then have v_eq: "v = Statement 3" and cnd_eq: "cnd = Not (Eq (V (STR ''y'')) (V (STR ''z'')))" by auto
  show "parity_check_query cnd (parity_ex_env v) = Some True"
    unfolding v_eq cnd_eq parity_ex_env_def by eval
qed

lemma parity_ex_proven_check_checks_proven:
  "checks_proven {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))} parity_ex_reach"
proof (rule parity_checks_proven_sound)
  fix v :: pp and cnd :: exp
  assume "(v, cnd) \<in> {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))}"
  then show "parity_ex_reach v \<le> \<lbrakk>parity_ex_env v\<rbrakk>"
    using parity_ex_node_sound_3 by auto
next
  show "parity_checks_proven {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))} parity_ex_env"
    by (rule parity_ex_proven_check_discharged)
qed

text \<open>Non-vacuity: \<open>parity_ex_reach\<close> is not merely vacuously true because no
  store ever reaches these nodes. Threading \<open>x := 7\<close> and \<open>w := 99\<close> through the
  compiled prefix, admissible \<^const>\<open>EA_Special\<close> choices, reaches both the
  proved/refuted checks' shared node pair and the unknown check's own node.\<close>
lemma parity_ex_reach3_witness:
  "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15)
     \<in> parity_ex_reach (Statement 3)"
proof -
  have zero_init: "(\<lambda>_. 0) \<in> cinit_stores parity_ex_gs" unfolding cinit_stores_def by simp
  have s0: "(\<lambda>_. 0) \<in> parity_ex_reach (FunctionEntry (STR ''main''))"
  proof -
    have "(\<lambda>_. 0) \<in> ltr_collect parity_ex_gs (prog_cfg parity_ex_program) (cinit_stores parity_ex_gs)
            (cfg_entry (prog_cfg parity_ex_program))"
      by (rule ltr_collect_init[OF zero_init])
    then show ?thesis unfolding parity_ex_reach_def parity_ex_entry_eval .
  qed
  have e0: "(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0) \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have s1: "(\<lambda>_. 0) \<in> parity_ex_reach (Statement 0)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" parity_ex_gs "prog_cfg parity_ex_program"
        "cinit_stores parity_ex_gs" "FunctionEntry (STR ''main'')" "EA_Body (STR ''main'')" "Statement 0"]
    using s0 e0 unfolding parity_ex_reach_def by simp
  have e1: "(Statement 0, EA_Special Nondet_Int (STR ''x''), Statement 1) \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have s2: "(\<lambda>_. 0)((STR ''x'') := 7) \<in> parity_ex_reach (Statement 1)"
    using ltr_collect_intra_step[of "\<lambda>_. 0" parity_ex_gs "prog_cfg parity_ex_program"
        "cinit_stores parity_ex_gs" "Statement 0" "EA_Special Nondet_Int (STR ''x'')" "Statement 1"
        "(\<lambda>_. 0)((STR ''x'') := 7)"]
    using s1 e1 unfolding parity_ex_reach_def by force
  have e2: "(Statement 1, EA_Assign (STR ''y'') (Times (V (STR ''x'')) (N 2)), Statement 2)
              \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have s3: "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14) \<in> parity_ex_reach (Statement 2)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 7)" parity_ex_gs "prog_cfg parity_ex_program"
        "cinit_stores parity_ex_gs" "Statement 1" "EA_Assign (STR ''y'') (Times (V (STR ''x'')) (N 2))" "Statement 2"
        "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14)"]
    using s2 e2 unfolding parity_ex_reach_def by force
  have e3: "(Statement 2, EA_Assign (STR ''z'') (Plus (V (STR ''y'')) (N 1)), Statement 3)
              \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15) \<in> parity_ex_reach (Statement 3)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14)" parity_ex_gs
        "prog_cfg parity_ex_program" "cinit_stores parity_ex_gs"
        "Statement 2" "EA_Assign (STR ''z'') (Plus (V (STR ''y'')) (N 1))" "Statement 3"
        "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15)"]
    using s3 e3 unfolding parity_ex_reach_def by force
  then show ?thesis by blast
qed


lemma parity_ex_reach6_nonempty: "parity_ex_reach (Statement 6) \<noteq> {}"
proof -
  have s3_ne: "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15) \<in> parity_ex_reach (Statement 3)"
    by (simp add: parity_ex_reach3_witness)
  have e4: "(Statement 3, EA_Check (Not (Eq (V (STR ''y'')) (V (STR ''z'')))), Statement 4)
              \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have s4: "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15) \<in> parity_ex_reach (Statement 4)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15)" parity_ex_gs
        "prog_cfg parity_ex_program" "cinit_stores parity_ex_gs"
        "Statement 3" "EA_Check (Not (Eq (V (STR ''y'')) (V (STR ''z''))))" "Statement 4"]
    using s3_ne e4 unfolding parity_ex_reach_def by force
  have e5: "(Statement 4, EA_Check (Eq (V (STR ''y'')) (V (STR ''z''))), Statement 5)
              \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have s5: "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15) \<in> parity_ex_reach (Statement 5)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15)" parity_ex_gs
        "prog_cfg parity_ex_program" "cinit_stores parity_ex_gs"
        "Statement 4" "EA_Check (Eq (V (STR ''y'')) (V (STR ''z'')))" "Statement 5"]
    using s4 e5 unfolding parity_ex_reach_def by force
  have e6: "(Statement 5, EA_Special Nondet_Int (STR ''w''), Statement 6) \<in> intra (prog_cfg parity_ex_program)"
    by (simp add: parity_ex_intra_eval)
  have "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15, (STR ''w'') := 99) \<in> parity_ex_reach (Statement 6)"
    using ltr_collect_intra_step[of "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15)" parity_ex_gs
        "prog_cfg parity_ex_program" "cinit_stores parity_ex_gs"
        "Statement 5" "EA_Special Nondet_Int (STR ''w'')" "Statement 6"
        "(\<lambda>_. 0)((STR ''x'') := 7, (STR ''y'') := 14, (STR ''z'') := 15, (STR ''w'') := 99)"]
    using s5 e6 unfolding parity_ex_reach_def by force
  then show ?thesis by blast
qed

subsection \<open>Whole-program check report\<close>

text \<open>
  The entire report in one shot, computed --- not hand-assembled --- from
  \<^const>\<open>classify_checks\<close> over the compiled \<^const>\<open>intra\<close> edges, in the
  checks' own compiled order: the same three outcomes the per-node lemmas
  above establish individually (\<open>parity_ex_classify_3\<close>/\<open>_4\<close>/\<open>_6\<close>), now read
  off the whole program at once.
\<close>

lemma parity_ex_report_eval:
  "analyse_parity_report_for parity_ex_gs parity_ex_program =
     [(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))), Check_Proved),
      (Statement 4, Eq (V (STR ''y'')) (V (STR ''z'')), Check_Refuted),
      (Statement 6, Eq (V (STR ''y'')) (V (STR ''w'')), Check_Unknown)]"
  by eval

text \<open>The wrapper is exactly \<^const>\<open>classify_checks\<close> applied to this
  program's own compiled CFG and computed environment --- no separate
  representation to drift from the per-node facts above.\<close>

lemma parity_ex_report_unfold:
  "analyse_parity_report_for parity_ex_gs parity_ex_program
     = classify_checks (prog_cfg parity_ex_program) parity_ex_env parity_classify_check"
  unfolding analyse_parity_report_for_def surface_unfold parity_ex_env_def
            prog_main_name_def
  by simp

text \<open>Agreement with the existing per-node classification: the first report
  entry is derivable directly from \<open>classify_checks_mem_iff\<close> together with
  the compiled \<^const>\<open>EA_Check\<close> edge (\<open>parity_ex_intra_eval\<close>) and the
  already-proven node-local classification (\<open>parity_ex_classify_3\<close>), not
  merely re-derived by \<open>eval\<close>.\<close>

corollary parity_ex_report_agrees_with_node_classification:
  "(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))), Check_Proved)
     \<in> set (analyse_parity_report_for parity_ex_gs parity_ex_program)"
  unfolding parity_ex_report_unfold
  using classify_checks_mem_iff[of "prog_cfg parity_ex_program"
      "Statement 3" "Not (Eq (V (STR ''y'')) (V (STR ''z'')))" Check_Proved parity_ex_env parity_classify_check]
  using parity_ex_intra_eval parity_ex_classify_3
  by (auto simp: parity_ex_intra_eval)

text \<open>The proved entry, discharged against the collecting semantics rather
  than against the computed table: \<open>analyse_parity_report_sound_proved_for\<close>
  (\<^theory>\<open>Voblint_CLI.Parity_Entry\<close>) turns a \<^term>\<open>Check_Proved\<close> report
  entry into a statement about every store \<^const>\<open>ltr_collect\<close> admits at that
  node, from the same four coverage facts the node-soundness bridge uses.\<close>

corollary parity_ex_report_proved_entry_sound:
  "\<forall>t \<in> parity_ex_reach (Statement 3). truthy (aval (Not (Eq (V (STR ''y'')) (V (STR ''z'')))) t)"
  unfolding parity_ex_reach_def
  using analyse_parity_report_sound_proved_for
          [OF parity_ex_reserved parity_ex_solver_terminates parity_ex_entry_cov
              parity_ex_fwd_ok parity_ex_call_fwd_ok parity_ex_comb_fwd_ok
              parity_ex_report_agrees_with_node_classification]
  by (simp add: prog_main_name_def)

subsection \<open>CFG rendering, checks colored by executable classification\<close>

text \<open>
  The compiled CFG is rendered through the same generic
  \<^theory>\<open>Voblint_Analysis_Base.Analysis_GraphViz\<close> pipeline every other example uses
  (\<^const>\<open>raw_cfg_dot_lit\<close>), through the same check-agnostic
  \<^type>\<open>graphviz_node_annotation\<close> hook. There is no manually maintained
  \<^typ>\<open>pp\<close>-to-\<^typ>\<open>exp\<close> table: \<^const>\<open>check_report_node_annotation\<close> looks
  each node up directly in the computed \<^const>\<open>analyse_parity_report_for\<close>.
  \<^term>\<open>Check_Proved\<close> renders dark green, \<^term>\<open>Check_Refuted\<close> red,
  \<^term>\<open>Check_Unknown\<close> grey. The unrelated \<open>FunctionResult (STR ''main'')\<close> exit
  node gets its own neutral-grey annotation through the same hook.
\<close>

definition parity_ex_node_annotation :: "pp \<Rightarrow> graphviz_node_annotation option" where
  "parity_ex_node_annotation v =
     (case check_report_node_annotation
             (analyse_parity_report_for parity_ex_gs parity_ex_program) v of
        Some ann \<Rightarrow> Some ann
      | None \<Rightarrow>
          if v = FunctionResult (STR ''main'') then
            Some (Node_Annotation '''' NS_Exit)
          else None)"

text \<open>Validation that the generic renderer's hook actually carries all three
  computed classifications, not merely that this file's check table intends
  them to.\<close>

lemma parity_ex_annotation_proved:
  "parity_ex_node_annotation (Statement 3) =
     Some (check_result_annotation Check_Proved (Not (Eq (V (STR ''y'')) (V (STR ''z'')))))"
  unfolding parity_ex_node_annotation_def by eval

lemma parity_ex_annotation_refuted:
  "parity_ex_node_annotation (Statement 4) =
     Some (check_result_annotation Check_Refuted (Eq (V (STR ''y'')) (V (STR ''z''))))"
  unfolding parity_ex_node_annotation_def by eval

lemma parity_ex_annotation_unknown:
  "parity_ex_node_annotation (Statement 6) =
     Some (check_result_annotation Check_Unknown (Eq (V (STR ''y'')) (V (STR ''w''))))"
  unfolding parity_ex_node_annotation_def by eval

definition parity_ex_dot_lit :: String.literal where
  "parity_ex_dot_lit =
     raw_cfg_dot_with_report_lit (prog_table parity_ex_program) (prog_procs parity_ex_program)
       parity_ex_node_annotation
       (analyse_parity_report_for parity_ex_gs parity_ex_program)"

end
