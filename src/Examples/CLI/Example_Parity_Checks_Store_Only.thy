section \<open>Example: Parity check-discharge, node-local, store-only\<close>

theory Example_Parity_Checks_Store_Only
  imports "Voblint_Framework.Checks" "Voblint_Analysis_Parity.Parity_Entry"
          "Voblint_CLI.Analysis_Graph_Export" "Voblint_VIMP.VIMP_Notation"
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

text \<open>The nondeterministic reads compile to \<^const>\<open>EA_Special\<close> intra edges, so the graph has
  no call edges and the node-soundness bridge's call-closure obligations hold vacuously.\<close>

lemma parity_ex_calls_eval: "calls (prog_cfg parity_ex_program) = {}"
  unfolding prog_cfg_def
  by (rule compile_prog_calls_empty)
     (simp_all add: parity_ex_program_def special_table_def
        special_pname_nondet_int_def main_body_def prog_main_name_def)

lemma parity_ex_solver_terminates:
  "parity_conf_terminates_prog parity_ex_gs parity_ex_program"
  by (rule parity_conf_terminates_prog_via_solve_c) eval

lemma parity_ex_entry_cov:
  "(cfg_entry (prog_cfg parity_ex_program), ())
     \<in> fst (parity_conf_sol_prog parity_ex_gs parity_ex_program)"
  by eval

lemma parity_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg parity_ex_program).
     (u, ()) \<in> fst (parity_conf_sol_prog parity_ex_gs parity_ex_program) \<longrightarrow>
     (w, ()) \<in> fst (parity_conf_sol_prog parity_ex_gs parity_ex_program)"
  by eval

definition parity_ex_reach :: "pp \<Rightarrow> store set" where
  "parity_ex_reach v =
     ltr_collect parity_ex_gs (prog_cfg parity_ex_program)
       (cinit_stores parity_ex_gs) v"

text \<open>The computed Parity environment at an arbitrary node, read out of the
  routed-unit solved table \<^const>\<open>analyse_parity_result_for\<close> the production
  report also reads, with an unreachable node concretizing to \<^term>\<open>bot\<close>.\<close>
definition parity_ex_env :: "pp \<Rightarrow> parity abs_state" where
  "parity_ex_env v =
     (case lookup_context (analyse_parity_result_for parity_ex_gs parity_ex_program) v () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

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

lemma parity_ex_entry_eval: "cfg_entry (prog_cfg parity_ex_program) = FunctionEntry (STR ''main'')"
  unfolding prog_cfg_def by (simp add: prog_main_name_def)

lemma parity_ex_node_sound: "parity_ex_reach v \<le> \<lbrakk>parity_ex_env v\<rbrakk>"
  unfolding parity_ex_reach_def parity_ex_env_def
  using parity_ex_fwd_ok_ball
  by (intro analyse_parity_result_node_sound_for parity_ex_solver_terminates
        parity_ex_entry_cov)
     (auto simp: parity_ex_calls_eval)

text \<open>Executable classification at each check's own node --- \<open>y\<close> is \<open>PEven\<close>
  and \<open>z\<close> is \<open>POdd\<close> at both \<open>Statement 3\<close> and \<open>Statement 4\<close> (checks do not
  change the store), and \<open>w\<close> is \<open>PTop\<close> at \<open>Statement 6\<close>.\<close>
lemma parity_ex_classify_3:
  "parity_classify_check (Not (Eq (V (STR ''y'')) (V (STR ''z''))))
     (parity_ex_env (Statement 3)) = Check_Proved"
  unfolding parity_ex_env_def by eval

lemma parity_ex_classify_4:
  "parity_classify_check (Eq (V (STR ''y'')) (V (STR ''z'')))
     (parity_ex_env (Statement 4)) = Check_Refuted"
  unfolding parity_ex_env_def by eval

lemma parity_ex_classify_6:
  "parity_classify_check (Eq (V (STR ''y'')) (V (STR ''w'')))
     (parity_ex_env (Statement 6)) = Check_Unknown"
  unfolding parity_ex_env_def by eval

corollary parity_ex_first_check_holds:
  assumes "t \<in> parity_ex_reach (Statement 3)"
  shows "truthy (aval (Not (Eq (V (STR ''y'')) (V (STR ''z'')))) t)"
  using assms parity_ex_node_sound parity_classify_check_proved[OF parity_ex_classify_3]
  by blast

corollary parity_ex_second_check_refuted:
  assumes "t \<in> parity_ex_reach (Statement 4)"
  shows "\<not> truthy (aval (Eq (V (STR ''y'')) (V (STR ''z''))) t)"
  using assms parity_ex_node_sound parity_classify_check_refuted[OF parity_ex_classify_4]
  by blast

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Framework.Checks\<close> bridge,
  exercised on the one check that is actually true: a blanket \<open>checks_proven\<close> over the
  compiler's whole \<^const>\<open>checks\<close> table would be false, since the second check is refuted.\<close>

lemma parity_ex_proven_check_discharged:
  "parity_checks_proven {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))} parity_ex_env"
proof (rule parity_checks_provenI)
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))}"
  then have v_eq: "v = Statement 3"
    and cnd_eq: "cnd = Not (Eq (V (STR ''y'')) (V (STR ''z'')))"
    by auto
  show "parity_check_query cnd (parity_ex_env v) = Some True"
    unfolding v_eq cnd_eq parity_ex_env_def by eval
qed

lemma parity_ex_proven_check_checks_proven:
  "checks_proven {(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))))} parity_ex_reach"
  by (rule parity_checks_proven_sound)
     (use parity_ex_node_sound parity_ex_proven_check_discharged in auto)

text \<open>Non-vacuity: reading \<open>7\<close> for \<open>x\<close> and \<open>99\<close> for \<open>w\<close>, the all-zero initial store reaches
  the proved/refuted checks' node pair and the unknown check's node.\<close>

lemma parity_ex_reach_nonempty:
  "parity_ex_reach (Statement 3) \<noteq> {}" "parity_ex_reach (Statement 6) \<noteq> {}"
proof -
  note step = ltr_collect_intra_step[where gs = parity_ex_gs and g = "prog_cfg parity_ex_program"
      and S = "cinit_stores parity_ex_gs", folded parity_ex_reach_def]
  have "(\<lambda>_. 0) \<in> parity_ex_reach (cfg_entry (prog_cfg parity_ex_program))"
    unfolding parity_ex_reach_def by (rule ltr_collect_init) (simp add: cinit_stores_def)
  then have "(\<lambda>_. 0) \<in> parity_ex_reach (Statement 0)"
    by (rule step) (auto simp: parity_ex_entry_eval parity_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 7) \<in> parity_ex_reach (Statement 1)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 7, STR ''y'' := 14) \<in> parity_ex_reach (Statement 2)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  then have s3: "(\<lambda>_. 0)(STR ''x'' := 7, STR ''y'' := 14, STR ''z'' := 15)
      \<in> parity_ex_reach (Statement 3)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 7, STR ''y'' := 14, STR ''z'' := 15)
      \<in> parity_ex_reach (Statement 4)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 7, STR ''y'' := 14, STR ''z'' := 15)
      \<in> parity_ex_reach (Statement 5)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''x'' := 7, STR ''y'' := 14, STR ''z'' := 15, STR ''w'' := 99)
      \<in> parity_ex_reach (Statement 6)"
    by (rule step) (auto simp: parity_ex_intra_eval)
  with s3 show "parity_ex_reach (Statement 3) \<noteq> {}" "parity_ex_reach (Statement 6) \<noteq> {}"
    by blast+
qed

subsection \<open>Whole-program check report\<close>

lemma parity_ex_report_eval:
  "analyse_parity_report_for parity_ex_gs parity_ex_program =
     [(Statement 3, Not (Eq (V (STR ''y'')) (V (STR ''z''))), Check_Proved),
      (Statement 4, Eq (V (STR ''y'')) (V (STR ''z'')), Check_Refuted),
      (Statement 6, Eq (V (STR ''y'')) (V (STR ''w'')), Check_Unknown)]"
  by eval

text \<open>The proved entry, discharged against the collecting semantics rather than against
  the computed table, by the report-level soundness theorem of
  \<^theory>\<open>Voblint_Analysis_Parity.Parity_Entry\<close>.\<close>

corollary parity_ex_report_proved_entry_sound:
  "\<forall>t \<in> parity_ex_reach (Statement 3). truthy (aval (Not (Eq (V (STR ''y'')) (V (STR ''z'')))) t)"
  unfolding parity_ex_reach_def
  using parity_ex_fwd_ok_ball
  by (intro analyse_parity_report_sound_proved_for parity_ex_solver_terminates
        parity_ex_entry_cov)
     (auto simp: parity_ex_calls_eval parity_ex_report_eval)

end
