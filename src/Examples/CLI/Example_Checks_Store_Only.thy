section \<open>Example: checks_proven/checks_provenD alone, store-only\<close>

theory Example_Checks_Store_Only
  imports "Voblint_Framework.Checks"
          "Voblint_Analysis_Sign.Sign_Analyses"
          "Voblint_VIMP.VIMP_Notation"
          "Voblint_Examples_CFG.Example_Compile_Call_Free"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N

text \<open>
  Exercises \<^const>\<open>checks_proven\<close> against a computed (not hand-built) Sign
  post-solution, discharged node-locally through the generic
  \<^theory>\<open>Voblint_Analysis_Sign.Sign_Classify\<close> interface rather than by forwarding each
  check node's stores to the procedure exit. The compiled \<^const>\<open>checks\<close> field
  comes from a real \<^const>\<open>compile_prog\<close> run, not a hand-built table;
  \<open>y\<close> is overwritten (\<open>y := 0\<close>) between the first and second check, and \<open>z\<close> is
  set by a nondeterministic \<open>__voblint_nondet_int()\<close> read, so the three checks land in each
  of the three possible outcomes: the first is \<^term>\<open>Check_Proved\<close>, the second
  --- checking \<open>0 < y\<close> again after \<open>y := 0\<close> --- is \<^term>\<open>Check_Refuted\<close>, and
  the third --- \<open>z = 1\<close> against an unconstrained \<open>z\<close> --- is \<^term>\<open>Check_Unknown\<close>.
  The run is Sign's unit-context registration \<open>sign_rule\<close> at \<^const>\<open>Globals_Join\<close>,
  and its node-soundness endpoint \<open>sign_rule.result_node_sound_closure\<close> connects
  the computed table back to \<^const>\<open>ltr_collect\<close> at each check's own node ---
  every covered node, not only the solver's query seed. No ghost or
  trace-projection content: the check
  condition is a plain \<^typ>\<open>exp\<close>.
\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so it cannot be
  written inside the \<open>program { ... }\<close> quotation the way other calls can: Pure's inner-syntax
  lexer reserves leading-underscore tokens for translation-internal nonterminals, rejecting any
  user identifier that begins with one.  The call is spliced in directly instead.\<close>
definition checks_ex_program :: imp_prog where
  "checks_ex_program = mk_program []
     (Seq (Seq (imp \<lbrakk> y = 5; __voblint_check(0 < y); y = 0; __voblint_check(0 < y); \<rbrakk>)
                (VIMP_Proc.com.Call (Some (STR ''z'')) special_pname_nondet_int []))
          (imp \<lbrakk> __voblint_check(z == 1); \<rbrakk>))
     []"

text \<open>Computed, not asserted: the three \<open>check(...)\<close> statements land at the
  nodes \<^const>\<open>compile\<close> actually assigns them.\<close>
lemma checks_ex_checks_eval:
  "checks (prog_cfg checks_ex_program) =
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

text \<open>The nondeterministic read compiles to an \<^const>\<open>EA_Special\<close> intra edge, not a
  \<^const>\<open>CallEdge\<close>, so the graph has no call edges and the node-soundness bridge's two
  call-closure obligations hold vacuously.  The remaining coverage facts are computed.\<close>

lemma checks_ex_calls_eval: "calls (prog_cfg checks_ex_program) = {}"
  unfolding prog_cfg_def
  by (rule compile_prog_calls_empty)
     (simp_all add: checks_ex_program_def main_body_def prog_main_name_def
        special_table_def special_pname_nondet_int_def)

lemma checks_ex_solver_terminates:
  "sign_rule.terminates Globals_Join checks_ex_gs checks_ex_program"
  by (rule sign_rule.terminates_of_solve_c) (simp only: sign_rule.root_query_def, eval)

lemma checks_ex_entry_cov:
  "(cfg_entry (prog_cfg checks_ex_program), ())
     \<in> sign_rule.sol_vars Globals_Join checks_ex_gs checks_ex_program"
  by eval

lemma checks_ex_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg checks_ex_program).
     (u, ()) \<in> sign_rule.sol_vars Globals_Join checks_ex_gs checks_ex_program \<longrightarrow>
     (w, ()) \<in> sign_rule.sol_vars Globals_Join checks_ex_gs checks_ex_program"
  by eval

definition checks_ex_reach :: "pp \<Rightarrow> store set" where
  "checks_ex_reach v =
     ltr_collect checks_ex_gs (prog_cfg checks_ex_program)
       (cinit_stores checks_ex_gs) v"

text \<open>The computed Sign environment at an arbitrary node, read out of the
  routed-unit solved table \<open>sign_rule.result\<close> the production
  report also reads -- one solve, queried per node, with an unreachable node
  concretizing to \<^term>\<open>bot\<close>.\<close>
definition checks_ex_env :: "pp \<Rightarrow> sign abs_state" where
  "checks_ex_env v =
     (case lookup_context (sign_rule.result Globals_Join checks_ex_gs checks_ex_program) v () of
        Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"

text \<open>The compiled edges: the proved check leaves \<open>Statement 1\<close>, \<open>y := 0\<close> runs before the
  refuted check at \<open>Statement 3\<close>, and the unconstrained \<open>z\<close> is read just before the unknown
  check at \<open>Statement 5\<close>.\<close>
lemma checks_ex_intra_eval:
  "intra (prog_cfg checks_ex_program) =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 0, EA_Assign (STR ''y'') (N 5), Statement 1),
      (Statement 1, EA_Check (Less (N 0) (V (STR ''y''))), Statement 2),
      (Statement 2, EA_Assign (STR ''y'') (N 0), Statement 3),
      (Statement 3, EA_Check (Less (N 0) (V (STR ''y''))), Statement 4),
      (Statement 4, EA_Special Nondet_Int (STR ''z''), Statement 5),
      (Statement 5, EA_Check (Eq (V (STR ''z'')) (N 1)), Statement 6),
      (Statement 6, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma checks_ex_entry_eval: "cfg_entry (prog_cfg checks_ex_program) = FunctionEntry (STR ''main'')"
  by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)

text \<open>Node-local collecting soundness at every node --- no store is forwarded to the exit,
  and no reachability-to-exit premise is needed.\<close>

lemma checks_ex_node_sound: "checks_ex_reach v \<le> \<lbrakk>checks_ex_env v\<rbrakk>"
  unfolding checks_ex_reach_def checks_ex_env_def sign_rule.state_at_unfold[symmetric]
  using checks_ex_fwd_ok_ball
  by (intro sign_rule.result_node_sound_closure checks_ex_solver_terminates
        checks_ex_entry_cov)
     (auto simp: checks_ex_calls_eval)

text \<open>Executable classification at each check's own node --- \<open>y\<close> is \<open>SPos\<close>
  right after \<open>y := 5\<close>, \<open>SZero\<close> right after \<open>y := 0\<close> (so the second \<open>0 < y\<close> is refuted,
  not merely unproven), and \<open>z\<close> is \<open>STop\<close> at \<open>Statement 5\<close>.\<close>
lemma checks_ex_classify_1:
  "sign_classify_check (Less (N 0) (V (STR ''y''))) (checks_ex_env (Statement 1)) = Check_Proved"
  unfolding checks_ex_env_def by eval

lemma checks_ex_classify_3:
  "sign_classify_check (Less (N 0) (V (STR ''y''))) (checks_ex_env (Statement 3)) = Check_Refuted"
  unfolding checks_ex_env_def by eval

lemma checks_ex_classify_5:
  "sign_classify_check (Eq (V (STR ''z'')) (N 1)) (checks_ex_env (Statement 5)) = Check_Unknown"
  unfolding checks_ex_env_def by eval

text \<open>The proved check's condition holds at every reaching store and the refuted check's
  fails at every reaching store; the unknown check gets no such corollary, by design.\<close>

corollary checks_ex_first_check_holds:
  assumes "t \<in> checks_ex_reach (Statement 1)"
  shows "truthy (aval (Less (N 0) (V (STR ''y''))) t)"
  using assms checks_ex_node_sound sign_classify_check_proved[OF checks_ex_classify_1] by blast

corollary checks_ex_second_check_refuted:
  assumes "t \<in> checks_ex_reach (Statement 3)"
  shows "\<not> truthy (aval (Less (N 0) (V (STR ''y''))) t)"
  using assms checks_ex_node_sound sign_classify_check_refuted[OF checks_ex_classify_3] by blast

text \<open>The generic \<^const>\<open>checks_proven\<close>/\<^theory>\<open>Voblint_Framework.Checks\<close> bridge,
  exercised on exactly the checks that are actually true: the compiler's own
  \<^const>\<open>checks\<close> table names all three, but a blanket \<open>checks_proven\<close> over the
  whole table would be a false statement here, since the second check is a
  genuine bug (refuted, not merely unproven).\<close>

lemma checks_ex_proven_check_discharged:
  "sign_checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_env"
proof (rule sign_checks_provenI)
  fix v :: pp and cnd :: exp
  assume mem: "(v, cnd) \<in> {(Statement 1, Less (N 0) (V (STR ''y'')))}"
  then have v_eq: "v = Statement 1" and cnd_eq: "cnd = Less (N 0) (V (STR ''y''))" by auto
  show "sign_check_query cnd (checks_ex_env v) = Some True"
    unfolding v_eq cnd_eq checks_ex_env_def by eval
qed

lemma checks_ex_proven_check_checks_proven:
  "checks_proven {(Statement 1, Less (N 0) (V (STR ''y'')))} checks_ex_reach"
  by (rule sign_checks_proven_sound)
     (use checks_ex_node_sound checks_ex_proven_check_discharged in auto)

text \<open>Non-vacuity: stores do reach the check nodes.  The all-zero initial store runs the
  compiled prefix to the first check and, reading \<open>7\<close> for \<open>z\<close>, on to the third.\<close>

lemma checks_ex_reach_nonempty:
  "checks_ex_reach (Statement 1) \<noteq> {}" "checks_ex_reach (Statement 5) \<noteq> {}"
proof -
  note step = ltr_collect_intra_step[where gs = checks_ex_gs and g = "prog_cfg checks_ex_program"
      and S = "cinit_stores checks_ex_gs", folded checks_ex_reach_def]
  have "(\<lambda>_. 0) \<in> checks_ex_reach (cfg_entry (prog_cfg checks_ex_program))"
    unfolding checks_ex_reach_def by (rule ltr_collect_init) (simp add: cinit_stores_def)
  then have "(\<lambda>_. 0) \<in> checks_ex_reach (Statement 0)"
    by (rule step) (auto simp: checks_ex_entry_eval checks_ex_intra_eval)
  then have s1: "(\<lambda>_. 0)(STR ''y'' := 5) \<in> checks_ex_reach (Statement 1)"
    by (rule step) (auto simp: checks_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''y'' := 5) \<in> checks_ex_reach (Statement 2)"
    by (rule step) (auto simp: checks_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''y'' := 0) \<in> checks_ex_reach (Statement 3)"
    by (rule step) (auto simp: checks_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''y'' := 0) \<in> checks_ex_reach (Statement 4)"
    by (rule step) (auto simp: checks_ex_intra_eval)
  then have "(\<lambda>_. 0)(STR ''y'' := 0, STR ''z'' := 7) \<in> checks_ex_reach (Statement 5)"
    by (rule step) (auto simp: checks_ex_intra_eval)
  with s1 show "checks_ex_reach (Statement 1) \<noteq> {}" "checks_ex_reach (Statement 5) \<noteq> {}"
    by blast+
qed

subsection \<open>Whole-program check report\<close>

text \<open>
  The report computed from \<^const>\<open>classify_checks\<close> over the compiled \<^const>\<open>intra\<close>
  edges, in the checks' compiled order, agrees with the three per-node classifications
  above.  It is shown once here; the Interval and Parity siblings pin only the evaluated
  report.
\<close>

lemma checks_ex_report_eval:
  "sign_rule.report Globals_Join checks_ex_gs checks_ex_program =
     [(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved),
      (Statement 3, Less (N 0) (V (STR ''y'')), Check_Refuted),
      (Statement 5, Eq (V (STR ''z'')) (N 1), Check_Unknown)]"
  unfolding sign_rule.report_def by eval

lemma checks_ex_report_unfold:
  "sign_rule.report Globals_Join checks_ex_gs checks_ex_program
     = classify_checks (prog_cfg checks_ex_program) checks_ex_env sign_classify_check"
  unfolding sign_rule.report_def surface_unfold checks_ex_env_def
  by (simp add: prog_main_name_def)

corollary checks_ex_report_agrees_with_node_classification:
  "(Statement 1, Less (N 0) (V (STR ''y'')), Check_Proved)
     \<in> set (sign_rule.report Globals_Join checks_ex_gs checks_ex_program)"
  unfolding checks_ex_report_unfold
  using classify_checks_mem_iff[of "prog_cfg checks_ex_program"
      "Statement 1" "Less (N 0) (V (STR ''y''))" Check_Proved checks_ex_env sign_classify_check]
  using checks_ex_intra_eval checks_ex_classify_1
  by (auto simp: checks_ex_intra_eval)

end

