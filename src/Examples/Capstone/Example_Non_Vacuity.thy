theory Example_Non_Vacuity
  imports "Voblint_CLI.Run_Voblint"
begin

section \<open>The headline theorems are not vacuous\<close>

text \<open>
  A theorem whose premises no configuration meets is true and says nothing. This
  theory shows, for the endpoints of \<^theory>\<open>Voblint_CLI.Run_Voblint\<close>, that their
  premises hold together on one concrete program, and that the conclusion is then
  informative: the verdict it constrains is \<^const>\<open>Check_Proved\<close> or \<^const>\<open>Dead\<close>, not
  \<^const>\<open>Check_Unknown\<close>. It then shows five conditions to be load-bearing: the
  definite verdicts a report states, the transfer obligation of the congruence
  remainder, the context correlation of RETURN and the TOTAL obligation in
  \<^const>\<open>gactivation_coverage\<close>, and the pairing in \<^const>\<open>entry_pairs_cover\<close>. Dropping
  or weakening each admits an answer that misses a concrete execution.

  Non-vacuity is a property of the premises. It says nothing about whether
  \<^const>\<open>pstep\<close> models the intended language.
\<close>

subsection \<open>The two-call program\<close>

text \<open>
  \<open>bump\<close> is called with \<open>5\<close> and with \<open>4\<close>. Entry-state contexts keep the two
  activations apart, so both checks are proved; without contexts the entry of
  \<open>bump\<close> joins \<open>[4, 5]\<close> and neither is.
\<close>

definition nv_prog :: imp_prog where
  "nv_prog = program {
     fun bump(n) { return n + 1; }
     fun main() {
       a = bump(5);
       b = bump(4);
       __voblint_check(a == 6);
       __voblint_check(b == 5);
     }
   }"

definition nv_conf :: voblint_conf where
  "nv_conf = \<lparr>conf_analyses = [Interval], conf_context = Entry_State,
     conf_globals = Globals_Warrow, conf_program_globals = Program_Globals_Flow_Sensitive,
     conf_sem = default_sem_conf\<rparr>"

lemma nv_report:
  "(case run_voblint nv_conf [] nv_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
          = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]
    | _ \<Rightarrow> False)"
  by eval

lemma nv_analysed:
  obtains res where
    "run_voblint nv_conf [] nv_prog = Analysed res"
    "map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
       = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
  using nv_report by (cases "run_voblint nv_conf [] nv_prog") auto

subsection \<open>The premises, discharged\<close>

text \<open>
  Each premise of the source-level endpoints, proved for \<open>nv_prog\<close>: the zero store is
  initial, and the typed run reaches the first check (\<open>nv_to_check\<close>).
\<close>

abbreviation nv_var :: "vname \<Rightarrow> var_id" where
  "nv_var x \<equiv> ScopedId (STR ''main'') x"

lemma nv_init: "(\<lambda>_. 0) \<in> init_stores (kenv_of [])"
  by (simp add: init_stores_def all_in_kinds_def kenv_of_def)

lemma nv_bump:
  "elab_ptable nv_prog [] (STR ''bump'')
     = Some \<lparr>formals = [ScopedId (STR ''bump'') (STR ''n'')],
             body = Return () (Some (TArith I32 AAdd (TVar I32 (ScopedId (STR ''bump'') (STR ''n'')))
                                       (TN I32 1)))\<rparr>"
  by eval

lemma nv_main:
  "main_body (elab_ptable nv_prog [])
     = Seq (Seq (Seq (gcom.Call () (Some (nv_var (STR ''a''))) (STR ''bump'') [TN I32 5])
                     (gcom.Call () (Some (nv_var (STR ''b''))) (STR ''bump'') [TN I32 4]))
                (Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6))))
           (Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''b''))) (TN I32 5)))"
  by eval

text \<open>One call of \<open>bump\<close>: enter, return \<open>n + 1\<close>, and resume the caller.\<close>

lemma nv_call:
  assumes k: "k \<in> ik_range I32" and k1: "k + 1 \<in> ik_range I32"
  shows
    "(kenv_of []),(elab_ptable nv_prog []) \<turnstile> (gcom.Call () (Some (nv_var x)) (STR ''bump'') [TN I32 k], t, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), t(nv_var x := k + 1), [])"
proof -
  let ?\<kappa> = "kenv_of []" and ?\<Pi> = "elab_ptable nv_prog []"
  let ?n = "ScopedId (STR ''bump'') (STR ''n'')"
  let ?E = "TArith I32 AAdd (TVar I32 ?n) (TN I32 1)"
  let ?c = "bind_formals [?n] (map2 (\<lambda>y. kind_conv ?\<kappa> (Some y)) [?n] [eval (TN I32 k) t])
              (enter_state is_global t)"
  let ?c' = "?c(ReturnVar := eval ?E ?c)"
  have s1:
    "?\<kappa>,?\<Pi> \<turnstile> (gcom.Call () (Some (nv_var x)) (STR ''bump'') [TN I32 k], t, []) \<rightarrow>\<^sub>p (Seq (Return () (Some ?E)) (Restore ()), ?c, [Frame t (Some (nv_var x))])"
    using vimp.pstep_Call[where \<Pi> = ?\<Pi> and p = "STR ''bump''", OF nv_bump,
        of "[TN I32 k]" ?\<kappa> "()" "Some (nv_var x)" t "[]"]
    by simp
  have s2:
    "?\<kappa>,?\<Pi> \<turnstile> (Seq (Return () (Some ?E)) (Restore ()), ?c, [Frame t (Some (nv_var x))]) \<rightarrow>\<^sub>p (Seq (Unwind ()) (Restore ()), ?c', [Frame t (Some (nv_var x))])"
    by (rule vimp.Seq2) (rule vimp.ReturnSome)
  have s3:
    "?\<kappa>,?\<Pi> \<turnstile> (Seq (Unwind ()) (Restore ()), ?c', [Frame t (Some (nv_var x))]) \<rightarrow>\<^sub>p (SKIP (), combine_assign (Some (nv_var x)) (kind_conv ?\<kappa> (Some (nv_var x)) (?c' ReturnVar)) (combine_env is_global t ?c'), [])"
    by (rule vimp.UnwindAct)
  have eq: "combine_assign (Some (nv_var x)) (kind_conv ?\<kappa> (Some (nv_var x)) (?c' ReturnVar))
              (combine_env is_global t ?c') = t(nv_var x := k + 1)"
    using k k1
    by (auto simp: fun_eq_iff combine_env_def enter_state_def kenv_of_def simp del: ik_range_iff)
  show ?thesis
    using s1 s2 s3 by (simp only: eq[symmetric]) (meson star.step star.refl)
qed

abbreviation nv_final :: store where
  "nv_final \<equiv> (\<lambda>_. 0)(nv_var (STR ''a'') := 6, nv_var (STR ''b'') := 5)"

abbreviation nv_checks :: "(unit, var_id, exp) gcom" where
  "nv_checks \<equiv> Seq (Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6)))
                  (Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''b''))) (TN I32 5)))"

text \<open>The typed run, stopped with the first check about to execute.\<close>

lemma nv_to_check:
  "(kenv_of []),(elab_ptable nv_prog []) \<turnstile> (main_body (elab_ptable nv_prog []), \<lambda>_. 0, []) \<rightarrow>\<^sub>p\<^sup>* (nv_checks, nv_final, [])"
proof -
  let ?\<kappa> = "kenv_of []" and ?\<Pi> = "elab_ptable nv_prog []"
  let ?C1 = "gcom.Call () (Some (nv_var (STR ''a''))) (STR ''bump'') [TN I32 5]"
  let ?C2 = "gcom.Call () (Some (nv_var (STR ''b''))) (STR ''bump'') [TN I32 4]"
  let ?K1 = "Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6))"
  let ?K2 = "Check () (0, 0) (TCmp CEq (TVar I32 (nv_var (STR ''b''))) (TN I32 5))"
  let ?t1 = "(\<lambda>_. 0)(nv_var (STR ''a'') := 6) :: store"
  have r: "(4::int) \<in> ik_range I32" "(5::int) \<in> ik_range I32" "(6::int) \<in> ik_range I32"
    by eval+
  have c1: "?\<kappa>,?\<Pi> \<turnstile> (?C1, \<lambda>_. 0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), ?t1, [])"
    using nv_call[where k = 5 and x = "STR ''a''" and t = "\<lambda>_. 0", OF r(2)] r(3) by simp
  have c2: "?\<kappa>,?\<Pi> \<turnstile> (?C2, ?t1, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), nv_final, [])"
    using nv_call[where k = 4 and x = "STR ''b''" and t = ?t1, OF r(1)] r(2) by simp
  have calls: "?\<kappa>,?\<Pi> \<turnstile> (Seq ?C1 ?C2, \<lambda>_. 0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP (), nv_final, [])"
    using vimp.psteps_Seq2[OF c1, of ?C2] c2 by (meson vimp.Seq1 star.step star_trans)
  have "?\<kappa>,?\<Pi> \<turnstile> (Seq (Seq ?C1 ?C2) ?K1, \<lambda>_. 0, []) \<rightarrow>\<^sub>p\<^sup>* (?K1, nv_final, [])"
    using vimp.psteps_Seq2[OF calls, of ?K1] by (meson vimp.Seq1 star.step star.refl star_trans)
  then show ?thesis unfolding nv_main by (rule vimp.psteps_Seq2)
qed

subsection \<open>The endpoints, instantiated\<close>

text \<open>
  With the premises discharged, \<open>run_voblint_source_sound\<close> and its siblings apply to
  \<open>nv_prog\<close> and to \<open>nv_dead_prog\<close>, and the verdicts they constrain are \<open>Check_Proved\<close>
  and \<open>Dead\<close>.
\<close>

theorem nv_source_certified:
  "\<exists>res v stk.
     run_voblint nv_conf [] nv_prog = Analysed res
   \<and> map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
       = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]
   \<and> elab_ptable nv_prog [], elab_cfg nv_prog [], prog_main_name
       \<turnstile> (nv_checks, nv_final, []) \<approx> (v, nv_final, stk)
   \<and> nv_final \<in> reaching [] nv_prog v
   \<and> (\<exists>d. Lifted d \<in> report_states_at res v
          \<and> nv_final \<in> mcp.act_gamma [] (activation_of (conf_analyses nv_conf)) d)
   \<and> \<not> DEAD res v"
proof -
  obtain res where ans: "run_voblint nv_conf [] nv_prog = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
                   = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
    by (rule nv_analysed)
  from run_voblint_source_sound [OF ans nv_init nv_to_check]
  obtain v stk where
    sim: "elab_ptable nv_prog [], elab_cfg nv_prog [], prog_main_name
            \<turnstile> (nv_checks, nv_final, []) \<approx> (v, nv_final, stk)"
    and reach: "nv_final \<in> reaching [] nv_prog v"
    and st: "\<exists>d. Lifted d \<in> report_states_at res v
               \<and> nv_final \<in> mcp.act_gamma [] (activation_of (conf_analyses nv_conf)) d"
    and live: "\<not> DEAD res v"
    by blast
  show ?thesis
    by (rule exI[of _ res], rule exI[of _ v], rule exI[of _ stk])
       (simp only: ans checks sim reach st live simp_thms)
qed

text \<open>
  Read at the check: the store the run holds there reaches a listed check for
  \<open>a == 6\<close>, that check says \<^const>\<open>Check_Proved\<close>, and the condition holds.
\<close>

theorem nv_check_proved_sound:
  "\<exists>res. run_voblint nv_conf [] nv_prog = Analysed res
     \<and> (\<exists>chk \<in> set (report_checks res).
          check_exp chk = TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6)
          \<and> nv_final \<in> reaching [] nv_prog (check_point chk)
          \<and> check_verdict chk = Decided Check_Proved
          \<and> truthy (eval (TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6)) nv_final))"
proof -
  obtain res where ans: "run_voblint nv_conf [] nv_prog = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
                   = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
    by (rule nv_analysed)
  have nc:
    "next_check nv_checks = Some ((0, 0), TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6))"
    by simp
  from run_voblint_check_sound [OF ans nv_init nv_to_check nc]
  obtain chk where listed: "chk \<in> set (report_checks res)"
    and re: "check_exp chk = TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6)"
    and mem: "nv_final \<in> reaching [] nv_prog (check_point chk)"
    and pr: "check_verdict chk = Decided Check_Proved
               \<longrightarrow> truthy (eval (TCmp CEq (TVar I32 (nv_var (STR ''a''))) (TN I32 6)) nv_final)"
    by blast
  have "(check_point chk, check_verdict chk)
          \<in> set [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
    unfolding checks [symmetric] using listed by auto
  then have "check_verdict chk = Decided Check_Proved" by auto
  with ans listed re mem pr show ?thesis by blast
qed

definition nv_dead_prog :: imp_prog where
  "nv_dead_prog = program {
     fun main() {
       x = 1;
       __voblint_check(x == 0);
       if (x < 0) { __voblint_check(x == 5); } else { x = 2; }
     }
   }"

definition nv_dead_conf :: voblint_conf where
  "nv_dead_conf = \<lparr>conf_analyses = [Interval], conf_context = Call_String 0,
     conf_globals = Globals_Join, conf_program_globals = Program_Globals_Flow_Sensitive,
     conf_sem = default_sem_conf\<rparr>"

lemma nv_dead_report:
  "(case run_voblint nv_dead_conf [] nv_dead_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
          = [(Statement 1, Decided Check_Refuted), (Statement 3, Dead)]
    | _ \<Rightarrow> False)"
  by eval

lemma nv_dead_analysed:
  obtains res where
    "run_voblint nv_dead_conf [] nv_dead_prog = Analysed res"
    "map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
       = [(Statement 1, Decided Check_Refuted), (Statement 3, Dead)]"
  using nv_dead_report by (cases "run_voblint nv_dead_conf [] nv_dead_prog") auto

theorem nv_dead_unreached: "reaching [] nv_dead_prog (Statement 3) = {}"
proof -
  obtain res where ans: "run_voblint nv_dead_conf [] nv_dead_prog = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_verdict chk)) (report_checks res)
                   = [(Statement 1, Decided Check_Refuted), (Statement 3, Dead)]"
    by (rule nv_dead_analysed)
  obtain chk where mem: "chk \<in> set (report_checks res)" and pt: "check_point chk = Statement 3"
    and dead: "check_verdict chk = Dead"
    using checks by (cases "report_checks res" rule: remdups_adj.cases) auto
  from ans have wf: "wf_program_compile_input nv_dead_prog"
    and rep: "report_run nv_dead_conf [] nv_dead_prog = Some res"
    by (auto elim!: run_voblint_AnalysedE intro: wf_program_compile_input_exec_sound)
  show ?thesis
    using report_check_live[OF wf rep _ mem pt] dead by blast
qed

section \<open>Load-bearing conditions\<close>

text \<open>
  Each subsection below drops or weakens one condition and exhibits an answer that
  meets everything else yet misses a concrete execution.
\<close>

subsection \<open>Soundness alone is cheap\<close>

text \<open>
  The guarantees constrain only definite verdicts, so a report that answers
  \<^const>\<open>Check_Unknown\<close> at every check meets them at every store. The endpoint is
  informative because the verdicts \<^const>\<open>run_voblint\<close> actually returns above are
  \<^const>\<open>Check_Proved\<close> and \<^const>\<open>Dead\<close>.
\<close>

definition answer_all :: "contextual_verdict \<Rightarrow> report \<Rightarrow> report" where
  "answer_all vd res =
     res\<lparr>report_checks := map (\<lambda>chk. chk\<lparr>check_verdict := vd\<rparr>) (report_checks res)\<rparr>"

lemma unknown_everywhere_sound:
  "\<forall>chk \<in> set (report_checks (answer_all (Decided Check_Unknown) res)).
     (check_verdict chk = Decided Check_Proved \<longrightarrow> P chk)
     \<and> (check_verdict chk = Decided Check_Refuted \<longrightarrow> Q chk)"
  by (auto simp: answer_all_def)

text \<open>
  An answer of \<^const>\<open>Check_Proved\<close> everywhere is not sound: the store after
  \<open>x = 1\<close> reaches the check \<open>x == 0\<close>, which it falsifies.
\<close>

lemma nv_dead_reaches_first_check:
  "(\<lambda>_. 0)(nv_var (STR ''x'') := 1) \<in> reaching [] nv_dead_prog (Statement 1)"
proof -
  have intra: "(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0)
                 \<in> intra (elab_cfg nv_dead_prog [])"
    "(Statement 0, EA_Assign (nv_var (STR ''x'')) (TN I32 1), Statement 1)
                 \<in> intra (elab_cfg nv_dead_prog [])"
    by eval+
  have entry: "cfg_entry (elab_cfg nv_dead_prog []) = FunctionEntry (STR ''main'')"
    by eval
  have e0: "(\<lambda>_. 0) \<in> reaching [] nv_dead_prog (FunctionEntry (STR ''main''))"
    using vimp.node_collect_init [OF nv_init, of "kenv_of []" "elab_cfg nv_dead_prog []"]
    by (simp add: entry)
  have s0: "(\<lambda>_. 0) \<in> reaching [] nv_dead_prog (Statement 0)"
    by (rule vimp.node_collect_intra_step [OF e0 intra(1)]) simp
  show ?thesis
    by (rule vimp.node_collect_intra_step [OF s0 intra(2)]) (simp add: kenv_of_def)
qed

theorem proved_everywhere_unsound:
  assumes "run_voblint nv_dead_conf [] nv_dead_prog = Analysed res"
  shows "\<exists>chk \<in> set (report_checks (answer_all (Decided Check_Proved) res)).
           check_verdict chk = Decided Check_Proved
           \<and> (\<lambda>_. 0)(nv_var (STR ''x'') := 1) \<in> reaching [] nv_dead_prog (check_point chk)
           \<and> \<not> truthy (eval (check_exp chk) ((\<lambda>_. 0)(nv_var (STR ''x'') := 1)))"
proof -
  have exps: "map (\<lambda>chk. (check_point chk, check_exp chk)) (report_checks res)
      = [(Statement 1, TCmp CEq (TVar I32 (nv_var (STR ''x''))) (TN I32 0)),
         (Statement 3, TCmp CEq (TVar I32 (nv_var (STR ''x''))) (TN I32 5))]"
  proof -
    have "(case run_voblint nv_dead_conf [] nv_dead_prog of
             Analysed res \<Rightarrow> map (\<lambda>chk. (check_point chk, check_exp chk)) (report_checks res)
                = [(Statement 1, TCmp CEq (TVar I32 (nv_var (STR ''x''))) (TN I32 0)),
                   (Statement 3, TCmp CEq (TVar I32 (nv_var (STR ''x''))) (TN I32 5))]
           | _ \<Rightarrow> False)"
      by eval
    then show ?thesis using assms by simp
  qed
  then obtain chk where mem: "chk \<in> set (report_checks res)" and pt: "check_point chk = Statement 1"
      and ex: "check_exp chk = TCmp CEq (TVar I32 (nv_var (STR ''x''))) (TN I32 0)"
    by (cases "report_checks res" rule: remdups_adj.cases) auto
  have mem': "chk\<lparr>check_verdict := Decided Check_Proved\<rparr>
                \<in> set (report_checks (answer_all (Decided Check_Proved) res))"
    using mem by (simp add: answer_all_def)
  show ?thesis
    using nv_dead_reaches_first_check pt ex
    by (intro bexI[OF _ mem']) simp
qed

subsection \<open>The pre-fix Goblint congruence remainder\<close>

text \<open>
  Before Goblint pull request 1161, the remainder of the odd class \<open>1 + 2\<int>\<close> by the
  constant \<open>2\<close> was the constant \<open>1\<close>. Any abstract remainder that answers so violates
  the obligation \<open>congruence_mod_sound\<close> discharges for the shipped one: \<open>-5\<close> is
  odd, and its truncating remainder by \<open>2\<close> is \<open>-1\<close>.
\<close>

theorem prefix_congruence_mod_unsound:
  assumes const: "f (mk_congruence 1 2) (mk_congruence 2 0) = mk_congruence 1 0"
  shows "\<not> (\<forall>a b i j. i \<in> gamma_congruence a \<longrightarrow> j \<in> gamma_congruence b
                     \<longrightarrow> c_mod i j \<in> gamma_congruence (f a b))"
proof
  assume sound: "\<forall>a b i j. i \<in> gamma_congruence a \<longrightarrow> j \<in> gamma_congruence b
                     \<longrightarrow> c_mod i j \<in> gamma_congruence (f a b)"
  have "c_mod (-5) 2 \<in> gamma_congruence (mk_congruence 1 0)"
    using sound [rule_format, of "-5" "mk_congruence 1 2" 2 "mk_congruence 2 0"]
    by (simp add: const gamma_congruence_def)
  then show False by (simp add: gamma_congruence_def c_mod_def c_div_def)
qed

section \<open>The paired-coverage, RETURN and TOTAL counterexamples\<close>

text \<open>
  Three weakenings of \<open>gactivation_coverage\<close> fail: RETURN read at the caller's
  context, TOTAL dropped, and entry coverage without pairing. They belong to the
  generic framework and are shown at the typed instance the analyzer uses. \<open>ret_prog\<close>
  calls \<open>f\<close> with \<open>1\<close> and then \<open>5\<close>; every variable has the default kind
  \<^const>\<open>I32\<close>.
\<close>

definition ret_prog :: imp_prog where
  "ret_prog = program {
     fun f(n) { return n; }
     fun main() { a = f(1); b = f(5); }
   }"

abbreviation ret_n :: var_id where
  "ret_n \<equiv> ScopedId (STR ''f'') (STR ''n'')"

abbreviation ret_\<kappa> :: kenv where
  "ret_\<kappa> \<equiv> kenv_of []"

abbreviation ret_g :: "(var_id, exp) gcfg" where
  "ret_g \<equiv> elab_cfg ret_prog []"

lemma ret_norm [simp]: "ik_norm I32 1 = 1" "ik_norm I32 5 = 5" "(1::int) \<in> ik_range I32"
  by eval+

lemma ret_intra:
  "intra ret_g =
     {(FunctionEntry (STR ''f''), EA_Body (STR ''f''), Statement 0),
      (Statement 0, EA_Ret (Some (TVar I32 ret_n)) (STR ''f''), FunctionResult (STR ''f'')),
      (Statement 1, EA_Ret None (STR ''f''), FunctionResult (STR ''f'')),
      (FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 2),
      (Statement 4, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  by eval

lemma ret_calls:
  "calls ret_g =
     {(Statement 2, CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1],
       FunctionEntry (STR ''f''), Statement 3),
      (Statement 3, CallEdge (Some (nv_var (STR ''b''))) [ret_n] [TN I32 5],
       FunctionEntry (STR ''f''), Statement 4)}"
  by eval

lemma ret_entry: "cfg_entry ret_g = FunctionEntry (STR ''main'')"
  by eval

lemma ret_enter:
  "vimp.gcall_enter ret_\<kappa> (CallEdge dst [ret_n] [e]) s
     = (enter_state is_global s)(ret_n := ik_norm I32 (eval e s))"
  by (simp add: vimp.call_enter_CallEdge kenv_of_def)

lemma ret_enter_zero [simp]: "enter_state is_global (\<lambda>_. 0) = (\<lambda>_. 0)"
  by (simp add: enter_state_def enter_frame_def fun_eq_iff)

lemma ret_combine:
  assumes "\<And>v. is_global v \<Longrightarrow> t v = 0"
  shows
    "vimp.gcombine_collect \<kappa> (Some x) (\<lambda>_. 0) t = (\<lambda>_. 0)(x := kind_conv \<kappa> (Some x) (t ReturnVar))"
  using assms by (auto simp: cfg_transfer_sem.gcombine_collect_def fun_eq_iff)

text \<open>The policy of the illustration: the callee context is the entry value of \<open>n\<close>.\<close>

definition ret_R :: "(var_id, exp, int) gcontext_policy" where
  "ret_R = context_policy_of_fun (\<lambda>_ _ es. es ret_n)"

text \<open>
  The claim: \<open>main\<close> is covered in the initial context \<open>0\<close> up to its first call site
  and nowhere after it; \<open>f\<close> is covered everywhere, but only in the contexts its
  calls create.
\<close>

definition ret_cover :: "cfg_node \<Rightarrow> int \<Rightarrow> store set" where
  "ret_cover v ctx =
     (if v \<in> {FunctionEntry (STR ''f''), Statement 0, FunctionResult (STR ''f'')}
      then (if ctx = 0 then {} else UNIV)
      else if ctx = 0 \<and> v \<in> {FunctionEntry (STR ''main''), Statement 2} then UNIV else {})"

lemma ret_weak_obligations:
  shows "\<forall>s. s \<in> init_stores ret_\<kappa> \<longrightarrow> s \<in> ret_cover (cfg_entry ret_g) 0"
    and "\<forall>u a v c s s'. (u, a, v) \<in> intra ret_g \<longrightarrow> s \<in> ret_cover u c
              \<longrightarrow> s' \<in> vimp.gedge_step ret_\<kappa> a s \<longrightarrow> s' \<in> ret_cover v c"
    and "\<forall>u dst pars args p cont c c' s.
              (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ret_g
              \<longrightarrow> s \<in> ret_cover u c
              \<longrightarrow> c' \<in> ret_R u c (call_info_of (CallEdge dst pars args) p) s
                    (vimp.gcall_enter ret_\<kappa> (CallEdge dst pars args) s)
              \<longrightarrow> vimp.gcall_enter ret_\<kappa> (CallEdge dst pars args) s
                    \<in> ret_cover (FunctionEntry p) c'"
    and "\<forall>cl dst pars args p cont c1 s t.
              (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ret_g
              \<longrightarrow> s \<in> ret_cover cl c1 \<longrightarrow> t \<in> ret_cover (FunctionResult p) c1
              \<longrightarrow> vimp.gcombine_collect ret_\<kappa> dst s t \<in> ret_cover cont c1"
    and "vimp.gcall_context_total_on ret_\<kappa> ret_cover ret_R ret_g"
  by (auto simp: ret_entry ret_intra ret_calls ret_cover_def ret_R_def ret_enter
                 vimp.gcall_context_total_on_def)

lemma ret_not_coverage:
  "\<not> gactivation_coverage eval ReturnVar (kind_conv ret_\<kappa>) is_global ret_g
       (init_stores ret_\<kappa>) ret_cover ret_R 0"
proof
  assume "gactivation_coverage eval ReturnVar (kind_conv ret_\<kappa>) is_global ret_g
            (init_stores ret_\<kappa>) ret_cover ret_R 0"
  then interpret C: gactivation_coverage eval ReturnVar "kind_conv ret_\<kappa>" is_global
    ret_g "init_stores ret_\<kappa>" ret_cover ret_R 0 .
  have e: "(Statement 2, CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1],
             FunctionEntry (STR ''f''), Statement 3) \<in> calls ret_g"
    by (simp add: ret_calls)
  have adm: "vimp.gadmits_call_context ret_\<kappa> ret_g ret_R
               (Statement 2) 0 (STR ''f'') (\<lambda>_. 0)
               (vimp.gcall_enter ret_\<kappa>
                  (CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1]) (\<lambda>_. 0)) 1"
    unfolding vimp.gadmits_call_context_def
    by (rule exI [of _ "Some (nv_var (STR ''a''))"], rule exI [of _ "[ret_n]"],
        rule exI [of _ "[TN I32 1]"], rule exI [of _ "Statement 3"])
       (simp add: e ret_R_def ret_enter)
  have "vimp.gcombine_collect ret_\<kappa> (Some (nv_var (STR ''a''))) (\<lambda>_. 0) (\<lambda>_. 0)
          \<in> ret_cover (Statement 3) 0"
    by (rule C.RETURN [OF e _ adm]) (simp_all add: ret_cover_def)
  then show False by (simp add: ret_cover_def)
qed

lemma ret_f_body:
  "star (vimp.gcfg_intra_step ret_\<kappa> ret_g)
     (FunctionEntry (STR ''f''), (\<lambda>_. 0)(ret_n := k))
     (FunctionResult (STR ''f''), ((\<lambda>_. 0)(ret_n := k))(ReturnVar := k))"
proof (rule star_trans)
  show "star (vimp.gcfg_intra_step ret_\<kappa> ret_g)
          (FunctionEntry (STR ''f''), (\<lambda>_. 0)(ret_n := k))
          (Statement 0, (\<lambda>_. 0)(ret_n := k))"
    by (rule vimp.intra_path_single [where a = "EA_Body (STR ''f'')"]) (auto simp: ret_intra)
next
  show "star (vimp.gcfg_intra_step ret_\<kappa> ret_g)
          (Statement 0, (\<lambda>_. 0)(ret_n := k))
          (FunctionResult (STR ''f''), ((\<lambda>_. 0)(ret_n := k))(ReturnVar := k))"
    by (rule vimp.intra_path_single [where a = "EA_Ret (Some (TVar I32 ret_n)) (STR ''f'')"])
       (auto simp: ret_intra)
qed

lemma ret_globals_zero: "is_global v \<Longrightarrow> (((\<lambda>_. 0)(ret_n := k))(ReturnVar := k)) v = 0"
  by (cases v) simp_all

lemma ret_reaches_second_call:
  "(\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<in> \<C>\<^bsub>ret_\<kappa>,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 3)"
proof -
  have e0: "(\<lambda>_. 0) \<in> \<C>\<^bsub>ret_\<kappa>,ret_g,init_stores ret_\<kappa>\<^esub> (FunctionEntry (STR ''main''))"
    using vimp.node_collect_init [OF nv_init, of ret_\<kappa> ret_g] by (simp add: ret_entry)
  have s2: "(\<lambda>_. 0) \<in> \<C>\<^bsub>ret_\<kappa>,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 2)"
    by (rule vimp.node_collect_intra_step [OF e0, where a = "EA_Body (STR ''main'')"])
       (auto simp: ret_intra)
  have ce: "(Statement 2, CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1],
             FunctionEntry (STR ''f''), Statement 3) \<in> calls ret_g"
    by (simp add: ret_calls)
  have bd: "star (vimp.gcfg_intra_step ret_\<kappa> ret_g)
              (FunctionEntry (STR ''f''),
               vimp.gcall_enter ret_\<kappa> (CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1]) (\<lambda>_. 0))
              (FunctionResult (STR ''f''), ((\<lambda>_. 0)(ret_n := 1))(ReturnVar := 1))"
    using ret_f_body [where k = 1] by (simp add: ret_enter)
  show ?thesis
    using vimp.node_collect_call_return_step [OF s2 ce bd]
    by (simp add: ret_combine [OF ret_globals_zero] kenv_of_def)
qed

text \<open>
  Reading the callee at the caller's own context: the claim meets INIT, INTRA,
  CALL, the weakened RETURN and TOTAL, yet it covers no store at the second call
  site in any context, although a concrete trace reaches it. So \<open>b = f(5)\<close> is
  declared unreachable.
\<close>

theorem return_at_caller_context_unsound:
  "(\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<in> \<C>\<^bsub>ret_\<kappa>,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 3)
   \<and> (\<Union>c. ret_cover (Statement 3) c) = {}"
  using ret_reaches_second_call by (simp add: ret_cover_def)

subsection \<open>TOTAL is load-bearing\<close>

text \<open>
  A resumed caller carries its own context whatever its callee carries, so the
  continuation of a call is collected in the caller's bucket even when the relation
  admits no callee context. Such a relation makes CALL and RETURN vacuous.
\<close>

lemma resume_keeps_context:
  assumes s: "s \<in> \<A>\<^bsub>\<kappa>,adm,c0,g,S\<^esub> u ctx"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls g"
    and body: "star (vimp.gcfg_intra_step \<kappa> g)
                 (FunctionEntry q, vimp.gcall_enter \<kappa> (CallEdge dst pars args) s)
                 (FunctionResult q, t)"
  shows "vimp.gcombine_collect \<kappa> dst s t \<in> \<A>\<^bsub>\<kappa>,adm,c0,g,S\<^esub> cont ctx"
proof -
  from s obtain caller where cv: "caller \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
    and cn: "sink_node caller = u" and ck: "vimp.gactivation_context_rel \<kappa> adm c0 g caller ctx"
    and cs: "sink_store caller = s"
    by (rule vimp.activation_collect_E)
  let ?entered = "Call caller [(FunctionEntry q, vimp.gcall_enter \<kappa> (CallEdge dst pars args) s)]"
  have ev: "?entered \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
    using vimp.gvalid_activation_trace.call [OF cv, where dst = dst and pars = pars and args = args
                            and p = q and cont = cont]
      ce cn cs by simp
  obtain callee where dv: "callee \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
    and dn: "sink_node callee = FunctionResult q" and ds: "sink_store callee = t"
    and dc: "caller_of callee = caller_of ?entered"
    by (rule vimp.valid_activation_trace_intra_path_extend [OF _ ev]) (use body in simp_all)
  let ?r = "Resume caller callee
              (path_of caller @ [(cont, vimp.gcombine_collect \<kappa> dst
                  (sink_store caller) (sink_store callee))])"
  have rv: "?r \<in> \<T>\<^bsub>\<kappa>,g,S\<^esub>"
    by (rule vimp.gvalid_activation_trace.ret [OF dv _ dn]) (use dc ce cn in simp_all)
  have "sink_store ?r \<in> \<A>\<^bsub>\<kappa>,adm,c0,g,S\<^esub> (sink_node ?r) ctx"
    by (rule vimp.activation_collect_I [OF rv refl]) (use ck in simp)
  then show ?thesis using cs ds by (simp add: sink_node_def sink_store_def)
qed

text \<open>The relation that admits no context, and the claim that covers \<open>main\<close> up to its first
  call site in the initial context and nothing else.\<close>

definition tot_R :: "(var_id, exp, int) gcontext_policy" where
  "tot_R u ctx ci s es = {}"

definition tot_cover :: "cfg_node \<Rightarrow> int \<Rightarrow> store set" where
  "tot_cover v ctx =
     (if ctx = 0 \<and> v \<in> {FunctionEntry (STR ''main''), Statement 2} then UNIV else {})"

lemma tot_weak_obligations:
  shows "\<forall>s. s \<in> init_stores ret_\<kappa> \<longrightarrow> s \<in> tot_cover (cfg_entry ret_g) 0"
    and "\<forall>u a v c s s'. (u, a, v) \<in> intra ret_g \<longrightarrow> s \<in> tot_cover u c
              \<longrightarrow> s' \<in> vimp.gedge_step ret_\<kappa> a s \<longrightarrow> s' \<in> tot_cover v c"
    and "\<forall>u dst pars args p cont c c' s.
              (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ret_g
              \<longrightarrow> s \<in> tot_cover u c
              \<longrightarrow> c' \<in> tot_R u c (call_info_of (CallEdge dst pars args) p) s
                    (vimp.gcall_enter ret_\<kappa> (CallEdge dst pars args) s)
              \<longrightarrow> vimp.gcall_enter ret_\<kappa> (CallEdge dst pars args) s
                    \<in> tot_cover (FunctionEntry p) c'"
    and "\<forall>cl dst pars args p cont c1 c' p' s t es.
              (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls ret_g
              \<longrightarrow> s \<in> tot_cover cl c1
              \<longrightarrow> vimp.gadmits_call_context ret_\<kappa> ret_g tot_R cl c1 p' s es c'
              \<longrightarrow> t \<in> tot_cover (FunctionResult p) c'
              \<longrightarrow> vimp.gcombine_collect ret_\<kappa> dst s t \<in> tot_cover cont c1"
    and "\<not> vimp.gcall_context_total_on ret_\<kappa> tot_cover tot_R ret_g"
  by (auto simp: ret_entry ret_intra ret_calls tot_cover_def tot_R_def vimp.gadmits_call_context_def
                 vimp.gcall_context_total_on_def)

text \<open>
  The claim meets INIT, INTRA, CALL and RETURN and fails only TOTAL. The run resumes at
  the second call site in the initial context, where the claim is empty, so the
  per-context conclusion of \<open>gactivation_collect_sound\<close> fails.
\<close>

theorem total_dropped_unsound:
  "(\<lambda>_. 0)(nv_var (STR ''a'') := 1)
     \<in> \<A>\<^bsub>ret_\<kappa>,tot_R,0,ret_g,init_stores ret_\<kappa>\<^esub> (Statement 3) 0
   \<and> (\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<notin> tot_cover (Statement 3) 0"
proof
  let ?S = "init_stores ret_\<kappa>"
  let ?t0 = "Root [(FunctionEntry (STR ''main''), \<lambda>_. 0)]"
  have v0: "?t0 \<in> \<T>\<^bsub>ret_\<kappa>,ret_g,?S\<^esub>"
    using vimp.gvalid_activation_trace.root [where s = "\<lambda>_. 0" and S = ?S and g = ret_g]
      nv_init by (simp add: ret_entry)
  have v1: "Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)]
              \<in> \<T>\<^bsub>ret_\<kappa>,ret_g,?S\<^esub>"
    using vimp.gvalid_activation_trace.intra
      [OF v0, where a = "EA_Body (STR ''main'')" and v = "Statement 2" and s' = "\<lambda>_. 0"]
    by (simp add: ret_intra sink_node_def sink_store_def)
  have s2: "(\<lambda>_. 0) \<in> \<A>\<^bsub>ret_\<kappa>,tot_R,0,ret_g,?S\<^esub> (Statement 2) 0"
  proof -
    have "sink_store (Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)])
            \<in> \<A>\<^bsub>ret_\<kappa>,tot_R,0,ret_g,?S\<^esub>
                (sink_node (Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)])) 0"
      by (rule vimp.activation_collect_I [OF v1]) (simp_all add: sink_node_def)
    then show ?thesis by (simp add: sink_node_def sink_store_def)
  qed
  have ce: "(Statement 2, CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1],
             FunctionEntry (STR ''f''), Statement 3) \<in> calls ret_g"
    by (simp add: ret_calls)
  have bd: "star (vimp.gcfg_intra_step ret_\<kappa> ret_g)
              (FunctionEntry (STR ''f''),
               vimp.gcall_enter ret_\<kappa> (CallEdge (Some (nv_var (STR ''a''))) [ret_n] [TN I32 1]) (\<lambda>_. 0))
              (FunctionResult (STR ''f''), ((\<lambda>_. 0)(ret_n := 1))(ReturnVar := 1))"
    using ret_f_body [where k = 1] by (simp add: ret_enter)
  show "(\<lambda>_. 0)(nv_var (STR ''a'') := 1)
          \<in> \<A>\<^bsub>ret_\<kappa>,tot_R,0,ret_g,?S\<^esub> (Statement 3) 0"
    using resume_keeps_context [OF s2 ce bd]
    by (simp add: ret_combine [OF ret_globals_zero] kenv_of_def)
  show "(\<lambda>_. 0)(nv_var (STR ''a'') := 1) \<notin> tot_cover (Statement 3) 0"
    by (simp add: tot_cover_def)
qed

subsection \<open>Entry coverage must be paired\<close>

text \<open>
  \<open>y = p(x)\<close> with \<open>fun p(a) { return a; }\<close> and \<open>x = 1\<close>, all of kind \<^const>\<open>I32\<close>.
  Abstract values are represented by their concretizations, which hold values of kind
  \<^const>\<open>I32\<close> at \<open>a\<close>, so
  \<^const>\<open>entry_pairs_cover\<close> is taken at \<^const>\<open>id\<close>. The answer
  \<open>[(x > 0, a < 0), (\<bottom>, a > 0)]\<close> covers the caller store with its first pair and the
  entered store with its second. Each pair's callee result, \<open>a\<close> published as the return
  value, is combined with that pair's own continuation; the union excludes the run's
  \<open>y = 1\<close>.
\<close>

abbreviation up_x :: var_id where "up_x \<equiv> (nv_var (STR ''x''))"
abbreviation up_y :: var_id where "up_y \<equiv> (nv_var (STR ''y''))"
abbreviation up_a :: var_id where "up_a \<equiv> ScopedId (STR ''p'') (STR ''a'')"

definition unpaired_answer :: "(store set \<times> store set) list" where
  "unpaired_answer =
     [({t. 0 < t up_x}, {t. t up_a \<in> ik_range I32 \<and> t up_a < 0}),
      ({}, {t. t up_a \<in> ik_range I32 \<and> 0 < t up_a})]"

definition pairwise_contribution :: "(store set \<times> store set) list \<Rightarrow> store set" where
  "pairwise_contribution P =
     (\<Union>(q, e) \<in> set P.
        {vimp.gcombine_collect (ret_\<kappa>) (Some up_y) s0 (t(ReturnVar := t up_a))
         | s0 t. s0 \<in> q \<and> t \<in> e})"

theorem unpaired_entry_cover_unsound:
  defines "s \<equiv> (\<lambda>_. 0)(up_x := 1) :: store"
      and "s' \<equiv> (\<lambda>_. 0)(up_a := 1) :: store"
  shows "s' = vimp.gcall_enter (ret_\<kappa>) (CallEdge (Some up_y) [up_a] [TVar I32 up_x]) s"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s \<in> q)"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s' \<in> e)"
    and "\<not> entry_pairs_cover id s s' unpaired_answer"
    and "\<forall>u \<in> pairwise_contribution unpaired_answer. u up_y < 0"
    and "vimp.gcombine_collect (ret_\<kappa>) (Some up_y) s (s'(ReturnVar := s' up_a)) up_y = 1"
  by (auto simp: s_def s'_def unpaired_answer_def pairwise_contribution_def
                 entry_pairs_cover_def vimp.call_enter_CallEdge enter_state_def enter_frame_def
                 cfg_transfer_sem.gcombine_collect_def kenv_of_def fun_eq_iff)

end
