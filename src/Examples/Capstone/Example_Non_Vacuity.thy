theory Example_Non_Vacuity
  imports Example_End_To_End_Certificate
begin

section \<open>The headline theorems are not vacuous\<close>

text \<open>
  A theorem whose premises no configuration meets is true and says nothing. This
  theory shows, for each endpoint of \<^theory>\<open>Voblint_CLI.Analysis_Certified\<close>, that its
  premises hold together on one concrete program, and that the conclusion is then
  informative: the verdict it constrains is \<^const>\<open>Check_Proved\<close> or \<^const>\<open>Dead\<close>, not
  \<^const>\<open>Check_Unknown\<close>. It then shows five conditions to be load-bearing: the
  verdict clause of \<^const>\<open>checks_sound_at\<close>, the transfer obligation of the
  congruence remainder, the context correlation of RETURN and the TOTAL obligation in
  \<^const>\<open>ltr_coverage\<close>, and the pairing in \<^const>\<open>entry_pairs_cover\<close>. Dropping
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

lemma nv_report:
  "(case run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res)
          = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]
    | _ \<Rightarrow> False)"
  by eval

lemma nv_analysed:
  obtains res where
    "run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog = Analysed res"
    "map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res)
       = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
  using nv_report
  by (cases "run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog") auto

subsection \<open>The premises, discharged\<close>

lemma nv_init: "(\<lambda>_. 0) \<in> cinit_stores (declared_global nv_prog)"
  by (simp add: cinit_stores_def)

lemma nv_no_globals: "declared_global nv_prog = (\<lambda>_. False)"
  by (simp add: nv_prog_def fun_eq_iff)

lemma nv_table:
  "prog_table nv_prog (STR ''bump'')
     = Some \<lparr>formals = [STR ''n''],
              body = VIMP_Proc.com.Return (Some (Plus (V (STR ''n'')) (N 1)))\<rparr>"
  by (simp add: nv_prog_def prog_main_name_def)

lemma nv_main:
  "main_body (prog_table nv_prog)
     = VIMP_Proc.com.Seq
         (VIMP_Proc.com.Seq
            (VIMP_Proc.com.Seq
               (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 5])
               (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 4]))
            (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6))))
         (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''b'')) (N 5)))"
  by (simp add: nv_prog_def main_body_def prog_main_name_def)

lemma nv_call:
  "pcompletes (declared_global nv_prog) (prog_table nv_prog)
     (VIMP_Proc.com.Call (Some x) (STR ''bump'') [N k]) s (s(x := k + 1))"
  using pcompletes_Call_return
          [where \<Pi> = "prog_table nv_prog" and p = "STR ''bump''"
             and decl = "\<lparr>formals = [STR ''n''],
                          body = VIMP_Proc.com.Return (Some (Plus (V (STR ''n'')) (N 1)))\<rparr>"
             and e = "Plus (V (STR ''n'')) (N 1)" and actuals = "[N k]" and dst = "Some x"
             and \<G> = "declared_global nv_prog" and s = s,
           OF nv_table]
  by (simp add: nv_no_globals enter_state_def combine_env_def)

abbreviation nv_final :: store where
  "nv_final \<equiv> (\<lambda>_. 0)(STR ''a'' := 6, STR ''b'' := 5)"

lemma nv_calls:
  "pcompletes (declared_global nv_prog) (prog_table nv_prog)
     (VIMP_Proc.com.Seq (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 5])
        (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 4]))
     (\<lambda>_. 0) nv_final"
proof -
  have c1: "pcompletes (declared_global nv_prog) (prog_table nv_prog)
              (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 5]) (\<lambda>_. 0)
              ((\<lambda>_. 0)(STR ''a'' := 6))"
    using nv_call [where x = "STR ''a''" and k = 5 and s = "\<lambda>_. 0"] by simp
  have c2: "pcompletes (declared_global nv_prog) (prog_table nv_prog)
              (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 4])
              ((\<lambda>_. 0)(STR ''a'' := 6)) nv_final"
    using nv_call [where x = "STR ''b''" and k = 4 and s = "(\<lambda>_. 0)(STR ''a'' := 6)"]
    by simp
  show ?thesis by (rule pcompletes_Seq [OF c1 c2])
qed

text \<open>The source run, stopped with the first check about to execute.\<close>

lemma nv_to_check:
  "star (pstep (declared_global nv_prog) (prog_table nv_prog))
     (main_body (prog_table nv_prog), \<lambda>_. 0, [])
     (VIMP_Proc.com.Seq (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6)))
        (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''b'')) (N 5))), nv_final, [])"
proof -
  have "star (pstep (declared_global nv_prog) (prog_table nv_prog))
          (VIMP_Proc.com.Seq
             (VIMP_Proc.com.Seq (VIMP_Proc.com.Call (Some (STR ''a'')) (STR ''bump'') [N 5])
                (VIMP_Proc.com.Call (Some (STR ''b'')) (STR ''bump'') [N 4]))
             (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6))), \<lambda>_. 0, [])
          (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6)), nv_final, [])"
    using psteps_Seq2 [OF nv_calls] by (meson Seq1 star.step star.refl star_trans)
  then show ?thesis unfolding nv_main by (rule psteps_Seq2)
qed

lemma nv_solve_c:
  "TD_side_rule_Interp_solve_c Globals_Warrow
     (interval_es_rule.equations (declared_global nv_prog) nv_prog)
     (interval_es_rule.root_query nv_prog) \<noteq> None"
  unfolding interval_es_rule.root_query_def by eval

lemma nv_terminates:
  "config_terminates Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog"
  by (simp add: interval_es_rule.terminates_of_solve_c [OF nv_solve_c])

subsection \<open>The endpoints, instantiated\<close>

theorem nv_source_certified:
  "\<exists>res v stk.
     run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog
       = Analysed res
   \<and> map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res)
       = [(Statement 4, Decided Check_Proved),
          (Statement 5, Decided Check_Proved)]
   \<and> csim (prog_table nv_prog) (prog_cfg nv_prog)
       (VIMP_Proc.com.Seq
          (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6)))
          (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''b'')) (N 5))),
        nv_final, [])
       (v, nv_final, stk)
   \<and> nv_final \<in> ltr_collect (declared_global nv_prog) (prog_cfg nv_prog)
                   (cinit_stores (declared_global nv_prog)) v
   \<and> analysis_result_covers
       Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog v nv_final
   \<and> checks_sound_at res v nv_final"
proof -
  obtain res where ans: "run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog
                           = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res)
                   = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
    by (rule nv_analysed)
  from run_voblint_certified_source_sound [OF nv_init nv_to_check nv_terminates ans]
  show ?thesis using ans checks by meson
qed

text \<open>
  Read at the check: the store the run holds there reaches a listed check for
  \<open>a == 6\<close>, that check says \<^const>\<open>Check_Proved\<close>, and the condition holds.
\<close>

theorem nv_check_proved_sound:
  "\<exists>res. run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog = Analysed res
     \<and> (\<exists>chk \<in> set (res_checks res). check_exp chk = Eq (V (STR ''a'')) (N 6)
          \<and> nv_final \<in> ltr_collect (declared_global nv_prog) (prog_cfg nv_prog)
                          (cinit_stores (declared_global nv_prog)) (check_point chk)
          \<and> check_verdict chk = Decided Check_Proved
          \<and> truthy (aval (Eq (V (STR ''a'')) (N 6)) nv_final))"
proof -
  obtain res where ans: "run_voblint Interval_Analysis Globals_Warrow Ctx_EntryState nv_prog
                           = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_verdict chk)) (res_checks res)
                   = [(Statement 4, Decided Check_Proved), (Statement 5, Decided Check_Proved)]"
    by (rule nv_analysed)
  have nc: "next_check (VIMP_Proc.com.Seq (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''a'')) (N 6)))
              (VIMP_Proc.com.Check (0, 0) (Eq (V (STR ''b'')) (N 5)))) = Some ((0, 0), Eq (V (STR ''a'')) (N 6))"
    by simp
  from run_voblint_check_sound [OF nv_init nv_to_check nc nv_terminates ans]
  obtain chk
    where listed: "chk \<in> set (res_checks res)"
      and re: "check_exp chk = Eq (V (STR ''a'')) (N 6)"
      and mem: "nv_final \<in> ltr_collect (declared_global nv_prog) (prog_cfg nv_prog)
                              (cinit_stores (declared_global nv_prog)) (check_point chk)"
      and pr: "check_verdict chk = Decided Check_Proved
                 \<longrightarrow> truthy (aval (Eq (V (STR ''a'')) (N 6)) nv_final)"
    by auto
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

lemma nv_dead_report:
  "(case run_voblint Interval_Analysis Globals_Join Ctx_None nv_dead_prog of
      Analysed res \<Rightarrow>
        map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = [(Statement 1, Eq (V (STR ''x'')) (N 0), Decided Check_Refuted),
             (Statement 3, Eq (V (STR ''x'')) (N 5), Dead)]
    | _ \<Rightarrow> False)"
  by eval

lemma nv_dead_analysed:
  obtains res where
    "run_voblint Interval_Analysis Globals_Join Ctx_None nv_dead_prog = Analysed res"
    "map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
       = [(Statement 1, Eq (V (STR ''x'')) (N 0), Decided Check_Refuted),
          (Statement 3, Eq (V (STR ''x'')) (N 5), Dead)]"
  using nv_dead_report
  by (cases "run_voblint Interval_Analysis Globals_Join Ctx_None nv_dead_prog") auto

lemma nv_dead_terminates:
  "config_terminates Interval_Analysis Globals_Join Ctx_None nv_dead_prog"
  by (simp, rule interval_rule.terminates_of_solve_c)
     (simp only: interval_rule.root_query_def, eval)

theorem nv_dead_unreached:
  "ltr_collect (declared_global nv_dead_prog) (prog_cfg nv_dead_prog)
     (cinit_stores (declared_global nv_dead_prog)) (Statement 3) = {}"
proof -
  obtain res where ans: "run_voblint Interval_Analysis Globals_Join Ctx_None nv_dead_prog
                           = Analysed res"
    and checks: "map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
                   = [(Statement 1, Eq (V (STR ''x'')) (N 0), Decided Check_Refuted),
                      (Statement 3, Eq (V (STR ''x'')) (N 5), Dead)]"
    by (rule nv_dead_analysed)
  then obtain chk where "chk \<in> set (res_checks res)" "check_point chk = Statement 3"
      "check_verdict chk = Dead"
    by (cases "res_checks res" rule: remdups_adj.cases) auto
  with run_voblint_dead_check_unreached [OF nv_dead_terminates ans] show ?thesis by metis
qed

section \<open>Load-bearing conditions\<close>

subsection \<open>Soundness alone is cheap\<close>

text \<open>
  \<^const>\<open>checks_sound_at\<close> constrains only decided and dead verdicts, so a result
  that answers \<^const>\<open>Check_Unknown\<close> at every check meets it at every node and
  store. The endpoint is informative because the verdicts \<^const>\<open>run_voblint\<close>
  actually returns above are \<^const>\<open>Check_Proved\<close> and \<^const>\<open>Dead\<close>.
\<close>

definition answer_all :: "contextual_verdict \<Rightarrow> 'v run_result \<Rightarrow> 'v run_result" where
  "answer_all vd res =
     res\<lparr>res_checks := map (\<lambda>chk. chk\<lparr>check_verdict := vd\<rparr>) (res_checks res)\<rparr>"

lemma unknown_everywhere_sound:
  "checks_sound_at (answer_all (Decided Check_Unknown) res) v s"
  by (auto simp: checks_sound_at_def answer_all_def)

text \<open>
  An answer of \<^const>\<open>Check_Proved\<close> everywhere is not sound: the store after
  \<open>x = 1\<close> reaches the check \<open>x == 0\<close>, which it falsifies.
\<close>

lemma nv_dead_reaches_first_check:
  "(\<lambda>_. 0)(STR ''x'' := 1)
     \<in> ltr_collect (declared_global nv_dead_prog) (prog_cfg nv_dead_prog)
         (cinit_stores (declared_global nv_dead_prog)) (Statement 1)"
proof -
  have intra: "intra (prog_cfg nv_dead_prog) =
     {(FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 0),
      (Statement 5, EA_Ret None (STR ''main''), FunctionResult (STR ''main'')),
      (Statement 1, EA_Check (0, 0) (Eq (V (STR ''x'')) (N 0)), Statement 2),
      (Statement 0, EA_Assign (STR ''x'') (N 1), Statement 1),
      (Statement 3, EA_Check (0, 0) (Eq (V (STR ''x'')) (N 5)), Statement 5),
      (Statement 2, EA_Assume (Less (V (STR ''x'')) (N 0)), Statement 3),
      (Statement 2, EA_AssumeNot (Less (V (STR ''x'')) (N 0)), Statement 4),
      (Statement 4, EA_Assign (STR ''x'') (N 2), Statement 5)}"
    unfolding prog_cfg_def by eval
  have entry: "cfg_entry (prog_cfg nv_dead_prog) = FunctionEntry (STR ''main'')"
    by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)
  have e0: "(\<lambda>_. 0) \<in> ltr_collect (declared_global nv_dead_prog) (prog_cfg nv_dead_prog)
              (cinit_stores (declared_global nv_dead_prog)) (FunctionEntry (STR ''main''))"
    using ltr_collect_init [of "\<lambda>_. 0" "cinit_stores (declared_global nv_dead_prog)"
                               "declared_global nv_dead_prog" "prog_cfg nv_dead_prog"]
    by (simp add: entry cinit_stores_def)
  have s0: "(\<lambda>_. 0) \<in> ltr_collect (declared_global nv_dead_prog) (prog_cfg nv_dead_prog)
              (cinit_stores (declared_global nv_dead_prog)) (Statement 0)"
    by (rule ltr_collect_intra_step [OF e0, where a = "EA_Body (STR ''main'')"])
       (auto simp: intra)
  show ?thesis
    by (rule ltr_collect_intra_step [OF s0, where a = "EA_Assign (STR ''x'') (N 1)"])
       (auto simp: intra)
qed

theorem proved_everywhere_unsound:
  assumes "run_voblint Interval_Analysis Globals_Join Ctx_None nv_dead_prog = Analysed res"
  shows "\<not> checks_sound_at (answer_all (Decided Check_Proved) res) (Statement 1)
                           ((\<lambda>_. 0)(STR ''x'' := 1))"
proof -
  from nv_dead_report assms
  have "map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (res_checks res)
          = [(Statement 1, Eq (V (STR ''x'')) (N 0), Decided Check_Refuted),
             (Statement 3, Eq (V (STR ''x'')) (N 5), Dead)]"
    by simp
  then obtain chk where "chk \<in> set (res_checks res)" "check_point chk = Statement 1"
      "check_exp chk = Eq (V (STR ''x'')) (N 0)"
    by (cases "res_checks res" rule: remdups_adj.cases) auto
  then show ?thesis
    by (auto simp: checks_sound_at_def answer_all_def)
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

definition ret_prog :: imp_prog where
  "ret_prog = program {
     fun f(n) { return n; }
     fun main() { a = f(1); b = f(5); }
   }"

lemma ret_intra:
  "intra (prog_cfg ret_prog) =
     {(FunctionEntry (STR ''f''), EA_Body (STR ''f''), Statement 0),
      (Statement 0, EA_Ret (Some (V (STR ''n''))) (STR ''f''), FunctionResult (STR ''f'')),
      (FunctionEntry (STR ''main''), EA_Body (STR ''main''), Statement 2),
      (Statement 4, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))}"
  unfolding prog_cfg_def by eval

lemma ret_calls:
  "calls (prog_cfg ret_prog) =
     {(Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1], FunctionEntry (STR ''f''),
       Statement 3),
      (Statement 3, CallEdge (Some (STR ''b'')) [STR ''n''] [N 5], FunctionEntry (STR ''f''),
       Statement 4)}"
  unfolding prog_cfg_def by eval

lemma ret_entry: "cfg_entry (prog_cfg ret_prog) = FunctionEntry (STR ''main'')"
  by (simp only: prog_cfg_def cfg_entry_compile_prog prog_main_name_def)

lemma ret_no_globals: "declared_global ret_prog = (\<lambda>_. False)"
  by (simp add: ret_prog_def fun_eq_iff)

lemma ret_enter:
  "call_enter (declared_global ret_prog) (CallEdge dst [STR ''n''] [e]) s
     = (\<lambda>_. 0)(STR ''n'' := aval e s)"
  by (simp add: ret_no_globals call_enter_CallEdge enter_binding_def enter_frame_def fun_eq_iff)

text \<open>The policy of the illustration: the callee context is the entry value of \<open>n\<close>.\<close>

definition ret_R :: "int call_context_rel" where
  "ret_R = call_context_rel_of_fun (\<lambda>_ _ es. es (STR ''n''))"

text \<open>
  The claim: \<open>main\<close> is covered in the start context \<open>0\<close> up to its first call site
  and nowhere after it; \<open>f\<close> is covered everywhere, but only in the contexts its
  calls create.
\<close>

definition ret_cover :: "cfg_node \<Rightarrow> int \<Rightarrow> store set" where
  "ret_cover v ctx =
     (if v \<in> {FunctionEntry (STR ''f''), Statement 0, FunctionResult (STR ''f'')}
      then (if ctx = 0 then {} else UNIV)
      else if ctx = 0 \<and> v \<in> {FunctionEntry (STR ''main''), Statement 2} then UNIV else {})"

lemma ret_weak_obligations:
  shows "\<forall>s. s \<in> cinit_stores (declared_global ret_prog)
              \<longrightarrow> s \<in> ret_cover (cfg_entry (prog_cfg ret_prog)) 0"
    and "\<forall>u a v c s s'. (u, a, v) \<in> intra (prog_cfg ret_prog) \<longrightarrow> s \<in> ret_cover u c
              \<longrightarrow> s' \<in> edge_step a s \<longrightarrow> s' \<in> ret_cover v c"
    and "\<forall>u dst pars args p cont c c' s.
              (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (prog_cfg ret_prog)
              \<longrightarrow> s \<in> ret_cover u c
              \<longrightarrow> ret_R u c (call_info_of (CallEdge dst pars args) p) s
                    (call_enter (declared_global ret_prog) (CallEdge dst pars args) s) c'
              \<longrightarrow> call_enter (declared_global ret_prog) (CallEdge dst pars args) s
                    \<in> ret_cover (FunctionEntry p) c'"
    and "\<forall>cl dst pars args p cont c1 s t.
              (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (prog_cfg ret_prog)
              \<longrightarrow> s \<in> ret_cover cl c1 \<longrightarrow> t \<in> ret_cover (FunctionResult p) c1
              \<longrightarrow> combine_collect (declared_global ret_prog) dst s t \<in> ret_cover cont c1"
    and "call_context_total_on ret_cover ret_R (declared_global ret_prog) (prog_cfg ret_prog)"
  by (auto simp: ret_entry ret_intra ret_calls ret_cover_def ret_R_def ret_enter
                 call_context_total_on_def)

lemma ret_not_coverage:
  "\<not> ltr_coverage (prog_cfg ret_prog) (cinit_stores (declared_global ret_prog)) ret_cover
       ret_R 0 (declared_global ret_prog)"
proof
  assume "ltr_coverage (prog_cfg ret_prog) (cinit_stores (declared_global ret_prog)) ret_cover
            ret_R 0 (declared_global ret_prog)"
  then interpret C: ltr_coverage "prog_cfg ret_prog" "cinit_stores (declared_global ret_prog)"
      ret_cover ret_R 0 "declared_global ret_prog" .
  have e: "(Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1], FunctionEntry (STR ''f''),
             Statement 3) \<in> calls (prog_cfg ret_prog)"
    by (simp add: ret_calls)
  have adm: "admits_call_context (declared_global ret_prog) (prog_cfg ret_prog) ret_R
               (Statement 2) 0 (STR ''f'') (\<lambda>_. 0)
               (call_enter (declared_global ret_prog)
                  (CallEdge (Some (STR ''a'')) [STR ''n''] [N 1]) (\<lambda>_. 0)) 1"
    unfolding admits_call_context_def
    by (rule exI [of _ "Some (STR ''a'')"], rule exI [of _ "[STR ''n'']"],
        rule exI [of _ "[N 1]"], rule exI [of _ "Statement 3"])
       (simp add: e ret_R_def ret_enter)
  have "combine_collect (declared_global ret_prog) (Some (STR ''a'')) (\<lambda>_. 0) (\<lambda>_. 0)
          \<in> ret_cover (Statement 3) 0"
    by (rule C.RETURN [OF e _ adm]) (simp_all add: ret_cover_def)
  then show False by (simp add: ret_cover_def)
qed

lemma ret_f_body:
  "intra_path (prog_cfg ret_prog)
     (FunctionEntry (STR ''f''), (\<lambda>_. 0)(STR ''n'' := k))
     (FunctionResult (STR ''f''), ((\<lambda>_. 0)(STR ''n'' := k))(ret_var := k))"
proof (rule star_trans)
  show "intra_path (prog_cfg ret_prog)
          (FunctionEntry (STR ''f''), (\<lambda>_. 0)(STR ''n'' := k))
          (Statement 0, (\<lambda>_. 0)(STR ''n'' := k))"
    by (rule intra_path_single [where a = "EA_Body (STR ''f'')"]) (auto simp: ret_intra)
next
  show "intra_path (prog_cfg ret_prog)
          (Statement 0, (\<lambda>_. 0)(STR ''n'' := k))
          (FunctionResult (STR ''f''), ((\<lambda>_. 0)(STR ''n'' := k))(ret_var := k))"
    by (rule intra_path_single [where a = "EA_Ret (Some (V (STR ''n''))) (STR ''f'')"])
       (auto simp: ret_intra)
qed

lemma ret_reaches_second_call:
  "(\<lambda>_. 0)(STR ''a'' := 1)
     \<in> ltr_collect (declared_global ret_prog) (prog_cfg ret_prog)
         (cinit_stores (declared_global ret_prog)) (Statement 3)"
proof -
  have e0: "(\<lambda>_. 0) \<in> ltr_collect (declared_global ret_prog) (prog_cfg ret_prog)
              (cinit_stores (declared_global ret_prog)) (FunctionEntry (STR ''main''))"
    using ltr_collect_init [of "\<lambda>_. 0" "cinit_stores (declared_global ret_prog)"
                               "declared_global ret_prog" "prog_cfg ret_prog"]
    by (simp add: ret_entry cinit_stores_def)
  have s2: "(\<lambda>_. 0) \<in> ltr_collect (declared_global ret_prog) (prog_cfg ret_prog)
              (cinit_stores (declared_global ret_prog)) (Statement 2)"
    by (rule ltr_collect_intra_step [OF e0, where a = "EA_Body (STR ''main'')"])
       (auto simp: ret_intra)
  have ce: "(Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1],
             FunctionEntry (STR ''f''), Statement 3) \<in> calls (prog_cfg ret_prog)"
    by (simp add: ret_calls)
  have bd: "intra_path (prog_cfg ret_prog)
              (FunctionEntry (STR ''f''),
               call_enter (declared_global ret_prog)
                 (CallEdge (Some (STR ''a'')) [STR ''n''] [N 1]) (\<lambda>_. 0))
              (FunctionResult (STR ''f''), ((\<lambda>_. 0)(STR ''n'' := 1))(ret_var := 1))"
    using ret_f_body [where k = 1] by (simp add: ret_enter)
  show ?thesis
    using ltr_collect_call_return_step [OF s2 ce bd]
    by (simp add: ret_no_globals combine_collect_def combine_env_def ret_var_def fun_eq_iff)
qed

text \<open>
  Reading the callee at the caller's own context: the claim meets INIT, INTRA,
  CALL, the weakened RETURN and TOTAL, yet it covers no store at the second call
  site in any context, although a concrete trace reaches it. So \<open>b = f(5)\<close> is
  declared unreachable.
\<close>

theorem return_at_caller_context_unsound:
  "(\<lambda>_. 0)(STR ''a'' := 1)
     \<in> ltr_collect (declared_global ret_prog) (prog_cfg ret_prog)
         (cinit_stores (declared_global ret_prog)) (Statement 3)
   \<and> (\<Union>c. ret_cover (Statement 3) c) = {}"
  using ret_reaches_second_call by (simp add: ret_cover_def)

subsection \<open>TOTAL is load-bearing\<close>

text \<open>
  A resumed caller carries its own context whatever its callee carries, so the
  continuation of a call is collected in the caller's bucket even when the relation
  admits no callee context. Such a relation makes CALL and RETURN vacuous.
\<close>

lemma resume_keeps_context:
  assumes s: "s \<in> activation_collect \<G> R c0 g S u ctx"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls g"
    and body: "intra_path g (FunctionEntry q, call_enter \<G> (CallEdge dst pars args) s)
                 (FunctionResult q, t)"
  shows "combine_collect \<G> dst s t \<in> activation_collect \<G> R c0 g S cont ctx"
proof -
  from s obtain caller where cv: "caller \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
    and cn: "sink_node caller = u" and ck: "trace_context \<G> R c0 g caller ctx"
    and cs: "sink_store caller = s"
    by (rule activation_collect_E)
  let ?entered = "Call caller [(FunctionEntry q, call_enter \<G> (CallEdge dst pars args) s)]"
  have ev: "?entered \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
    using valid_ltr.call [OF cv, where dst = dst and pars = pars and args = args
                            and p = q and cont = cont]
      ce cn cs by simp
  obtain callee where dv: "callee \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
    and dn: "sink_node callee = FunctionResult q" and ds: "sink_store callee = t"
    and dc: "caller_of callee = caller_of ?entered"
    by (rule valid_ltr_intra_path_extend [OF _ ev]) (use body in simp_all)
  let ?r = "Resume caller callee
              (path caller @ [(cont, combine_collect \<G> dst (sink_store caller) (sink_store callee))])"
  have rv: "?r \<in> \<T>\<^bsub>\<G>,g,S\<^esub>"
    by (rule valid_ltr.ret [OF dv _ dn]) (use dc ce cn in simp_all)
  have "sink_store ?r \<in> activation_collect \<G> R c0 g S (sink_node ?r) ctx"
    by (rule activation_collect_I [OF rv refl]) (use ck in simp)
  then show ?thesis using cs ds by (simp add: sink_node_def sink_store_def)
qed

text \<open>The relation that admits no context, and the claim that covers \<open>main\<close> up to its first
  call site in the start context and nothing else.\<close>

definition tot_R :: "int call_context_rel" where
  "tot_R u ctx ci s es ctx' \<longleftrightarrow> False"

definition tot_cover :: "cfg_node \<Rightarrow> int \<Rightarrow> store set" where
  "tot_cover v ctx =
     (if ctx = 0 \<and> v \<in> {FunctionEntry (STR ''main''), Statement 2} then UNIV else {})"

lemma tot_weak_obligations:
  shows "\<forall>s. s \<in> cinit_stores (declared_global ret_prog)
              \<longrightarrow> s \<in> tot_cover (cfg_entry (prog_cfg ret_prog)) 0"
    and "\<forall>u a v c s s'. (u, a, v) \<in> intra (prog_cfg ret_prog) \<longrightarrow> s \<in> tot_cover u c
              \<longrightarrow> s' \<in> edge_step a s \<longrightarrow> s' \<in> tot_cover v c"
    and "\<forall>u dst pars args p cont c c' s.
              (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (prog_cfg ret_prog)
              \<longrightarrow> s \<in> tot_cover u c
              \<longrightarrow> tot_R u c (call_info_of (CallEdge dst pars args) p) s
                    (call_enter (declared_global ret_prog) (CallEdge dst pars args) s) c'
              \<longrightarrow> call_enter (declared_global ret_prog) (CallEdge dst pars args) s
                    \<in> tot_cover (FunctionEntry p) c'"
    and "\<forall>cl dst pars args p cont c1 c' p' s t es.
              (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (prog_cfg ret_prog)
              \<longrightarrow> s \<in> tot_cover cl c1
              \<longrightarrow> admits_call_context (declared_global ret_prog) (prog_cfg ret_prog) tot_R
                    cl c1 p' s es c'
              \<longrightarrow> t \<in> tot_cover (FunctionResult p) c'
              \<longrightarrow> combine_collect (declared_global ret_prog) dst s t \<in> tot_cover cont c1"
    and "\<not> call_context_total_on tot_cover tot_R (declared_global ret_prog) (prog_cfg ret_prog)"
  by (auto simp: ret_entry ret_intra ret_calls tot_cover_def tot_R_def admits_call_context_def
                 call_context_total_on_def)

text \<open>
  The claim meets INIT, INTRA, CALL and RETURN and fails only TOTAL. The run resumes at
  the second call site in the start context, where the claim is empty, so the
  per-context conclusion of \<open>activation_collect_sound\<close> fails.
\<close>

theorem total_dropped_unsound:
  "(\<lambda>_. 0)(STR ''a'' := 1)
     \<in> activation_collect (declared_global ret_prog) tot_R 0 (prog_cfg ret_prog)
         (cinit_stores (declared_global ret_prog)) (Statement 3) 0
   \<and> (\<lambda>_. 0)(STR ''a'' := 1) \<notin> tot_cover (Statement 3) 0"
proof
  let ?S = "cinit_stores (declared_global ret_prog)"
  let ?t0 = "Root [(FunctionEntry (STR ''main''), \<lambda>_. 0)]"
  have v0: "?t0 \<in> \<T>\<^bsub>declared_global ret_prog,prog_cfg ret_prog,?S\<^esub>"
    using valid_ltr.init [where s = "\<lambda>_. 0" and S = ?S and \<G> = "declared_global ret_prog"
                                and g = "prog_cfg ret_prog"]
    by (simp add: ret_entry cinit_stores_def)
  have v1: "Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)]
              \<in> \<T>\<^bsub>declared_global ret_prog,prog_cfg ret_prog,?S\<^esub>"
    using valid_ltr.intra [OF v0, where a = "EA_Body (STR ''main'')" and v = "Statement 2"
                                  and s' = "\<lambda>_. 0"]
    by (simp add: ret_intra sink_node_def sink_store_def)
  have s2: "(\<lambda>_. 0) \<in> activation_collect (declared_global ret_prog) tot_R 0 (prog_cfg ret_prog)
              ?S (Statement 2) 0"
  proof -
    have "sink_store (Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)])
            \<in> activation_collect (declared_global ret_prog) tot_R 0 (prog_cfg ret_prog) ?S
                (sink_node (Root [(FunctionEntry (STR ''main''), \<lambda>_. 0), (Statement 2, \<lambda>_. 0)])) 0"
      by (rule activation_collect_I [OF v1 refl]) simp
    then show ?thesis by (simp add: sink_node_def sink_store_def)
  qed
  have ce: "(Statement 2, CallEdge (Some (STR ''a'')) [STR ''n''] [N 1],
             FunctionEntry (STR ''f''), Statement 3) \<in> calls (prog_cfg ret_prog)"
    by (simp add: ret_calls)
  have bd: "intra_path (prog_cfg ret_prog)
              (FunctionEntry (STR ''f''),
               call_enter (declared_global ret_prog)
                 (CallEdge (Some (STR ''a'')) [STR ''n''] [N 1]) (\<lambda>_. 0))
              (FunctionResult (STR ''f''), ((\<lambda>_. 0)(STR ''n'' := 1))(ret_var := 1))"
    using ret_f_body [where k = 1] by (simp add: ret_enter)
  show "(\<lambda>_. 0)(STR ''a'' := 1)
          \<in> activation_collect (declared_global ret_prog) tot_R 0 (prog_cfg ret_prog)
              ?S (Statement 3) 0"
    using resume_keeps_context [OF s2 ce bd]
    by (simp add: ret_no_globals combine_collect_def combine_env_def ret_var_def fun_eq_iff)
  show "(\<lambda>_. 0)(STR ''a'' := 1) \<notin> tot_cover (Statement 3) 0"
    by (simp add: tot_cover_def)
qed

subsection \<open>Entry coverage must be paired\<close>

text \<open>
  \<open>y = p(x)\<close> with \<open>fun p(a) { return a; }\<close> and \<open>x = 1\<close>. Abstract values are
  represented by their concretizations, so \<^const>\<open>entry_pairs_cover\<close> is taken at
  \<^const>\<open>id\<close>. The answer \<open>[(x > 0, a < 0), (\<bottom>, a > 0)]\<close> covers the caller store
  with its first pair and the entered store with its second. Each pair's callee
  result, \<open>a\<close> published as the return value, is combined with that pair's own
  continuation; the union excludes the run's \<open>y = 1\<close>.
\<close>

definition unpaired_answer :: "(store set \<times> store set) list" where
  "unpaired_answer =
     [({t. 0 < t (STR ''x'')}, {t. t (STR ''a'') < 0}), ({}, {t. 0 < t (STR ''a'')})]"

definition pairwise_contribution :: "(store set \<times> store set) list \<Rightarrow> store set" where
  "pairwise_contribution P =
     (\<Union>(q, e) \<in> set P.
        {combine_collect (\<lambda>_. False) (Some (STR ''y'')) s0 (t(ret_var := t (STR ''a'')))
         | s0 t. s0 \<in> q \<and> t \<in> e})"

theorem unpaired_entry_cover_unsound:
  defines "s \<equiv> (\<lambda>_. 0)(STR ''x'' := 1) :: store"
      and "s' \<equiv> (\<lambda>_. 0)(STR ''a'' := 1) :: store"
  shows "s' = call_enter (\<lambda>_. False) (CallEdge (Some (STR ''y'')) [STR ''a''] [V (STR ''x'')]) s"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s \<in> q)"
    and "(\<exists>(q, e) \<in> set unpaired_answer. s' \<in> e)"
    and "\<not> entry_pairs_cover id s s' unpaired_answer"
    and "\<forall>u \<in> pairwise_contribution unpaired_answer. u (STR ''y'') < 0"
    and "combine_collect (\<lambda>_. False) (Some (STR ''y'')) s (s'(ret_var := s' (STR ''a'')))
           (STR ''y'') = 1"
  by (auto simp: s_def s'_def unpaired_answer_def pairwise_contribution_def
                 entry_pairs_cover_def call_enter_CallEdge enter_binding_def enter_frame_def
                 combine_collect_def combine_env_def ret_var_def fun_eq_iff)

end

