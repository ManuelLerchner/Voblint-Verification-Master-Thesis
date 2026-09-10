theory Analysis_Run_Sound
  imports Analysis_Run
begin

section \<open>What a run of this analyser proves about a run of the program\<close>

text \<open>
  A context-free answer's check column is the dispatcher's own report. The two are
  not merely consistent: a decided row \<^emph>\<open>is\<close> an entry of \<^const>\<open>analyse\<close>, at the
  same point, the same condition and the same verdict.

  A \<^const>\<open>Bot\<close> row has no counterpart and needs none. It marks a check no
  execution reaches, where \<^const>\<open>analyse\<close> still prints whatever classifying the
  bottom state yields; the endpoint below matches only decided rows against that
  report, and rules out a \<^const>\<open>Bot\<close> row wherever a run can stand.
\<close>

lemma decided_flat_row_in_classify_checks:
  assumes "(v, cnd, Lifted res) \<in> set (flat_rows_of classify bot_state r p)"
  shows "(v, cnd, res)
           \<in> set (classify_checks (prog_cfg p)
                     (\<lambda>u. case lookup_context r u () of
                            Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st) classify)"
proof -
  from assms obtain u c r' unr st
    where mem: "(u, c, r', unr, st)
                  \<in> set (classify_checks_with_state (prog_cfg p)
                           (\<lambda>w. case lookup_context r w () of
                                  Bot \<Rightarrow> (True, bot_state) | Lifted s \<Rightarrow> (False, s))
                           (\<lambda>cn (_, s). classify cn s))"
      and eq: "(v, cnd, Lifted res) = (u, c, if unr then Bot else Lifted r')"
    unfolding flat_rows_of_def by auto
  from eq have "v = u" "cnd = c" "\<not> unr" "res = r'"
    by (auto split: if_splits)
  with mem
  have "(v, cnd, res)
          \<in> set (map (\<lambda>(u, c, r', _, _). (u, c, r'))
                   (classify_checks_with_state (prog_cfg p)
                      (\<lambda>w. case lookup_context r w () of
                             Bot \<Rightarrow> (True, bot_state) | Lifted s \<Rightarrow> (False, s))
                      (\<lambda>cn (_, s). classify cn s)))"
    by force
  moreover
  have eqm: "map (\<lambda>(u, c, r', _, _). (u, c, r'))
               (classify_checks_with_state (prog_cfg p)
                  (\<lambda>w. case lookup_context r w () of
                         Bot \<Rightarrow> (True, bot_state) | Lifted s \<Rightarrow> (False, s))
                  (\<lambda>cn (_, s). classify cn s))
             = classify_checks (prog_cfg p)
                 (\<lambda>u. case lookup_context r u () of
                        Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st) classify"
    using map_classify_checks_with_state_flagged [where h = id] by (simp add: comp_def)
  ultimately show ?thesis unfolding eqm [symmetric] by simp
qed

lemma dead_flat_row_lookup_bot:
  assumes "(v, cnd, Bot) \<in> set (flat_rows_of classify bot_state r p)"
  shows "lookup_context r v () = Bot"
proof -
  from assms obtain u c r' unr st
    where mem: "(u, c, r', unr, st)
                  \<in> set (classify_checks_with_state (prog_cfg p)
                           (\<lambda>w. case lookup_context r w () of
                                  Bot \<Rightarrow> (True, bot_state) | Lifted s \<Rightarrow> (False, s))
                           (\<lambda>cn (_, s). classify cn s))"
      and eq: "(v, cnd, Bot) = (u, c, if unr then Bot else Lifted r')"
    unfolding flat_rows_of_def by auto
  from eq have vu: "v = u" and unr: "unr"
    by (auto split: if_splits)
  from mem have flag: "(unr, st) = (case lookup_context r u () of
                                      Bot \<Rightarrow> (True, bot_state) | Lifted s \<Rightarrow> (False, s))"
    unfolding classify_checks_with_state_def by auto
  show ?thesis
  proof (cases "lookup_context r u ()")
    case Bot
    with vu show ?thesis by simp
  next
    case (Lifted s)
    with flag unr show ?thesis by simp
  qed
qed

lemma decided_row_of_check_rows:
  assumes "row \<in> set (check_rows_of env rows)"
      and "row_verdict row = Lifted res"
  shows "(row_point row, row_exp row, Lifted res) \<in> set rows"
  using assms by (auto simp: check_rows_of_def)

lemma dead_row_of_check_rows:
  assumes "row \<in> set (check_rows_of env rows)"
      and "row_verdict row = Bot"
  shows "(row_point row, row_exp row, Bot) \<in> set rows"
  using assms by (auto simp: check_rows_of_def)

lemma out_checks_of_flat_output:
  assumes "flat_output_of view into classify bot_state r globals p = Analysed out"
  shows "out_checks out
           = check_rows_of (project_env into r) (flat_rows_of classify bot_state r p)"
  using assms
  by (cases view)
     (auto simp: flat_output_of_def collapsed_output_def report_output_def Let_def)

text \<open>
  Each context-free plan's check column, in the vocabulary \<^const>\<open>analyse\<close> speaks.
  The two are the same \<^const>\<open>classify_checks\<close> call over the same table, so this is
  an unfolding rather than an agreement --- which is what makes it worth having:
  five tables are named by hand in \<^const>\<open>plan_answer\<close>, and a branch reading a
  neighbouring one would still typecheck and still print.
\<close>

lemma analyse_eq_classify_checks:
  "analyse Sign_Analysis p
     = classify_checks (prog_cfg p)
         (\<lambda>u. case lookup_context (analyse_sign_result p) u () of
                Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) sign_classify_check"
  "analyse Interval_Analysis p
     = classify_checks (prog_cfg p)
         (\<lambda>u. case lookup_context (analyse_interval_result p) u () of
                Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) interval_classify_check"
  "analyse Int_Analysis p
     = classify_checks (prog_cfg p)
         (\<lambda>u. case lookup_context (analyse_int_result p) u () of
                Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) int_classify_check"
  "analyse Parity_Analysis p
     = classify_checks (prog_cfg p)
         (\<lambda>u. case lookup_context (analyse_parity_result p) u () of
                Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) parity_classify_check"
  "analyse Congruence_Analysis p
     = classify_checks (prog_cfg p)
         (\<lambda>u. case lookup_context (analyse_congruence_result p) u () of
                Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) congruence_classify_check"
  by (simp_all add: surface_unfold
        analyse_sign_report_def analyse_sign_report_for_def
        analyse_sign_result_def analyse_sign_result_for_def sign_join.report_def
        analyse_interval_report_def analyse_interval_report_for_def
        analyse_interval_result_def analyse_interval_result_for_def
        interval_warrow_asm.report_def
        analyse_int_report_def analyse_int_report_for_def
        analyse_int_result_def analyse_int_result_for_def
        analyse_parity_report_def analyse_parity_report_for_def
        analyse_parity_result_def analyse_parity_result_for_def parity_join.report_def
        analyse_congruence_report_def analyse_congruence_report_for_def
        analyse_congruence_result_def analyse_congruence_result_for_def
        congruence_join.report_def)

lemma decided_row_in_analyse:
  assumes ans: "run_voblint D None Ctx_None view p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dec: "row_verdict row = Lifted res"
  shows "(row_point row, row_exp row, res) \<in> set (analyse D p)"
proof (cases D)
  case Sign_Analysis
  obtain r gvs where sol: "analyse_sign_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_sign_result p"
    by (metis analyse_sign_result_def fst_analyse_sign_ctx_solved_for fst_conv)
  from ans Sign_Analysis
  have "flat_output_of view SignValue sign_classify_check bot r
          (rendered_globals SignValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dec r
  have "(row_point row, row_exp row, Lifted res)
          \<in> set (flat_rows_of sign_classify_check bot (analyse_sign_result p) p)"
    by (simp add: decided_row_of_check_rows)
  from decided_flat_row_in_classify_checks [OF this]
  show ?thesis unfolding Sign_Analysis analyse_eq_classify_checks(1) .
next
  case Interval_Analysis
  obtain r gvs where sol: "analyse_interval_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_interval_result p"
    by (metis analyse_interval_result_def fst_analyse_interval_ctx_solved_for fst_conv)
  from ans Interval_Analysis
  have "flat_output_of view IntervalValue interval_classify_check bot r
          (rendered_globals IntervalValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dec r
  have "(row_point row, row_exp row, Lifted res)
          \<in> set (flat_rows_of interval_classify_check bot (analyse_interval_result p) p)"
    by (simp add: decided_row_of_check_rows)
  from decided_flat_row_in_classify_checks [OF this]
  show ?thesis unfolding Interval_Analysis analyse_eq_classify_checks(2) .
next
  case Int_Analysis
  obtain r gvs
    where sol: "analyse_int_ctx_solved_warrow_for Refine_Fixpoint (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_int_result p"
    by (metis analyse_int_result_def analyse_int_result_for_def
        fst_analyse_int_ctx_solved_warrow_for fst_conv)
  from ans Int_Analysis
  have "flat_output_of view IntDomValue int_classify_check bot r
          (rendered_globals IntDomValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dec r
  have "(row_point row, row_exp row, Lifted res)
          \<in> set (flat_rows_of int_classify_check bot (analyse_int_result p) p)"
    by (simp add: decided_row_of_check_rows)
  from decided_flat_row_in_classify_checks [OF this]
  show ?thesis unfolding Int_Analysis analyse_eq_classify_checks(3) .
next
  case Parity_Analysis
  obtain r gvs where sol: "analyse_parity_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_parity_result p"
    by (metis analyse_parity_result_def fst_analyse_parity_ctx_solved_for fst_conv)
  from ans Parity_Analysis
  have "flat_output_of view ParityValue parity_classify_check bot r
          (rendered_globals ParityValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dec r
  have "(row_point row, row_exp row, Lifted res)
          \<in> set (flat_rows_of parity_classify_check bot (analyse_parity_result p) p)"
    by (simp add: decided_row_of_check_rows)
  from decided_flat_row_in_classify_checks [OF this]
  show ?thesis unfolding Parity_Analysis analyse_eq_classify_checks(4) .
next
  case Congruence_Analysis
  obtain r gvs where sol: "analyse_congruence_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_congruence_result p"
    by (metis analyse_congruence_result_def fst_analyse_congruence_ctx_solved_for fst_conv)
  from ans Congruence_Analysis
  have "flat_output_of view CongruenceValue congruence_classify_check bot r
          (rendered_globals CongruenceValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dec r
  have "(row_point row, row_exp row, Lifted res)
          \<in> set (flat_rows_of congruence_classify_check bot (analyse_congruence_result p) p)"
    by (simp add: decided_row_of_check_rows)
  from decided_flat_row_in_classify_checks [OF this]
  show ?thesis unfolding Congruence_Analysis analyse_eq_classify_checks(5) .
qed

text \<open>
  The other half: a row the answer marks dead is at a node whose solved entry is
  \<^const>\<open>Bot\<close>, and the concretization of the bottom state is empty. So no store the
  analysis covers at that node exists --- which is what makes the analyser's
  unreachability claims sound, rather than merely unrefuted.
\<close>

lemma dead_row_not_covered:
  assumes ans: "run_voblint D None Ctx_None view p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dead: "row_verdict row = Bot"
  shows "\<not> analyse_state_covers D p (row_point row) s"
proof (cases D)
  case Sign_Analysis
  obtain r gvs where sol: "analyse_sign_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_sign_result p"
    by (metis analyse_sign_result_def fst_analyse_sign_ctx_solved_for fst_conv)
  from ans Sign_Analysis
  have "flat_output_of view SignValue sign_classify_check bot r
          (rendered_globals SignValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dead r
  have "(row_point row, row_exp row, Bot)
          \<in> set (flat_rows_of sign_classify_check bot (analyse_sign_result p) p)"
    by (simp add: dead_row_of_check_rows)
  from dead_flat_row_lookup_bot [OF this]
  show ?thesis unfolding Sign_Analysis by simp
next
  case Interval_Analysis
  obtain r gvs where sol: "analyse_interval_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_interval_result p"
    by (metis analyse_interval_result_def fst_analyse_interval_ctx_solved_for fst_conv)
  from ans Interval_Analysis
  have "flat_output_of view IntervalValue interval_classify_check bot r
          (rendered_globals IntervalValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dead r
  have "(row_point row, row_exp row, Bot)
          \<in> set (flat_rows_of interval_classify_check bot (analyse_interval_result p) p)"
    by (simp add: dead_row_of_check_rows)
  from dead_flat_row_lookup_bot [OF this]
  show ?thesis unfolding Interval_Analysis by simp
next
  case Int_Analysis
  obtain r gvs
    where sol: "analyse_int_ctx_solved_warrow_for Refine_Fixpoint (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_int_result p"
    by (metis analyse_int_result_def analyse_int_result_for_def
        fst_analyse_int_ctx_solved_warrow_for fst_conv)
  from ans Int_Analysis
  have "flat_output_of view IntDomValue int_classify_check bot r
          (rendered_globals IntDomValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dead r
  have "(row_point row, row_exp row, Bot)
          \<in> set (flat_rows_of int_classify_check bot (analyse_int_result p) p)"
    by (simp add: dead_row_of_check_rows)
  from dead_flat_row_lookup_bot [OF this]
  show ?thesis unfolding Int_Analysis by simp
next
  case Parity_Analysis
  obtain r gvs where sol: "analyse_parity_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_parity_result p"
    by (metis analyse_parity_result_def fst_analyse_parity_ctx_solved_for fst_conv)
  from ans Parity_Analysis
  have "flat_output_of view ParityValue parity_classify_check bot r
          (rendered_globals ParityValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dead r
  have "(row_point row, row_exp row, Bot)
          \<in> set (flat_rows_of parity_classify_check bot (analyse_parity_result p) p)"
    by (simp add: dead_row_of_check_rows)
  from dead_flat_row_lookup_bot [OF this]
  show ?thesis unfolding Parity_Analysis by simp
next
  case Congruence_Analysis
  obtain r gvs where sol: "analyse_congruence_ctx_solved_for (declared_global p) p = (r, gvs)"
    by fastforce
  then have r: "r = analyse_congruence_result p"
    by (metis analyse_congruence_result_def fst_analyse_congruence_ctx_solved_for fst_conv)
  from ans Congruence_Analysis
  have "flat_output_of view CongruenceValue congruence_classify_check bot r
          (rendered_globals CongruenceValue (program_vars p) gvs) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def sol split: if_splits)
  from out_checks_of_flat_output [OF this] row dead r
  have "(row_point row, row_exp row, Bot)
          \<in> set (flat_rows_of congruence_classify_check bot (analyse_congruence_result p) p)"
    by (simp add: dead_row_of_check_rows)
  from dead_flat_row_lookup_bot [OF this]
  show ?thesis unfolding Congruence_Analysis by simp
qed

text \<open>
  The endpoint, over the operation \<open>export_code\<close> exports.

  Compile the program, solve, take the answer --- then run the source program
  itself and stop wherever you like. Three things hold at once of the store in
  your hands. It sits at a graph node with a frame stack (\<^const>\<open>csim\<close>), so the
  run and the analysis are talking about the same place, with no separate
  reachability argument. The abstract state the analysis computed for that node
  contains it, which is over-approximation at the point where it can be checked.
  And every decided check the answer reports for that node holds of it: a
  \<^const>\<open>Check_Proved\<close> condition is true, a \<^const>\<open>Check_Refuted\<close> one false, and no
  row the analyser called dead is where you are standing.

  What the premises still ask for is worth reading as carefully as what they give.
  \<^const>\<open>analyse_certified\<close> is decided per program, not once and for all: it says
  the solver returned a partial post-solution \<^emph>\<open>for this program\<close> and that the
  solve covered enough keys. Nothing here proves the solver terminates on every
  input. Stated without those, this would be the definition-statement drift the
  autoformalization audit warns about.

  The configuration is context-free. The contextual plans are proved sound over
  \<^emph>\<open>activation-keyed\<close> collecting semantics, and carrying that to this shape needs
  transport steps that do not yet exist here; widening the statement to cover them
  would claim coverage the theory does not have.
\<close>

theorem run_voblint_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and ans: "run_voblint D None Ctx_None view p = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> analyse_state_covers D p v s
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from source_reaches_ltr_collect [OF wf s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  have covers: "analyse_state_covers D p v s"
    by (rule analyse_state_node_sound [OF wf cert mem])
  have rows: "\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
                (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
              \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
              \<and> row_verdict row \<noteq> Bot"
  proof (intro ballI impI conjI)
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
       and dv: "row_verdict row = Lifted Check_Proved"
    from decided_row_in_analyse [OF ans rm dv] at
    have "(v, row_exp row, Check_Proved) \<in> set (analyse D p)" by simp
    from analyse_proved_sound [OF wf cert this] mem
    show "truthy (aval (row_exp row) s)" by blast
  next
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
       and dv: "row_verdict row = Lifted Check_Refuted"
    from decided_row_in_analyse [OF ans rm dv] at
    have "(v, row_exp row, Check_Refuted) \<in> set (analyse D p)" by simp
    from analyse_refuted_sound [OF wf cert this] mem
    show "\<not> truthy (aval (row_exp row) s)" by blast
  next
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
    show "row_verdict row \<noteq> Bot"
    proof
      assume dead: "row_verdict row = Bot"
      have "\<not> analyse_state_covers D p v s"
        using dead_row_not_covered [OF ans rm dead] at by simp
      with covers show False by blast
    qed
  qed
  from m mem covers rows show ?thesis by blast
qed

subsection \<open>The endpoint over an arbitrary unit-context solve\<close>

text \<open>
  \<open>run_voblint_source_sound\<close> is stated over \<^const>\<open>analyse\<close>, so it reaches
  only the discipline each domain publishes as its default.  Naming a solver
  instead lands on a different solved table with the same shape, and this is
  what those configurations instantiate: everything but the solve is fixed
  here, and a caller owes the per-node bound its own discipline proves.

  What separates this from the contextual endpoint is the row builder, not the
  verdict type: \<open>contextual_verdict\<close> is a synonym for
  \<^typ>\<open>check_result lifted\<close>, and \<open>Dead\<close>/\<open>Decided\<close> abbreviate \<^const>\<open>Bot\<close> and
  \<^const>\<open>Lifted\<close>.  The unit route reads \<^const>\<open>flat_rows_of\<close>, one verdict per
  point off the table at the unit context; the contextual route reads
  \<^const>\<open>classify_checks_verdicts\<close>, an aggregate over the contexts a point was
  solved at.  The conclusion is the same shape as the dispatcher's, including
  the reachability witness that pins the node.
\<close>

theorem flat_source_sound_of_collect:
  fixes p :: imp_prog and s0 s :: store
    and r :: "(unit, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and cap: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                        (cinit_stores (declared_global p)) u
                  \<subseteq> \<lbrakk>case lookup_context r u () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                        \<Longrightarrow> \<not> truthy (aval c t)"
      and rows: "out_checks out = check_rows_of env (flat_rows_of classify bot r p)"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  from source_reaches_ltr_collect [OF wf s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  have rows_at: "\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
                   (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
                 \<and> (row_verdict row = Lifted Check_Refuted
                      \<longrightarrow> \<not> truthy (aval (row_exp row) s))
                 \<and> row_verdict row \<noteq> Bot"
  proof (intro ballI impI conjI)
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
       and dv: "row_verdict row = Lifted Check_Proved"
    from decided_row_of_check_rows [OF rm [unfolded rows] dv] at
    have flat: "(v, row_exp row, Lifted Check_Proved)
                  \<in> set (flat_rows_of classify bot r p)"
      by simp
    have "\<forall>t \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v. truthy (aval (row_exp row) t)"
      by (rule classify_checks_proved_sound
            [where gamma_state = "\<lambda>d :: 'a abs_state. \<lbrakk>d\<rbrakk>"
               and env = "\<lambda>u. case lookup_context r u () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
               and reach = "ltr_collect (declared_global p) (prog_cfg p)
                              (cinit_stores (declared_global p))"
               and v = v,
             OF finI decided_flat_row_in_classify_checks [OF flat] proved cap [of v]])
    then show "truthy (aval (row_exp row) s)" using mem by blast
  next
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
       and dv: "row_verdict row = Lifted Check_Refuted"
    from decided_row_of_check_rows [OF rm [unfolded rows] dv] at
    have flat: "(v, row_exp row, Lifted Check_Refuted)
                  \<in> set (flat_rows_of classify bot r p)"
      by simp
    have "\<forall>t \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v. \<not> truthy (aval (row_exp row) t)"
      by (rule classify_checks_refuted_sound
            [where gamma_state = "\<lambda>d :: 'a abs_state. \<lbrakk>d\<rbrakk>"
               and env = "\<lambda>u. case lookup_context r u () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
               and reach = "ltr_collect (declared_global p) (prog_cfg p)
                              (cinit_stores (declared_global p))"
               and v = v,
             OF finI decided_flat_row_in_classify_checks [OF flat] refuted cap [of v]])
    then show "\<not> truthy (aval (row_exp row) s)" using mem by blast
  next
    fix row
    assume rm: "row \<in> set (out_checks out)" and at: "row_point row = v"
    show "row_verdict row \<noteq> Bot"
    proof
      assume dead: "row_verdict row = Bot"
      from dead_row_of_check_rows [OF rm [unfolded rows] dead] at
      have "(v, row_exp row, Bot) \<in> set (flat_rows_of classify bot r p)" by simp
      from dead_flat_row_lookup_bot [OF this] cap [of v] mem
      show False by simp
    qed
  qed
  from m mem rows_at show ?thesis by blast
qed

subsection \<open>Sign at an explicitly chosen per-origin discipline\<close>

text \<open>
  The first unit configuration reached by naming a solver.  Its registration is
  a \<^theory_text>\<open>global_interpretation\<close> of \<open>unit_dg_analysis\<close>, so the per-node
  bound comes from that locale's own two-premise endpoint and the endpoint above
  consumes it unchanged.
\<close>

theorem run_voblint_sign_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "sign_po_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (sign_po_vars (declared_global p) p)"
      and ans: "run_voblint Sign_Analysis (Some Solver_PerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view SignValue sign_classify_check bot
          (analyse_sign_result_per_origin p)
          (unit_seed_globals SignValue (analyse_sign_result_per_origin p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ sign_classify_check_proved sign_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_per_origin p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using sign_po_asm.result_node_sound [OF solves cover, of u]
      by (simp add: sign_po_asm.state_at_unfold analyse_sign_result_per_origin_def
          analyse_sign_result_per_origin_for_def)
  qed
qed

theorem run_voblint_parity_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "parity_po_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (parity_po_vars (declared_global p) p)"
      and ans: "run_voblint Parity_Analysis (Some Solver_PerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view ParityValue parity_classify_check bot
          (analyse_parity_result_per_origin p)
          (unit_seed_globals ParityValue (analyse_parity_result_per_origin p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ parity_classify_check_proved parity_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_parity_result_per_origin p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using parity_po_asm.result_node_sound [OF solves cover, of u]
      by (simp add: parity_po_asm.state_at_unfold analyse_parity_result_per_origin_def
          analyse_parity_result_per_origin_for_def)
  qed
qed

theorem run_voblint_congruence_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "congruence_po_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (congruence_po_vars (declared_global p) p)"
      and ans: "run_voblint Congruence_Analysis (Some Solver_PerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view CongruenceValue congruence_classify_check bot
          (analyse_congruence_result_per_origin p)
          (unit_seed_globals CongruenceValue (analyse_congruence_result_per_origin p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ congruence_classify_check_proved congruence_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_congruence_result_per_origin p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using congruence_po_asm.result_node_sound [OF solves cover, of u]
      by (simp add: congruence_po_asm.state_at_unfold
          analyse_congruence_result_per_origin_def
          analyse_congruence_result_per_origin_for_def)
  qed
qed

theorem run_voblint_interval_join_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_join_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (interval_join_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_Join) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntervalValue interval_classify_check bot
          (analyse_interval_result_join p)
          (unit_seed_globals IntervalValue (analyse_interval_result_join p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ interval_classify_check_proved interval_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_join p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using interval_join_asm.result_node_sound [OF solves cover, of u]
      by (simp add: interval_join_asm.state_at_unfold analyse_interval_result_join_def
          analyse_interval_result_join_for_def)
  qed
qed

theorem run_voblint_interval_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_po_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (interval_po_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_PerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntervalValue interval_classify_check bot
          (analyse_interval_result_per_origin p)
          (unit_seed_globals IntervalValue (analyse_interval_result_per_origin p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ interval_classify_check_proved interval_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_per_origin p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using interval_po_asm.result_node_sound [OF solves cover, of u]
      by (simp add: interval_po_asm.state_at_unfold analyse_interval_result_per_origin_def
          analyse_interval_result_per_origin_for_def)
  qed
qed

theorem run_voblint_interval_wpo_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_wpo_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (interval_wpo_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntervalValue interval_classify_check bot
          (analyse_interval_result_wpo p)
          (unit_seed_globals IntervalValue (analyse_interval_result_wpo p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ interval_classify_check_proved interval_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_interval_result_wpo p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using interval_wpo_asm.result_node_sound [OF solves cover, of u]
      by (simp add: interval_wpo_asm.state_at_unfold analyse_interval_result_wpo_def
          analyse_interval_result_wpo_for_def)
  qed
qed

theorem run_voblint_int_join_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_join_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (int_join_vars (declared_global p) p)"
      and ans: "run_voblint Int_Analysis (Some Solver_Join) Ctx_None view p = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntDomValue int_classify_check bot
          (analyse_int_join_result p)
          (unit_seed_globals IntDomValue (analyse_int_join_result p) p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_int_join_result p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using int_join_asm.result_node_sound [OF solves cover, of u]
      by (simp add: int_join_asm.state_at_unfold analyse_int_join_result_def
          analyse_int_join_result_for_def int_join_result_def)
  qed
qed

theorem run_voblint_int_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_po_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (int_po_vars (declared_global p) p)"
      and ans: "run_voblint Int_Analysis (Some Solver_PerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntDomValue int_classify_check bot
          (analyse_int_per_origin_result p)
          (unit_seed_globals IntDomValue (analyse_int_per_origin_result p) p) p
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_int_per_origin_result p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using int_po_asm.result_node_sound [OF solves cover, of u]
      by (simp add: int_po_asm.state_at_unfold analyse_int_per_origin_result_def
          analyse_int_per_origin_result_for_def int_po_result_def)
  qed
qed

theorem run_voblint_int_wpo_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_wpo_terminates (declared_global p) p"
      and cover: "vars_cover (prog_cfg p) (int_wpo_vars (declared_global p) p)"
      and ans: "run_voblint Int_Analysis (Some Solver_WarrowPerOrigin) Ctx_None view p
                  = Analysed out"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              (row_verdict row = Lifted Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s))
            \<and> row_verdict row \<noteq> Bot)"
proof -
  from ans
  have "flat_output_of view IntDomValue int_classify_check bot
          (analyse_int_wpo_result p)
          (unit_seed_globals IntDomValue (analyse_int_wpo_result p) p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def Let_def
        split: if_splits)
  note rows = out_checks_of_flat_output [OF this]
  show ?thesis
  proof (rule flat_source_sound_of_collect
      [OF wf s0 run _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> \<lbrakk>case lookup_context (analyse_int_wpo_result p) u () of
                  Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
      using int_wpo_asm.result_node_sound [OF solves cover, of u]
      by (simp add: int_wpo_asm.state_at_unfold analyse_int_wpo_result_def
          analyse_int_wpo_result_for_def int_wpo_result_def)
  qed
qed

text \<open>
  What a dead row claims, stated at the node rather than at a run.  The endpoint
  above is existential in its witness, so reading it backwards --- "this row is
  dead, therefore nothing reaches it" --- does not follow: it constrains the
  rows at the one node it produced, not at an arbitrary node someone names.  The
  statement people want is this one, and it is proved forwards instead: a store
  collected at the point would have to be covered there, and a dead row says
  nothing is.
\<close>

theorem dead_row_unreached:
  fixes p :: imp_prog
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and cert: "analyse_certified D p"
      and ans: "run_voblint D None Ctx_None view p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dead: "row_verdict row = Bot"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (row_point row) = {}"
proof (rule ccontr)
  assume "ltr_collect (declared_global p) (prog_cfg p)
            (cinit_stores (declared_global p)) (row_point row) \<noteq> {}"
  then obtain s where mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                                  (cinit_stores (declared_global p)) (row_point row)"
    by blast
  from analyse_state_node_sound [OF wf cert mem] dead_row_not_covered [OF ans row dead]
  show False by blast
qed


end
