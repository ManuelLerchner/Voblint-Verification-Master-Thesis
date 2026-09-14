theory Analysis_Certified
  imports Analysis_Run_Solver_Sound
begin

section \<open>One soundness statement over every configuration the CLI answers\<close>

text \<open>
  The tables so far are one per configuration: a domain, a solver discipline and
  a context policy, each with its own \<open>sound_table\<close> instance. This theory states
  the result once, for an arbitrary configuration, over \<^const>\<open>run_voblint\<close>
  alone.

  The case split lives in functions over \<^typ>\<open>analysis_plan\<close>, the one thing
  \<^const>\<open>resolve_analysis_config\<close> resolves a legal configuration to.
  \<open>plan_terminates\<close> names the one per-program fact a plan needs --- its solver
  run completed --- and \<open>plan_covers\<close> names the table it built. Both are
  functions for the reason \<^const>\<open>analyse_state_covers\<close> already is: an abstract
  state's type is the domain's own carrier, so nothing polymorphic can hold all
  five. Indexing by plan rather than by configuration means the resolver's legality
  table and its defaults are consulted, not restated: a configuration owes what its
  plan owes.

  Coverage of the solve is not a premise: the keys of a terminating solve that a run
  can reach are closed on their own, which \<^theory>\<open>Voblint_Result.Routed_Live_Keys\<close>
  proves from what the generated equations read.  Neither is configuration legality
  --- an unsupported pairing answers \<^const>\<open>Unsupported_Configuration\<close> --- nor
  well-formedness: a malformed program answers \<^const>\<open>Malformed_Program\<close>.
\<close>

subsection \<open>What a plan owes, and what its table claims\<close>

fun plan_terminates :: "analysis_plan \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "plan_terminates (Plan_Sign Solver_Join) p = sign_join.terminates (declared_global p) p"
| "plan_terminates (Plan_Sign Solver_PerOrigin) p = sign_po_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval Solver_Warrow) p =
     interval_warrow_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval Solver_Join) p =
     interval_join_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval Solver_PerOrigin) p =
     interval_po_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval Solver_WarrowPerOrigin) p =
     interval_wpo_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Int Solver_Warrow) p = int_warrow_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Int Solver_Join) p = int_join_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Int Solver_PerOrigin) p = int_po_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Int Solver_WarrowPerOrigin) p =
     int_wpo_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Parity Solver_Join) p = parity_join.terminates (declared_global p) p"
| "plan_terminates (Plan_Parity Solver_PerOrigin) p =
     parity_po_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Congruence Solver_Join) p =
     congruence_join.terminates (declared_global p) p"
| "plan_terminates (Plan_Congruence Solver_PerOrigin) p =
     congruence_po_asm.terminates (declared_global p) p"
| "plan_terminates (Plan_Sign_EntryState Solver_Join) p =
     sign_entry_state_terminates_for (declared_global p) p"
| "plan_terminates (Plan_Interval_EntryState Solver_Warrow) p =
     entry_state_terminates_prog (declared_global p) p"
| "plan_terminates (Plan_Interval_EntryState Solver_Join) p =
     interval_es_join.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval_EntryState Solver_PerOrigin) p =
     interval_es_po.terminates (declared_global p) p"
| "plan_terminates (Plan_Interval_EntryState Solver_WarrowPerOrigin) p =
     interval_es_wpo.terminates (declared_global p) p"
| "plan_terminates (Plan_Int_EntryState Solver_Join) p =
     int_es_join_terminates (declared_global p) p"
| "plan_terminates (Plan_Int_EntryState Solver_Warrow) p = int_es_terminates (declared_global p) p"
| "plan_terminates (Plan_Parity_EntryState Solver_Join) p =
     parity_entry_state_terminates_for (declared_global p) p"
| "plan_terminates (Plan_Congruence_EntryState Solver_Join) p =
     congruence_entry_state_terminates_for (declared_global p) p"
| "plan_terminates (Plan_Sign_CallString Solver_Join k) p =
     sign_cs_terminates k (declared_global p) p"
| "plan_terminates (Plan_Interval_CallString Solver_Warrow k) p =
     interval_cs_terminates k (declared_global p) p"
| "plan_terminates (Plan_Interval_CallString Solver_Join k) p =
     interval_cs_join_terminates k (declared_global p) p"
| "plan_terminates (Plan_Interval_CallString Solver_PerOrigin k) p =
     interval_cs_po_terminates k (declared_global p) p"
| "plan_terminates (Plan_Interval_CallString Solver_WarrowPerOrigin k) p =
     interval_cs_wpo_terminates k (declared_global p) p"
| "plan_terminates (Plan_Int_CallString Solver_Join k) p =
     int_cs_join_terminates k (declared_global p) p"
| "plan_terminates (Plan_Int_CallString Solver_Warrow k) p =
     int_cs_terminates k (declared_global p) p"
| "plan_terminates (Plan_Parity_CallString Solver_Join k) p =
     parity_cs_terminates k (declared_global p) p"
| "plan_terminates (Plan_Congruence_CallString Solver_Join k) p =
     congruence_cs_terminates k (declared_global p) p"
| "plan_terminates _ p = False"

fun plan_covers :: "analysis_plan \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "plan_covers (Plan_Sign Solver_Join) p = table_covers (analyse_sign_result p)"
| "plan_covers (Plan_Sign Solver_PerOrigin) p =
     table_covers (analyse_sign_result_per_origin p)"
| "plan_covers (Plan_Interval Solver_Warrow) p = table_covers (analyse_interval_result p)"
| "plan_covers (Plan_Interval Solver_Join) p = table_covers (analyse_interval_result_join p)"
| "plan_covers (Plan_Interval Solver_PerOrigin) p =
     table_covers (analyse_interval_result_per_origin p)"
| "plan_covers (Plan_Interval Solver_WarrowPerOrigin) p =
     table_covers (analyse_interval_result_wpo p)"
| "plan_covers (Plan_Int Solver_Warrow) p = table_covers (analyse_int_result p)"
| "plan_covers (Plan_Int Solver_Join) p = table_covers (analyse_int_join_result p)"
| "plan_covers (Plan_Int Solver_PerOrigin) p = table_covers (analyse_int_per_origin_result p)"
| "plan_covers (Plan_Int Solver_WarrowPerOrigin) p = table_covers (analyse_int_wpo_result p)"
| "plan_covers (Plan_Parity Solver_Join) p = table_covers (analyse_parity_result p)"
| "plan_covers (Plan_Parity Solver_PerOrigin) p =
     table_covers (analyse_parity_result_per_origin p)"
| "plan_covers (Plan_Congruence Solver_Join) p = table_covers (analyse_congruence_result p)"
| "plan_covers (Plan_Congruence Solver_PerOrigin) p =
     table_covers (analyse_congruence_result_per_origin p)"
| "plan_covers (Plan_Sign_EntryState Solver_Join) p =
     table_covers (analyse_sign_entry_state_result p)"
| "plan_covers (Plan_Interval_EntryState Solver_Warrow) p =
     table_covers (analyse_interval_entry_state_result p)"
| "plan_covers (Plan_Interval_EntryState Solver_Join) p =
     table_covers (interval_es_join.result (declared_global p) p)"
| "plan_covers (Plan_Interval_EntryState Solver_PerOrigin) p =
     table_covers (interval_es_po.result (declared_global p) p)"
| "plan_covers (Plan_Interval_EntryState Solver_WarrowPerOrigin) p =
     table_covers (interval_es_wpo.result (declared_global p) p)"
| "plan_covers (Plan_Int_EntryState Solver_Join) p =
     table_covers (analyse_int_entry_state_result p)"
| "plan_covers (Plan_Int_EntryState Solver_Warrow) p =
     table_covers (analyse_int_entry_state_result_warrow p)"
| "plan_covers (Plan_Parity_EntryState Solver_Join) p =
     table_covers (analyse_parity_entry_state_result p)"
| "plan_covers (Plan_Congruence_EntryState Solver_Join) p =
     table_covers (analyse_congruence_entry_state_result p)"
| "plan_covers (Plan_Sign_CallString Solver_Join k) p =
     table_covers (analyse_sign_call_string_result k p)"
| "plan_covers (Plan_Interval_CallString Solver_Warrow k) p =
     table_covers (analyse_interval_call_string_result k p)"
| "plan_covers (Plan_Interval_CallString Solver_Join k) p =
     table_covers (interval_cs_join_result k (declared_global p) p)"
| "plan_covers (Plan_Interval_CallString Solver_PerOrigin k) p =
     table_covers (interval_cs_po_result k (declared_global p) p)"
| "plan_covers (Plan_Interval_CallString Solver_WarrowPerOrigin k) p =
     table_covers (interval_cs_wpo_result k (declared_global p) p)"
| "plan_covers (Plan_Int_CallString Solver_Join k) p =
     table_covers (analyse_int_call_string_result k p)"
| "plan_covers (Plan_Int_CallString Solver_Warrow k) p =
     table_covers (analyse_int_call_string_result_warrow k p)"
| "plan_covers (Plan_Parity_CallString Solver_Join k) p =
     table_covers (analyse_parity_call_string_result k p)"
| "plan_covers (Plan_Congruence_CallString Solver_Join k) p =
     table_covers (analyse_congruence_call_string_result k p)"
| "plan_covers _ p = (\<lambda>_ _. False)"

definition config_terminates ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "config_terminates D solver ctx p =
     (case resolve_analysis_config (mk_analysis_config D solver ctx) of
        None \<Rightarrow> False
      | Some pl \<Rightarrow> plan_terminates pl p)"

definition analysis_result_covers ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode
       \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "analysis_result_covers D solver ctx p v s =
     (case resolve_analysis_config (mk_analysis_config D solver ctx) of
        None \<Rightarrow> False
      | Some pl \<Rightarrow> plan_covers pl p v s)"

lemma run_voblint_AnalysedE [elim]:
  assumes "run_voblint D solver ctx view p = Analysed out"
  obtains pl where "wf_program_compile_input_exec p"
    and "resolve_analysis_config (mk_analysis_config D solver ctx) = Some pl"
    and "plan_answer pl view p = Analysed out"
  using assms unfolding run_voblint_def by (auto split: if_splits option.splits)

text \<open>
  What a plan's answer unfolds to: its builder applied to its own table, with the
  plan's functions read at the same plan.
\<close>

lemmas plan_answer_report_defs =
  analyse_interval_entry_state_join_def analyse_interval_entry_state_per_origin_def
  analyse_interval_entry_state_wpo_def interval_es_join.verdict_report_def
  interval_es_po.verdict_report_def interval_es_wpo.verdict_report_def
  analyse_interval_call_string_report_join_def
  analyse_interval_call_string_report_per_origin_def
  analyse_interval_call_string_report_wpo_def routed_dg_pipeline.verdict_report_def

lemmas plan_answer_unfold =
  plan_terminates.simps plan_covers.simps plan_answer_def
  analysis_plan.case solver_choice.case Let_def plan_answer_report_defs

subsection \<open>Every plan's answer is sound at every collected store\<close>

text \<open>
  The four builders an answer comes from, each read at one store the collecting
  semantics admits. The table premise comes before the store so that a caller can
  leave both as subgoals.
\<close>

lemma flat_output_sound:
  assumes "flat_output_of view into classify bot_state r globals p = Analysed out"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at out v s \<and> diagnostics_sound_at out p v s"
  by (rule sound_table.output_sound_at [OF assms(2) out_checks_of_flat_output [OF assms(1)]
          out_diagnostics_of_flat_output [OF assms(1)] assms(3)])

lemma entry_state_output_sound:
  assumes "entry_state_output_of view enter into classify r p = Analysed out"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at out v s \<and> diagnostics_sound_at out p v s"
  by (rule sound_table.output_sound_at
        [OF assms(2) out_checks_of_entry_state_output [OF assms(1)]
          out_diagnostics_of_entry_state_output [OF assms(1)] assms(3)])

lemma cs_output_sound:
  assumes "cs_output_of view into classify r k p = Analysed out"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at out v s \<and> diagnostics_sound_at out p v s"
  by (rule sound_table.output_sound_at [OF assms(2) out_checks_of_cs_output [OF assms(1)]
          out_diagnostics_of_cs_output [OF assms(1)] assms(3)])


text \<open>
  One line per plan the resolver can return. A pairing it rejects never reaches
  here; a plan \<^const>\<open>plan_answer\<close> refuses answers
  \<^const>\<open>Unsupported_Configuration\<close>, which the closing method of each case
  dismisses. Every table asks for well-formedness and termination, and for
  nothing else.
\<close>

lemma plan_answer_sound:
  assumes wf: "wf_program_compile_input p"
      and terminates: "plan_terminates pl p"
      and ans: "plan_answer pl view p = Analysed out"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "plan_covers pl p v s \<and> checks_sound_at out v s \<and> diagnostics_sound_at out p v s"
proof (cases pl)
  case (Plan_Sign sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign Solver_Join plan_answer_unfold case_prod_unfold
        fst_analyse_sign_ctx_solved_for analyse_sign_result_def [symmetric]
      by - (rule flat_output_sound [OF _ sign_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign Solver_PerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ sign_po_table])
  qed (use ans in \<open>simp_all add: Plan_Sign plan_answer_def\<close>)
next
  case (Plan_Interval sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_Warrow plan_answer_unfold case_prod_unfold
        fst_analyse_interval_ctx_solved_for analyse_interval_result_def [symmetric]
      by - (rule flat_output_sound [OF _ interval_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_Join plan_answer_unfold
      by - (rule flat_output_sound [OF _ interval_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_PerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ interval_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_WarrowPerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ interval_wpo_table])
  qed
next
  case (Plan_Int sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_Warrow plan_answer_unfold case_prod_unfold
        fst_analyse_int_ctx_solved_warrow_for analyse_int_result_for_def [symmetric]
        analyse_int_result_def [symmetric]
      by - (rule flat_output_sound [OF _ int_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_Join plan_answer_unfold
      by - (rule flat_output_sound [OF _ int_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_PerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ int_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_WarrowPerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ int_wpo_table])
  qed
next
  case (Plan_Parity sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity Solver_Join plan_answer_unfold case_prod_unfold
        fst_analyse_parity_ctx_solved_for analyse_parity_result_def [symmetric]
      by - (rule flat_output_sound [OF _ parity_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity Solver_PerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ parity_po_table])
  qed (use ans in \<open>simp_all add: Plan_Parity plan_answer_def\<close>)
next
  case (Plan_Congruence sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence Solver_Join plan_answer_unfold case_prod_unfold
        fst_analyse_congruence_ctx_solved_for analyse_congruence_result_def [symmetric]
      by - (rule flat_output_sound [OF _ congruence_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence Solver_PerOrigin plan_answer_unfold
      by - (rule flat_output_sound [OF _ congruence_po_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence plan_answer_def\<close>)
next
  case (Plan_Sign_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign_EntryState Solver_Join plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ sign_es_table])
  qed (use ans in \<open>simp_all add: Plan_Sign_EntryState plan_answer_def\<close>)
next
  case (Plan_Interval_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_Warrow plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ interval_es_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_Join plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ interval_es_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_PerOrigin plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ interval_es_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_WarrowPerOrigin plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ interval_es_wpo_table])
  qed
next
  case (Plan_Int_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_EntryState Solver_Join plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ int_es_join_table])
  next
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_EntryState Solver_Warrow plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ int_es_table])
  qed (use ans in \<open>simp_all add: Plan_Int_EntryState plan_answer_def\<close>)
next
  case (Plan_Parity_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity_EntryState Solver_Join plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ parity_es_table])
  qed (use ans in \<open>simp_all add: Plan_Parity_EntryState plan_answer_def\<close>)
next
  case (Plan_Congruence_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence_EntryState Solver_Join plan_answer_unfold
      by - (rule entry_state_output_sound [OF _ congruence_es_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence_EntryState plan_answer_def\<close>)
next
  case (Plan_Sign_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign_CallString Solver_Join plan_answer_unfold
      by - (rule cs_output_sound [OF _ sign_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Sign_CallString plan_answer_def\<close>)
next
  case (Plan_Interval_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_Warrow plan_answer_unfold
      by - (rule cs_output_sound [OF _ interval_cs_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_Join plan_answer_unfold
      by - (rule cs_output_sound [OF _ interval_cs_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_PerOrigin plan_answer_unfold
      by - (rule cs_output_sound [OF _ interval_cs_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_WarrowPerOrigin plan_answer_unfold
      by - (rule cs_output_sound [OF _ interval_cs_wpo_table])
  qed
next
  case (Plan_Int_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_CallString Solver_Join plan_answer_unfold
      by - (rule cs_output_sound [OF _ int_cs_join_table])
  next
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_CallString Solver_Warrow plan_answer_unfold
      by - (rule cs_output_sound [OF _ int_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Int_CallString plan_answer_def\<close>)
next
  case (Plan_Parity_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity_CallString Solver_Join plan_answer_unfold
      by - (rule cs_output_sound [OF _ parity_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Parity_CallString plan_answer_def\<close>)
next
  case (Plan_Congruence_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence_CallString Solver_Join plan_answer_unfold
      by - (rule cs_output_sound [OF _ congruence_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence_CallString plan_answer_def\<close>)
qed

text \<open>
  Which rows an answer has does not depend on the table behind it: every plan's
  check column has one row per compiled check, whatever it concluded there.
\<close>

lemma plan_answer_check_sites:
  assumes "plan_answer pl view p = Analysed out"
  shows "map (\<lambda>row. (row_point row, row_exp row)) (out_checks out) = check_sites (prog_cfg p)"
  using assms
  by (cases pl)
     (auto simp: plan_answer_def plan_answer_report_defs Let_def
        split: solver_choice.splits prod.splits
        dest!: flat_output_check_sites entry_state_output_check_sites cs_output_check_sites)

text \<open>
  The same claim read through \<^const>\<open>run_voblint\<close>: an \<^const>\<open>Analysed\<close>
  answer names the plan and was only given for a well-formed program, and the
  configuration's termination is its plan's.
\<close>

lemma run_voblint_sound_at:
  assumes terminates: "config_terminates D solver ctx p"
      and ans: "run_voblint D solver ctx view p = Analysed out"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "analysis_result_covers D solver ctx p v s \<and> checks_sound_at out v s \<and> diagnostics_sound_at out p v s"
proof -
  from ans obtain pl
    where wfx: "wf_program_compile_input_exec p"
      and pl: "resolve_analysis_config (mk_analysis_config D solver ctx) = Some pl"
      and pans: "plan_answer pl view p = Analysed out"
    by (rule run_voblint_AnalysedE)
  from terminates have "plan_terminates pl p"
    unfolding config_terminates_def pl option.case .
  from plan_answer_sound [OF wf_program_compile_input_exec_sound [OF wfx] this pans mem]
  show ?thesis
    unfolding analysis_result_covers_def pl option.case .
qed

text \<open>
  Whatever the configuration, the report has one row per compiled check, at the
  check's node and with its condition, in graph order.  Pairing those rows with
  source positions happens outside this development.
\<close>

theorem run_voblint_arithmetic_safe:
  assumes terminates: "config_terminates D solver ctx p"
    and ans: "run_voblint D solver ctx view p = Analysed out"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and absent: "\<forall>d \<in> set (out_diagnostics out). diagnostic_point d \<noteq> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
  using run_voblint_sound_at[OF terminates ans mem] absent
  unfolding diagnostics_sound_at_def by blast

corollary run_voblint_arithmetic_intra_safe:
  assumes "config_terminates D solver ctx p"
    and "run_voblint D solver ctx view p = Analysed out"
    and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and "\<forall>d \<in> set (out_diagnostics out). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (arithmetic_edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "aval divisor s \<noteq> 0"
  using run_voblint_arithmetic_safe[OF assms(1-4)]
    arithmetic_expression_sites_intra[OF finite_intra_prog_cfg assms(5)] assms(6,7)
  unfolding arithmetic_safe_at_def by blast

corollary run_voblint_check_sites:
  assumes "run_voblint D solver ctx view p = Analysed out"
  shows "map (\<lambda>row. (row_point row, row_exp row)) (out_checks out) = check_sites (prog_cfg p)"
  using assms by (blast intro: plan_answer_check_sites)

subsection \<open>The endpoint\<close>

text \<open>
  Run the source program, stop wherever you like, and ask any accepted
  configuration for a report: there is a graph node and frame stack for where you
  stopped, the store in your hands is one the collecting semantics really admits
  there, the table that configuration built describes it, and every check printed
  beside it holds of it, with no row there marked unreachable.
\<close>

theorem run_voblint_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and terminates: "config_terminates D solver ctx p"
      and ans: "run_voblint D solver ctx view p = Analysed out"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> analysis_result_covers D solver ctx p v s
               \<and> checks_sound_at out v s"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from ans have "wf_program_compile_input_exec p" by (rule run_voblint_AnalysedE)
  from source_reaches_ltr_collect
         [OF wf_program_compile_input_exec_sound [OF this] s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  with run_voblint_sound_at [OF terminates ans mem] show ?thesis by blast
qed

text \<open>
  The same endpoint, read at a check.  A run about to execute \<open>Check e\<close> finds a row
  for \<open>e\<close> in the report, printed at a node this very store reaches, and that row's
  verdict holds of the store.  The row is existential and cannot be otherwise: a
  source state does not determine its node.  Two procedures with the same body,
  called on the two branches of a conditional, leave the same source state inside
  either, and each body's check has its own row; only the node the store reaches
  says which row is this execution's.
\<close>

theorem run_voblint_check_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and chk: "next_check residual = Some e"
      and terminates: "config_terminates D solver ctx p"
      and ans: "run_voblint D solver ctx view p = Analysed out"
  shows "\<exists>row \<in> set (out_checks out). row_exp row = e
           \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) (row_point row)
           \<and> row_verdict row \<noteq> Dead
           \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval e s))
           \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval e s))"
proof -
  from run_voblint_certified_source_sound [OF s0 run terminates ans]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
      and sound: "checks_sound_at out v s"
    by blast
  from csim_next_check_edge [OF m chk]
  have "(v, e) \<in> set (check_sites (prog_cfg p))" by auto
  then obtain row
    where "row \<in> set (out_checks out)" and "row_point row = v" and "row_exp row = e"
    unfolding run_voblint_check_sites [OF ans, symmetric] by auto
  with mem sound show ?thesis unfolding checks_sound_at_def by blast
qed

text \<open>
  What a dead row claims, stated at the point rather than at a run, and for every
  accepted configuration. The endpoint above is existential in its witness, so
  reading it backwards does not follow from it; this is proved forwards instead,
  from the claim at every collected store.
\<close>

corollary run_voblint_dead_row_unreached:
  assumes terminates: "config_terminates D solver ctx p"
      and ans: "run_voblint D solver ctx view p = Analysed out"
      and row: "row \<in> set (out_checks out)"
      and dead: "row_verdict row = Dead"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (row_point row) = {}"
proof (rule equals0I)
  fix s
  assume "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) (row_point row)"
  from run_voblint_sound_at [OF terminates ans this]
  have "checks_sound_at out (row_point row) s" by blast
  with row dead show False unfolding checks_sound_at_def by blast
qed

text \<open>
  The same endpoint at a domain's default configuration, in the vocabulary
  \<^const>\<open>analyse\<close> speaks: at the unit context a table covering a store is the one
  entry describing it.
\<close>

lemma table_covers_unit_iff:
  fixes r :: "(unit, 'a::sound_domain abs_state) analysis_result"
  shows "table_covers r v s \<longleftrightarrow> s \<in> gamma_point (lookup_context r v ())"
proof
  assume "table_covers r v s"
  then obtain c st where "lookup_context r v c = Lifted st" and "s \<in> \<lbrakk>st\<rbrakk>"
    unfolding table_covers_def by blast
  then show "s \<in> gamma_point (lookup_context r v ())" by (cases c) simp
next
  assume "s \<in> gamma_point (lookup_context r v ())"
  then show "table_covers r v s"
    by (cases "lookup_context r v ()") (simp_all add: table_coversI)
qed

corollary run_voblint_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes terminates: "config_terminates D None Ctx_None p"
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
  from run_voblint_certified_source_sound [OF s0 run terminates ans]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
      and cov: "analysis_result_covers D None Ctx_None p v s"
      and chk: "checks_sound_at out v s"
    by blast
  from cov have "analyse_state_covers D p v s"
    by (cases D)
       (simp_all add: analysis_result_covers_def mk_analysis_config_def table_covers_unit_iff)
  with m mem chk show ?thesis
    unfolding checks_sound_at_def by blast
qed

end

