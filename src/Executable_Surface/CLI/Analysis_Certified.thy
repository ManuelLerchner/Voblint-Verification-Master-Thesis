theory Analysis_Certified
  imports Analysis_Run_Solver_Sound
begin

section \<open>One soundness statement over every configuration the CLI answers\<close>

text \<open>
  The tables so far are one per configuration: a domain, a solver discipline and
  a context policy, each with its own \<open>sound_table\<close> instance. This theory states
  the result once, for an arbitrary configuration, over \<^const>\<open>run_program\<close>
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
  --- an unsupported pairing answers \<^const>\<open>Result_Unsupported\<close> --- nor
  well-formedness: a malformed program answers \<^const>\<open>Result_Malformed\<close>.
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

lemma analyse_program_AnalysedE [elim]:
  assumes "analyse_program D solver ctx p = Result_Analysed res"
  obtains pl where "wf_program_compile_input_exec p"
    and "resolve_analysis_config (mk_analysis_config D solver ctx) = Some pl"
    and "plan_result pl p = Some res"
  using assms unfolding analyse_program_def by (auto split: if_splits option.splits)

lemma run_program_AnalysedE [elim]:
  assumes "run_program D solver ctx p = Result_Analysed res"
  obtains typed where "analyse_program D solver ctx p = Result_Analysed typed"
    and "res = map_run_result string_of_abstract_value typed"
  using assms unfolding run_program_def
  by (cases "analyse_program D solver ctx p") auto

text \<open>
  What a plan's result unfolds to: its builder applied to its own table, with the
  plan's functions read at the same plan.
\<close>

lemmas plan_result_report_defs =
  analyse_interval_entry_state_join_def analyse_interval_entry_state_per_origin_def
  analyse_interval_entry_state_wpo_def interval_es_join.verdict_report_def
  interval_es_po.verdict_report_def interval_es_wpo.verdict_report_def
  analyse_interval_call_string_report_join_def
  analyse_interval_call_string_report_per_origin_def
  analyse_interval_call_string_report_wpo_def routed_dg_pipeline.verdict_report_def

lemmas plan_result_unfold =
  plan_terminates.simps plan_covers.simps plan_result_def
  analysis_plan.case solver_choice.case Let_def plan_result_report_defs

subsection \<open>Every plan's result is sound at every collected store\<close>

text \<open>
  The three builders a result comes from, each read at one store the collecting
  semantics admits. The table premise comes before the store so that a caller can
  leave both as subgoals.
\<close>

lemma run_result_sound:
  assumes "res = run_result_of into ctx_key ctx_view targets classify r globals p"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  by (rule sound_table.result_sound_at [OF assms(2) _ _ assms(3)]) (simp_all add: assms(1))

lemma unit_run_result_sound:
  assumes "Some (unit_run_result into enter classify r p) = Some res"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  using assms(1) unfolding unit_run_result_def option.inject
  by (rule run_result_sound [OF sym assms(2,3)])

lemma entry_state_run_result_sound:
  assumes "Some (entry_state_run_result into enter classify r p) = Some res"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  using assms(1) unfolding entry_state_run_result_def option.inject
  by (rule run_result_sound [OF sym assms(2,3)])

lemma call_string_run_result_sound:
  assumes "Some (call_string_run_result into enter classify r k p) = Some res"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  using assms(1) unfolding call_string_run_result_def option.inject
  by (rule run_result_sound [OF sym assms(2,3)])

text \<open>
  One line per plan the resolver can return. A pairing it rejects never reaches
  here; a plan \<^const>\<open>plan_result\<close> refuses has no result, which the closing method
  of each case dismisses. Every table asks for well-formedness and termination,
  and for nothing else.
\<close>

lemma plan_result_sound:
  assumes wf: "wf_program_compile_input p"
      and terminates: "plan_terminates pl p"
      and ans: "plan_result pl p = Some res"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "plan_covers pl p v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
proof (cases pl)
  case (Plan_Sign sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign Solver_Join plan_result_unfold
        fst_analyse_sign_ctx_solved_for analyse_sign_result_def [symmetric]
      by - (rule unit_run_result_sound [OF _ sign_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign Solver_PerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ sign_po_table])
  qed (use ans in \<open>simp_all add: Plan_Sign plan_result_def\<close>)
next
  case (Plan_Interval sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_Warrow plan_result_unfold
        fst_analyse_interval_ctx_solved_for analyse_interval_result_def [symmetric]
      by - (rule unit_run_result_sound [OF _ interval_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_Join plan_result_unfold
      by - (rule unit_run_result_sound [OF _ interval_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_PerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ interval_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval Solver_WarrowPerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ interval_wpo_table])
  qed
next
  case (Plan_Int sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_Warrow plan_result_unfold
        fst_analyse_int_ctx_solved_warrow_for analyse_int_result_for_def [symmetric]
        analyse_int_result_def [symmetric]
      by - (rule unit_run_result_sound [OF _ int_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_Join plan_result_unfold
      by - (rule unit_run_result_sound [OF _ int_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_PerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ int_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int Solver_WarrowPerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ int_wpo_table])
  qed
next
  case (Plan_Parity sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity Solver_Join plan_result_unfold
        fst_analyse_parity_ctx_solved_for analyse_parity_result_def [symmetric]
      by - (rule unit_run_result_sound [OF _ parity_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity Solver_PerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ parity_po_table])
  qed (use ans in \<open>simp_all add: Plan_Parity plan_result_def\<close>)
next
  case (Plan_Congruence sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence Solver_Join plan_result_unfold
        fst_analyse_congruence_ctx_solved_for analyse_congruence_result_def [symmetric]
      by - (rule unit_run_result_sound [OF _ congruence_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence Solver_PerOrigin plan_result_unfold
      by - (rule unit_run_result_sound [OF _ congruence_po_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence plan_result_def\<close>)
next
  case (Plan_Sign_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign_EntryState Solver_Join plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ sign_es_table])
  qed (use ans in \<open>simp_all add: Plan_Sign_EntryState plan_result_def\<close>)
next
  case (Plan_Interval_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_Warrow plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ interval_es_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_Join plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ interval_es_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_PerOrigin plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ interval_es_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_EntryState Solver_WarrowPerOrigin plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ interval_es_wpo_table])
  qed
next
  case (Plan_Int_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_EntryState Solver_Join plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ int_es_join_table])
  next
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_EntryState Solver_Warrow plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ int_es_table])
  qed (use ans in \<open>simp_all add: Plan_Int_EntryState plan_result_def\<close>)
next
  case (Plan_Parity_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity_EntryState Solver_Join plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ parity_es_table])
  qed (use ans in \<open>simp_all add: Plan_Parity_EntryState plan_result_def\<close>)
next
  case (Plan_Congruence_EntryState sc)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence_EntryState Solver_Join plan_result_unfold
      by - (rule entry_state_run_result_sound [OF _ congruence_es_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence_EntryState plan_result_def\<close>)
next
  case (Plan_Sign_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Sign_CallString Solver_Join plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ sign_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Sign_CallString plan_result_def\<close>)
next
  case (Plan_Interval_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_Warrow plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ interval_cs_table])
  next
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_Join plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ interval_cs_join_table])
  next
    case Solver_PerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_PerOrigin plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ interval_cs_po_table])
  next
    case Solver_WarrowPerOrigin
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Interval_CallString Solver_WarrowPerOrigin plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ interval_cs_wpo_table])
  qed
next
  case (Plan_Int_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_CallString Solver_Join plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ int_cs_join_table])
  next
    case Solver_Warrow
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Int_CallString Solver_Warrow plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ int_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Int_CallString plan_result_def\<close>)
next
  case (Plan_Parity_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Parity_CallString Solver_Join plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ parity_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Parity_CallString plan_result_def\<close>)
next
  case (Plan_Congruence_CallString sc k)
  show ?thesis
  proof (cases sc)
    case Solver_Join
    show ?thesis
      using wf terminates ans mem
      unfolding Plan_Congruence_CallString Solver_Join plan_result_unfold
      by - (rule call_string_run_result_sound [OF _ congruence_cs_table])
  qed (use ans in \<open>simp_all add: Plan_Congruence_CallString plan_result_def\<close>)
qed

text \<open>
  Which checks a result lists does not depend on the table behind it: every plan's
  check column has one entry per compiled check, whatever it concluded there.
\<close>

lemma plan_result_check_sites:
  assumes "plan_result pl p = Some res"
  shows "map (\<lambda>chk. (check_point chk, check_exp chk)) (res_checks res)
           = check_sites (prog_cfg p)"
  using assms
  by (cases pl)
     (auto simp: plan_result_def run_result_builder_defs result_checks_of_sites
        split: solver_choice.splits)

text \<open>
  The same claims read through \<^const>\<open>run_program\<close>: an analysed answer names the
  plan and was only given for a well-formed program, the configuration's termination
  is its plan's, and rendering abstract values changes neither the check column nor
  the diagnostics.
\<close>

lemma run_program_analysed_plan:
  assumes "run_program D solver ctx p = Result_Analysed res"
  obtains pl typed where "wf_program_compile_input_exec p"
    and "resolve_analysis_config (mk_analysis_config D solver ctx) = Some pl"
    and "plan_result pl p = Some typed"
    and "res = map_run_result string_of_abstract_value typed"
  using assms by (elim run_program_AnalysedE analyse_program_AnalysedE) blast

lemma run_program_sound_at:
  assumes terminates: "config_terminates D solver ctx p"
      and ans: "run_program D solver ctx p = Result_Analysed res"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "analysis_result_covers D solver ctx p v s \<and> checks_sound_at res v s
           \<and> diagnostics_sound_at res p v s"
proof -
  from ans obtain pl typed
    where wfx: "wf_program_compile_input_exec p"
      and pl: "resolve_analysis_config (mk_analysis_config D solver ctx) = Some pl"
      and pres: "plan_result pl p = Some typed"
      and res: "res = map_run_result string_of_abstract_value typed"
    by (rule run_program_analysed_plan)
  from terminates have "plan_terminates pl p"
    unfolding config_terminates_def pl option.case .
  from plan_result_sound [OF wf_program_compile_input_exec_sound [OF wfx] this pres mem]
  show ?thesis
    unfolding analysis_result_covers_def pl option.case res map_run_result_sound_at .
qed

theorem run_program_arithmetic_safe:
  assumes terminates: "config_terminates D solver ctx p"
    and ans: "run_program D solver ctx p = Result_Analysed res"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and absent: "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
  using run_program_sound_at[OF terminates ans mem] absent
  unfolding diagnostics_sound_at_def by blast

corollary run_program_arithmetic_intra_safe:
  assumes "config_terminates D solver ctx p"
    and "run_program D solver ctx p = Result_Analysed res"
    and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (arithmetic_edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "aval divisor s \<noteq> 0"
  using run_program_arithmetic_safe[OF assms(1-4)]
    arithmetic_expression_sites_intra[OF finite_intra_prog_cfg assms(5)] assms(6,7)
  unfolding arithmetic_safe_at_def by blast

text \<open>
  Whatever the configuration, the result lists one check per compiled check, at the
  check's node and with its condition, in graph order.  Pairing those checks with
  source positions happens outside this development.
\<close>

corollary run_program_check_sites:
  assumes "run_program D solver ctx p = Result_Analysed res"
  shows "map (\<lambda>chk. (check_point chk, check_exp chk)) (res_checks res)
           = check_sites (prog_cfg p)"
proof -
  from assms obtain pl typed
    where "plan_result pl p = Some typed"
      and res: "res = map_run_result string_of_abstract_value typed"
    by (rule run_program_analysed_plan)
  from plan_result_check_sites [OF this(1)] show ?thesis by (simp add: res)
qed

subsection \<open>The endpoint\<close>

text \<open>
  Run the source program, stop wherever you like, and ask any accepted
  configuration for a result: there is a graph node and frame stack for where you
  stopped, the store in your hands is one the collecting semantics really admits
  there, the table that configuration built describes it, and every check listed
  there holds of it, with none there marked unreachable.
\<close>

theorem run_program_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and terminates: "config_terminates D solver ctx p"
      and ans: "run_program D solver ctx p = Result_Analysed res"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> analysis_result_covers D solver ctx p v s
               \<and> checks_sound_at res v s"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from ans have "wf_program_compile_input_exec p" by (rule run_program_analysed_plan)
  from source_reaches_ltr_collect
         [OF wf_program_compile_input_exec_sound [OF this] s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  with run_program_sound_at [OF terminates ans mem] show ?thesis by blast
qed

text \<open>
  The same endpoint, read at a check.  A run about to execute \<open>Check e\<close> finds a
  check for \<open>e\<close> in the result, listed at a node this very store reaches, and that
  check's verdict holds of the store.  The check is existential and cannot be
  otherwise: a source state does not determine its node.  Two procedures with the
  same body, called on the two branches of a conditional, leave the same source
  state inside either, and each body's check is listed separately; only the node the
  store reaches says which one is this execution's.
\<close>

theorem run_program_check_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and chk: "next_check residual = Some e"
      and terminates: "config_terminates D solver ctx p"
      and ans: "run_program D solver ctx p = Result_Analysed res"
  shows "\<exists>c \<in> set (res_checks res). check_exp c = e
           \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (aval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval e s))"
proof -
  from run_program_certified_source_sound [OF s0 run terminates ans]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
      and sound: "checks_sound_at res v s"
    by blast
  from csim_next_check_edge [OF m chk]
  have "(v, e) \<in> set (check_sites (prog_cfg p))" by auto
  then obtain c
    where "c \<in> set (res_checks res)" and "check_point c = v" and "check_exp c = e"
    unfolding run_program_check_sites [OF ans, symmetric] by auto
  with mem sound show ?thesis unfolding checks_sound_at_def by blast
qed

text \<open>
  What a dead check claims, stated at the point rather than at a run, and for every
  accepted configuration. The endpoint above is existential in its witness, so
  reading it backwards does not follow from it; this is proved forwards instead,
  from the claim at every collected store.
\<close>

corollary run_program_dead_check_unreached:
  assumes terminates: "config_terminates D solver ctx p"
      and ans: "run_program D solver ctx p = Result_Analysed res"
      and listed: "chk \<in> set (res_checks res)"
      and dead: "check_verdict chk = Dead"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (check_point chk) = {}"
proof (rule equals0I)
  fix s
  assume "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) (check_point chk)"
  from run_program_sound_at [OF terminates ans this]
  have "checks_sound_at res (check_point chk) s" by blast
  with listed dead show False unfolding checks_sound_at_def by blast
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

corollary run_program_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes terminates: "config_terminates D None Ctx_None p"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and ans: "run_program D None Ctx_None p = Result_Analysed res"
  shows "\<exists>v stk.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) v
         \<and> analyse_state_covers D p v s
         \<and> (\<forall>c \<in> set (res_checks res). check_point c = v \<longrightarrow>
              (check_verdict c = Lifted Check_Proved \<longrightarrow> truthy (aval (check_exp c) s))
            \<and> (check_verdict c = Lifted Check_Refuted \<longrightarrow> \<not> truthy (aval (check_exp c) s))
            \<and> check_verdict c \<noteq> Bot)"
proof -
  from run_program_certified_source_sound [OF s0 run terminates ans]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
      and cov: "analysis_result_covers D None Ctx_None p v s"
      and chk: "checks_sound_at res v s"
    by blast
  from cov have "analyse_state_covers D p v s"
    by (cases D)
       (simp_all add: analysis_result_covers_def mk_analysis_config_def table_covers_unit_iff)
  with m mem chk show ?thesis
    unfolding checks_sound_at_def by blast
qed

end

