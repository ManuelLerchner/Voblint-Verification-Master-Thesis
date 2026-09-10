theory Analysis_Run_Solver_Sound
  imports Analysis_Run_Ctx_Sound
begin

section \<open>What a run at a non-default solver discipline proves about a run of the program\<close>

text \<open>
  Which solver runs an equation system is independent of which context policy
  generated it, so a configuration naming an explicit discipline -- always-join,
  per-origin, warrowing-per-origin -- solves the same system the shipped default
  solves and earns the same endpoint. This theory instantiates
  \<open>ctx_source_sound_of_activation\<close> at those configurations; the ones at each
  policy's default discipline are @{theory Voblint_CLI.Analysis_Run_Ctx_Sound}'s.

  Nothing here is new mathematics. Every cell names its own registration's solved
  table, its coverage endpoints and its finiteness fact, and the argument is the
  default one with those names substituted -- which is the point: the endpoint
  does not know which discipline produced the table it reads.

  A cell whose configuration carries a call-string bound \<open>k\<close> cannot name a
  \<^locale>\<open>routed_dg_pipeline\<close> binder, because no interpretation can fix a runtime
  parameter; it spells the pipeline application out in abbreviations instead and
  cites the registration's \<open>lemmas\<close> aliases. That is the only visible difference
  between an entry-state cell and a call-string one.
\<close>

subsection \<open>Interval at its explicitly chosen entry-state disciplines\<close>

text \<open>
  These six route through \<^const>\<open>verdict_report_answer\<close>, so they reach the
  endpoint through the bridge above rather than through
  \<^const>\<open>entry_state_output_of\<close>.  Nothing else differs: each names its own
  registration's solved table and coverage endpoints, and the argument is the
  warrowing one with those names substituted.
\<close>

theorem run_voblint_interval_entry_state_join_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_es_join.terminates (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_es_join.ctx_succ (declared_global p) p) []
                    (interval_es_join.sol_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_Join) Ctx_EntryState view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (interval_es_join.admitted_contexts (declared_global p) p) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_es_join.result (declared_global p) p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_entry_state_join p) = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_entry_state_join_def
                  interval_es_join.verdict_report_def [symmetric]]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows [unfolded interval_es_join.verdict_report_def]])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (interval_es_join.admitted_contexts (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: interval_es_join.entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (interval_es_join.admitted_contexts (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_es_join.result (declared_global p) p) u ctx)"
      using interval_es_join.entry_state_activation_collect_sound_of_cover [OF cov]
      unfolding interval_es_join.gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (interval_es_join.result (declared_global p) p)"
      using interval_es_join.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def interval_es_join.result_def
          interval_es_join.sol_vars_def)
  qed
qed

theorem run_voblint_interval_entry_state_per_origin_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_es_po.terminates (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_es_po.ctx_succ (declared_global p) p) []
                    (interval_es_po.sol_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_PerOrigin) Ctx_EntryState view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (interval_es_po.admitted_contexts (declared_global p) p) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_es_po.result (declared_global p) p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_entry_state_per_origin p) = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_entry_state_per_origin_def
                  interval_es_po.verdict_report_def [symmetric]]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows [unfolded interval_es_po.verdict_report_def]])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (interval_es_po.admitted_contexts (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: interval_es_po.entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (interval_es_po.admitted_contexts (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_es_po.result (declared_global p) p) u ctx)"
      using interval_es_po.entry_state_activation_collect_sound_of_cover [OF cov]
      unfolding interval_es_po.gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (interval_es_po.result (declared_global p) p)"
      using interval_es_po.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def interval_es_po.result_def
          interval_es_po.sol_vars_def)
  qed
qed

theorem run_voblint_interval_entry_state_wpo_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_es_wpo.terminates (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_es_wpo.ctx_succ (declared_global p) p) []
                    (interval_es_wpo.sol_vars (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin) Ctx_EntryState
                  view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (interval_es_wpo.admitted_contexts (declared_global p) p) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_es_wpo.result (declared_global p) p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_entry_state_wpo p) = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_entry_state_wpo_def
                  interval_es_wpo.verdict_report_def [symmetric]]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows [unfolded interval_es_wpo.verdict_report_def]])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (interval_es_wpo.admitted_contexts (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: interval_es_wpo.entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (interval_es_wpo.admitted_contexts (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_es_wpo.result (declared_global p) p) u ctx)"
      using interval_es_wpo.entry_state_activation_collect_sound_of_cover [OF cov]
      unfolding interval_es_wpo.gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (interval_es_wpo.result (declared_global p) p)"
      using interval_es_wpo.vars_finite_of_terminates [OF solves]
      by (simp add: finite_analysis_result_def interval_es_wpo.result_def
          interval_es_wpo.sol_vars_def)
  qed
qed

subsection \<open>Int at an explicitly chosen join discipline\<close>

text \<open>
  The first configuration reached by naming a solver rather than taking the
  default. Int publishes both disciplines, so its join registration carries the
  same facts under unsuffixed names, and the argument is the warrowing one with
  those names substituted --- which is the point: the discipline is sealed
  inside the coverage endpoints and the endpoint proof never inspects it.
\<close>

abbreviation int_es_join_terminates where
  "int_es_join_terminates \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation int_es_join_ctx_succ where
  "int_es_join_ctx_succ \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

abbreviation int_es_join_vars where
  "int_es_join_vars \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

abbreviation int_es_join_ctx_rel where
  "int_es_join_ctx_rel \<equiv>
     routed_dg_analysis.admitted_contexts (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       (Analysis_Global ()) Activation_Seed exec_formals_route []
       TD_side_always_join_Interp_solve"

theorem run_voblint_int_entry_state_join_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_es_join_terminates (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (int_es_join_ctx_succ (declared_global p) p) []
                    (int_es_join_vars (declared_global p) p)"
      and ans: "run_voblint Int_Analysis (Some Solver_Join) Ctx_EntryState view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (int_es_join_ctx_rel (declared_global p) p) [] (prog_cfg p)
                   (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_int_entry_state_result p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "entry_state_output_of view (enter_int_dom_for Refine_Fixpoint) IntDomValue
          int_classify_check (analyse_int_entry_state_result p) p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_entry_state_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (int_es_join_ctx_rel (declared_global p) p) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (simp add: analyse_int_entry_state_ltr_collect_eq_Union_of_cover [OF cov])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (int_es_join_ctx_rel (declared_global p) p) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_int_entry_state_result p) u ctx)"
      using analyse_int_entry_state_sound_of_cover [OF cov]
      unfolding analyse_int_entry_state_result_def
                analyse_int_entry_state_result_for_def
                analyse_int_entry_state_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_int_entry_state_result p)"
      using analyse_int_entry_state_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_int_entry_state_result_def
          analyse_int_entry_state_result_for_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

subsection \<open>Interval at its explicitly chosen call-string disciplines\<close>

abbreviation interval_cs_join_terminates where
  "interval_cs_join_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation interval_cs_join_ctx_succ where
  "interval_cs_join_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_join_vars where
  "interval_cs_join_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation interval_cs_join_result where
  "interval_cs_join_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

theorem run_voblint_interval_call_string_join_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_cs_join_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_cs_join_ctx_succ k (declared_global p) p) []
                    (interval_cs_join_vars k (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_Join) (Ctx_CallString k) view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_cs_join_result k (declared_global p) p) v ctx
             = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_call_string_report_join k p)
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_call_string_report_join_def
                  routed_dg_pipeline.verdict_report_def]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_interval_call_string_ltr_collect_eq_Union_join
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_cs_join_result k (declared_global p) p) u ctx)"
      using analyse_interval_call_string_sound_of_cover_join [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_interval_call_string_gamma_reader_eq_lookup_join .
  next
    show "finite_analysis_result (interval_cs_join_result k (declared_global p) p)"
      using analyse_interval_call_string_vars_finite_join [OF solves]
      by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
          routed_dg_pipeline.sol_vars_def)
  qed
qed


abbreviation interval_cs_po_terminates where
  "interval_cs_po_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_per_origin)"

abbreviation interval_cs_po_ctx_succ where
  "interval_cs_po_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

abbreviation interval_cs_po_vars where
  "interval_cs_po_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

abbreviation interval_cs_po_result where
  "interval_cs_po_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_per_origin_Interp_solve"

theorem run_voblint_interval_call_string_po_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_cs_po_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_cs_po_ctx_succ k (declared_global p) p) []
                    (interval_cs_po_vars k (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_PerOrigin) (Ctx_CallString k) view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_cs_po_result k (declared_global p) p) v ctx
             = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_call_string_report_per_origin k p)
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_call_string_report_per_origin_def
                  routed_dg_pipeline.verdict_report_def]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_interval_call_string_ltr_collect_eq_Union_po
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_cs_po_result k (declared_global p) p) u ctx)"
      using analyse_interval_call_string_sound_of_cover_po [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_interval_call_string_gamma_reader_eq_lookup_po .
  next
    show "finite_analysis_result (interval_cs_po_result k (declared_global p) p)"
      using analyse_interval_call_string_vars_finite_po [OF solves]
      by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
          routed_dg_pipeline.sol_vars_def)
  qed
qed


abbreviation interval_cs_wpo_terminates where
  "interval_cs_wpo_terminates k \<equiv>
     routed_dg_pipeline.terminates ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_warrowing_per_origin)"

abbreviation interval_cs_wpo_ctx_succ where
  "interval_cs_wpo_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

abbreviation interval_cs_wpo_vars where
  "interval_cs_wpo_vars k \<equiv>
     routed_dg_pipeline.sol_vars ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

abbreviation interval_cs_wpo_result where
  "interval_cs_wpo_result k \<equiv>
     routed_dg_pipeline.result ivl_tf_st_for ivl_enter_st_for cinit_ivl_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_warrowing_per_origin_Interp_solve"

theorem run_voblint_interval_call_string_wpo_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "interval_cs_wpo_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p)
                    (interval_cs_wpo_ctx_succ k (declared_global p) p) []
                    (interval_cs_wpo_vars k (declared_global p) p)"
      and ans: "run_voblint Interval_Analysis (Some Solver_WarrowPerOrigin)
                  (Ctx_CallString k) view p = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (interval_cs_wpo_result k (declared_global p) p) v ctx
             = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "verdict_report_answer view (analyse_interval_call_string_report_wpo k p)
          = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_verdict_report_answer [OF this,
                unfolded analyse_interval_call_string_report_wpo_def
                  routed_dg_pipeline.verdict_report_def]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ interval_classify_check_proved interval_classify_check_refuted
          rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_interval_call_string_ltr_collect_eq_Union_wpo
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point
                 (lookup_context (interval_cs_wpo_result k (declared_global p) p) u ctx)"
      using analyse_interval_call_string_sound_of_cover_wpo [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_interval_call_string_gamma_reader_eq_lookup_wpo .
  next
    show "finite_analysis_result (interval_cs_wpo_result k (declared_global p) p)"
      using analyse_interval_call_string_vars_finite_wpo [OF solves]
      by (simp add: finite_analysis_result_def routed_dg_pipeline.result_def
          routed_dg_pipeline.sol_vars_def)
  qed
qed
subsection \<open>Int at an explicitly chosen join discipline, call-string\<close>

abbreviation int_cs_join_terminates where
  "int_cs_join_terminates k \<equiv>
     routed_dg_pipeline.terminates (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       (TD_side_upd_rule.solve_dom init_basic_ug_state update_global_always_join)"

abbreviation int_cs_join_ctx_succ where
  "int_cs_join_ctx_succ k \<equiv>
     routed_dg_pipeline.ctx_succ (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

abbreviation int_cs_join_vars where
  "int_cs_join_vars k \<equiv>
     routed_dg_pipeline.sol_vars (int_tf_st_for Refine_Fixpoint)
       (int_dom_enter_st_for Refine_Fixpoint) cinit_int_dom_st
       Call_String_Context.Global Call_String_Context.Seed (\<lambda>_. cs_route k) []
       TD_side_always_join_Interp_solve"

theorem run_voblint_int_call_string_join_source_sound:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and solves: "int_cs_join_terminates k (declared_global p) p"
      and cover: "ctx_vars_cover (prog_cfg p) (int_cs_join_ctx_succ k (declared_global p) p) []
                    (int_cs_join_vars k (declared_global p) p)"
      and ans: "run_voblint Int_Analysis (Some Solver_Join) (Ctx_CallString k) view p
                  = Analysed out"
  shows "\<exists>v stk ctx st.
           csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
         \<and> s \<in> activation_collect (declared_global p)
                   (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                   (prog_cfg p) (cinit_stores (declared_global p)) v ctx
         \<and> lookup_context (analyse_int_call_string_result k p) v ctx = Lifted st
         \<and> s \<in> \<lbrakk>st\<rbrakk>
         \<and> (\<forall>row \<in> set (out_checks out). row_point row = v \<longrightarrow>
              row_verdict row \<noteq> Dead
            \<and> (row_verdict row = Decided Check_Proved \<longrightarrow> truthy (aval (row_exp row) s))
            \<and> (row_verdict row = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval (row_exp row) s)))"
proof -
  note cov = solves cover
  from ans
  have "cs_output_of view IntDomValue int_classify_check
          (analyse_int_call_string_result k p) k p = Analysed out"
    by (simp add: run_voblint_def mk_analysis_config_def plan_answer_def split: if_splits)
  note rows = out_checks_of_cs_output [OF this]
  show ?thesis
  proof (rule ctx_source_sound_of_activation
      [OF wf s0 run _ _ _ int_classify_check_proved int_classify_check_refuted rows])
    fix u
    show "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) u
            \<subseteq> (\<Union>c. activation_collect (declared_global p)
                       (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
                       (prog_cfg p) (cinit_stores (declared_global p)) u c)"
      by (rule equalityD1
            [OF analyse_int_call_string_ltr_collect_eq_Union
                  [where ctx_fun = "cs_context k"]])
  next
    fix u ctx
    show "activation_collect (declared_global p)
             (call_context_rel_of_fun (\<lambda>u c t. cs_context k u c t)) []
             (prog_cfg p) (cinit_stores (declared_global p)) u ctx
            \<subseteq> gamma_point (lookup_context (analyse_int_call_string_result k p) u ctx)"
      using analyse_int_call_string_sound_of_cover [OF cov, where s = "\<lambda>u c t. t"]
      unfolding analyse_int_call_string_result_def
                analyse_int_call_string_result_for_def
                analyse_int_call_string_gamma_reader_eq_lookup .
  next
    show "finite_analysis_result (analyse_int_call_string_result k p)"
      using analyse_int_call_string_vars_finite [OF solves]
      by (simp add: finite_analysis_result_def analyse_int_call_string_result_def
          analyse_int_call_string_result_for_def
          routed_dg_pipeline.result_def routed_dg_pipeline.sol_vars_def)
  qed
qed

end
