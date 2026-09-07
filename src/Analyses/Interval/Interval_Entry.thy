theory Interval_Entry
  imports Interval_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>Interval codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  \<open>analyse_interval_dg_eqs_for\<close>/\<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close>
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Exec_Sound\<close>) and \<open>analyse_interval_td_report_for\<close>/
  \<open>analyse_interval_td_report\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) are pure
  computation, so they live one session earlier (Analysis).
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

text \<open>
  \<open>analyse_interval_td_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_interval_td_result_for\<close>'s \<^type>\<open>analysis_result\<close> table, which is
  now \<^const>\<open>analyse_interval_ctx_result_warrow_for\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_td_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>interval_conf_result_node_sound_warrow\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from \<open>p_reg\<close>/\<open>analyse_interval_dg_for\<close> --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_td_result_node_sound_for:
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "interval_conf_sol_prog_warrow pgs p
      = interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p)"
    unfolding interval_conf_sol_prog_warrow_def interval_conf_eqs_prog_def interval_conf_sol_warrow_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "interval_conf_terminates_warrow pgs empty_pred (prog_table p) (prog_procs p)"
    using solve unfolding interval_conf_terminates_prog_warrow_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores pgs \<subseteq> interval_gamma pgs (Lifted cinit_ivl_st) Bot"
    by (rule interval_conf_cinit_le_cinit_ivl_st_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have node_sound: "activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p)))
                 (fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for pgs)))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule interval_conf_result_node_sound_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_td_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred (locals (snd (interval_conf_sol_prog_warrow pgs p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_interval_td_result_for_def analyse_interval_ctx_result_warrow_for_def lookup_context_def
              empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p)))
             (fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()
      = (if (v, ()) \<in> fst (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))
         then readback_result_value pgs
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_warrow pgs empty_pred (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
    by (rule interval_conf_analyse_result_eq_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred (locals (snd (interval_conf_sol_prog_warrow pgs p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol_prog_warrow pgs p))
             (fst (interval_conf_sol_prog_warrow pgs p)) (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_td_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_td_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_td_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def surface_unfold] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_td_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_td_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_td_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def surface_unfold] interval_classify_check_refuted node_sound])
qed

subsection \<open>Coverage as one checkable side condition\<close>

text \<open>
  The four coverage facts the bridges above take apart are the four conjuncts of
  \<^const>\<open>vars_cover\<close>, read at the one context this routed solve uses. Bundling
  them is what makes the side condition decidable in a single step:
  \<^const>\<open>vars_cover_exec\<close> walks the two edge enumerations, so a caller discharges
  coverage \<open>by eval\<close> instead of by four hand-written case analyses over the
  solved key set.
\<close>

lemma interval_conf_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p) (fst (interval_conf_sol_prog_warrow pgs p))"
  shows "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow pgs p))"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

lemma analyse_interval_td_result_node_sound_of_cover:
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow pgs p))"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof (rule analyse_interval_td_result_node_sound_for[OF solve])
  show "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
    by (rule vars_cover_entryD[OF cover])
next
  fix u a w ctx
  assume e: "(u, a, w) \<in> intra (prog_cfg p)"
  show "(w, ctx) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
    using vars_cover_edgeD[OF cover e] by simp
next
  fix u ctx dst fs as q k
  assume e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
    by (rule vars_cover_enterD[OF cover e])
next
  fix cl c1 dst fs as q k
  assume e: "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(k, c1) \<in> fst (interval_conf_sol_prog_warrow pgs p)"
    using vars_cover_combineD[OF cover e] by simp
qed

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  Interval's counterparts of Sign's \<open>analyse_sign_source_sound_for\<close> and
  \<open>analyse_sign_completed_run_sound_for\<close>: run the source program, stop anywhere, and
  the store you are holding is described by the entry the analysis returned for the
  program point you are standing at; a run that finishes lands in the entry at
  \<^const>\<open>cfg_exit\<close>. The simulation \<^const>\<open>csim\<close> is what names that point.

  No new reasoning happens here. \<open>source_sound_from_ltr_collecting_cap\<close> and
  \<open>source_completes_ltr_collect_exit\<close>
  (\<^theory>\<open>Voblint_Soundness.Source_Activation_Sound\<close>) supply the source side, and
  \<open>analyse_interval_td_result_node_sound_of_cover\<close> is the per-node cap they take.
\<close>

theorem analyse_interval_td_source_sound_for:
  fixes s0 s :: store
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  show ?thesis
    unfolding cfg_eq
    by (rule source_sound_from_ltr_collecting_cap[OF wf s0 run])
       (use analyse_interval_td_result_node_sound_of_cover[OF solve cover] in
          \<open>simp add: cfg_eq\<close>)
qed

theorem analyse_interval_td_completed_run_sound_for:
  fixes s0 s :: store
  assumes solve: "interval_conf_terminates_prog_warrow pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (interval_conf_sol_prog_warrow pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result_for pgs p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) (cfg_exit (prog_cfg p))"
    using source_completes_ltr_collect_exit[OF wf s0 run] unfolding cfg_eq .
  then show ?thesis
    using analyse_interval_td_result_node_sound_of_cover[OF solve cover] by blast
qed

end

text \<open>
  \<open>analyse_interval_dg_eqs\<close>/\<open>analyse_interval_dg\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Exec_Sound\<close>)
  and \<open>analyse_interval_td_report\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Checks\<close>) are the
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances the context above's \<open>_for\<close> layer already
  feeds, matching \<open>analyse_sign_report_sound_proved\<close>'s own shape.
  \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close> discharges the context's \<open>reserved\<close>
  assumption from the concrete program's own well-formedness fact --- the same
  instantiation step Sign's own entry-point corollaries use.
\<close>

corollary analyse_interval_td_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_td_report_def]])

corollary analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_warrow (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_td_report_def]])

text \<open>
  The headline pair, at \<^const>\<open>declared_global\<close> \<open>p\<close> and over
  \<^const>\<open>analyse_interval_td_result\<close> --- the table the runtime API hands back on the
  branch \<open>analyse\<close> takes for Interval, mirroring Sign's
  \<open>analyse_sign_source_sound\<close>/\<open>analyse_sign_completed_run_sound\<close>.  Two side conditions
  survive, and both are decided per program rather than proved once: the solver reached
  a fixpoint (\<^const>\<open>interval_conf_terminates_prog_warrow\<close>), and it solved enough keys
  (\<^const>\<open>vars_cover\<close>, decidable through \<open>interval_conf_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_interval_td_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_interval_td_result_def
  by (rule analyse_interval_td_source_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

corollary analyse_interval_td_completed_run_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "interval_conf_terminates_prog_warrow (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (interval_conf_sol_prog_warrow (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_interval_td_result p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_interval_td_result_def
  by (rule analyse_interval_td_completed_run_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

section \<open>Solver-choice soundness: join and per-origin update rules\<close>

text \<open>
  Solver-choice siblings of the warrowing soundness above: the join and per-origin
  update rules each read their own routed-unit result table
  (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>). Each block below writes
  \<^term>\<open>declared_global p\<close> out in full rather than reusing the \<open>pgs\<close> abbreviation:
  \<open>pgs\<close> is local to the first context block above and, once that block closes, its global
  residue takes \<open>p\<close> as an explicit argument, so a second same-named local abbreviation here
  would clash.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin


text \<open>
  \<open>analyse_interval_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_interval_join_result_for\<close>'s \<^type>\<open>analysis_result\<close> table, which is
  now \<^const>\<open>analyse_interval_ctx_result_for\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_join_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>interval_conf_result_node_sound\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from the flat \<open>analyse_interval_dg_join_for\<close> route --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_join_result_node_sound_for:
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for (declared_global p) s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "interval_conf_sol_prog (declared_global p) p
      = interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p)"
    unfolding interval_conf_sol_prog_def interval_conf_eqs_prog_def interval_conf_sol_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "interval_conf_terminates (declared_global p) empty_pred (prog_table p) (prog_procs p)"
    using solve unfolding interval_conf_terminates_prog_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores (declared_global p)
        \<subseteq> interval_gamma (declared_global p) (Lifted cinit_ivl_st) Bot"
    by (rule interval_conf_cinit_le_cinit_ivl_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have node_sound: "activation_collect (declared_global p) (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores (declared_global p)) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p)))
                 (fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for (declared_global p))))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule interval_conf_result_node_sound
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      = activation_collect (declared_global p) (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores (declared_global p)) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_join_result_for (declared_global p) p) v ()
      = (if (v, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_prog (declared_global p) p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_interval_join_result_for_def analyse_interval_ctx_result_for_def lookup_context_def
              empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p)))
             (fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for (declared_global p))))
          v ()
      = (if (v, ()) \<in> fst (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol (declared_global p) empty_pred (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
    by (rule interval_conf_analyse_result_eq[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_prog (declared_global p) p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol_prog (declared_global p) p))
             (fst (interval_conf_sol_prog (declared_global p) p))
             (map_lift (fun_of_resolved_st_q_for (declared_global p))))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_join_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def surface_unfold] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_join_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def surface_unfold] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_def]])

corollary analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_def]])

text \<open>Per-origin sibling of the join block above: the vendored solver has the identical
  \<open>part_post_solution_of_solve_c\<close> bridge fact under \<^const>\<open>TD_side_per_origin_Interp.solve\<close>, so
  the same proof shape carries over verbatim.\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin


text \<open>
  \<open>analyse_interval_report_per_origin_for\<close> reads its per-node state through
  \<^const>\<open>analyse_interval_per_origin_result_for\<close>'s \<^type>\<open>analysis_result\<close> table, which is
  now \<^const>\<open>analyse_interval_ctx_result_per_origin_for\<close> (\<^theory>\<open>Voblint_Analysis_Interval.Interval_Analyses\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_per_origin_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>interval_conf_result_node_sound_per_origin\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from the flat \<open>analyse_interval_dg_per_origin_for\<close> route --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_per_origin_result_node_sound_for:
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
  shows "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for (declared_global p) s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "interval_conf_sol_prog_per_origin (declared_global p) p
      = interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)"
    unfolding interval_conf_sol_prog_per_origin_def interval_conf_eqs_prog_def interval_conf_sol_per_origin_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "interval_conf_terminates_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)"
    using solve unfolding interval_conf_terminates_prog_per_origin_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores (declared_global p)
        \<subseteq> interval_gamma (declared_global p) (Lifted cinit_ivl_st) Bot"
    by (rule interval_conf_cinit_le_cinit_ivl_st_per_origin[OF solves' exact entry_cov' fwd_ok' call_fwd_ok'
                                                     comb_fwd_ok'])
  have node_sound: "activation_collect (declared_global p) (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores (declared_global p)) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)))
                 (fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for (declared_global p))))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule interval_conf_result_node_sound_per_origin
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      = activation_collect (declared_global p) (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores (declared_global p)) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v ()
      = (if (v, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_prog_per_origin (declared_global p) p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_interval_per_origin_result_for_def analyse_interval_ctx_result_per_origin_for_def
              lookup_context_def empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)))
             (fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for (declared_global p))))
          v ()
      = (if (v, ()) \<in> fst (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_per_origin (declared_global p) empty_pred (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
    by (rule interval_conf_analyse_result_eq_per_origin[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
         then readback_result_value (declared_global p)
                (canonicalize_lift empty_pred
                  (locals (snd (interval_conf_sol_prog_per_origin (declared_global p) p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (interval_conf_sol_prog_per_origin (declared_global p) p))
             (fst (interval_conf_sol_prog_per_origin (declared_global p) p))
             (map_lift (fun_of_resolved_st_q_for (declared_global p))))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_report_per_origin_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_per_origin_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
              interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_per_origin_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_interval_per_origin_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
              interval_classify_check_refuted node_sound])
qed
end

corollary analyse_interval_report_per_origin_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_per_origin_def]])

corollary analyse_interval_report_per_origin_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "interval_conf_terminates_prog_per_origin (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (interval_conf_sol_prog_per_origin (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_per_origin_def]])

end
