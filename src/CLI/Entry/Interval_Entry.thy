theory Interval_Entry
  imports Voblint_Analysis.Interval_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>Interval codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  \<open>analyse_interval_dg_eqs_for\<close>/\<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>) and \<open>analyse_interval_td_report_for\<close>/
  \<open>analyse_interval_td_report\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) are pure
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
  now \<^const>\<open>analyse_interval_ctx_result_warrow_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_td_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>ictx_activation_collect_sound_warrow\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from \<open>p_reg\<close>/\<open>analyse_interval_dg_for\<close> --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_td_result_node_sound_for:
  assumes solve: "ictx_terminates_prog_warrow pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "ictx_sol_prog_warrow pgs prog_main_name p
      = ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding ictx_sol_prog_warrow_def ictx_eqs_prog_def ictx_sol_warrow_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "ictx_terminates_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding ictx_terminates_prog_warrow_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores pgs \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for pgs) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for pgs) (Bot::ivl exec_dg_st lifted))"
    using ictx_cinit_le_cinit_ivl_st_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect pgs (admiss_exact enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (ictx_sigma_abs_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                 (fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
    by (rule ictx_result_node_sound_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      = activation_collect pgs (admiss_exact enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_td_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (ictx_sol_prog_warrow pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_interval_td_result_for_def analyse_interval_ctx_result_warrow_for_def lookup_context_def
              is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
          v ()
      = (if (v, ()) \<in> fst (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                    (Inl (v, ())))))
         else Unreachable)"
    by (rule ictx_analyse_result_eq_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (ictx_sol_prog_warrow pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_warrow pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol_prog_warrow pgs prog_main_name p)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_td_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_td_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_td_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def surface_unfold] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_td_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow pgs prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_td_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_td_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def surface_unfold] interval_classify_check_refuted node_sound])
qed

end

text \<open>
  \<open>analyse_interval_dg_eqs\<close>/\<open>analyse_interval_dg\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>)
  and \<open>analyse_interval_td_report\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) are the
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances the context above's \<open>_for\<close> layer already
  feeds, matching \<open>analyse_sign_sound\<close>/\<open>analyse_sign_report_sound_proved\<close>'s own shape.
  \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close> discharges the context's \<open>reserved\<close>
  assumption from the concrete program's own well-formedness fact --- the same
  instantiation step \<open>analyse_sign_sound\<close> uses.
\<close>

corollary analyse_interval_td_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_warrow (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_td_report_def]])

corollary analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_warrow (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_td_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_td_report_def]])

section \<open>Solver-choice soundness: join and per-origin update rules\<close>

text \<open>
  Solver-choice siblings of the warrowing soundness above: the join and per-origin
  update rules each read their own routed-unit result table
  (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>). Each block below writes
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
  now \<^const>\<open>analyse_interval_ctx_result_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_join_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>ictx_activation_collect_sound\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from \<open>p_reg_join\<close>/\<open>analyse_interval_dg_join_for\<close> --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_join_result_node_sound_for:
  assumes solve: "ictx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for (declared_global p) s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "ictx_sol_prog (declared_global p) prog_main_name p
      = ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding ictx_sol_prog_def ictx_eqs_prog_def ictx_sol_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "ictx_terminates (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding ictx_terminates_prog_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores (declared_global p) \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for (declared_global p)) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for (declared_global p)) (Bot::ivl exec_dg_st lifted))"
    using ictx_cinit_le_cinit_ivl_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect (declared_global p) (admiss_exact enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores (declared_global p)) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (ictx_sigma_abs (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                 (fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
    by (rule ictx_result_node_sound
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      = activation_collect (declared_global p) (admiss_exact enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores (declared_global p)) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_join_result_for (declared_global p) p) v ()
      = (if (v, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog (declared_global p) prog_main_name p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_interval_join_result_for_def analyse_interval_ctx_result_for_def lookup_context_def
              is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
          v ()
      = (if (v, ()) \<in> fst (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                    (Inl (v, ())))))
         else Unreachable)"
    by (rule ictx_analyse_result_eq[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog (declared_global p) prog_main_name p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol_prog (declared_global p) prog_main_name p)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_join_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def surface_unfold] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_join_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def surface_unfold] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_def]])

corollary analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
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
  now \<^const>\<open>analyse_interval_ctx_result_per_origin_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Ctx_None_Sound\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_interval_per_origin_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<open>ictx_activation_collect_sound_per_origin\<close> (the routed
  spine's own activation-indexed collecting soundness) composed with
  \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse
  to \<^const>\<open>ltr_collect\<close>) rather than from \<open>p_reg_per_origin\<close>/\<open>analyse_interval_dg_per_origin_for\<close> --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_interval_per_origin_result_node_sound_for:
  assumes solve: "ictx_terminates_prog_per_origin (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for (declared_global p) s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "ictx_sol_prog_per_origin (declared_global p) prog_main_name p
      = ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding ictx_sol_prog_per_origin_def ictx_eqs_prog_def ictx_sol_per_origin_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "ictx_terminates_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding ictx_terminates_prog_per_origin_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores (declared_global p) \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for (declared_global p)) (Lifted cinit_ivl_st))
        (map_lift (fun_of_resolved_st_q_for (declared_global p)) (Bot::ivl exec_dg_st lifted))"
    using ictx_cinit_le_cinit_ivl_st_per_origin[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect (declared_global p) (admiss_exact enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores (declared_global p)) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (ictx_sigma_abs_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                 (fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
    by (rule ictx_result_node_sound_per_origin
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      = activation_collect (declared_global p) (admiss_exact enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores (declared_global p)) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v ()
      = (if (v, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog_per_origin (declared_global p) prog_main_name p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_interval_per_origin_result_for_def analyse_interval_ctx_result_per_origin_for_def
              lookup_context_def is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
          v ()
      = (if (v, ()) \<in> fst (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                    (Inl (v, ())))))
         else Unreachable)"
    by (rule ictx_analyse_result_eq_per_origin[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
         then normalize_point (declared_global p)
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog_per_origin (declared_global p) prog_main_name p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_per_origin (declared_global p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_interval_report_per_origin_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_per_origin (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_per_origin_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
              interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_per_origin_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_per_origin (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_per_origin_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def surface_unfold]
              interval_classify_check_refuted node_sound])
qed
end

corollary analyse_interval_report_per_origin_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_per_origin (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_per_origin_def]])

corollary analyse_interval_report_per_origin_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_per_origin (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_per_origin (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_interval_report_per_origin_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_interval_report_per_origin_def]])

end
