theory Int_Entry
  imports "Voblint_Analysis.Int_Checks" "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>Int codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  \<open>analyse_int_dg_eqs_for\<close>/\<open>analyse_int_dg_for\<close>/\<open>analyse_int_dg_env_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Sound\<close>) and \<open>analyse_int_report_for\<close>/\<open>analyse_int_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Int_Checks\<close>) are pure computation, so they live one session
  earlier (Analysis).
\<close>

context
  fixes p :: imp_prog and mode :: refine_mode
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

text \<open>
  \<open>analyse_int_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_int_ctx_result_warrow_for\<close>'s \<^type>\<open>analysis_result\<close> table directly
  (\<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>): the routed-unit producer's own solved
  table, at \<open>mode\<close> and \<open>prog_main_name\<close>. \<open>analyse_int_ctx_result_warrow_node_sound_for\<close>
  below is the node-soundness bridge for that table, built from
  \<open>ictx_activation_collect_sound_warrow\<close> (the routed spine's own activation-indexed
  collecting soundness) composed with \<open>activation_collect_unit_eq_ltr_collect\<close> (the
  unit-context collapse to \<^const>\<open>ltr_collect\<close>) --- the routed spine needs no
  \<open>wf_compile_input\<close>/finiteness/node-membership premise, so this bridge only takes the
  four coverage-and-termination facts the routed solve genuinely turns on.
\<close>


text \<open>
  \<open>analyse_int_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_int_ctx_result_warrow_for\<close>'s \<^type>\<open>analysis_result\<close> table directly
  (\<^theory>\<open>Voblint_Analysis.Int_Ctx_None_Sound\<close>): the routed-unit producer's own solved
  table, at \<open>mode\<close> and \<open>prog_main_name\<close>. \<open>analyse_int_ctx_result_warrow_node_sound_for\<close>
  below is the node-soundness bridge for that table, built from
  \<open>ictx_activation_collect_sound_warrow\<close> (the routed spine's own activation-indexed
  collecting soundness) composed with \<open>activation_collect_unit_eq_ltr_collect\<close> (the
  unit-context collapse to \<^const>\<open>ltr_collect\<close>) rather than from
  \<open>p_reg\<close>/\<open>analyse_int_dg_for\<close> --- the routed spine needs no
  \<open>wf_compile_input\<close>/finiteness/node-membership premise, so this bridge only takes the
  four coverage-and-termination facts the routed solve genuinely turns on.
\<close>

lemma analyse_int_ctx_result_warrow_node_sound_for:
  assumes solve: "ictx_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "int_dom resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "ictx_sol_prog_warrow mode pgs p
      = ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p)"
    unfolding ictx_sol_prog_warrow_def ictx_eqs_prog_def ictx_sol_warrow_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "ictx_terminates_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p)"
    using solve unfolding ictx_terminates_prog_warrow_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores pgs \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for pgs) (Lifted cinit_int_dom_st))
        (map_lift (fun_of_resolved_st_q_for pgs) (Bot::int_dom exec_dg_st lifted))"
    using ictx_cinit_le_cinit_int_dom_st_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect pgs enterc_unit ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (ictx_sigma_abs_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
                 (fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))) id)
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
    by (rule ictx_result_node_sound_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs enterc_unit ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v ()
      = (if (v, ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog_warrow mode pgs p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_int_ctx_result_warrow_for_def lookup_context_def is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
             (fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))) id)
          v ()
      = (if (v, ()) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Unreachable)"
    by (rule ictx_analyse_result_eq_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (ictx_sol_prog_warrow mode pgs p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (ictx_sigma_abs_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p))
             (fst (ictx_sol_prog_warrow mode pgs p)) id)
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_int_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_int_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def surface_unfold] int_classify_check_proved node_sound])
qed

theorem analyse_int_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_int_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def surface_unfold] int_classify_check_refuted node_sound])
qed

end

text \<open>
  \<open>analyse_int_report\<close> (\<^theory>\<open>Voblint_Analysis.Int_Checks\<close>) is the \<^const>\<open>declared_global\<close>
  \<open>p\<close> convenience instance the context above's \<open>_for\<close> layer already feeds, pinned at
  \<^const>\<open>Refine_Fixpoint\<close>, matching \<open>analyse_interval_td_report_sound_proved\<close>'s own
  shape. \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close> discharges the context's
  \<open>reserved\<close> assumption from the concrete program's own well-formedness fact --- the same
  instantiation step Interval's own corollary uses.
\<close>

corollary analyse_int_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "ictx_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_int_report_def
  by (rule analyse_int_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_int_report_def]])

corollary analyse_int_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "ictx_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_int_report_def
  by (rule analyse_int_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_int_report_def]])

end

