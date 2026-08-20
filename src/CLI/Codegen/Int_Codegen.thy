theory Int_Codegen
  imports "Voblint_Analysis.Int_Checks" "Voblint_Formalization.Run_Analysis_Sound"
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
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Ctx_Sound\<close>): the routed-unit producer's own solved
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
  (\<^theory>\<open>Voblint_Analysis.Int_Exec_Ctx_Sound\<close>): the routed-unit producer's own solved
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
  assumes solve: "ictx_terminates_prog_warrow mode pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "int_dom resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "ictx_sol_prog_warrow mode pgs prog_main_name p
      = ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding ictx_sol_prog_warrow_def ictx_eqs_prog_def ictx_sol_warrow_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "ictx_terminates_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding ictx_terminates_prog_warrow_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have sg_eq0: "ictx_sg_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)
      = ictx_sg_exec_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule ictx_sg_warrow_def[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have act_sound: "activation_collect pgs (admiss_exact enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()
      \<subseteq> gamma_state_lift
          (ictx_sg_exec_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p) (Inl (v, ())))"
    using ictx_activation_collect_sound_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    unfolding sg_eq0 .
  have ltr_eq: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      = activation_collect pgs (admiss_exact enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have bot_sound2: "\<And>s::int_dom resolved_st_q. resolved_st_q_is_bot_for (declared_global_vars p) s
      \<Longrightarrow> is_bot_state (fun_of_resolved_st_q_for pgs s)"
    using exact unfolding is_bot_pred_def by blast
  have final: "gamma_state_lift
        (ictx_sg_exec_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p) (Inl (v, ())))
      \<subseteq> gamma_point (lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v ())"
  proof (cases "(v, ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)")
    case True
    let ?q = "locals (snd (ictx_sol_prog_warrow mode pgs prog_main_name p) (Inl (v, ())))"
    have lookup_eq: "lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v ()
        = normalize_point pgs (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p)) ?q)"
      unfolding analyse_int_ctx_result_warrow_for_def lookup_context_def
      using True by simp
    have sg_exec_eq: "ictx_sg_exec_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p) (Inl (v, ()))
        = map_lift (fun_of_resolved_st_q_for pgs) ?q"
      unfolding ictx_sg_exec_warrow_def ictx_sigma_abs_exec_warrow_def sol_eq[symmetric]
      using True by simp
    have gpeq: "gamma_point (normalize_point pgs (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p)) ?q))
        = gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) ?q)"
      by (rule gamma_point_normalize_point_canonicalize_lift[OF bot_sound2])
    show ?thesis
      unfolding sg_exec_eq lookup_eq gpeq by (rule order_refl)
  next
    case False
    have uncovered: "(v, ())
        \<notin> fst (ictx_sol_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      using False unfolding sol_eq[symmetric] .
    have lhs_empty: "gamma_state_lift
          (ictx_sg_exec_warrow mode is_bot_pred pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p) (Inl (v, ())))
        = {}"
      unfolding ictx_sg_exec_warrow_def using uncovered by simp
    show ?thesis unfolding lhs_empty by simp
  qed
  show ?thesis
    unfolding ltr_eq gamma_state_of_reachable_env using act_sound final by (rule subset_trans)
qed

theorem analyse_int_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow mode pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_int_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def Let_def] int_classify_check_proved node_sound])
qed

theorem analyse_int_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "ictx_terminates_prog_warrow mode pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow mode pgs prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_int_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs prog_main_name p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def Let_def] int_classify_check_refuted node_sound])
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
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_int_report_def
  by (rule analyse_int_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_int_report_def]])

corollary analyse_int_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "ictx_terminates_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (ictx_sol_prog_warrow Refine_Fixpoint (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_int_report_def
  by (rule analyse_int_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_int_report_def]])

end

