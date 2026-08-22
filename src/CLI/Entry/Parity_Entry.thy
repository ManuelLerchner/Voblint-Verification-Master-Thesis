theory Parity_Entry
  imports Voblint_Analysis.Parity_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

hide_const phase.N

section \<open>Parity codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  The Parity analogue of \<open>Sign_Entry\<close>'s node- and report-soundness bridges, for the
  branch the unified dispatcher takes when the configured domain is Parity.  Everything
  here is packaging: \<open>Parity_Checks.pctx_result_node_sound\<close> and
  \<open>Parity_Checks.pctx_analyse_result_eq\<close> already carry the argument, inside the
  six-assumption adapter context; the theorems below re-express them against the public
  \<^const>\<open>analyse_parity_result_for\<close> / \<^const>\<open>analyse_parity_report_for\<close> surface, taking
  only the four coverage-and-termination facts a caller can compute.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

lemma analyse_parity_result_node_sound_for:
  assumes solve: "pctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_parity_result_for pgs p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "parity resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "pctx_sol_prog pgs prog_main_name p
      = pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding pctx_sol_prog_def pctx_eqs_prog_def pctx_sol_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "pctx_terminates pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding pctx_terminates_prog_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have ltr_eq: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      = activation_collect pgs (admiss_exact enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have s0_sound: "cinit_stores pgs \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for pgs) (Lifted cinit_parity_st))
        (map_lift (fun_of_resolved_st_q_for pgs) (Bot::parity exec_dg_st lifted))"
    using pctx_cinit_le_cinit_parity_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect pgs (admiss_exact enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (pctx_sigma_abs pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                 (fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
    by (rule pctx_result_node_sound
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'
              entry_cov' s0_sound])
  have result_eq: "lookup_context (analyse_parity_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (pctx_sol_prog pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_parity_result_for_def analyse_parity_ctx_result_for_def lookup_context_def is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (pctx_sigma_abs pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
          v ()
      = (if (v, ()) \<in> fst (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (pctx_sol pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                    (Inl (v, ())))))
         else Unreachable)"
    by (rule pctx_analyse_result_eq
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (pctx_sol_prog pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (pctx_sigma_abs pgs is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (pctx_sol_prog pgs prog_main_name p)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_parity_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "pctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_parity_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_parity_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_parity_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_parity_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = parity_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: parity abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_parity_report_for_def Let_def] parity_classify_check_proved node_sound])
qed

theorem analyse_parity_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "pctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_parity_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_parity_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_parity_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_parity_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = parity_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: parity abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_parity_report_for_def Let_def] parity_classify_check_refuted node_sound])
qed

end

text \<open>
  \<^const>\<open>analyse_parity_report\<close>'s own soundness corollaries: the check-report layer's
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances, matching Sign's
  \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close>.
\<close>

corollary analyse_parity_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "pctx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_parity_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_parity_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_parity_report_def]])

corollary analyse_parity_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "pctx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_parity_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_parity_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_parity_report_def]])

end
