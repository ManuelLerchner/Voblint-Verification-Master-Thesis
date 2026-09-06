theory Parity_Entry
  imports Voblint_Analysis_Parity.Parity_Checks "Voblint_Soundness.Run_Analysis_Sound"
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
  assumes solve: "pctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (pctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_parity_result_for pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "parity resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "pctx_sol_prog pgs p
      = pctx_sol pgs empty_pred (prog_table p) (prog_procs p)"
    unfolding pctx_sol_prog_def pctx_eqs_prog_def pctx_sol_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "pctx_terminates pgs empty_pred (prog_table p) (prog_procs p)"
    using solve unfolding pctx_terminates_prog_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have ltr_eq: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have s0_sound: "cinit_stores pgs \<subseteq> pctx_gamma pgs (Lifted cinit_parity_st) Bot"
    by (rule pctx_cinit_le_cinit_parity_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have node_sound: "activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (pctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
                 (fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for pgs)))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule pctx_result_node_sound
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'
              entry_cov' s0_sound])
  have result_eq: "lookup_context (analyse_parity_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (pctx_sol_prog pgs p)
         then normalize_point pgs
                (canonicalize_lift empty_pred (locals (snd (pctx_sol_prog pgs p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_parity_result_for_def analyse_parity_ctx_result_for_def lookup_context_def empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (pctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
             (fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()
      = (if (v, ()) \<in> fst (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))
         then normalize_point pgs
                (canonicalize_lift empty_pred
                  (locals (snd (pctx_sol pgs empty_pred (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
    by (rule pctx_analyse_result_eq
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (pctx_sol_prog pgs p)
         then normalize_point pgs
                (canonicalize_lift empty_pred (locals (snd (pctx_sol_prog pgs p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (pctx_sol_prog pgs p))
             (fst (pctx_sol_prog pgs p)) (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_parity_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "pctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (pctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_parity_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_parity_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_parity_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_parity_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = parity_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: parity abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_parity_report_for_def surface_unfold] parity_classify_check_proved node_sound])
qed

theorem analyse_parity_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "pctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (pctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog pgs p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_parity_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_parity_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_parity_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_parity_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = parity_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: parity abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_parity_report_for_def surface_unfold] parity_classify_check_refuted node_sound])
qed

end

text \<open>
  \<^const>\<open>analyse_parity_report\<close>'s own soundness corollaries: the check-report layer's
  \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances, matching Sign's
  \<open>analyse_sign_report_sound_proved\<close>/\<open>_refuted\<close>.
\<close>

corollary analyse_parity_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "pctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_parity_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_parity_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_parity_report_def]])

corollary analyse_parity_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "pctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (pctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (pctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_parity_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_parity_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_parity_report_def]])

end
