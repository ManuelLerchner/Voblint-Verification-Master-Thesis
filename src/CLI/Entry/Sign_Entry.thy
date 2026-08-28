theory Sign_Entry
  imports Voblint_Analysis.Sign_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

hide_const phase.N

section \<open>Sign codegen API: an arbitrary VIMP program, and its OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>activation_collect_unit_eq_ltr_collect\<close> (\<^theory>\<open>Voblint_Core.Routed_Context_Unit\<close>,
  reached transitively through \<open>Sign_Ctx_None_Sound\<close>) is the domain-generic unit-context
  collapse this file's own node-soundness bridge below needs: no Sign-specific fact is used
  in its proof, so it is proved once there rather than re-derived per domain -- Interval's
  routed cutover cites the same lemma.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

text \<open>
  \<open>analyse_sign_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_sign_result_for\<close>'s \<^type>\<open>analysis_result\<close> table, which is
  now \<^const>\<open>analyse_sign_ctx_result_for\<close> (\<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_sign_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>'s generic
  \<open>analyse_result_node_sound\<close> (\<open>Sign_Checks.sctx_result_node_sound\<close>), composed
  with \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse to
  \<^const>\<open>ltr_collect\<close>) and \<open>Sign_Checks.sctx_analyse_result_eq\<close> (identifying the
  adapter's own result reading with \<^const>\<open>analyse_sign_ctx_result_for\<close>'s
  \<open>normalize_point\<close>/\<open>canonicalize_lift\<close> construction) rather than re-deriving
  \<open>routed_context_hetero\<close>'s coverage/sigma-projection argument by hand --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_sign_result_node_sound_for:
  assumes solve: "sctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
  shows "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_sign_result_for pgs p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  define is_bot_pred :: "sign resolved_st_q \<Rightarrow> bool"
    where "is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
    unfolding is_bot_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "sctx_sol_prog pgs prog_main_name p
      = sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    unfolding sctx_sol_prog_def sctx_eqs_prog_def sctx_sol_def is_bot_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg prog_main_name p = compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    by (rule prog_cfg_def)
  have solves': "sctx_terminates pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
    using solve unfolding sctx_terminates_prog_def is_bot_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
      \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
      \<Longrightarrow> (k, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have ltr_eq: "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      = activation_collect (prog_tyenv p) pgs (admiss_exact enterc_unit) ()
          (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have s0_sound: "cinit_stores pgs \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for pgs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for pgs) (Bot::sign exec_dg_st lifted))"
    using sctx_cinit_le_cinit_sign_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok']
    by (simp add: gamma_dg_base_def)
  have node_sound: "activation_collect (prog_tyenv p) pgs (admiss_exact enterc_unit) ()
        (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (sctx_sigma_abs pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                 (fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
              v () of
            Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
  proof (rule sctx_result_node_sound)
    show "sctx_terminates pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      by (rule solves')
    show "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
      by (rule exact)
    show "(cfg_entry (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
        \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule entry_cov')
    show "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (u, a, v) \<in> intra (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule fwd_ok')
    show "\<And>u ctx dst pars args pa cont.
        (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (FunctionEntry pa, ()) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule call_fwd_ok')
    show "\<And>cl c1 dst pars args pa cont.
        (cl, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule comb_fwd_ok')
    show "(cfg_entry (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
        \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule entry_cov')
    show "cinit_stores pgs \<subseteq> gamma_dg_base
        (map_lift (fun_of_resolved_st_q_for pgs) (Lifted cinit_sign_st))
        (map_lift (fun_of_resolved_st_q_for pgs) (Bot::sign exec_dg_st lifted))"
      by (rule s0_sound)
  qed
  have result_eq: "lookup_context (analyse_sign_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (sctx_sol_prog pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)"
    unfolding analyse_sign_result_for_def analyse_sign_ctx_result_for_def lookup_context_def is_bot_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (sctx_sigma_abs pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))))
          v ()
      = (if (v, ()) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
         then normalize_point pgs
                (canonicalize_lift is_bot_pred
                  (locals (snd (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
                    (Inl (v, ())))))
         else Unreachable)"
  proof (rule sctx_analyse_result_eq)
    show "sctx_terminates pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      by (rule solves')
    show "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for pgs s)"
      by (rule exact)
    show "(cfg_entry (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)), ())
        \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule entry_cov')
    show "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (u, a, v) \<in> intra (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule fwd_ok')
    show "\<And>u ctx dst pars args pa cont.
        (u, ctx) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (FunctionEntry pa, ()) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule call_fwd_ok')
    show "\<And>cl c1 dst pars args pa cont.
        (cl, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_tyenv p) (prog_table p) (prog_procs p) prog_main_name (prog_main p))
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))"
      by (rule comb_fwd_ok')
  qed
  have adapter_eq: "(if (v, ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)
         then normalize_point pgs
                (canonicalize_lift is_bot_pred (locals (snd (sctx_sol_prog pgs prog_main_name p) (Inl (v, ())))))
         else Unreachable)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (sctx_sigma_abs pgs (prog_tyenv p) is_bot_pred (prog_table p) (prog_procs p) prog_main_name (prog_main p))
             (fst (sctx_sol_prog pgs prog_main_name p)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_sign_report_sound_proved_for:
  fixes v :: pp and c :: texp
  assumes solve: "sctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (teval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_sign_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            sign_classify_check]
    by auto
  have node_sound: "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_sign_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = sign_classify_check
             and reach = "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def surface_unfold] sign_classify_check_proved node_sound])
qed

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: texp
  assumes solve: "sctx_terminates_prog pgs prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (teval c s)"
proof -
  have finI: "finite (intra (prog_cfg prog_main_name p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_sign_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            sign_classify_check]
    by auto
  have node_sound: "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_sign_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = sign_classify_check
             and reach = "ltr_collect (prog_tyenv p) pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def surface_unfold] sign_classify_check_refuted node_sound])
qed

end



text \<open>
  \<open>analyse_sign_report\<close>'s own soundness corollaries below are the
  check-report layer's \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances,
  matching \<open>analyse_sign_report_sound_proved_for\<close>/\<open>_refuted_for\<close> above.
\<close>

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: texp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "sctx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (prog_tyenv p) (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (teval c s)"
  by (rule analyse_sign_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: texp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and solve: "sctx_terminates_prog (declared_global p) prog_main_name p"
      and entry_cov: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) prog_main_name p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (prog_tyenv p) (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (teval c s)"
  by (rule analyse_sign_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_sign_report_def]])

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> (\<open>Exec_Sign_DG_Run\<close>, Examples) are the
  \<open>gs = sign_ex_gs\<close>, \<open>p = sign_ex_prog\<close> instance of the arbitrary-classifier,
  arbitrary-program chain above, not a separate parallel definition.
\<close>

text \<open>
  No per-domain \<open>export_code\<close> here: a caller reaches the generic, already-sound
  \<^const>\<open>analyse_sign_report\<close> through the unified dispatcher \<open>analyse\<close>
  (\<open>Analyse_Dispatch\<close>, downstream), which is the one thing exported to OCaml.
  A second, domain-specific export module would be a parallel, redundant API
  surface for the same computation.
\<close>
subsection \<open>Base-style flow-sensitive global regressions\<close>

text \<open>
  Acceptance regressions for the Base-style migration: \<open>D\<close> carries the whole abstract
  state (VIMP globals included), reachability-lifted, instead of routing globals
  through a separate flow-\<^emph>\<open>in\<close>sensitive solver-global unknown.
\<close>

definition sign_flow_sensitive_global_prog :: imp_prog where
  "sign_flow_sensitive_global_prog = program { global int32 Gx;
     void f() { Gx := 1 }
     void main() { Gx := 0; f(); __voblint_check(0 < Gx) } }"

text \<open>
  Under the old unlifted routing, \<open>Gx := 0\<close> and \<open>Gx := 1\<close> both feed the same
  flow-insensitive shared summary and join to \<open>SNonNeg\<close>, leaving the check
  \<open>UNKNOWN\<close>. With the whole state lifted into \<open>D\<close>, the call's own local answer
  at the \<open>main\<close> exit carries \<open>Gx\<close>'s value exactly as \<^const>\<open>sign_tf_st_for\<close>
  and \<^const>\<open>sign_enter_st_for\<close> left it, so the check is exact.
\<close>

lemma sign_flow_sensitive_global_result:
  "(Statement 4, TLess (TN I32 0) (TVar I32 (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_flow_sensitive_global_prog)"
  by eval

definition sign_dead_branch_bot_prog :: imp_prog where
  "sign_dead_branch_bot_prog = program { global int32 Gx;
     void f(int32 n) { if (n < 0) { Gx := -1 } else { Gx := 1 } }
     void main() { Gx := 0; f(5); __voblint_check(0 < Gx) } }"

text \<open>
  \<open>f\<close> is called with \<open>n = 5\<close>, abstracted to \<open>SPos\<close>: Sign's own comparison-against-zero
  tables refute \<open>n < 0\<close> exactly (\<open>SPos < SZero\<close> is definitely false), so the \<open>Gx := -1\<close>
  arm's own local answer is genuinely \<^const>\<open>Bot\<close> in the lifted carrier, not merely an
  imprecise contribution the exit join has to absorb. The two arms deliberately carry
  \<^emph>\<open>different\<close> signs so a leaked dead arm is observable: were the reachability-lift
  fix absent (or otherwise defeated), the join \<open>SNeg \<squnion> SPos = STop\<close> would leave the
  check \<open>UNKNOWN\<close> instead of \<open>PROVED\<close>. Contrast a numeric-bound guard such as \<open>n < 2\<close>
  at \<open>n = 5\<close>: Sign cannot refute that from \<open>SPos\<close> alone (unlike Interval, which tracks
  exact bounds -- see \<open>03-procedures/precision/05-dead_branch_no_bottom_leak.vimp\<close>), so
  that shape does not isolate this property for Sign.
\<close>

lemma sign_dead_branch_bot_result:
  "(Statement 6, TLess (TN I32 0) (TVar I32 (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_dead_branch_bot_prog)"
  by eval

subsection \<open>Recursion and repeated call sites\<close>

text \<open>
  Sign otherwise has no regression fixture exercising recursion or a procedure called
  from two call sites -- the mechanism that separates how callee-entry values thread
  through the equation system (a flow-sensitive local unknown revisited per predecessor
  vs. a keyed-seed slot per callee entry). \<open>sign_factorial_prog\<close> mirrors Interval's own
  recursive-factorial regression at Sign's coarser granularity; Sign has no
  \<open>--context\<close> flag, so there is no CLI parameter to fix here, only the program shape.
  The entry check \<open>0 < n\<close> stays \<open>UNKNOWN\<close>: Sign has no context-sensitivity feature, so
  the callee entry joins over every call site's argument (here \<open>3\<close> and \<open>4\<close>).
\<close>

definition sign_factorial_prog :: imp_prog where
  "sign_factorial_prog =
     program {
       int32 factorial(int32 n) {
         __voblint_check(0 < n);
         if (n < 2) {
           return 1
         } else {
           r := factorial(n - 1);
           __voblint_check(0 < r);
           return n * r
         }
       }
       void main() {
         a := factorial(3);
         b := factorial(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

text \<open>
  Every verdict here is \<open>UNKNOWN\<close>, and the mechanism is multiplication under
  wraparound. \<^const>\<open>sign_cast\<close> at a signed kind can only answer \<open>top\<close> for
  anything but \<open>SZero\<close>, because sign carries no magnitude and so cannot rule
  out that \<open>n * r\<close> left \<^term>\<open>ik_range I32\<close>; the returned value is therefore
  \<open>STop\<close>, and every check downstream of a returned product is \<open>UNKNOWN\<close>.
  This is a genuine limit of the abstraction, not an artefact of how the guard
  reaches the classifier: the concrete results (\<open>3! = 6\<close>, \<open>4! = 24\<close>) are
  positive and fixed, but no sign-only domain can establish that once the
  concrete semantics is allowed to wrap. \<open>int_dom\<close> recovers these, since
  its interval component bounds the magnitude and its cast is exact on a bounded
  value. Contrast \<open>sign_flow_sensitive_global_result\<close> and
  \<open>sign_dead_branch_bot_result\<close> above, which stay \<open>PROVED\<close>: those write
  literals, and a literal is abstracted from its already-normed value
  (\<open>aval_sign_t (TN ik n) = sign_of_int (ik_norm ik n)\<close>), so no cast is applied
  and no precision is lost.
\<close>

lemma sign_factorial_result:
  "set (analyse_sign_report sign_factorial_prog) =
     {(Statement 0, TLess (TN I32 0) (TVar I32 (STR ''n'')), Check_Unknown),
      (Statement 4, TLess (TN I32 0) (TVar I32 (STR ''r'')), Check_Unknown),
      (Statement 9, TLess (TN I32 0) (TVar I32 (STR ''a'')), Check_Unknown),
      (Statement 10, TLess (TN I32 0) (TVar I32 (STR ''b'')), Check_Unknown)}"
  by eval

text \<open>
  \<open>sign_two_call_sites_prog\<close> mirrors
  \<open>tests/regression/03-procedures/known-imprecision/01-two_call_sites_same_procedure.vimp\<close>:
  one non-recursive procedure, two call sites, isolating repeated-entry-node evaluation
  without recursion's added complexity. Both checks are \<open>UNKNOWN\<close>, but not for the
  repeated-call-site reason the Interval analogue isolates: Sign's finite height and its
  always-join solver rule never separate the two call sites' contributions. The loss is
  the same one \<open>sign_factorial_result\<close> records -- \<open>square\<close> returns \<open>n * n\<close>, and a
  sign-only domain cannot rule out that the product wrapped, so \<^const>\<open>sign_cast\<close>
  widens it to \<open>STop\<close>. A single call site would lose exactly as much.
\<close>

definition sign_two_call_sites_prog :: imp_prog where
  "sign_two_call_sites_prog =
     program {
       int32 square(int32 n) {
         return n * n
       }
       void main() {
         a := square(3);
         b := square(4);
         __voblint_check(0 < a);
         __voblint_check(0 < b)
       }
     }"

lemma sign_two_call_sites_result:
  "set (analyse_sign_report sign_two_call_sites_prog) =
     {(Statement 4, TLess (TN I32 0) (TVar I32 (STR ''a'')), Check_Unknown),
      (Statement 5, TLess (TN I32 0) (TVar I32 (STR ''b'')), Check_Unknown)}"
  by eval

end
