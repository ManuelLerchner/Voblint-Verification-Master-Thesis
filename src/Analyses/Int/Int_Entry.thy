theory Int_Entry
  imports Int_Checks "Voblint_Soundness.Run_Analysis_Sound"
begin

section \<open>Int codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  \<open>analyse_int_dg_eqs_for\<close>/\<open>analyse_int_dg_for\<close>/\<open>analyse_int_dg_env_for\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Exec_Sound\<close>) and \<open>analyse_int_report_for\<close>/\<open>analyse_int_report\<close>
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Checks\<close>) are pure computation, so they live one session
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
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>): the routed-unit producer's own solved
  table, at \<open>mode\<close> and \<open>prog_main_name\<close>. \<open>analyse_int_ctx_result_warrow_node_sound_for\<close>
  below is the node-soundness bridge for that table, built from
  \<open>int_conf_activation_collect_sound_warrow\<close> (the routed spine's own activation-indexed
  collecting soundness) composed with \<open>activation_collect_unit_eq_ltr_collect\<close> (the
  unit-context collapse to \<^const>\<open>ltr_collect\<close>) --- the routed spine needs no
  \<open>wf_compile_input\<close>/finiteness/node-membership premise, so this bridge only takes the
  four coverage-and-termination facts the routed solve genuinely turns on.
\<close>


text \<open>
  \<open>analyse_int_report_for\<close> reads its per-node state through
  \<^const>\<open>analyse_int_ctx_result_warrow_for\<close>'s \<^type>\<open>analysis_result\<close> table directly
  (\<^theory>\<open>Voblint_Analysis_Int.Int_Analyses\<close>): the routed-unit producer's own solved
  table, at \<open>mode\<close> and \<open>prog_main_name\<close>. \<open>analyse_int_ctx_result_warrow_node_sound_for\<close>
  below is the node-soundness bridge for that table, built from
  \<open>int_conf_activation_collect_sound_warrow\<close> (the routed spine's own activation-indexed
  collecting soundness) composed with \<open>activation_collect_unit_eq_ltr_collect\<close> (the
  unit-context collapse to \<^const>\<open>ltr_collect\<close>) rather than from
  \<open>p_reg\<close>/\<open>analyse_int_dg_for\<close> --- the routed spine needs no
  \<open>wf_compile_input\<close>/finiteness/node-membership premise, so this bridge only takes the
  four coverage-and-termination facts the routed solve genuinely turns on.
\<close>

lemma analyse_int_ctx_result_warrow_node_sound_for:
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "int_dom resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "int_conf_sol_prog_warrow mode pgs p
      = int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p)"
    unfolding int_conf_sol_prog_warrow_def int_conf_eqs_prog_def int_conf_sol_warrow_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "int_conf_terminates_warrow mode empty_pred pgs (prog_table p) (prog_procs p)"
    using solve unfolding int_conf_terminates_prog_warrow_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have s0_sound: "cinit_stores pgs \<subseteq> int_dom_gamma pgs (Lifted cinit_int_dom_st) Bot"
    by (rule int_conf_cinit_le_cinit_int_dom_st_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok'
                                                     comb_fwd_ok'])
  have node_sound: "activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p)))
                 (fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for pgs)))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule int_conf_result_node_sound_warrow
          [OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok' entry_cov' s0_sound])
  have ltr_eq: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have result_eq: "lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v ()
      = (if (v, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred
                  (locals (snd (int_conf_sol_prog_warrow mode pgs p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_int_ctx_result_warrow_for_def lookup_context_def empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p)))
             (fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()
      = (if (v, ()) \<in> fst (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))
         then readback_result_value pgs
                (canonicalize_lift empty_pred
                  (locals (snd (int_conf_sol_warrow mode empty_pred pgs (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
    by (rule int_conf_analyse_result_eq_warrow[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have adapter_eq: "(if (v, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred
                  (locals (snd (int_conf_sol_prog_warrow mode pgs p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (int_conf_sol_prog_warrow mode pgs p))
             (fst (int_conf_sol_prog_warrow mode pgs p)) (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_int_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_int_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def surface_unfold] int_classify_check_proved node_sound])
qed

theorem analyse_int_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report_for mode pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_int_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            int_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = int_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: int_dom abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_int_report_for_def surface_unfold] int_classify_check_refuted node_sound])
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

lemma int_conf_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p) (fst (int_conf_sol_prog_warrow mode pgs p))"
  shows "vars_cover (prog_cfg p) (fst (int_conf_sol_prog_warrow mode pgs p))"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

lemma analyse_int_ctx_result_warrow_node_sound_of_cover:
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (int_conf_sol_prog_warrow mode pgs p))"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof (rule analyse_int_ctx_result_warrow_node_sound_for[OF solve])
  show "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
    by (rule vars_cover_entryD[OF cover])
next
  fix u a w ctx
  assume e: "(u, a, w) \<in> intra (prog_cfg p)"
  show "(w, ctx) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
    using vars_cover_edgeD[OF cover e] by simp
next
  fix u ctx dst fs as q k
  assume e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
    by (rule vars_cover_enterD[OF cover e])
next
  fix cl c1 dst fs as q k
  assume e: "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(k, c1) \<in> fst (int_conf_sol_prog_warrow mode pgs p)"
    using vars_cover_combineD[OF cover e] by simp
qed

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  Int's counterparts of Sign's \<open>analyse_sign_source_sound_for\<close> and
  \<open>analyse_sign_completed_run_sound_for\<close>: run the source program, stop anywhere, and
  the store you are holding is described by the entry the analysis returned for the
  program point you are standing at; a run that finishes lands in the entry at
  \<^const>\<open>cfg_exit\<close>. The simulation \<^const>\<open>csim\<close> is what names that point.

  No new reasoning happens here. \<open>source_sound_from_ltr_collecting_cap\<close> and
  \<open>source_completes_ltr_collect_exit\<close>
  (\<^theory>\<open>Voblint_Soundness.Source_Activation_Sound\<close>) supply the source side, and
  \<open>analyse_int_ctx_result_warrow_node_sound_of_cover\<close> is the per-node cap they take.
\<close>

theorem analyse_int_source_sound_for:
  fixes s0 s :: store
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (int_conf_sol_prog_warrow mode pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  show ?thesis
    unfolding cfg_eq
    by (rule source_sound_from_ltr_collecting_cap[OF wf s0 run])
       (use analyse_int_ctx_result_warrow_node_sound_of_cover[OF solve cover] in
          \<open>simp add: cfg_eq\<close>)
qed

theorem analyse_int_completed_run_sound_for:
  fixes s0 s :: store
  assumes solve: "int_conf_terminates_prog_warrow mode pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (int_conf_sol_prog_warrow mode pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_int_ctx_result_warrow_for mode pgs p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) (cfg_exit (prog_cfg p))"
    using source_completes_ltr_collect_exit[OF wf s0 run] unfolding cfg_eq .
  then show ?thesis
    using analyse_int_ctx_result_warrow_node_sound_of_cover[OF solve cover] by blast
qed

end

text \<open>
  \<open>analyse_int_report\<close> (\<^theory>\<open>Voblint_Analysis_Int.Int_Checks\<close>) is the \<^const>\<open>declared_global\<close>
  \<open>p\<close> convenience instance the context above's \<open>_for\<close> layer already feeds, pinned at
  \<^const>\<open>Refine_Fixpoint\<close>, matching \<open>analyse_interval_td_report_sound_proved\<close>'s own
  shape. \<open>wf[THEN wf_compile_input_reserved_ret_var]\<close> discharges the context's
  \<open>reserved\<close> assumption from the concrete program's own well-formedness fact --- the same
  instantiation step Interval's own corollary uses.
\<close>

corollary analyse_int_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
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
      and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_int_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_int_report_def
  by (rule analyse_int_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_int_report_def]])

text \<open>
  The headline pair, at \<^const>\<open>declared_global\<close> \<open>p\<close> and over
  \<^const>\<open>analyse_int_result\<close> --- the table the runtime API hands back, pinned at
  \<^const>\<open>Refine_Fixpoint\<close> like \<open>analyse_int_report_sound_proved\<close> above and mirroring
  Sign's \<open>analyse_sign_source_sound\<close>/\<open>analyse_sign_completed_run_sound\<close>.  Two side
  conditions survive, and both are decided per program rather than proved once: the
  solver reached a fixpoint (\<^const>\<open>int_conf_terminates_prog_warrow\<close>), and it solved
  enough keys (\<^const>\<open>vars_cover\<close>, decidable through
  \<open>int_conf_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_int_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_int_result p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_int_result_def analyse_int_result_for_def
  by (rule analyse_int_source_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

corollary analyse_int_completed_run_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "int_conf_terminates_prog_warrow Refine_Fixpoint (declared_global p) p"
    and cover: "vars_cover (prog_cfg p)
                  (fst (int_conf_sol_prog_warrow Refine_Fixpoint (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_int_result p) (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_int_result_def analyse_int_result_for_def
  by (rule analyse_int_completed_run_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

end

