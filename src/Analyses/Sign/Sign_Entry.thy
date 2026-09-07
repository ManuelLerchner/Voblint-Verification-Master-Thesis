theory Sign_Entry
  imports Sign_Checks "Voblint_Soundness.Run_Analysis_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

hide_const phase.N

section \<open>Sign codegen API: an arbitrary VIMP program, and its OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>activation_collect_unit_eq_ltr_collect\<close> (\<^theory>\<open>Voblint_Framework.Routed_Context_Unit\<close>,
  reached transitively through \<open>Sign_Analyses\<close>) is the domain-generic unit-context
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
  now \<^const>\<open>analyse_sign_ctx_result_for\<close> (\<^theory>\<open>Voblint_Analysis_Sign.Sign_Analyses\<close>):
  the  routed-unit producer's own solved table, at \<open>prog_main_name\<close>.
  \<open>analyse_sign_result_node_sound_for\<close> below is the node-soundness bridge for
  that table, built from \<^theory>\<open>Voblint_Framework.DG_Analysis_Adapter\<close>'s generic
  \<open>analyse_result_node_sound\<close> (\<open>Sign_Checks.sctx_result_node_sound\<close>), composed
  with \<open>activation_collect_unit_eq_ltr_collect\<close> (the unit-context collapse to
  \<^const>\<open>ltr_collect\<close>) and \<open>Sign_Checks.sctx_analyse_result_eq\<close> (identifying the
  adapter's own result reading with \<^const>\<open>analyse_sign_ctx_result_for\<close>'s
  \<open>readback_result_value\<close>/\<open>canonicalize_lift\<close> construction) rather than re-deriving
  \<open>routed_context_base_hetero\<close>'s coverage argument by hand --- the
  routed spine needs no \<open>wf_compile_input\<close>/finiteness/node-membership premise,
  so this bridge only takes the four coverage-and-termination facts the
  routed solve genuinely turns on.
\<close>

lemma analyse_sign_result_node_sound_for:
  assumes solve: "sctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  define empty_pred :: "sign resolved_st_q \<Rightarrow> bool"
    where "empty_pred = resolved_st_q_is_bot_for (declared_global_vars p)"
  have exact: "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
    unfolding empty_pred_def by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])
  have sol_eq: "sctx_sol_prog pgs p
      = sctx_sol pgs empty_pred (prog_table p) (prog_procs p)"
    unfolding sctx_sol_prog_def sctx_eqs_prog_def sctx_sol_def empty_pred_def prog_cfg_def by simp
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have solves': "sctx_terminates pgs empty_pred (prog_table p) (prog_procs p)"
    using solve unfolding sctx_terminates_prog_def empty_pred_def .
  have entry_cov': "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
      \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using entry_cov unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have fwd_ok': "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, a, w) \<in> intra (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have call_fwd_ok': "\<And>u ctx dst fs as q k.
      (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using call_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have comb_fwd_ok': "\<And>cl c1 dst fs as q k.
      (cl, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
      \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (compile_prog (prog_table p) (prog_procs p))
      \<Longrightarrow> (k, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
    using comb_fwd_ok unfolding sol_eq[symmetric] cfg_eq[symmetric] .
  have ltr_eq: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
          (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()"
    unfolding cfg_eq by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  have s0_sound: "cinit_stores pgs \<subseteq> sctx_gamma pgs (Lifted cinit_sign_st) Bot"
    by (rule sctx_cinit_le_cinit_sign_st[OF solves' exact entry_cov' fwd_ok' call_fwd_ok' comb_fwd_ok'])
  have node_sound: "activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
        (compile_prog (prog_table p) (prog_procs p)) (cinit_stores pgs) v ()
      \<subseteq> \<lbrakk>case lookup_context
              (dg_analysis_adapter.analyse_result
                 (snd (sctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
                 (fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
                 (map_lift (fun_of_resolved_st_q_for pgs)))
              v () of
            Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  proof (rule sctx_result_node_sound)
    show "sctx_terminates pgs empty_pred (prog_table p) (prog_procs p)"
      by (rule solves')
    show "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
      by (rule exact)
    show "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
        \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule entry_cov')
    show "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (u, a, v) \<in> intra (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule fwd_ok')
    show "\<And>u ctx dst pars args pa cont.
        (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (FunctionEntry pa, ()) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule call_fwd_ok')
    show "\<And>cl c1 dst pars args pa cont.
        (cl, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule comb_fwd_ok')
    show "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
        \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule entry_cov')
    show "cinit_stores pgs \<subseteq> sctx_gamma pgs (Lifted cinit_sign_st) Bot"
      by (rule s0_sound)
  qed
  have result_eq: "lookup_context (analyse_sign_result_for pgs p) v ()
      = (if (v, ()) \<in> fst (sctx_sol_prog pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred (locals (snd (sctx_sol_prog pgs p) (Inl (v, ())))))
         else Bot)"
    unfolding analyse_sign_result_for_def analyse_sign_ctx_result_for_def lookup_context_def empty_pred_def
    by simp
  have adapter_eq0: "lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (sctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
             (fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p)))
             (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()
      = (if (v, ()) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
         then readback_result_value pgs
                (canonicalize_lift empty_pred
                  (locals (snd (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
                    (Inl (v, ())))))
         else Bot)"
  proof (rule sctx_analyse_result_eq)
    show "sctx_terminates pgs empty_pred (prog_table p) (prog_procs p)"
      by (rule solves')
    show "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
      by (rule exact)
    show "(cfg_entry (compile_prog (prog_table p) (prog_procs p)), ())
        \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule entry_cov')
    show "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (u, a, v) \<in> intra (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule fwd_ok')
    show "\<And>u ctx dst pars args pa cont.
        (u, ctx) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (FunctionEntry pa, ()) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule call_fwd_ok')
    show "\<And>cl c1 dst pars args pa cont.
        (cl, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry pa, cont) \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol pgs empty_pred (prog_table p) (prog_procs p))"
      by (rule comb_fwd_ok')
  qed
  have adapter_eq: "(if (v, ()) \<in> fst (sctx_sol_prog pgs p)
         then readback_result_value pgs
                (canonicalize_lift empty_pred (locals (snd (sctx_sol_prog pgs p) (Inl (v, ())))))
         else Bot)
      = lookup_context
          (dg_analysis_adapter.analyse_result
             (snd (sctx_sol_prog pgs p))
             (fst (sctx_sol_prog pgs p)) (map_lift (fun_of_resolved_st_q_for pgs)))
          v ()"
    using adapter_eq0[unfolded sol_eq[symmetric]]
    by (rule sym)
  show ?thesis
    unfolding ltr_eq result_eq adapter_eq
    using node_sound[unfolded sol_eq[symmetric]] by simp
qed

theorem analyse_sign_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "sctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_sign_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            sign_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_sign_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = sign_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def surface_unfold] sign_classify_check_proved node_sound])
qed

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "sctx_terminates_prog pgs p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog pgs p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog pgs p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog pgs p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog pgs p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg p)"
    using mem[unfolded analyse_sign_report_for_def surface_unfold]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
            sign_classify_check]
    by auto
  have node_sound: "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule analyse_sign_result_node_sound_for[OF solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p"
             and env = "\<lambda>v. case lookup_context (analyse_sign_result_for pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st"
             and classify = sign_classify_check
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def surface_unfold] sign_classify_check_refuted node_sound])
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

lemma sctx_vars_cover_prog_of_exec:
  assumes cover: "vars_cover_exec (prog_cfg p) (fst (sctx_sol_prog pgs p))"
  shows "vars_cover (prog_cfg p) (fst (sctx_sol_prog pgs p))"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

lemma analyse_sign_result_node_sound_of_cover:
  assumes solve: "sctx_terminates_prog pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog pgs p))"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p) v () of
                             Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof (rule analyse_sign_result_node_sound_for[OF solve])
  show "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog pgs p)"
    by (rule vars_cover_entryD[OF cover])
next
  fix u a w ctx
  assume e: "(u, a, w) \<in> intra (prog_cfg p)"
  show "(w, ctx) \<in> fst (sctx_sol_prog pgs p)"
    using vars_cover_edgeD[OF cover e] by simp
next
  fix u ctx dst fs as q k
  assume e: "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog pgs p)"
    by (rule vars_cover_enterD[OF cover e])
next
  fix cl c1 dst fs as q k
  assume e: "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)"
  show "(k, c1) \<in> fst (sctx_sol_prog pgs p)"
    using vars_cover_combineD[OF cover e] by simp
qed

subsection \<open>Source runs, in the vocabulary the runtime API returns\<close>

text \<open>
  What a caller of \<^const>\<open>analyse_sign_result_for\<close> actually wants to know: run the
  source program, stop anywhere, and the store you are holding is described by the
  entry the analysis returned for the program point you are standing at. The
  simulation \<^const>\<open>csim\<close> is what names that point --- a partly executed command and
  its frame stack sit at a graph node, and it is that node's table entry the store
  belongs to.

  No new reasoning happens here. \<open>source_sound_from_ltr_collecting_cap\<close>
  (\<^theory>\<open>Voblint_Soundness.Source_Activation_Sound\<close>) turns any per-node cap on
  \<^const>\<open>ltr_collect\<close> into exactly this statement, and
  \<open>analyse_sign_result_node_sound_of_cover\<close> is that cap.
\<close>

theorem analyse_sign_source_sound_for:
  fixes s0 s :: store
  assumes solve: "sctx_terminates_prog pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  show ?thesis
    unfolding cfg_eq
    by (rule source_sound_from_ltr_collecting_cap[OF wf s0 run])
       (use analyse_sign_result_node_sound_of_cover[OF solve cover] in
          \<open>simp add: cfg_eq\<close>)
qed

text \<open>
  The completed-run reading of the same fact, and the one a reader meets first: a
  source run that finishes leaves its final store inside the analysis result at the
  program exit. It is weaker --- one point instead of all of them --- but it needs no
  \<^const>\<open>csim\<close> witness to state, because \<open>source_completes_ltr_collect_exit\<close> has
  already identified the point as \<^const>\<open>cfg_exit\<close>.
\<close>

theorem analyse_sign_completed_run_sound_for:
  fixes s0 s :: store
  assumes solve: "sctx_terminates_prog pgs p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog pgs p))"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_sign_result_for pgs p)
                            (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) (cfg_exit (prog_cfg p))"
    using source_completes_ltr_collect_exit[OF wf s0 run] unfolding cfg_eq .
  then show ?thesis
    using analyse_sign_result_node_sound_of_cover[OF solve cover] by blast
qed

end



text \<open>
  \<open>analyse_sign_report\<close>'s own soundness corollaries below are the
  check-report layer's \<^const>\<open>declared_global\<close> \<open>p\<close> convenience instances,
  matching \<open>analyse_sign_report_sound_proved_for\<close>/\<open>_refuted_for\<close> above.
\<close>

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
  by (rule analyse_sign_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and solve: "sctx_terminates_prog (declared_global p) p"
      and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and fwd_ok:
        "\<And>u a w ctx. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, a, w) \<in> intra (prog_cfg p) \<Longrightarrow> (w, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and call_fwd_ok:
        "\<And>u ctx dst fs as q k. (u, ctx) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and comb_fwd_ok:
        "\<And>cl c1 dst fs as q k. (cl, c1) \<in> fst (sctx_sol_prog (declared_global p) p)
           \<Longrightarrow> (cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg p)
           \<Longrightarrow> (k, c1) \<in> fst (sctx_sol_prog (declared_global p) p)"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
  by (rule analyse_sign_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem[unfolded analyse_sign_report_def]])

text \<open>
  The headline pair, at \<^const>\<open>declared_global\<close> \<open>p\<close> and over
  \<^const>\<open>analyse_sign_result\<close> --- the table the runtime API hands back. Two side
  conditions survive, and both are decided per program rather than proved once:
  the solver reached a fixpoint (\<^const>\<open>sctx_terminates_prog\<close>; no result here
  proves the solver terminates on every input), and it solved enough keys
  (\<^const>\<open>vars_cover\<close>, decidable through \<open>sctx_vars_cover_prog_of_exec\<close>).
\<close>

corollary analyse_sign_source_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) v () of
                                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_sign_result_def
  by (rule analyse_sign_source_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

corollary analyse_sign_completed_run_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
    and solve: "sctx_terminates_prog (declared_global p) p"
    and cover: "vars_cover (prog_cfg p) (fst (sctx_sol_prog (declared_global p) p))"
    and s0: "s0 \<in> cinit_stores (declared_global p)"
    and run: "star (pstep (declared_global p) (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>case lookup_context (analyse_sign_result p) (cfg_exit (prog_cfg p)) () of
                          Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
  unfolding analyse_sign_result_def
  by (rule analyse_sign_completed_run_sound_for
        [OF wf[THEN wf_compile_input_reserved_ret_var] solve cover wf s0 run])

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
  "sign_flow_sensitive_global_prog = program { global Gx;
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
  "(Statement 4, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_flow_sensitive_global_prog)"
  by eval

definition sign_dead_branch_bot_prog :: imp_prog where
  "sign_dead_branch_bot_prog = program { global Gx;
     void f(n) { if (n < 0) { Gx := -1 } else { Gx := 1 } }
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
  "(Statement 6, Less (N 0) (V (STR ''Gx'')), Check_Proved) \<in> set (analyse_sign_report sign_dead_branch_bot_prog)"
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
       void factorial(n) {
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

lemma sign_factorial_result:
  "set (analyse_sign_report sign_factorial_prog) =
     {(Statement 0, Less (N 0) (V (STR ''n'')), Check_Unknown),
      (Statement 4, Less (N 0) (V (STR ''r'')), Check_Proved),
      (Statement 9, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 10, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

text \<open>
  \<open>sign_two_call_sites_prog\<close> mirrors
  \<open>tests/regression/03-procedures/known-imprecision/01-two_call_sites_same_procedure.vimp\<close>:
  one non-recursive procedure, two call sites, isolating repeated-entry-node evaluation
  without recursion's added complexity. Unlike Interval's analogue, which genuinely loses
  precision at a repeated call site under Interval's infinite-height carrier and its
  warrowing solver, both checks here stay \<open>PROVED\<close>: Sign's finite height and its
  always-join solver rule never separate the two call sites' contributions here.
\<close>

definition sign_two_call_sites_prog :: imp_prog where
  "sign_two_call_sites_prog =
     program {
       void square(n) {
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
     {(Statement 4, Less (N 0) (V (STR ''a'')), Check_Proved),
      (Statement 5, Less (N 0) (V (STR ''b'')), Check_Proved)}"
  by eval

end

