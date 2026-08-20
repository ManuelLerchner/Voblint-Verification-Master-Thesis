theory Interval_Codegen
  imports Voblint_Analysis.Interval_Checks "Voblint_Formalization.Run_Analysis_Sound"
begin

section \<open>Interval codegen API: an arbitrary VIMP program, and its production soundness\<close>

text \<open>
  Mirrors Sign's \<open>Sign_Codegen\<close>: \<open>analyse_interval_dg_eqs_for\<close>/
  \<open>analyse_interval_dg_for\<close>/\<open>analyse_interval_dg_env_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Exec_Sound\<close>)
  and \<open>analyse_interval_td_report_for\<close>/\<open>analyse_interval_td_report\<close>
  (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) are pure computation, no dependence on the
  \<open>base_dg_exec_analysis\<close> locale interpreted below, so they live one session earlier
  (Analysis). Only the soundness half needs that locale, one session later than Analysis
  in the locked six-session chain, so it lives here.

  Unlike Sign, Interval's local carrier has infinite height (an unbounded integer bound),
  so this interpretation solves via \<^const>\<open>TD_side_warrowing_apinis_Interp.solve\<close>/
  \<open>.solve_c\<close> instead of the always-join rule Sign uses --- \<open>base_dg_exec_analysis\<close> is
  generic in the solver, so this is a like-for-like swap of the locale's \<open>solve\<close>/
  \<open>solve_c\<close> parameters, not a different registration shape.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

interpretation p_reg:
  base_dg_exec_analysis pgs
    "ivl_tf_for pgs" "ivl_tf_st_for pgs" "ivl_enter_st_for pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_warrowing_apinis_Interp.solve" "TD_side_warrowing_apinis_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for pgs "ivl_tf_for pgs"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis pgs (ivl_tf_for pgs)
          (ivl_tf_st_for pgs) (ivl_enter_st_for pgs) (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_warrowing_apinis_Interp.solve TD_side_warrowing_apinis_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_warrowing_apinis_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  \<open>p_reg\<close> is local to this context block, so its qualified constants do not survive past
  the closing \<open>end\<close> --- \<open>analyse_interval_dg_gamma_for\<close> names the fully-applied locale
  concretization once, mirroring \<open>analyse_sign_gamma_for\<close>, so the soundness corollaries
  below can state their conclusion after the context closes.
\<close>

definition analyse_interval_dg_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_for = p_reg.gamma"

text \<open>
  The per-node collecting soundness connection: reuses
  \<open>base_dg_exec_analysis.collect_sound\<close> exactly as \<open>flagship_ex_reg.run_source_sound\<close> does
  in \<open>Example_Interval_DG_Flagship\<close>, just with the solver-domain, well-formedness, and
  coverage facts left as hypotheses instead of discharged \<open>by eval\<close> --- a symbolic \<open>p\<close>
  cannot be run through the executable solver at proof time the way a hard-coded example
  program can. \<open>sound0\<close> stays internal: it never depends on the program, only on
  \<open>cinit_ivl_st\<close> and the classifier.
\<close>

theorem analyse_interval_dg_collect_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> analyse_interval_dg_gamma_for
               (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v"
proof -
  have sound0:
    "cinit_stores pgs \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for pgs) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_for_def analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale predicate
  \<open>base_dg_exec_analysis\<close>) do not survive past the closing \<open>end\<close> either ---
  \<open>analyse_interval_dg_env_for\<close> reads the local unknown at \<open>v\<close> directly, and
  \<open>analyse_interval_dg_gamma_eq_env_for\<close> proves it is exactly what
  \<open>analyse_interval_dg_gamma_for\<close> already concretizes, mirroring
  \<open>analyse_sign_gamma_eq_env_for\<close> --- via \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new
  soundness argument.
\<close>

lemma analyse_interval_dg_gamma_eq_env_for:
  "analyse_interval_dg_gamma_for
     (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)) v
     = \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_for_def analyse_interval_dg_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

text \<open>
  The corollary the CLI's exported \<open>unreachable\<close> flag
  (\<^const>\<open>resolved_st_q_lifted_is_bot_for\<close>, \<^theory>\<open>Voblint_Core.Exec_St\<close>) needs,
  mirroring \<open>analyse_sign_report_unreachable_sound_for\<close>'s Sign counterpart:
  when that flag holds at a report entry's own solved local unknown, the
  point is genuinely unreachable under the collecting semantics, not merely
  witness-bottom by construction.
\<close>

theorem analyse_interval_td_report_unreachable_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and unreachable: "resolved_st_q_lifted_is_bot_for (declared_global_vars p)
        (locals (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ()))))"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v = {}"
proof -
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_interval_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_for .
  have empty: "\<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk> = {}"
    using unreachable[unfolded resolved_st_q_lifted_is_bot_for_iff[OF declared_global_iff]
                                is_bot_state_lift_iff]
    unfolding analyse_interval_dg_env_for_def
    by (cases "map_lift (fun_of_exec_dg_st_for pgs)
                 (locals (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ()))))")
       (simp_all add: gamma_state_bot fun_of_exec_dg_st_for_def)
  from node_sound empty show ?thesis by blast
qed

text \<open>
  \<open>analyse_interval_td_report_for\<close> (\<^theory>\<open>Voblint_Analysis.Interval_Checks\<close>) reads its
  per-node state through \<^const>\<open>analyse_interval_td_result_for\<close>'s \<^type>\<open>analysis_result\<close>
  table rather than through \<open>analyse_interval_dg_env_for\<close> directly.
  \<open>analyse_interval_td_result_node_sound_for\<close> below is the node-soundness bridge across
  that boundary, mirroring \<open>analyse_sign_result_node_sound_for\<close>: the two envs'
  concretizations agree at every genuine CFG node, not merely a solver-covered one,
  because \<^const>\<open>analyse_interval_td_result_for\<close>'s key domain is \<^const>\<open>cfg_node_list\<close>
  itself, and \<open>gamma_point_normalize_point_canonicalize_lift\<close> transports the raw
  concretization across \<^const>\<open>canonicalize_lift\<close>/\<open>normalize_point\<close> unconditionally.
\<close>

lemma analyse_interval_td_result_node_sound_for:
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
  shows "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  have old_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
    using analyse_interval_dg_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_for .
  have mem_keys: "v \<in> set (cfg_node_list (prog_cfg prog_main_name p))"
    using node finI finC by simp
  have lookup_eq: "lookup_context (analyse_interval_td_result_for pgs p) v () =
      normalize_point pgs (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
        (locals (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ())))))"
    unfolding analyse_interval_td_result_for_def
    by (simp add: lookup_context_monovariant_analysis_result_for mem_keys)
  have bot_sound: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
      \<Longrightarrow> is_bot_state (fun_of_resolved_st_q_for pgs s)"
    using resolved_st_q_is_bot_for_iff[OF declared_global_iff] by blast
  have raw_eq: "gamma_point (lookup_context (analyse_interval_td_result_for pgs p) v ()) =
      \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
  proof -
    let ?q = "locals (snd (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p) (Inl (v, ())))"
    have step1: "gamma_point (lookup_context (analyse_interval_td_result_for pgs p) v ()) =
        gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) ?q)"
      unfolding lookup_eq
      by (rule gamma_point_normalize_point_canonicalize_lift[OF bot_sound])
    have step2: "gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) ?q) =
        \<lbrakk>analyse_interval_dg_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p v\<rbrakk>"
      unfolding analyse_interval_dg_env_for_def fun_of_exec_dg_st_for_def
      by (cases ?q) (simp_all add: gamma_state_bot)
    from step1 step2 show ?thesis by simp
  qed
  show ?thesis
    unfolding gamma_state_of_reachable_env raw_eq
    by (rule old_sound)
qed

theorem analyse_interval_td_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_td_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_td_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def Let_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_td_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input pgs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_for (resolved_st_q_is_bot_for (declared_global_vars p)) pgs p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report_for pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_td_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_td_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_td_result_for pgs p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect pgs (prog_cfg prog_main_name p) (cinit_stores pgs)"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_td_report_for_def Let_def] interval_classify_check_refuted node_sound])
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
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_td_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_td_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_def]
            cover_edge[unfolded analyse_interval_dg_def]
            cover_enter[unfolded analyse_interval_dg_def]
            cover_combine[unfolded analyse_interval_dg_def]
            finI finC mem[unfolded analyse_interval_td_report_def]])

corollary analyse_interval_td_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_warrowing_apinis_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_td_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_td_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_td_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_def]
            cover_edge[unfolded analyse_interval_dg_def]
            cover_enter[unfolded analyse_interval_dg_def]
            cover_combine[unfolded analyse_interval_dg_def]
            finI finC mem[unfolded analyse_interval_td_report_def]])

section \<open>Solver-choice soundness: join and per-origin update rules\<close>

text \<open>
  Mirrors the warrowing soundness block above exactly, one \<open>base_dg_exec_analysis\<close>
  interpretation per update rule --- the locale is generic in \<open>solve\<close>/\<open>solve_c\<close>, so swapping
  \<^const>\<open>TD_side_warrowing_apinis_Interp.solve\<close> for \<^const>\<open>TD_side_always_join_Interp.solve\<close> (here)
  and \<^const>\<open>TD_side_per_origin_Interp.solve\<close> (below) is a like-for-like registration, not a
  different proof shape. Sign's own soundness (\<open>Sign_Codegen.analyse_sign_sound_for\<close>) is
  exactly this join interpretation already; Interval needed its own copy only because Interval's
  \<open>ivl_tf_for\<close>/\<open>ivl_tf_st_for\<close>/\<open>ivl_enter_st_for\<close> transfer facts differ from Sign's. Each block
  below writes \<^term>\<open>declared_global p\<close> out in full rather than reusing the \<open>pgs\<close> abbreviation:
  \<open>pgs\<close> is local to the first context block above and, once that block closes, its global residue
  takes \<open>p\<close> as an explicit argument, so a second same-named local abbreviation here would clash.
\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

interpretation p_reg_join:
  base_dg_exec_analysis "declared_global p"
    "ivl_tf_for (declared_global p)" "ivl_tf_st_for (declared_global p)" "ivl_enter_st_for (declared_global p)"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for "declared_global p" "ivl_tf_for (declared_global p)"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis (declared_global p) (ivl_tf_for (declared_global p))
          (ivl_tf_st_for (declared_global p)) (ivl_enter_st_for (declared_global p))
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

definition analyse_interval_dg_gamma_join_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_join_for = p_reg_join.gamma"

theorem analyse_interval_dg_collect_join_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> analyse_interval_dg_gamma_join_for
               (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v"
proof -
  have sound0:
    "cinit_stores (declared_global p) \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_join_for_def analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg_join.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_join_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

lemma analyse_interval_dg_gamma_eq_env_join_for:
  "analyse_interval_dg_gamma_join_for
     (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v
     = \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_join_for_def analyse_interval_dg_join_env_for_def
  by (simp add: p_reg_join.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg_join.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg_join.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

lemma analyse_interval_join_result_node_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  have old_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_join_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_join_for .
  have mem_keys: "v \<in> set (cfg_node_list (prog_cfg prog_main_name p))"
    using node finI finC by simp
  have lookup_eq: "lookup_context (analyse_interval_join_result_for (declared_global p) p) v () =
      normalize_point (declared_global p) (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
        (locals (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p) (Inl (v, ())))))"
    unfolding analyse_interval_join_result_for_def
    by (simp add: lookup_context_monovariant_analysis_result_for mem_keys)
  have bot_sound: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
      \<Longrightarrow> is_bot_state (fun_of_resolved_st_q_for (declared_global p) s)"
    using resolved_st_q_is_bot_for_iff[OF declared_global_iff] by blast
  have raw_eq: "gamma_point (lookup_context (analyse_interval_join_result_for (declared_global p) p) v ()) =
      \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  proof -
    let ?q = "locals (snd (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p) (Inl (v, ())))"
    have step1: "gamma_point (lookup_context (analyse_interval_join_result_for (declared_global p) p) v ()) =
        gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p)) ?q)"
      unfolding lookup_eq
      by (rule gamma_point_normalize_point_canonicalize_lift[OF bot_sound])
    have step2: "gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p)) ?q) =
        \<lbrakk>analyse_interval_dg_join_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
      unfolding analyse_interval_dg_join_env_for_def fun_of_exec_dg_st_for_def
      by (cases ?q) (simp_all add: gamma_state_bot)
    from step1 step2 show ?thesis by simp
  qed
  show ?thesis
    unfolding gamma_state_of_reachable_env raw_eq
    by (rule old_sound)
qed

theorem analyse_interval_report_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_join_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def Let_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_join_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_join_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_for_def Let_def] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_join_def]
            cover_edge[unfolded analyse_interval_dg_join_def]
            cover_enter[unfolded analyse_interval_dg_join_def]
            cover_combine[unfolded analyse_interval_dg_join_def]
            finI finC mem[unfolded analyse_interval_report_def]])

corollary analyse_interval_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_join p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_join p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_report_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_join_def]
            cover_edge[unfolded analyse_interval_dg_join_def]
            cover_enter[unfolded analyse_interval_dg_join_def]
            cover_combine[unfolded analyse_interval_dg_join_def]
            finI finC mem[unfolded analyse_interval_report_def]])

text \<open>Per-origin sibling of the join block above: the vendored solver has the identical
  \<open>part_post_solution_of_solve_c\<close> bridge fact under \<^const>\<open>TD_side_per_origin_Interp.solve\<close>, so
  the same proof shape carries over verbatim.\<close>

context
  fixes p :: imp_prog
  assumes reserved: "reserved_ret_var (declared_global p)"
begin

interpretation p_reg_per_origin:
  base_dg_exec_analysis "declared_global p"
    "ivl_tf_for (declared_global p)" "ivl_tf_st_for (declared_global p)" "ivl_enter_st_for (declared_global p)"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    "TD_side_per_origin_Interp.solve" "TD_side_per_origin_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for "declared_global p" "ivl_tf_for (declared_global p)"
    by (rule ivl_is_sound_transfer_for)
  show "base_dg_exec_analysis (declared_global p) (ivl_tf_for (declared_global p))
          (ivl_tf_st_for (declared_global p)) (ivl_enter_st_for (declared_global p))
          (resolved_st_q_is_bot_for (declared_global_vars p))
          TD_side_per_origin_Interp.solve TD_side_per_origin_Interp.solve_c"
    by unfold_locales
       (rule reserved
             p_transfer.tf_sound_assign_for p_transfer.tf_sound_special_for
             p_transfer.tf_sound_branch_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_env_for
             ivl_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             ivl_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             resolved_st_q_is_bot_for_iff[OF declared_global_iff, folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF ivl_tf_st_for_reduces]
             action_reduces.ret_some[OF ivl_tf_st_for_reduces]
             action_reduces.check[OF ivl_tf_st_for_reduces]
             TD_side_per_origin_Interp.part_post_solution_of_solve_c)+
qed

definition analyse_interval_dg_gamma_per_origin_for ::
  "(pp \<times> unit + unit \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_interval_dg_gamma_per_origin_for = p_reg_per_origin.gamma"

theorem analyse_interval_dg_collect_per_origin_sound_for:
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> analyse_interval_dg_gamma_per_origin_for
               (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v"
proof -
  have sound0:
    "cinit_stores (declared_global p) \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))
                          (map_lift (fun_of_exec_dg_st_for (declared_global p)) (Lifted cinit_ivl_st))"
    by (auto simp: fun_of_exec_dg_st_for_def fun_of_st_cinit_ivl_st_for cinit_stores_def
                  gamma_state_def gamma_dg_base_def)
  show ?thesis
    unfolding analyse_interval_dg_gamma_per_origin_for_def analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def
              prog_cfg_def
    by (rule p_reg_per_origin.collect_sound
          [OF solve[unfolded analyse_interval_dg_eqs_for_def prog_cfg_def]
              wf
              vars_coverI[OF cover_entry[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_edge[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_enter[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]
                             cover_combine[unfolded analyse_interval_dg_per_origin_for_def analyse_interval_dg_eqs_for_def prog_cfg_def]]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0])
qed

lemma analyse_interval_dg_gamma_eq_env_per_origin_for:
  "analyse_interval_dg_gamma_per_origin_for
     (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)) v
     = \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  unfolding analyse_interval_dg_gamma_per_origin_for_def analyse_interval_dg_per_origin_env_for_def
  by (simp add: p_reg_per_origin.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg_per_origin.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg_per_origin.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_dg_base_def fun_of_dg_st_gen_def gamma_state_bot
         split: lifted.splits)

lemma analyse_interval_per_origin_result_node_sound_for:
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
           \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of
                             Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
proof -
  have old_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
    using analyse_interval_dg_collect_per_origin_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_interval_dg_gamma_eq_env_per_origin_for .
  have mem_keys: "v \<in> set (cfg_node_list (prog_cfg prog_main_name p))"
    using node finI finC by simp
  have lookup_eq: "lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () =
      normalize_point (declared_global p) (canonicalize_lift (resolved_st_q_is_bot_for (declared_global_vars p))
        (locals (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p) (Inl (v, ())))))"
    unfolding analyse_interval_per_origin_result_for_def
    by (simp add: lookup_context_monovariant_analysis_result_for mem_keys)
  have bot_sound: "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
      \<Longrightarrow> is_bot_state (fun_of_resolved_st_q_for (declared_global p) s)"
    using resolved_st_q_is_bot_for_iff[OF declared_global_iff] by blast
  have raw_eq: "gamma_point (lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v ()) =
      \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
  proof -
    let ?q = "locals (snd (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p) (Inl (v, ())))"
    have step1: "gamma_point (lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v ()) =
        gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p)) ?q)"
      unfolding lookup_eq
      by (rule gamma_point_normalize_point_canonicalize_lift[OF bot_sound])
    have step2: "gamma_state_lift (map_lift (fun_of_resolved_st_q_for (declared_global p)) ?q) =
        \<lbrakk>analyse_interval_dg_per_origin_env_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p v\<rbrakk>"
      unfolding analyse_interval_dg_per_origin_env_for_def fun_of_exec_dg_st_for_def
      by (cases ?q) (simp_all add: gamma_state_bot)
    from step1 step2 show ?thesis by simp
  qed
  show ?thesis
    unfolding gamma_state_of_reachable_env raw_eq
    by (rule old_sound)
qed

theorem analyse_interval_report_per_origin_sound_proved_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Proved
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_per_origin_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def Let_def] interval_classify_check_proved node_sound])
qed

theorem analyse_interval_report_per_origin_sound_refuted_for:
  fixes v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c
                    (analyse_interval_dg_eqs_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in>
                           fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow>
           (w, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin_for (resolved_st_q_is_bot_for (declared_global_vars p)) (declared_global p) p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin_for (declared_global p) p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> truthy (aval c s)"
proof -
  obtain tgt where edge: "(v, EA_Check c, tgt) \<in> intra (prog_cfg prog_main_name p)"
    using mem[unfolded analyse_interval_report_per_origin_for_def Let_def]
          classify_checks_mem_iff[OF finI, of v c Check_Refuted
            "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
            interval_classify_check]
    by auto
  have node: "v \<in> cfg_nodes (prog_cfg prog_main_name p)"
    using intra_endpoints_in_nodes(1)[OF edge] .
  have node_sound: "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v
      \<subseteq> gamma_state (case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"
    by (rule analyse_interval_per_origin_result_node_sound_for
          [OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC node])
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p"
             and env = "\<lambda>v. case lookup_context (analyse_interval_per_origin_result_for (declared_global p) p) v () of Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st"
             and classify = interval_classify_check
             and reach = "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))"
             and v = v and gamma_state = "gamma_state :: ivl abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_interval_report_per_origin_for_def Let_def] interval_classify_check_refuted node_sound])
qed

end

corollary analyse_interval_report_per_origin_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           truthy (aval c s)"
  unfolding analyse_interval_report_per_origin_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_per_origin_sound_proved_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_per_origin_def]
            cover_edge[unfolded analyse_interval_dg_per_origin_def]
            cover_enter[unfolded analyse_interval_dg_per_origin_def]
            cover_combine[unfolded analyse_interval_dg_per_origin_def]
            finI finC mem[unfolded analyse_interval_report_per_origin_def]])

corollary analyse_interval_report_per_origin_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: exp
  assumes solve: "TD_side_per_origin_Interp_solve_c (analyse_interval_dg_eqs p)
                    (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_interval_dg_per_origin p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_interval_report_per_origin p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v.
           \<not> truthy (aval c s)"
  unfolding analyse_interval_report_per_origin_def analyse_interval_dg_eqs_def
  by (rule analyse_interval_report_per_origin_sound_refuted_for
        [OF wf[THEN wf_compile_input_reserved_ret_var]
            solve[unfolded analyse_interval_dg_eqs_def]
            wf
            cover_entry[unfolded analyse_interval_dg_per_origin_def]
            cover_edge[unfolded analyse_interval_dg_per_origin_def]
            cover_enter[unfolded analyse_interval_dg_per_origin_def]
            cover_combine[unfolded analyse_interval_dg_per_origin_def]
            finI finC mem[unfolded analyse_interval_report_per_origin_def]])

end
