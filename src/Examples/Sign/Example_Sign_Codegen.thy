theory Example_Sign_Codegen
  imports Exec_Sign_DG_Run Voblint_Analysis.Sign_Checks
begin

section \<open>Sign codegen API: an arbitrary VIMP program, and its Haskell/OCaml export\<close>

subsection \<open>Whole-program entry point: an arbitrary VIMP program\<close>

text \<open>
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> in \<open>Exec_Sign_DG_Run\<close> fix one hard-coded example.
  This section widens that same native D/G chain to an arbitrary classifier
  \<open>gs\<close> and program \<open>p\<close>, reusing \<^const>\<open>prog_cfg\<close> for the compiled CFG.  The
  locale interpretation below is the classifier-generic twin of
  \<open>sign_ex_reg\<close> in \<open>Exec_Sign_DG_Run\<close>: the same five transfer facts
  discharge \<^locale>\<open>unit_dg_exec_analysis\<close> at any classifier, not only at
  \<open>sign_ex_gs\<close>, because \<open>sign_is_sound_transfer_for\<close>,
  \<open>sign_tf_st_for_commute\<close>, and \<open>sign_enter_st_for_commute\<close> are already
  stated for an arbitrary \<open>gs\<close>.  \<open>gs\<close> stays an explicit parameter (rather
  than hard-wired to \<^const>\<open>declared_global\<close> applied to \<open>p\<close>) so a caller can
  override which variables count as global; \<open>analyse_sign\<close> below is the
  convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
    and p :: imp_prog
begin

interpretation p_reg:
  unit_dg_exec_analysis gs
    "sign_tf_for gs" "sign_tf_st_for gs" "sign_enter_st_for gs"
    "TD_side_always_join_Interp.solve" "TD_side_always_join_Interp.solve_c"
proof -
  interpret p_transfer: sound_transfer_for gs "sign_tf_for gs"
    by (rule sign_is_sound_transfer_for)
  show "unit_dg_exec_analysis gs (sign_tf_for gs)
          (sign_tf_st_for gs) (sign_enter_st_for gs)
          TD_side_always_join_Interp.solve TD_side_always_join_Interp.solve_c"
    by unfold_locales
       (rule p_transfer.tf_sound_assign_for p_transfer.tf_sound_random_for
             p_transfer.tf_sound_assume_for p_transfer.tf_sound_assume_not_for
             p_transfer.tf_sound_enter_for p_transfer.tf_sound_combine_for
             sign_tf_st_for_commute[folded fun_of_exec_dg_st_for_def]
             sign_enter_st_for_commute[folded fun_of_exec_dg_st_for_def]
             action_reduces.ret_none[OF sign_tf_st_for_reduces]
             action_reduces.ret_some[OF sign_tf_st_for_reduces]
             action_reduces.check[OF sign_tf_st_for_reduces]
             TD_side_always_join_Interp.part_post_solution_of_solve_c)+
qed

text \<open>
  \<open>p_reg\<close> is local to this context block, so its qualified constants do not
  survive past the closing \<open>end\<close> --- \<open>analyse_sign_gamma_for\<close> names the
  fully-applied locale concretization once, the same way \<open>Sign_DG\<close>'s
  \<open>sign_dg_gamma\<close> names \<open>sound_dg_spec.dg_gamma\<close>, so \<open>analyse_sign_sound\<close>
  below can state its conclusion after the context closes.
\<close>

definition analyse_sign_gamma_for ::
  "(pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set" where
  "analyse_sign_gamma_for = p_reg.gamma"

text \<open>
  The native D/G equation system and its solved result, at an arbitrary
  classifier \<open>gs\<close> and program \<open>p\<close>.  \<open>analyse_sign_eqs_for\<close> and
  \<open>analyse_sign_for\<close> are exactly \<open>dgEx_eqs\<close> and \<open>dgEx_sol\<close> with \<open>gs\<close> and
  \<open>p\<close> in place of \<open>sign_ex_gs\<close> and \<open>sign_ex_prog\<close> --- \<^const>\<open>prog_cfg\<close>
  plays the role \<open>gEx\<close> played there.
\<close>

definition analyse_sign_eqs_for ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs_for =
     dg_gen_of
       (unit_dg_spec_st_for gs (sign_tf_st_for gs) (sign_enter_st_for gs))
       (prog_cfg prog_main_name p) bot cinit_sign_st cinit_sign_st"

definition analyse_sign_for ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign_for = TD_side_always_join_Interp_solve analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ())"

text \<open>
  The connection lemma: soundness for an arbitrary \<open>gs\<close> and \<open>p\<close> reuses
  \<open>unit_dg_exec_analysis.run_source_sound\<close> exactly as \<open>dgEx_source_run_sound\<close>
  does, just with the solver-domain, well-formedness, and coverage facts left
  as hypotheses instead of discharged \<open>by eval\<close> --- symbolic \<open>gs\<close>/\<open>p\<close> cannot
  be run through the executable solver at proof time the way the one
  hard-coded \<open>sign_ex_gs\<close>/\<open>sign_ex_prog\<close> can.  \<open>sound0\<close> stays internal: it
  never depended on the program, only on \<open>cinit_sign_st\<close> and the classifier,
  exactly as in \<open>dgEx_sound0\<close>.
\<close>

theorem analyse_sign_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst analyse_sign_for"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst analyse_sign_for"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst analyse_sign_for"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst analyse_sign_for"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep gs (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores gs"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (snd analyse_sign_for) v"
proof -
  have sound0:
    "cinit_stores gs \<subseteq>
       \<lbrakk>fun_of_exec_dg_st_for gs cinit_sign_st \<squnion>
        fun_of_exec_dg_st_for gs cinit_sign_st\<rbrakk>"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def sup.idem)
  show ?thesis
    unfolding analyse_sign_gamma_for_def analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def
    by (rule p_reg.run_source_sound
          [OF solve[unfolded analyse_sign_eqs_for_def prog_cfg_def]
              wf
              cover_entry[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_edge[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_enter[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_combine[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0[folded gamma_unit_def] init run])
qed

text \<open>
  The per-node collecting analogue of \<open>analyse_sign_sound_for\<close>, for a
  check-report layer that wants soundness at an arbitrary node without a
  concrete source run --- reuses \<open>p_reg.collect_sound\<close>, the same
  locale-level fact \<open>run_source_sound\<close> itself is built from
  (\<^theory>\<open>Voblint_Formalization.Run_Analysis_Sound\<close>).
\<close>

theorem analyse_sign_collect_sound_for:
  assumes solve: "TD_side_always_join_Interp_solve_c analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst analyse_sign_for"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst analyse_sign_for"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst analyse_sign_for"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst analyse_sign_for"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
  shows "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v
           \<subseteq> analyse_sign_gamma_for (snd analyse_sign_for) v"
proof -
  have sound0:
    "cinit_stores gs \<subseteq>
       \<lbrakk>fun_of_exec_dg_st_for gs cinit_sign_st \<squnion>
        fun_of_exec_dg_st_for gs cinit_sign_st\<rbrakk>"
    by (simp add: fun_of_exec_dg_st_for_def fun_of_st_cinit_sign_st_for cinit_stores_def
                  gamma_state_def sup.idem)
  show ?thesis
    unfolding analyse_sign_gamma_for_def analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def
    by (rule p_reg.collect_sound
          [OF solve[unfolded analyse_sign_eqs_for_def prog_cfg_def]
              wf
              cover_entry[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_edge[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_enter[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              cover_combine[unfolded analyse_sign_for_def analyse_sign_eqs_for_def prog_cfg_def]
              finI[unfolded prog_cfg_def] finC[unfolded prog_cfg_def]
              sound0[folded gamma_unit_def]])
qed

text \<open>
  \<open>p_reg\<close> is local, so its qualified constants (and the raw locale
  predicate \<open>unit_dg_exec_analysis\<close>) do not survive past the closing
  \<open>end\<close> either --- \<open>analyse_sign_env_for\<close> reads the exit-answer/side-effect
  split \<open>dg_state\<close> keeps (\<open>Inl (v, ())\<close> for the local answer at \<open>v\<close>,
  \<open>Inr ()\<close> for the global side effect) the same way \<open>dgEx_inspect\<close> in
  \<open>Exec_Sign_DG_Run\<close> does by hand, and \<open>analyse_sign_gamma_eq_env_for\<close>
  proves it is exactly what \<open>analyse_sign_gamma_for\<close> already concretizes ---
  via \<open>p_reg.gamma_def\<close> and \<open>p_reg.sds\<close>, not a new soundness argument.
\<close>

definition analyse_sign_env_for :: "pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env_for v =
     fun_of_exec_dg_st_for gs (locals (snd analyse_sign_for (Inl (v, ()))))
     \<squnion> fun_of_exec_dg_st_for gs (globs (snd analyse_sign_for (Inr ())))"

lemma analyse_sign_gamma_eq_env_for:
  "analyse_sign_gamma_for (snd analyse_sign_for) v = \<lbrakk>analyse_sign_env_for v\<rbrakk>"
  unfolding analyse_sign_gamma_for_def analyse_sign_env_for_def
  by (simp add: p_reg.gamma_def
                sound_dg_spec.dg_gamma_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_D_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                sound_dg_spec.dg_G_def[OF p_reg.sds[unfolded sound_dg_spec_ltr_for_def]]
                gamma_unit_def fun_of_dg_st_for_def)

text \<open>
  The check report itself is a thin composition, exactly mirroring
  \<open>sign_check_report\<close>/\<open>interval_check_report\<close>: \<^const>\<open>classify_checks\<close>
  owns the traversal and ordering, \<open>analyse_sign_env_for\<close> owns the
  node-indexed Sign environment, and \<open>sign_classify_check\<close> owns the
  per-check classification.
\<close>

definition analyse_sign_report_for :: "check_report_entry list" where
  "analyse_sign_report_for = classify_checks (prog_cfg prog_main_name p) analyse_sign_env_for sign_classify_check"

text \<open>
  The definitional equation above unfolds \<^const>\<open>analyse_sign_env_for\<close> at
  every check node, and that unfolding mentions \<^const>\<open>analyse_sign_for\<close>
  twice (once for \<open>locals\<close>, once for \<open>globs\<close>) --- so naive code generation
  from it would re-run the whole D/G solver twice per check, for an
  \<open>N\<close>-check program, \<open>2N\<close> solver runs instead of one. The \<open>[code]\<close>
  equation below is provably equal (a direct \<open>Let\<close>-unfold of the same
  definitions) but binds \<^term>\<open>snd analyse_sign_for\<close> once, outside the
  per-check closure \<^const>\<open>classify_checks\<close> applies; the target language
  compiles that \<open>let\<close> to a single shared thunk, so the generated
  Haskell/OCaml computes the solved system exactly once per report,
  regardless of how many checks the program has.
\<close>

declare analyse_sign_report_for_def [code del]

lemma analyse_sign_report_for_code [code]:
  "analyse_sign_report_for =
     (let sol = snd analyse_sign_for
      in classify_checks (prog_cfg prog_main_name p)
           (\<lambda>v. fun_of_exec_dg_st_for gs (locals (sol (Inl (v, ()))))
                \<squnion> fun_of_exec_dg_st_for gs (globs (sol (Inr ()))))
           sign_classify_check)"
  unfolding analyse_sign_report_for_def analyse_sign_env_for_def[abs_def] Let_def
  by (rule refl)

text \<open>
  Soundness reuses \<open>classify_checks_proved_sound\<close>/\<open>classify_checks_refuted_sound\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>, fully domain-generic already) with
  \<open>analyse_sign_collect_sound_for\<close> and \<open>analyse_sign_gamma_eq_env_for\<close>
  together supplying the one per-node fact each needs.
\<close>

theorem analyse_sign_report_sound_proved_for:
  fixes v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst analyse_sign_for"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst analyse_sign_for"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst analyse_sign_for"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst analyse_sign_for"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set analyse_sign_report_for"
  shows "\<forall>s \<in> ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v. bval c s"
proof -
  have node_sound: "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v \<subseteq> \<lbrakk>analyse_sign_env_for v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg prog_main_name p" and env = analyse_sign_env_for
             and classify = sign_classify_check
             and reach = "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def] sign_classify_check_proved node_sound])
qed

theorem analyse_sign_report_sound_refuted_for:
  fixes v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c analyse_sign_eqs_for (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst analyse_sign_for"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst analyse_sign_for"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst analyse_sign_for"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst analyse_sign_for"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set analyse_sign_report_for"
  shows "\<forall>s \<in> ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v. \<not> bval c s"
proof -
  have node_sound: "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs) v \<subseteq> \<lbrakk>analyse_sign_env_for v\<rbrakk>"
    using analyse_sign_collect_sound_for[OF solve wf cover_entry cover_edge cover_enter cover_combine finI finC]
    unfolding analyse_sign_gamma_eq_env_for .
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg prog_main_name p" and env = analyse_sign_env_for
             and classify = sign_classify_check
             and reach = "ltr_collect gs (prog_cfg prog_main_name p) (cinit_stores gs)"
             and v = v and gamma_state = "gamma_state :: sign abs_state \<Rightarrow> store set",
           OF finI mem[unfolded analyse_sign_report_for_def] sign_classify_check_refuted node_sound])
qed

end

text \<open>
  Convenience instances at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching the shape
  \<open>gEx\<close>/\<open>dgEx_eqs\<close>/\<open>dgEx_sol\<close> already use for \<open>sign_ex_gs\<close>.
\<close>

definition analyse_sign_eqs :: "imp_prog \<Rightarrow> pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "analyse_sign_eqs p = analyse_sign_eqs_for (declared_global p) p"

definition analyse_sign :: "imp_prog \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "analyse_sign p = analyse_sign_for (declared_global p) p"

corollary analyse_sign_sound:
  fixes p :: imp_prog
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and run: "star (pstep (declared_global p) (prog_table p)) (prog_main p, s, []) (residual, t, frs)"
      and init: "s \<in> cinit_stores (declared_global p)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg prog_main_name p) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> analyse_sign_gamma_for (declared_global p) (snd (analyse_sign p)) v"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_sound_for
        [OF solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC run init])

text \<open>
  Convenience instances of the check-report layer at \<^const>\<open>declared_global\<close>
  \<open>p\<close>, matching \<open>analyse_sign\<close>/\<open>analyse_sign_sound\<close> above.
\<close>

definition analyse_sign_env :: "imp_prog \<Rightarrow> pp \<Rightarrow> sign abs_state" where
  "analyse_sign_env p = analyse_sign_env_for (declared_global p) p"

definition analyse_sign_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report p = analyse_sign_report_for (declared_global p) p"

corollary analyse_sign_report_sound_proved:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Proved) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. bval c s"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_report_sound_proved_for
        [OF solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC mem[unfolded analyse_sign_report_def]])

corollary analyse_sign_report_sound_refuted:
  fixes p :: imp_prog and v :: pp and c :: bexp
  assumes solve: "TD_side_always_join_Interp_solve_c (analyse_sign_eqs p) (cfg_exit (prog_cfg prog_main_name p), ()) \<noteq> None"
      and wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p) prog_main_name (prog_main p)"
      and cover_entry: "(cfg_entry (prog_cfg prog_main_name p), ()) \<in> fst (analyse_sign p)"
      and cover_edge:
        "\<And>u a w. (u, a, w) \<in> intra (prog_cfg prog_main_name p) \<Longrightarrow> (w, ()) \<in> fst (analyse_sign p)"
      and cover_enter:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (analyse_sign p)"
      and cover_combine:
        "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name p)
           \<Longrightarrow> (k, ()) \<in> fst (analyse_sign p)"
      and finI: "finite (intra (prog_cfg prog_main_name p))"
      and finC: "finite (calls (prog_cfg prog_main_name p))"
      and mem: "(v, c, Check_Refuted) \<in> set (analyse_sign_report p)"
  shows "\<forall>s \<in> ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p)) v. \<not> bval c s"
  unfolding analyse_sign_def analyse_sign_eqs_def
  by (rule analyse_sign_report_sound_refuted_for
        [OF solve[unfolded analyse_sign_def analyse_sign_eqs_def]
            wf
            cover_entry[unfolded analyse_sign_def]
            cover_edge[unfolded analyse_sign_def]
            cover_enter[unfolded analyse_sign_def]
            cover_combine[unfolded analyse_sign_def]
            finI finC mem[unfolded analyse_sign_report_def]])

text \<open>
  \<open>gEx\<close>, \<open>dgEx_eqs\<close>, and \<open>dgEx_sol\<close> really are the \<open>gs = sign_ex_gs\<close>,
  \<open>p = sign_ex_prog\<close> instance of the arbitrary-classifier, arbitrary-program
  chain above, not a separate parallel definition.
\<close>

lemma gEx_prog_cfg: "gEx = prog_cfg prog_main_name sign_ex_prog"
  unfolding gEx_def prog_cfg_def sign_ex_pi_def by simp

lemma dgEx_eqs_is_analyse_sign_eqs: "dgEx_eqs = analyse_sign_eqs sign_ex_prog"
  unfolding dgEx_eqs_def analyse_sign_eqs_def analyse_sign_eqs_for_def gEx_prog_cfg by simp

lemma dgEx_sol_is_analyse_sign: "dgEx_sol = analyse_sign sign_ex_prog"
  unfolding dgEx_sol_def analyse_sign_def analyse_sign_for_def dgEx_eqs_is_analyse_sign_eqs
    analyse_sign_eqs_def gEx_prog_cfg by simp

subsection \<open>A second program through the same entry point\<close>

text \<open>
  \<open>analyse_sign_demo2_prog\<close> is a different program from \<open>sign_ex_prog\<close>, run
  through the very same \<open>analyse_sign\<close>: the entry point above is not
  specialized to one hard-coded example.
\<close>

definition analyse_sign_demo2_prog :: imp_prog where
  "analyse_sign_demo2_prog = program { void main() { a := 1; b := a; c := b } }"

text \<open>
  Same always-join imprecision as \<open>dgEx_inspect\<close> in \<open>Exec_Sign_DG_Run\<close>
  (every edge joins local answers with global side effects): the computed
  exit value is \<open>STop\<close>, not a hand-picked precise witness.  What matters
  here is that \<open>analyse_sign\<close> computes at all on a program it was never
  specialized to, not the resulting precision.
\<close>

lemma analyse_sign_demo2_result:
  "map_option (\<lambda>sol. lookup_resolved_st_q
                        (locals (snd sol (Inl (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ()))))
                        (location_of (declared_global analyse_sign_demo2_prog) ''c''))
     (TD_side_always_join_Interp_solve_c (analyse_sign_eqs analyse_sign_demo2_prog)
        (cfg_exit (prog_cfg prog_main_name analyse_sign_demo2_prog), ())) = Some STop"
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  \<open>dgEx_sol\<close>, \<open>analyse_sign_for\<close>, and \<open>analyse_sign\<close> export through
  Isabelle's code generator, not merely through \<open>eval\<close>/\<open>value\<close>: this is a
  stronger guarantee, since the code generator demands a complete code
  equation for every constant on the dependency path rather than falling
  back to the ML interpreter's built-in evaluation of the logical constants
  involved.
\<close>

export_code dgEx_sol analyse_sign_for analyse_sign analyse_sign_report
  in Haskell module_name Sign_Demo file_prefix "Sign_Demo"

export_code dgEx_sol analyse_sign_for analyse_sign analyse_sign_report
  in OCaml module_name Sign_Demo file_prefix "Sign_Demo_OCaml"

end
