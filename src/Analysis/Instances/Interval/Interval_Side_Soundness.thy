theory Interval_Side_Soundness
  imports Interval_Domain Voblint_Core.LTR_TD_Side_Eff_Exit
begin

section \<open>Interval domain: effectful transfer instance\<close>

text \<open>
  The Interval domain provides the effectful transfer record consumed by
  TD_side.  Each edge tree queries the local program point and the unit global
  slot, applies the interval transfer, then splits the result into local and
  global parts.
\<close>

definition ivl_etf :: "(vname \<Rightarrow> bool) \<Rightarrow> (unit, ivl) effectful_domain_transfer" where
  "ivl_etf gs = unit_etf_of_transfer gs (ivl_tf_for gs)"

lemma ivl_etf_edge_tree:
  "apply_etf (ivl_etf gs) a u = unit_edge_tree gs (apply_tf (ivl_tf_for gs) a) u"
  unfolding ivl_etf_def apply_etf_unit_of_transfer by simp

lemma ivl_etf_enter_tree:
  "etf_enter (ivl_etf gs) fs as cl = unit_edge_tree gs (enter\<^sup># (ivl_tf_for gs) fs as) cl"
  unfolding ivl_etf_def unit_etf_of_transfer_def by simp

lemma ivl_tf_for_enter_mono:
  "s1 \<le> s2 \<Longrightarrow> enter\<^sup># (ivl_tf_for gs) fs as s1 \<le> enter\<^sup># (ivl_tf_for gs) fs as s2"
  by (simp add: ivl_tf_for_def enter_ivl_for_mono)

lemma ivl_etf_combine_tree:
  "etf_combine_collect (ivl_etf gs) ci cc ex = unit_combine_tree gs (combine\<^sup># gs (ci_dst ci)) cc ex"
  unfolding ivl_etf_def etf_combine_collect_unit_of_transfer
  by (simp add: tf_combine_collect_abs_combine_env_abs ivl_tf_for_def)

lemma ivl_sound_etf:
  "sound_effectful_transfer gs (ivl_etf gs)"
  unfolding ivl_etf_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF ivl_is_sound_transfer_for])

lemma ivl_etf_cone_compatible: "cone_compatible_etf gs (ivl_etf gs)"
  by (rule cone_compatible_etf_unit_transfer[OF ivl_etf_edge_tree ivl_etf_enter_tree ivl_etf_combine_tree])

lemma ivl_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g (ivl_etf gs) bot0 s0 ())"
  by (rule threefold_mono_unit_transfer[OF ivl_etf_edge_tree ivl_etf_enter_tree ivl_etf_combine_tree
        ivl_tf_for_mono ivl_tf_for_enter_mono combine_collect_abs_mono])

section \<open>Interval domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Interval analysis, stated against the effectful side
  IP solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged from the native ivl_etf record shape; the unit seed-slot () carries
  the initial globals.
\<close>

theorem side_ivl_analysis_sound:
  fixes \<Pi> ps mnm main and s t :: store and s0 :: "ivl abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) (ivl_etf gs) bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "t \<in> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (ivl_etf gs) bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps mnm main)))"
proof -
  have sub: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))
     \<le> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (ivl_etf gs) bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps mnm main)))"
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone
          [OF ivl_sound_etf ivl_etf_threefold_mono ivl_etf_cone_compatible
              side_solve_dom sub])
  show ?thesis using collect collect_exit by blast
qed

end



