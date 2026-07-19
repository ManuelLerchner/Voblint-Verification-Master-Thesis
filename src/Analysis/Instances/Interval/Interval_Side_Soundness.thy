theory Interval_Side_Soundness
  imports Interval_Domain LTR_TD_Side_Eff_Exit
begin

section \<open>Interval domain: effectful transfer instance\<close>

text \<open>
  The Interval domain provides the effectful transfer record consumed by
  TD_side.  Each edge tree queries the local program point and the unit global
  slot, applies the interval transfer, then splits the result into local and
  global parts.
\<close>

definition ivl_etf :: "(unit, ivl) effectful_domain_transfer" where
  "ivl_etf = unit_etf_of_transfer ivl_tf"

lemma ivl_etf_edge_tree:
  "apply_etf ivl_etf a u = unit_edge_tree (apply_tf ivl_tf a) u"
  unfolding ivl_etf_def apply_etf_unit_of_transfer by simp

lemma ivl_etf_combine_tree:
  "etf_combine ivl_etf dst cc ex = unit_combine_tree dst cc ex"
  unfolding ivl_etf_def etf_combine_unit_of_transfer by simp

lemma ivl_sound_etf:
  "sound_effectful_transfer ivl_etf"
  unfolding ivl_etf_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF ivl_is_sound_transfer])

lemma ivl_etf_cone_compatible: "cone_compatible_etf ivl_etf"
  by (rule cone_compatible_etf_unit_transfer[OF ivl_etf_edge_tree ivl_etf_combine_tree])

lemma ivl_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  by (rule threefold_mono_unit_transfer[OF ivl_etf_edge_tree ivl_etf_combine_tree ivl_tf_mono])

section \<open>Interval domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Interval analysis, stated against the effectful side
  IP solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged from the native ivl_etf record shape; the unit seed-slot () carries
  the initial globals.
\<close>

theorem side_ivl_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "ivl abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) ivl_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  have gs: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "ltr_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> \<lbrakk>side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone
          [OF ivl_sound_etf ivl_etf_threefold_mono ivl_etf_cone_compatible
              side_solve_dom gs])
  show ?thesis using collect collect_exit by blast
qed

end

