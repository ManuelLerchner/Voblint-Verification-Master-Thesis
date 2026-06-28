theory Interval_Side_Soundness
  imports Interval_Domain TD_Side_Eff_Soundness
begin

section \<open>Interval domain: effectful transfer instance\<close>

text \<open>
  The Interval domain provides the effectful transfer record consumed by
  TD_side.  Each edge tree queries the local program point and the unit global
  slot, applies the interval transfer, then splits the result into local and
  global parts.
\<close>

definition ivl_etf :: "(unit, ivl) effectful_domain_transfer" where
  "ivl_etf = \<lparr>
    etf_nop        = pure_edge_tree ivl_tf EA_Nop,
    etf_assign     = (\<lambda>x e. pure_edge_tree ivl_tf (EA_Assign x e)),
    etf_assume     = (\<lambda>b. pure_edge_tree ivl_tf (EA_Assume b)),
    etf_assume_not = (\<lambda>b. pure_edge_tree ivl_tf (EA_AssumeNot b)),
    etf_enter      = pure_edge_tree ivl_tf EA_Enter,
    etf_combine    = pure_combine_tree
  \<rparr>"

lemma ivl_etf_pure_transfer:
  "pure_effectful_transfer ivl_tf ivl_etf"
  unfolding ivl_etf_def pure_effectful_transfer_def by simp

lemma ivl_sound_etf:
  "sound_effectful_transfer ivl_etf"
  by (rule sound_transfer_imp_sound_effectful_pure_etf
        [OF ivl_sound_tf.sound_transfer_axioms ivl_etf_pure_transfer])

lemma ivl_etf_cone_compatible: "cone_compatible_etf ivl_etf"
  by (rule cone_compatible_etf_pure_transfer[OF ivl_etf_pure_transfer])

lemma ivl_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  by (rule threefold_mono_pure_transfer[OF ivl_etf_pure_transfer ivl_tf_mono])

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
    "t \<in> cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) ivl_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  have gs: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> \<lbrakk>side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_pruned
          [OF ivl_sound_etf ivl_etf_threefold_mono ivl_etf_cone_compatible
              side_solve_dom gs])
  show ?thesis using collect collect_exit by blast
qed

end

