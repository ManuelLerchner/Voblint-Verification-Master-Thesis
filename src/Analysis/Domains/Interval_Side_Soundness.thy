theory Interval_Side_Soundness
  imports Interval_Domain TD_Side_Eff_Soundness
begin

section \<open>Interval domain: effectful transfer instance\<close>

text \<open>
  The Interval domain's effectful transfer functions, obtained by wrapping the
  pure ivl_tf record via the pure_edge_tree shim -- the concrete Interval witness
  for the Goblint-aligned effectful interface (mirrors sign_etf).
\<close>

definition ivl_etf :: "(unit, ivl) effectful_domain_transfer" where
  "ivl_etf = etf_from_tf ivl_tf"

lemma ivl_etf_is_mono_eq:
  "is_mono_eq (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  unfolding ivl_etf_def by (rule side_cfg_T_eff_is_mono_eq[OF ivl_tf_mono])

lemma ivl_etf_mono_sides:
  "mono_sides (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  unfolding ivl_etf_def by (rule side_cfg_T_eff_mono_sides[OF ivl_tf_mono])

lemma ivl_etf_mono_deps:
  "mono_deps (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  unfolding ivl_etf_def by (rule side_cfg_T_eff_mono_deps)

lemma ivl_sound_etf:
  "sound_effectful_transfer ivl_etf"
  unfolding ivl_etf_def
  by (rule sound_transfer_imp_sound_effectful[OF ivl_sound_tf.sound_transfer_axioms])

lemma ivl_etf_cone_compatible: "cone_compatible_etf ivl_etf"
  unfolding ivl_etf_def by (rule cone_compatible_etf_from_tf)

lemma ivl_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g ivl_etf bot0 s0 ())"
  unfolding ivl_etf_def by (rule threefold_mono_from_tf[OF ivl_tf_mono])

section \<open>Interval domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Interval analysis, stated against the effectful side
  IP solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged by the generic pure-shim lemmas; the unit seed-slot () carries the
  initial globals.
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

