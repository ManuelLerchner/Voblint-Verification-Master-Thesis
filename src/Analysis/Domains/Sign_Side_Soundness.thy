theory Sign_Side_Soundness
  imports Sign_Domain TD_Side_Eff_Soundness
begin

section \<open>Sign domain: effectful transfer instance\<close>

text \<open>
  The Sign domain's effectful transfer functions, obtained by wrapping the pure
  sign_tf record via the pure_edge_tree shim.  This is the concrete witness that
  a real domain instantiates the Goblint-aligned effectful interface.
\<close>

definition sign_etf :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf = etf_from_tf sign_tf"

lemma sign_etf_is_mono_eq:
  "is_mono_eq (side_cfg_T_eff g sign_etf bot0 s0 ())"
  unfolding sign_etf_def by (rule side_cfg_T_eff_is_mono_eq[OF sign_tf_mono])

lemma sign_etf_mono_sides:
  "mono_sides (side_cfg_T_eff g sign_etf bot0 s0 ())"
  unfolding sign_etf_def by (rule side_cfg_T_eff_mono_sides[OF sign_tf_mono])

lemma sign_etf_mono_deps:
  "mono_deps (side_cfg_T_eff g sign_etf bot0 s0 ())"
  unfolding sign_etf_def by (rule side_cfg_T_eff_mono_deps)

text \<open>
  The Sign domain satisfies the effectful soundness contract: every per-action
  tree's reassembled full result over-approximates the concrete edge step.  This
  is the concrete instantiation of sound_effectful_transfer, discharged from the
  existing sign_sound_tf via the shim -- closing the instantiation gap for the
  Goblint-aligned effectful interface.
\<close>

lemma sign_sound_etf:
  "sound_effectful_transfer sign_etf"
  unfolding sign_etf_def
  by (rule sound_transfer_imp_sound_effectful[OF sign_sound_tf.sound_transfer_axioms])

lemma sign_etf_cone_compatible: "cone_compatible_etf sign_etf"
  unfolding sign_etf_def by (rule cone_compatible_etf_from_tf)

lemma sign_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g sign_etf bot0 s0 ())"
  unfolding sign_etf_def by (rule threefold_mono_from_tf[OF sign_tf_mono])

section \<open>Sign domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Sign analysis, stated against the effectful side IP
  solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged by the generic pure-shim lemmas; the unit seed-slot () carries the
  initial globals.
\<close>

theorem side_sign_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) sign_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main sign_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
proof -
  have gs: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> \<lbrakk>side_analyse_eff \<Pi> ps main sign_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_pruned
          [OF sign_sound_etf sign_etf_threefold_mono sign_etf_cone_compatible
              side_solve_dom gs])
  show ?thesis using collect collect_exit by blast
qed

end

