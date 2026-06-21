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
  "sound_effectful_transfer gamma_ivl ivl_etf"
  unfolding ivl_etf_def
  by (rule sound_transfer_imp_sound_effectful[OF ivl_sound_tf.sound_transfer_axioms])

section \<open>Interval domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Interval analysis, stated against the effectful side
  IP solver (side_analyse_eff) and proved through the standalone effectful
  pipeline (mirrors side_sign_analysis_sound).  The unit seed-slot () carries the
  initial globals.  No pure side_analyse / pure IP soundness theorem is used.
\<close>

theorem side_ivl_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "ivl abs_state"
  assumes s_sound: "s \<in> ivl_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) ivl_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> ivl_domain.gamma_state
       (side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  interpret se: sound_effectful_transfer gamma_ivl ivl_etf
    by (rule ivl_sound_etf)
  have gs: "{s} \<le> sound_domain.gamma_state gamma_ivl s0"
    using s_sound
    unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have ed: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf ivl_etf b z)"
    unfolding ivl_etf_def by (rule dep_aux_apply_etf_from_tf_src)
  have cd1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine ivl_etf c2 e2)"
    unfolding ivl_etf_def by (rule dep_aux_etf_combine_from_tf_call)
  have cd2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine ivl_etf c2 e2)"
    unfolding ivl_etf_def by (rule dep_aux_etf_combine_from_tf_exit)
  have es: "\<And>a u. static_deps (apply_etf ivl_etf a u)"
    unfolding ivl_etf_def by (rule static_deps_apply_etf_from_tf)
  have cs: "\<And>cc ex. static_deps (etf_combine ivl_etf cc ex)"
    unfolding ivl_etf_def by (rule static_deps_etf_combine_from_tf)
  have collect:
    "cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> sound_domain.gamma_state gamma_ivl
         (side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps main)))"
    by (rule side_analyse_eff_collect_sound_exit_pruned_gen
          [OF ivl_sound_etf ivl_etf_is_mono_eq ivl_etf_mono_sides ivl_etf_mono_deps
              side_solve_dom gs ed cd1 cd2 es cs])
  have "t \<in> sound_domain.gamma_state gamma_ivl
       (side_analyse_eff \<Pi> ps main ivl_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main)))"
    using collect collect_exit by blast
  then show ?thesis
    unfolding ivl_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end

