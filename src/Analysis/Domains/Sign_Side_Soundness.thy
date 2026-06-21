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
  "sound_effectful_transfer gamma_sign sign_etf"
  unfolding sign_etf_def
  by (rule sound_transfer_imp_sound_effectful[OF sign_sound_tf.sound_transfer_axioms])

section \<open>Sign domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Sign analysis, stated against the effectful side IP
  solver (side_analyse_eff) and proved through the standalone effectful
  pipeline: side_analyse_eff_collect_sound_exit_pruned_gen instantiated at the
  Sign witness sign_sound_etf.  The five cone contracts are discharged generically
  for the shim etf (sign_etf = etf_from_tf sign_tf); the three TD_side
  preconditions come from sign_tf_mono.  The unit seed-slot () carries the
  initial globals.  No pure side_analyse / pure IP soundness theorem is used.
\<close>

theorem side_sign_analysis_sound:
  fixes \<Pi> ps main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> sign_domain.gamma_state s0"
  assumes collect_exit:
    "t \<in> cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps main) sign_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps main))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_eff \<Pi> ps main sign_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main)))"
proof -
  interpret se: sound_effectful_transfer gamma_sign sign_etf
    by (rule sign_sound_etf)
  have gs: "{s} \<le> sound_domain.gamma_state gamma_sign s0"
    using s_sound
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
  have ed: "\<And>b z \<sigma>'. Inl z \<in> dep_aux \<sigma>' (apply_etf sign_etf b z)"
    unfolding sign_etf_def by (rule dep_aux_apply_etf_from_tf_src)
  have cd1: "\<And>c2 e2 \<sigma>'. Inl c2 \<in> dep_aux \<sigma>' (etf_combine sign_etf c2 e2)"
    unfolding sign_etf_def by (rule dep_aux_etf_combine_from_tf_call)
  have cd2: "\<And>c2 e2 \<sigma>'. Inl e2 \<in> dep_aux \<sigma>' (etf_combine sign_etf c2 e2)"
    unfolding sign_etf_def by (rule dep_aux_etf_combine_from_tf_exit)
  have es: "\<And>a u. static_deps (apply_etf sign_etf a u)"
    unfolding sign_etf_def by (rule static_deps_apply_etf_from_tf)
  have cs: "\<And>cc ex. static_deps (etf_combine sign_etf cc ex)"
    unfolding sign_etf_def by (rule static_deps_etf_combine_from_tf)
  have collect:
    "cfg_collect (compile_prog \<Pi> ps main) {s}
       (cfg_exit (compile_prog \<Pi> ps main))
     \<le> sound_domain.gamma_state gamma_sign
         (side_analyse_eff \<Pi> ps main sign_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps main)))"
    by (rule side_analyse_eff_collect_sound_exit_pruned_gen
          [OF sign_sound_etf sign_etf_is_mono_eq sign_etf_mono_sides sign_etf_mono_deps
              side_solve_dom gs ed cd1 cd2 es cs])
  have "t \<in> sound_domain.gamma_state gamma_sign
       (side_analyse_eff \<Pi> ps main sign_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps main)))"
    using collect collect_exit by blast
  then show ?thesis
    unfolding sign_domain.gamma_state_def sound_domain.gamma_state_def by auto
qed

end

