theory Parity_Side_Soundness
  imports Parity_Domain Parity_Transfer Voblint_Core.LTR_TD_Side_Eff_Exit
begin

section \<open>Parity domain: effectful transfer instance\<close>

text \<open>
  Mirrors Voblint_Analysis.Interval_Side_Soundness at the parity
  domain: each edge tree queries the local program point and the unit global
  slot, applies the parity transfer, then splits the result into local and
  global parts.
\<close>

definition parity_etf :: "(vname \<Rightarrow> bool) \<Rightarrow> (unit, parity) effectful_domain_transfer" where
  "parity_etf gs = unit_etf_of_transfer gs (parity_tf_for gs)"

lemma parity_etf_edge_tree:
  "apply_etf (parity_etf gs) a u = unit_edge_tree gs (apply_tf (parity_tf_for gs) a) u"
  unfolding parity_etf_def apply_etf_unit_of_transfer by simp

lemma parity_etf_enter_tree:
  "etf_enter (parity_etf gs) fs as cl = unit_edge_tree gs (enter\<^sup># (parity_tf_for gs) fs as) cl"
  unfolding parity_etf_def unit_etf_of_transfer_def by simp

lemma parity_tf_for_enter_mono:
  "s1 \<le> s2 \<Longrightarrow> enter\<^sup># (parity_tf_for gs) fs as s1 \<le> enter\<^sup># (parity_tf_for gs) fs as s2"
  by (simp add: parity_tf_for_def enter_parity_for_mono)

lemma parity_etf_combine_tree:
  "etf_combine (parity_etf gs) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding parity_etf_def etf_combine_unit_of_transfer by simp

lemma parity_sound_etf:
  "sound_effectful_transfer gs (parity_etf gs)"
  unfolding parity_etf_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF parity_is_sound_transfer_for])

lemma parity_etf_cone_compatible: "cone_compatible_etf gs (parity_etf gs)"
  by (rule cone_compatible_etf_unit_transfer
        [OF parity_etf_edge_tree parity_etf_enter_tree parity_etf_combine_tree])

lemma parity_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g (parity_etf gs) bot0 s0 ())"
  by (rule threefold_mono_unit_transfer
        [OF parity_etf_edge_tree parity_etf_enter_tree parity_etf_combine_tree
            parity_tf_for_mono parity_tf_for_enter_mono])

section \<open>Parity domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Parity analysis, stated against the effectful
  side IP solver (\<open>side_analyse_eff\<close>), mirroring
  \<open>side_ivl_analysis_sound\<close>/\<open>side_sign_analysis_sound\<close>. Cone compatibility
  and threefold monotonicity are discharged from the native \<open>parity_etf\<close>
  record shape; the unit seed-slot \<open>()\<close> carries the initial globals.
\<close>

theorem side_parity_analysis_sound:
  fixes \<Pi> ps mnm main and s t :: store and s0 :: "parity abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) (parity_etf gs) bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "t \<in> \<lbrakk>side_analyse_eff gs \<Pi> ps mnm main (parity_etf gs) bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
proof -
  have sub: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))
     \<le> \<lbrakk>side_analyse_eff gs \<Pi> ps mnm main (parity_etf gs) bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone
          [OF parity_sound_etf parity_etf_threefold_mono parity_etf_cone_compatible
              side_solve_dom sub])
  show ?thesis using collect collect_exit by blast
qed

end
