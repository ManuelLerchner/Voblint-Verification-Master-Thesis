theory Sign_Side_Soundness
  imports Sign_Domain LTR_TD_Side_Eff_Exit
begin

section \<open>Sign domain: effectful transfer instance\<close>

text \<open>
  The Sign domain provides the effectful transfer record consumed by TD_side.
  @{const mixed_etf_of_transfer} dispatches local edges to
  @{const local_edge_tree} and global edges to @{const unit_edge_tree}.
\<close>

definition sign_etf :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf = mixed_etf_of_transfer sign_tf"

lemma sign_etf_edge_tree:
  "apply_etf sign_etf a u = mixed_etf_edge_tree sign_tf a u"
  unfolding sign_etf_def apply_etf_mixed_of_transfer by simp

lemma sign_etf_edge_tree_mixed:
  "apply_etf sign_etf a u =
   (if local_edge_action a then local_edge_tree (apply_tf sign_tf a) u
    else unit_edge_tree (apply_tf sign_tf a) u)"
  unfolding sign_etf_def apply_etf_mixed_of_transfer mixed_etf_edge_tree_def by simp

lemma sign_etf_combine_tree:
  "etf_combine sign_etf dst cc ex = unit_combine_tree dst cc ex"
  unfolding sign_etf_def etf_combine_mixed_of_transfer by simp

lemma sign_etf_enter_tree:
  "etf_enter sign_etf fs as cl = unit_edge_tree (tf_enter sign_tf fs as) cl"
  unfolding sign_etf_def mixed_etf_of_transfer_def by simp

lemma sign_tf_enter_mono:
  "s1 \<le> s2 \<Longrightarrow> tf_enter sign_tf fs as s1 \<le> tf_enter sign_tf fs as s2"
  by (simp add: sign_tf_def enter_sign_mono)

lemma sign_sound_etf:
  "sound_effectful_transfer sign_etf"
  unfolding sign_etf_def
  by (rule sound_effectful_transfer_mixed_of_transfer
        [OF sign_is_sound_transfer sign_tf_local_edge_invariant])

lemma sign_etf_cone_compatible: "cone_compatible_etf sign_etf"
  by (rule cone_compatible_etf_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_enter_tree sign_etf_combine_tree])

lemma sign_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g sign_etf bot0 s0 ())"
  by (rule threefold_mono_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_enter_tree sign_etf_combine_tree
           sign_tf_mono sign_tf_enter_mono])

subsection \<open>Unit-only sign ETF (executable transport)\<close>

text \<open>
  Exec soundness bridges unit-shaped executable trees to this abstract
  unit-only effectful record.  The mixed @{const sign_etf} is for
  @{const side_analyse_eff}.
\<close>

definition sign_etf_unit :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf_unit = unit_etf_of_transfer sign_tf"

lemma sign_etf_unit_edge_tree:
  "apply_etf sign_etf_unit a u = unit_edge_tree (apply_tf sign_tf a) u"
  unfolding sign_etf_unit_def apply_etf_unit_of_transfer by simp

lemma sign_etf_unit_combine_tree:
  "etf_combine sign_etf_unit dst cc ex = unit_combine_tree dst cc ex"
  unfolding sign_etf_unit_def etf_combine_unit_of_transfer by simp

lemma sign_etf_unit_enter_tree_tf:
  "etf_enter sign_etf_unit fs as cl = unit_edge_tree (tf_enter sign_tf fs as) cl"
  unfolding sign_etf_unit_def unit_etf_of_transfer_def by simp

lemma sign_etf_unit_enter_tree:
  "etf_enter sign_etf_unit xs es u =
    unit_edge_tree (\<lambda>s. bind_formals_abs xs
      (map (\<lambda>e. aval_sign e s) es) (enter_frame_sign s)) u"
proof -
  have enter:
    "enter_sign xs es = (\<lambda>s. bind_formals_abs xs
      (map (\<lambda>e. aval_sign e s) es) (enter_frame_sign s))"
    by (rule ext) (simp add: enter_sign_def enter_D_def enter_frame_sign_def)
  show ?thesis
    unfolding sign_etf_unit_def unit_etf_of_transfer_def
    by (simp add: sign_tf_def enter)
qed

lemma sign_sound_etf_unit:
  "sound_effectful_transfer sign_etf_unit"
  unfolding sign_etf_unit_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF sign_is_sound_transfer])


lemma sign_etf_unit_cone_compatible: "cone_compatible_etf sign_etf_unit"
  by (rule cone_compatible_etf_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_enter_tree_tf sign_etf_unit_combine_tree])

lemma sign_etf_unit_threefold_mono:
  "threefold_mono (side_cfg_T_eff g sign_etf_unit bot0 s0 ())"
  by (rule threefold_mono_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_enter_tree_tf sign_etf_unit_combine_tree
           sign_tf_mono sign_tf_enter_mono])

section \<open>Sign domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Sign analysis, stated against the effectful side IP
  solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged from the native sign_etf record shape; the unit seed-slot () carries
  the initial globals.
\<close>

theorem side_sign_analysis_sound:
  fixes \<Pi> ps mnm main and s t :: store and s0 :: "sign abs_state"
  assumes s_sound: "s \<in> \<lbrakk>s0\<rbrakk>"
  assumes collect_exit:
    "t \<in> ltr_collect is_global (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff (compile_prog \<Pi> ps mnm main) sign_etf bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps mnm main sign_etf bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
proof -
  have gs: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "ltr_collect is_global (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))
     \<le> \<lbrakk>side_analyse_eff \<Pi> ps mnm main sign_etf bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps mnm main))\<rbrakk>"
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone
          [OF sign_sound_etf sign_etf_threefold_mono sign_etf_cone_compatible
              side_solve_dom gs])
  show ?thesis using collect collect_exit by blast
qed

end


