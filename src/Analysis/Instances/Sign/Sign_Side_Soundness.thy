theory Sign_Side_Soundness
  imports Sign_Domain Voblint_Core.LTR_TD_Side_Eff_Exit
begin

section \<open>Sign domain: effectful transfer instance\<close>

text \<open>
  The Sign domain provides the effectful transfer record consumed by TD_side.
  @{const mixed_etf_of_transfer} dispatches local edges to
  @{const local_edge_tree} and global edges to @{const unit_edge_tree}.
\<close>

definition sign_etf :: "(vname \<Rightarrow> bool) \<Rightarrow> (unit, sign) effectful_domain_transfer" where
  "sign_etf gs = mixed_etf_of_transfer gs (sign_tf_for gs)"

lemma sign_etf_edge_tree:
  "apply_etf (sign_etf gs) a u = mixed_etf_edge_tree gs (sign_tf_for gs) a u"
  unfolding sign_etf_def apply_etf_mixed_of_transfer by simp

lemma sign_etf_edge_tree_mixed:
  "apply_etf (sign_etf gs) a u =
   (if local_edge_action gs a then local_edge_tree gs (apply_tf (sign_tf_for gs) a) u
    else unit_edge_tree gs (apply_tf (sign_tf_for gs) a) u)"
  unfolding sign_etf_def apply_etf_mixed_of_transfer mixed_etf_edge_tree_def by simp

lemma sign_etf_combine_tree:
  "etf_combine (sign_etf gs) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding sign_etf_def etf_combine_mixed_of_transfer by simp

lemma sign_etf_enter_tree:
  "etf_enter (sign_etf gs) fs as cl = unit_edge_tree gs (enter\<^sup># (sign_tf_for gs) fs as) cl"
  unfolding sign_etf_def mixed_etf_of_transfer_def by simp

lemma sign_tf_for_enter_mono:
  "s1 \<le> s2 \<Longrightarrow> enter\<^sup># (sign_tf_for gs) fs as s1 \<le> enter\<^sup># (sign_tf_for gs) fs as s2"
  by (simp add: sign_tf_for_def enter_sign_for_mono)

lemma sign_sound_etf:
  "sound_effectful_transfer gs (sign_etf gs)"
  unfolding sign_etf_def
  by (rule sound_effectful_transfer_mixed_of_transfer
        [OF sign_is_sound_transfer_for sign_tf_local_edge_invariant])

lemma sign_etf_cone_compatible: "cone_compatible_etf gs (sign_etf gs)"
  by (rule cone_compatible_etf_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_enter_tree sign_etf_combine_tree])

lemma sign_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g (sign_etf gs) bot0 s0 ())"
  by (rule threefold_mono_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_enter_tree sign_etf_combine_tree
           sign_tf_for_mono sign_tf_for_enter_mono])

subsection \<open>Unit-only sign ETF (executable transport)\<close>

text \<open>
  Exec soundness bridges unit-shaped executable trees to this abstract
  unit-only effectful record.  The mixed @{const sign_etf} is for
  @{const side_analyse_eff}.
\<close>

definition sign_etf_unit :: "(vname \<Rightarrow> bool) \<Rightarrow> (unit, sign) effectful_domain_transfer" where
  "sign_etf_unit gs = unit_etf_of_transfer gs (sign_tf_for gs)"

lemma sign_etf_unit_edge_tree:
  "apply_etf (sign_etf_unit gs) a u = unit_edge_tree gs (apply_tf (sign_tf_for gs) a) u"
  unfolding sign_etf_unit_def apply_etf_unit_of_transfer by simp

lemma sign_etf_unit_combine_tree:
  "etf_combine (sign_etf_unit gs) dst cc ex = unit_combine_tree gs dst cc ex"
  unfolding sign_etf_unit_def etf_combine_unit_of_transfer by simp

lemma sign_etf_unit_enter_tree_tf:
  "etf_enter (sign_etf_unit gs) fs as cl = unit_edge_tree gs (enter\<^sup># (sign_tf_for gs) fs as) cl"
  unfolding sign_etf_unit_def unit_etf_of_transfer_def by simp

lemma sign_etf_unit_enter_tree:
  "etf_enter (sign_etf_unit gs) xs es u =
    unit_edge_tree gs (\<lambda>s. bind_formals_abs xs
      (map (\<lambda>e. aval_sign e s) es) (enter_frame_sign_for gs s)) u"
proof -
  have enter:
    "enter_sign_for gs xs es = (\<lambda>s. bind_formals_abs xs
      (map (\<lambda>e. aval_sign e s) es) (enter_frame_sign_for gs s))"
    by (rule ext) (simp add: enter_sign_for_def enter_D_def enter_frame_sign_for_def)
  show ?thesis
    unfolding sign_etf_unit_def unit_etf_of_transfer_def
    by (simp add: sign_tf_for_def enter)
qed

lemma sign_sound_etf_unit:
  "sound_effectful_transfer gs (sign_etf_unit gs)"
  unfolding sign_etf_unit_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF sign_is_sound_transfer_for])


lemma sign_etf_unit_cone_compatible: "cone_compatible_etf gs (sign_etf_unit gs)"
  by (rule cone_compatible_etf_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_enter_tree_tf sign_etf_unit_combine_tree])

lemma sign_etf_unit_threefold_mono:
  "threefold_mono (side_cfg_T_eff gs g (sign_etf_unit gs) bot0 s0 ())"
  by (rule threefold_mono_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_enter_tree_tf sign_etf_unit_combine_tree
           sign_tf_for_mono sign_tf_for_enter_mono])

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
    "t \<in> ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  assumes side_solve_dom:
    "side_cfg_solve_dom_eff gs (compile_prog \<Pi> ps mnm main) (sign_etf gs) bot s0 ()
       (cfg_exit (compile_prog \<Pi> ps mnm main))"
  shows "t \<in> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (sign_etf gs) bot s0 ()
         (cfg_exit (compile_prog \<Pi> ps mnm main)))"
proof -
  have sub: "{s} \<le> \<lbrakk>s0\<rbrakk>" using s_sound by simp
  have collect:
    "ltr_collect gs (compile_prog \<Pi> ps mnm main) {s}
       (cfg_exit (compile_prog \<Pi> ps mnm main))
     \<le> gamma_state_lift (side_analyse_eff gs \<Pi> ps mnm main (sign_etf gs) bot s0 ()
           (cfg_exit (compile_prog \<Pi> ps mnm main)))"
    by (rule side_analyse_eff_collect_sound_exit_ltr_cone
          [OF sign_sound_etf sign_etf_threefold_mono sign_etf_cone_compatible
              side_solve_dom sub])
  show ?thesis using collect collect_exit by blast
qed

end


