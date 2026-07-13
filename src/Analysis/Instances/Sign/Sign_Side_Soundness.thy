theory Sign_Side_Soundness
  imports Sign_Domain TD_Side_Eff_Soundness Retain_Analysis
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
  "etf_combine sign_etf cc ex = unit_combine_tree cc ex"
  unfolding sign_etf_def etf_combine_mixed_of_transfer by simp

lemma sign_sound_etf:
  "sound_effectful_transfer sign_etf"
  unfolding sign_etf_def
  by (rule sound_effectful_transfer_mixed_of_transfer
        [OF sign_is_sound_transfer sign_tf_local_edge_invariant])

lemma sign_etf_cone_compatible: "cone_compatible_etf sign_etf"
  by (rule cone_compatible_etf_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_combine_tree])

lemma sign_etf_threefold_mono:
  "threefold_mono (side_cfg_T_eff g sign_etf bot0 s0 ())"
  by (rule threefold_mono_local_unit_transfer
       [OF sign_etf_edge_tree_mixed sign_etf_combine_tree sign_tf_mono])

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
  "etf_combine sign_etf_unit cc ex = unit_combine_tree cc ex"
  unfolding sign_etf_unit_def etf_combine_unit_of_transfer by simp

lemma sign_sound_etf_unit:
  "sound_effectful_transfer sign_etf_unit"
  unfolding sign_etf_unit_def
  by (rule sound_effectful_transfer_unit_of_transfer [OF sign_is_sound_transfer])

definition sign_etf_retain :: "(unit, sign) effectful_domain_transfer" where
  "sign_etf_retain = retain_etf_of_transfer sign_tf"

lemma sign_etf_retain_edge_tree:
  "apply_etf sign_etf_retain a u = retain_edge_tree (apply_tf sign_tf a) u"
  unfolding sign_etf_retain_def apply_etf_retain_of_transfer by simp

lemma sign_etf_retain_combine_tree:
  "etf_combine sign_etf_retain cc ex = unit_combine_tree cc ex"
  unfolding sign_etf_retain_def etf_combine_retain_of_transfer by simp

lemma sign_sound_etf_retain:
  "sound_effectful_transfer sign_etf_retain"
  unfolding sign_etf_retain_def
  by (rule sound_effectful_transfer_retain_of_transfer [OF sign_is_sound_transfer])

lemma sign_etf_retain_enter:
  "etf_enter sign_etf_retain u = retain_edge_tree enter_sign u"
proof -
  have tf: "apply_tf sign_tf EA_Enter = enter_sign"
    by (simp add: sign_tf_def fun_eq_iff)
  have "etf_enter sign_etf_retain u = apply_etf sign_etf_retain EA_Enter u" by simp
  also have "\<dots> = retain_edge_tree (apply_tf sign_tf EA_Enter) u"
    by (rule sign_etf_retain_edge_tree)
  also have "\<dots> = retain_edge_tree enter_sign u" by (simp add: tf)
  finally show ?thesis .
qed

text \<open>
  The fresh callee frame for the sign enter transfer: locals reset to @{term STop}
  (the abstraction of the zeroed callee frame), globals bot.  It is exactly
  @{term \<open>restrict_local (enter_sign x)\<close>}, independent of the input @{term x}.
\<close>

definition fresh_frame_sign :: "sign abs_state" where
  "fresh_frame_sign = (\<lambda>x. if is_global x then \<bottom> else STop)"

lemma sign_etf_unit_enter:
  "etf_enter sign_etf_unit u = unit_edge_tree enter_sign u"
proof -
  have tf: "apply_tf sign_tf EA_Enter = enter_sign"
    by (simp add: sign_tf_def fun_eq_iff)
  have "etf_enter sign_etf_unit u = apply_etf sign_etf_unit EA_Enter u" by simp
  also have "\<dots> = unit_edge_tree (apply_tf sign_tf EA_Enter) u"
    by (rule sign_etf_unit_edge_tree)
  also have "\<dots> = unit_edge_tree enter_sign u" by (simp add: tf)
  finally show ?thesis .
qed

lemma sign_sound_etf_unit_framed:
  "sound_effectful_transfer_framed sign_etf_unit fresh_frame_sign"
proof (rule sound_effectful_transfer_framed.intro)
  show "sound_effectful_transfer sign_etf_unit" by (rule sign_sound_etf_unit)
next
  show "sound_effectful_transfer_framed_axioms sign_etf_unit fresh_frame_sign"
    unfolding sound_effectful_transfer_framed_axioms_def
  proof (intro allI impI)
    fix u and \<sigma> :: "pp + unit \<Rightarrow> sign abs_state"
    assume inr: "inr_slot_locals_bot \<sigma>" and inl: "inl_slot_globals_bot \<sigma>"
    have "etf_full (etf_enter sign_etf_unit u) \<sigma>
            = enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      by (simp add: sign_etf_unit_enter etf_full_unit_edge_tree)
    also have "\<dots> \<le> fresh_frame_sign \<squnion> glob_env \<sigma>"
    proof (rule le_funI)
      fix x
      show "enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())) x \<le> (fresh_frame_sign \<squnion> glob_env \<sigma>) x"
      proof (cases "is_global x")
        case True
        have "\<sigma> (Inl u) x = \<bottom>" using inl True by (simp add: inl_slot_globals_bot_def)
        thus ?thesis using True
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit)
      next
        case False
        thus ?thesis
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit)
      qed
    qed
    finally show "etf_full (etf_enter sign_etf_unit u) \<sigma>
                    \<le> fresh_frame_sign \<squnion> glob_env \<sigma>" .
  qed
qed

text \<open>
  Retain companion: the enter bound also holds under the weaker
  @{const inl_glob_le_glob_env} premise, so the retain Sign spine (local slots
  carrying globals) discharges the framed contract.  Same proof, but the global
  case bounds @{term "\<sigma> (Inl u) x"} by @{const glob_env} rather than forcing it to
  @{term \<bottom>}.
\<close>
lemma sign_sound_etf_unit_framed_le:
  "sound_effectful_transfer_framed_le sign_etf_unit fresh_frame_sign"
proof (rule sound_effectful_transfer_framed_le.intro)
  show "sound_effectful_transfer sign_etf_unit" by (rule sign_sound_etf_unit)
next
  show "sound_effectful_transfer_framed_le_axioms sign_etf_unit fresh_frame_sign"
    unfolding sound_effectful_transfer_framed_le_axioms_def
  proof (intro allI impI)
    fix u and \<sigma> :: "pp + unit \<Rightarrow> sign abs_state"
    assume inr: "inr_slot_locals_bot \<sigma>" and inl: "inl_glob_le_glob_env \<sigma>"
    have "etf_full (etf_enter sign_etf_unit u) \<sigma>
            = enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      by (simp add: sign_etf_unit_enter etf_full_unit_edge_tree)
    also have "\<dots> \<le> fresh_frame_sign \<squnion> glob_env \<sigma>"
    proof (rule le_funI)
      fix x
      show "enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())) x \<le> (fresh_frame_sign \<squnion> glob_env \<sigma>) x"
      proof (cases "is_global x")
        case True
        have "\<sigma> (Inl u) x \<le> glob_env \<sigma> x"
          using inl True by (simp add: inl_glob_le_glob_env_def)
        thus ?thesis using True
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit sup_fun_def le_sup_iff)
      next
        case False
        thus ?thesis
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit)
      qed
    qed
    finally show "etf_full (etf_enter sign_etf_unit u) \<sigma>
                    \<le> fresh_frame_sign \<squnion> glob_env \<sigma>" .
  qed
qed

lemma sign_sound_etf_retain_framed_le:
  "sound_effectful_transfer_framed_le sign_etf_retain fresh_frame_sign"
proof (rule sound_effectful_transfer_framed_le.intro)
  show "sound_effectful_transfer sign_etf_retain" by (rule sign_sound_etf_retain)
next
  show "sound_effectful_transfer_framed_le_axioms sign_etf_retain fresh_frame_sign"
    unfolding sound_effectful_transfer_framed_le_axioms_def
  proof (intro allI impI)
    fix u and \<sigma> :: "pp + unit \<Rightarrow> sign abs_state"
    assume inr: "inr_slot_locals_bot \<sigma>" and inl: "inl_glob_le_glob_env \<sigma>"
    have "etf_full (etf_enter sign_etf_retain u) \<sigma>
            = enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
      by (simp add: sign_etf_retain_enter etf_full_retain_edge_tree)
    also have "\<dots> \<le> fresh_frame_sign \<squnion> glob_env \<sigma>"
    proof (rule le_funI)
      fix x
      show "enter_sign (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())) x \<le> (fresh_frame_sign \<squnion> glob_env \<sigma>) x"
      proof (cases "is_global x")
        case True
        have "\<sigma> (Inl u) x \<le> glob_env \<sigma> x"
          using inl True by (simp add: inl_glob_le_glob_env_def)
        thus ?thesis using True
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit sup_fun_def le_sup_iff)
      next
        case False
        thus ?thesis
          by (simp add: enter_sign_def fresh_frame_sign_def glob_env_unit)
      qed
    qed
    finally show "etf_full (etf_enter sign_etf_retain u) \<sigma>
                    \<le> fresh_frame_sign \<squnion> glob_env \<sigma>" .
  qed
qed

lemma sign_etf_unit_cone_compatible: "cone_compatible_etf sign_etf_unit"
  by (rule cone_compatible_etf_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree])

lemma sign_etf_unit_threefold_mono:
  "threefold_mono (side_cfg_T_eff g sign_etf_unit bot0 s0 ())"
  by (rule threefold_mono_unit_transfer
       [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree sign_tf_mono])

section \<open>Sign domain: standalone effectful interprocedural soundness\<close>

text \<open>
  Headline soundness for the Sign analysis, stated against the effectful side IP
  solver (side_analyse_eff).  Cone compatibility and threefold monotonicity are
  discharged from the native sign_etf record shape; the unit seed-slot () carries
  the initial globals.
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

