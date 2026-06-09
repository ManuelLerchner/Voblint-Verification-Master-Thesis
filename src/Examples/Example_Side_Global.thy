section \<open>Example: TD\_side Sign Analysis on a Global Assign\<close>

theory Example_Side_Global
  imports Sign_Side_Soundness CFG_Runs_To_Bridge
begin

text \<open>
  M3 witness (slice 0): a plain IMP program that writes a G-prefixed global.
  Discharges @{thm side_sign_analysis_sound} for @{const side_analyse} on sign.
\<close>

definition side_global_prog :: com where
  "side_global_prog = ''Gx'' ::= N 1"

definition side_global_s0 :: "sign abs_state" where
  "side_global_s0 = bot"

lemma side_global_s0_restrict_global:
  "restrict_global side_global_s0 = bot"
  unfolding side_global_s0_def restrict_global_def by (simp add: fun_eq_iff)

lemma side_global_prog_finite:
  "finite (edges (to_cfg side_global_prog))"
  by (rule to_cfg_finite)

lemma side_global_runs_to_exit:
  assumes "runs_to side_global_prog s t"
  shows "t \<in> cfg_collect (to_cfg side_global_prog) {s} (cfg_exit (to_cfg side_global_prog))"
  using assms unfolding runs_to_def by simp

theorem side_global_sign_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> sign_domain.gamma_state side_global_s0"
  assumes runs: "runs_to side_global_prog s t"
  assumes side_solve_dom:
    "side_cfg_solve_dom (to_cfg side_global_prog) sign_tf bot side_global_s0
       (cfg_exit (to_cfg side_global_prog))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse side_global_prog sign_tf bot side_global_s0
         (cfg_exit (to_cfg side_global_prog)))"
proof -
  from runs_to_imp_path[OF runs] obtain es where
    path: "cfg_path (to_cfg side_global_prog) (cfg_entry (to_cfg side_global_prog)) es
            (cfg_exit (to_cfg side_global_prog))"
    by blast
  show ?thesis
  proof (rule side_sign_analysis_sound)
    show "t \<in> cfg_collect (to_cfg side_global_prog) {s}
                    (cfg_exit (to_cfg side_global_prog))"
      using side_global_runs_to_exit[OF runs] .
    show "finite (edges (to_cfg side_global_prog))"
      by (rule side_global_prog_finite)
    show "cfg_path (to_cfg side_global_prog) (cfg_entry (to_cfg side_global_prog)) es
          (cfg_exit (to_cfg side_global_prog))"
      using path .
    show "side_cfg_solve_dom (to_cfg side_global_prog) sign_tf bot side_global_s0
          (cfg_exit (to_cfg side_global_prog))"
      using side_solve_dom .
    show "restrict_global side_global_s0 = bot"
      by (rule side_global_s0_restrict_global)
    show "s \<in> sign_domain.gamma_state side_global_s0"
      using s_sound .
  qed
qed

end
