section \<open>Example: TD\_side Sign Analysis on a Single Global Increment Call\<close>

theory Example_Side_Proc_Global
  imports Sign_Side_IP_Soundness CFG_Collect_IP_Adeq
begin

text \<open>
  Side-effecting interprocedural witness: @{const inc_pi} with a single call to
  procedure p.  Operational semantics via @{const pruns_to_ip}; soundness via
  @{const side_analyse_ip} (the side TD solver).  Mirrors the plain
  Example_Proc_Global.proc_global_sign_analysis on the side backend.
\<close>

definition side_proc_global_s0 :: "sign abs_state" where
  "side_proc_global_s0 = bot"

lemma side_proc_global_s0_restrict_global:
  "restrict_global side_proc_global_s0 = bot"
  unfolding side_proc_global_s0_def restrict_global_def by (simp add: fun_eq_iff)

theorem proc_global_side_sign_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> sign_domain.gamma_state side_proc_global_s0"
  assumes runs: "pruns_to_ip inc_pi [''p''] (PCall ''p'') s t"
  assumes side_solve_dom:
    "side_cfg_ip_solve_dom (compile_prog inc_pi [''p''] (PCall ''p'')) sign_tf bot
       side_proc_global_s0
       (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_ip inc_pi [''p''] (PCall ''p'') sign_tf bot side_proc_global_s0
         (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p''))))"
proof -
  have collect_exit:
    "t \<in> cfg_collect_ip (compile_prog inc_pi [''p''] (PCall ''p'')) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
    using runs unfolding pruns_to_ip_def
    by (metis singleton_store_def)
  show ?thesis
    by (rule side_ip_sign_analysis_sound[OF s_sound collect_exit side_solve_dom
          side_proc_global_s0_restrict_global])
qed

end
