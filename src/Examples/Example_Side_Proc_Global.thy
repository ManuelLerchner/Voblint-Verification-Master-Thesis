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

(* A non-trivial initial state: every variable -- including the globals --
   starts at STop, not bot.  Witnesses that the entry now seeds the initial
   globals, so soundness no longer needs restrict_global s0 = bot. *)
definition side_proc_global_s0 :: "sign abs_state" where
  "side_proc_global_s0 = (\<lambda>_. STop)"

theorem proc_global_side_sign_analysis:
  fixes s t :: store
  assumes s_sound: "s \<in> sign_domain.gamma_state side_proc_global_s0"
  assumes runs: "pruns_to_ip inc_pi [''p''] (Call ''p'') s t"
  assumes side_solve_dom:
    "side_cfg_ip_solve_dom (compile_prog inc_pi [''p''] (Call ''p'')) sign_tf bot
       side_proc_global_s0
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
  shows "t \<in> sign_domain.gamma_state
       (side_analyse_ip inc_pi [''p''] (Call ''p'') sign_tf bot side_proc_global_s0
         (cfg_exit (compile_prog inc_pi [''p''] (Call ''p''))))"
proof -
  have collect_exit:
    "t \<in> cfg_collect_ip (compile_prog inc_pi [''p''] (Call ''p'')) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')))"
    using runs unfolding pruns_to_ip_def
    by (metis singleton_store_def)
  show ?thesis
    by (rule side_ip_sign_analysis_sound[OF s_sound collect_exit side_solve_dom])
qed

end
