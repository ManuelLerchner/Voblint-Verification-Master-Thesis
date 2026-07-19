section \<open>Example: two callers, matched returns over the stack-faithful semantics\<close>

theory Example_Proc_Call_LTR
  imports
    Example_Proc_Call
    "Voblint_Analysis.LTR_Analysis_Sound"
begin

text \<open>
  Recursive-shape validation for the R5 trace-based solver soundness path.  It reuses the
  interval analysis of \<^theory>\<open>Voblint_Examples.Example_Proc_Call\<close>, whose program calls the shared
  procedure \<open>inc\<close> from two distinct sites (nodes 6 and 8) --- two callers reaching the same
  callee.  The same exit interval is restated against the stack-faithful local-trace collecting
  \<^const>\<open>ltr_collect\<close>.

  The proof applies the trace-based \<open>unified_ltr_post_fixpoint_sound\<close> to the post-fixpoint
  \<open>main_prog_postfix\<close> supplies the transfer closure.  Soundness follows from
  \<^const>\<open>valid_ltr\<close>'s matched return rule inside the trace-native endpoint.
  reachable caller with every reachable callee exit.  No key injectivity is assumed and no solver
  equation is changed.

  This theory carries the trace-based statement in a separate leaf so that the concrete-CFG
  literals of \<^theory>\<open>Voblint_Examples.Example_Proc_Call\<close> (which use a bare \<open>Call\<close> constructor)
  are not shadowed by \<^const>\<open>ltr.Call\<close>.
\<close>

theorem main_prog_interval_analysis_ltr:
  assumes S_sound: "S \<le> \<lbrakk>main_prog_s0\<rbrakk>"
  assumes s: "s \<in> ltr_collect main_cfg S (cfg_exit main_cfg)"
  shows "s ''Gx'' \<in> gamma_ivl (Ivl (Fin 25) (Fin 25))"
proof -
  have fin_e: "finite (edges main_cfg)" by (simp add: main_cfg_edges)
  have fin_c: "finite (combines main_cfg)" by (simp add: main_cfg_combines)
  have le: "ltr_collect main_cfg S (cfg_exit main_cfg)
              \<subseteq> \<lbrakk>main_prog_env (cfg_exit main_cfg)\<rbrakk>"
    using sound_transfer.unified_ltr_post_fixpoint_sound
          [OF ivl_sound_tf.sound_transfer_axioms fin_e fin_c main_prog_postfix S_sound]
    by blast
  from s le have "s \<in> \<lbrakk>main_prog_env (cfg_exit main_cfg)\<rbrakk>" by blast
  then have "s ''Gx'' \<in> gamma (main_prog_env (cfg_exit main_cfg) ''Gx'')"
    unfolding gamma_state_def by blast
  then show ?thesis by (simp add: main_prog_env_def main_cfg_exit)
qed

end
