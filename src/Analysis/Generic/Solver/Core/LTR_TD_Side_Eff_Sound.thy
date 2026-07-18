theory LTR_TD_Side_Eff_Sound
  imports TD_Side_Eff_Sound "Voblint_CFG.LTR_Abstract"
begin

section \<open>Effectful solver soundness against the stack-faithful semantics\<close>

text \<open>
  The effectful analogue of \<open>Voblint_Analysis.LTR_Analysis_Sound\<close>: a post-fixpoint of the
  effectful equation system soundly over-approximates the stack-faithful local-trace collecting
  \<^const>\<open>ltr_collect\<close>, stated directly over traces and proved through the domain-free interface
  \<^locale>\<open>ltr_gamma\<close> (\<^theory>\<open>Voblint_CFG.LTR_Abstract\<close>).

  Where the raw-CFG \<open>post_fixpoint_sound_at_eff\<close> concludes \<open>cfg_collect g S v0 <= gamma\<close> through the
  \<^const>\<open>cfg_witness\<close> induction, this concludes \<open>ltr_collect g S v0 <= gamma\<close> by interpreting
  \<^locale>\<open>ltr_gamma\<close> at the context-free concretization \<open>acc v _ = \<lbrakk>side_env sigma v\<rbrakk>\<close>.  The four
  closure obligations are discharged from exactly the effectful per-step bounds the raw-CFG proof
  uses (\<open>edge_collect_etf_sound\<close>, \<open>etf_collecting_full_le_side_env\<close>, \<open>etf_sound_combine\<close>); the
  \<open>COMB\<close> obligation only ever sees the caller and callee-exit slots of a single combine triple, so
  no caller/callee product is reconstructed --- the matched relation is supplied by
  \<^const>\<open>valid_ltr\<close>.  The proof does NOT route \<open>ltr_collect_le_cfg_collect\<close> then the broad
  \<^const>\<open>cfg_collect\<close> soundness --- that bridge is compatibility only.

  The raw-CFG \<open>post_fixpoint_sound_at_eff\<close> (over \<^const>\<open>cfg_collect\<close>) and its pruned consumers
  (\<open>side_collect_sound_exit_pruned_eff\<close>, \<open>side_analyse_eff_collect_sound_at\<close>) are retained
  unchanged.  This theory sits in a separate leaf: importing the trace stack brings
  \<^const>\<open>ltr.Call\<close> into scope, which shadows the bare \<open>Call\<close> constructor used in monovariant CFG
  examples, so the trace-based statement is kept off the effectful spine's wide consumer set.
\<close>

context sound_effectful_transfer
begin

text \<open>Single-store edge soundness under an effectful post-fixpoint bound: mirrors
  \<open>edge_of_bound\<close> for the reassembled effectful transfer.  Shared by the intra (\<open>EDGE\<close>) and
  enter (\<open>SEED\<close>) closure obligations.\<close>
lemma edge_step_sound_eff:
  assumes inr: "inr_slot_locals_bot \<sigma>"
    and bound: "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> v"
    and s: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
    and step: "edge_step a s = Some s'"
  shows "s' \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>side_env \<sigma> u\<rbrakk>"
    using s edge_collect_mono by blast
  also have "\<dots> \<subseteq> \<lbrakk>etf_collecting_full (apply_etf etf a u) \<sigma>\<rbrakk>"
    by (rule edge_collect_etf_sound[OF inr])
  also have "\<dots> \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    using gamma_state_mono[OF etf_collecting_full_le_side_env[OF bound]] by blast
  finally show ?thesis using m by blast
qed

text \<open>Effectful collecting soundness at a program point, stated over the stack-faithful
  \<^const>\<open>ltr_collect\<close>.  Mirrors \<open>post_fixpoint_sound_at_eff\<close>, with the same hypotheses, but its
  conclusion is over traces and its proof rides on \<^locale>\<open>ltr_gamma\<close> rather than the broad
  \<^const>\<open>cfg_witness\<close> induction.\<close>
theorem ltr_post_fixpoint_sound_at_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf dst c ex) \<sigma> \<le> side_env \<sigma> ret"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  shows "ltr_collect g S v0 \<subseteq> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v _. \<lbrakk>side_env \<sigma> v\<rbrakk>" "\<lambda>_ _. ()" "()"
  proof (standard, goal_cases ROOT EDGE SEED COMB)
    case (ROOT s)
    then show ?case using S_sound gamma_state_mono[OF entry_le] by blast
  next
    case (EDGE u a v c s s')
    show ?case
      by (rule edge_step_sound_eff[OF inr step_le[OF EDGE(1)] EDGE(3) EDGE(4)])
  next
    case (SEED u v c s s' xs es)
    show ?case
      by (rule edge_step_sound_eff[OF inr step_le[OF SEED(1)] SEED(2) SEED(3)])
  next
    case (COMB cl ex v dst c1 s t es)
    have "combine_collect dst s t \<in> \<lbrakk>etf_full (etf_combine etf dst cl ex) \<sigma>\<rbrakk>"
      using etf_sound_combine inr COMB(2) COMB(3) unfolding side_env_def by auto
    then show ?case
      using gamma_state_mono[OF combine_le[OF COMB(1)]] by blast
  qed
  show ?thesis
  proof
    fix x assume "x \<in> ltr_collect g S v0"
    then obtain u where u: "u \<in> valid_ltr g S" "sink_node u = v0" "sink_store u = x"
      unfolding ltr_collect_def by blast
    have "u \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr u(1) by blast
    then have "sink_store u \<in> \<lbrakk>side_env \<sigma> (sink_node u)\<rbrakk>" by (simp add: G.gamma_ltr_def)
    then show "x \<in> \<lbrakk>side_env \<sigma> v0\<rbrakk>" using u(2,3) by simp
  qed
qed

end

end
