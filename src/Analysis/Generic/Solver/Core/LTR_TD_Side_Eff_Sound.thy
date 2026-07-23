theory LTR_TD_Side_Eff_Sound
  imports TD_Side_Eff_Sound "Voblint_CFG.LTR_Abstract"
begin

section \<open>Effectful solver soundness against the stack-faithful semantics\<close>

text \<open>
  Effectful equation-system soundness over the stack-faithful local-trace collector
  \<^const>\<open>ltr_collect\<close>.  The proof interprets \<^locale>\<open>ltr_gamma\<close> at
  \<open>acc v _ = \<lbrakk>side_env sigma v\<rbrakk>\<close>.  EDGE, SEED, and COMB are discharged by the
  effectful per-step bounds; each return uses one caller and one callee exit.
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

text \<open>Single-store call-entry soundness under an effectful post-fixpoint bound: the
  reassembled effectful enter transfer over the call site dominates the concrete
  \<^const>\<open>call_enter\<close>.  Discharges the \<open>CALL\<close> closure obligation.\<close>
lemma call_enter_sound_eff:
  assumes inr: "inr_slot_locals_bot \<sigma>"
    and bound: "etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> v"
    and s: "s \<in> \<lbrakk>side_env \<sigma> u\<rbrakk>"
  shows "call_enter (CallEdge dst pars args) s \<in> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  have "call_enter (CallEdge dst pars args) s
          \<in> \<lbrakk>etf_collecting_full (etf_enter etf pars args u) \<sigma>\<rbrakk>"
    using etf_sound_enter inr s unfolding side_env_def call_enter_CallEdge by auto
  also have "\<lbrakk>etf_collecting_full (etf_enter etf pars args u) \<sigma>\<rbrakk> \<subseteq> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    using gamma_state_mono[OF etf_collecting_full_le_side_env[OF bound]] by blast
  finally show ?thesis .
qed

text \<open>Effectful collecting soundness at a program point is stated over the stack-faithful
  \<^const>\<open>ltr_collect\<close> and proved through \<^locale>\<open>ltr_gamma\<close>.\<close>
theorem ltr_post_fixpoint_sound_at_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
  assumes inr: "inr_slot_locals_bot \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> intra g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  assumes enter_le:
    "\<And>u dst pars args p cont. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env \<sigma> (FunctionEntry p)"
  assumes combine_le:
    "\<And>cl dst pars args p cont. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env \<sigma> cont"
  assumes entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
  shows "ltr_collect g S v0 \<subseteq> \<lbrakk>side_env \<sigma> v0\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v _. \<lbrakk>side_env \<sigma> v\<rbrakk>" "\<lambda>_ _. ()" "()"
  proof (standard, goal_cases ROOT EDGE CALL COMB)
    case (ROOT s)
    then show ?case using S_sound gamma_state_mono[OF entry_le] by blast
  next
    case (EDGE u a v c s s')
    show ?case
      by (rule edge_step_sound_eff[OF inr step_le[OF EDGE(1)] EDGE(2) EDGE(3)])
  next
    case (CALL u dst pars args p cont c s)
    show ?case
      by (rule call_enter_sound_eff[OF inr enter_le[OF CALL(1)] CALL(2)])
  next
    case (COMB cl dst pars args p cont c1 s t es)
    have "combine_collect dst s t \<in> \<lbrakk>etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma>\<rbrakk>"
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
