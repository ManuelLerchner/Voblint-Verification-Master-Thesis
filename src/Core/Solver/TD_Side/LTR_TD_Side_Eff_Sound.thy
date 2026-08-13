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
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
    and bound: "etf_full (apply_etf etf a u) \<sigma> \<le> side_env_lift \<sigma> v"
    and s: "s \<in> gamma_state_lift (side_env_lift \<sigma> u)"
    and step: "s' \<in> edge_step a s"
  shows "s' \<in> gamma_state_lift (side_env_lift \<sigma> v)"
proof -
  have m: "s' \<in> edge_collect a {s}" using step by (simp add: edge_collect_single)
  have "edge_collect a {s} \<subseteq> edge_collect a (gamma_state_lift (side_env_lift \<sigma> u))"
    using s edge_collect_mono by blast
  also have "\<dots> \<subseteq> gamma_state_lift (etf_collecting_full_lift (apply_etf etf a u) \<sigma>)"
    by (rule edge_collect_etf_sound[OF inr])
  also have "\<dots> \<subseteq> gamma_state_lift (side_env_lift \<sigma> v)"
    using gamma_lift_mono[OF gamma_state_mono etf_collecting_full_le_side_env_lift[OF bound]]
    by (simp add: bound etf_collecting_full_le_side_env_lift
        gamma_lift_mono gamma_state_mono)
  finally show ?thesis using m by blast
qed

text \<open>Single-store call-entry soundness under an effectful post-fixpoint bound: the
  reassembled effectful enter transfer over the call site dominates the concrete
  \<^const>\<open>call_enter\<close>.  Discharges the \<open>CALL\<close> closure obligation.\<close>
lemma call_enter_sound_eff:
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
    and bound: "etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env_lift \<sigma> v"
    and s: "s \<in> gamma_state_lift (side_env_lift \<sigma> u)"
  shows "call_enter gs (CallEdge dst pars args) s \<in> gamma_state_lift (side_env_lift \<sigma> v)"
proof -
  have "call_enter gs (CallEdge dst pars args) s
          \<in> gamma_state_lift (etf_collecting_full_lift (etf_enter etf pars args u) \<sigma>)"
    using etf_sound_enter inr s unfolding side_env_lift_def call_enter_CallEdge by auto
  also have "gamma_state_lift (etf_collecting_full_lift (etf_enter etf pars args u) \<sigma>)
               \<subseteq> gamma_state_lift (side_env_lift \<sigma> v)"
    using gamma_lift_mono[OF gamma_state_mono etf_collecting_full_le_side_env_lift[OF bound]]
    by fastforce
  finally show ?thesis .
qed

text \<open>Effectful collecting soundness at a program point is stated over the stack-faithful
  \<^const>\<open>ltr_collect\<close> and proved through \<^locale>\<open>ltr_gamma\<close>.\<close>
theorem ltr_post_fixpoint_sound_at_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
  assumes inr: "inr_slot_locals_bot gs \<sigma>"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> intra g
       \<Longrightarrow> etf_full (apply_etf etf a u) \<sigma> \<le> side_env_lift \<sigma> w"
  assumes enter_le:
    "\<And>u dst pars args p cont. (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       etf_full (etf_enter etf pars args u) \<sigma> \<le> side_env_lift \<sigma> (FunctionEntry p)"
  assumes combine_le:
    "\<And>cl dst pars args p cont. (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma> \<le> side_env_lift \<sigma> cont"
  assumes entry_le: "Lifted s0 \<le> side_env_lift \<sigma> (cfg_entry g)"
  shows "ltr_collect gs g S v0 \<subseteq> gamma_state_lift (side_env_lift \<sigma> v0)"
proof -
  interpret G: ltr_gamma g S "\<lambda>v _. gamma_state_lift (side_env_lift \<sigma> v)"
      "admiss_exact (\<lambda>_ _ _. ())" "()" gs
  proof (standard, goal_cases ROOT EDGE ADMISS_TOTAL CALL COMB)
    case (ROOT s)
    then show ?case
      using S_sound gamma_lift_mono[OF gamma_state_mono entry_le] by force
  next
    case (EDGE u a v c s s')
    show ?case
      by (rule edge_step_sound_eff[OF inr step_le[OF EDGE(1)] EDGE(2) EDGE(3)])
  next
    case ADMISS_TOTAL
    show ?case by (simp add: admiss_exact_def)
  next
    case (CALL u dst pars args p cont c s c')
    show ?case
      by (rule call_enter_sound_eff[OF inr enter_le[OF CALL(1)] CALL(2)])
  next
    case (COMB cl dst pars args p cont c1 c2 s t es)
    have "combine_collect gs dst s t
            \<in> gamma_state_lift (etf_full (etf_combine etf dst cl (FunctionResult p)) \<sigma>)"
      using etf_sound_combine inr COMB(2) COMB(4) unfolding side_env_lift_def by auto
    then show ?case
      using gamma_lift_mono[OF gamma_state_mono combine_le[OF COMB(1)]] by fastforce
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S v0"
    then obtain u where u: "u \<in> valid_ltr gs g S" "sink_node u = v0" "sink_store u = x"
      unfolding ltr_collect_def by blast
    have gt: "G.bnd u" using G.valid_ltr_subset_gamma_ltr u(1) by (auto simp: G.gamma_ltr_def)
    have ck: "ctx_key (admiss_exact (\<lambda>_ _ _. ())) () u ()"
      by (simp add: ctx_key_exact_iff)
    have "sink_store u \<in> gamma_state_lift (side_env_lift \<sigma> (sink_node u))" using gt ck by blast
    then show "x \<in> gamma_state_lift (side_env_lift \<sigma> v0)" using u(2,3) by simp
  qed
qed

end

end
