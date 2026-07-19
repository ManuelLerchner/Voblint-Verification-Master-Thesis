theory LTR_Analysis_Sound
  imports Constraint_System_Sound "Voblint_CFG.LTR_Abstract"
begin

section \<open>Solver soundness against the stack-faithful semantics\<close>

text \<open>
  Monovariant solver soundness is stated directly against the stack-faithful local-trace collector
  \<^const>\<open>ltr_collect\<close>.  The proof interprets \<^locale>\<open>ltr_gamma\<close> at the context-free
  concretization \<open>acc v _ = \<lbrakk>env v\<rbrakk>\<close>, discharging ROOT, EDGE, SEED, and COMB from the
  transfer bounds.  Each COMB obligation follows one concrete caller/callee return.
\<close>



context sound_transfer
begin

lemma ltr_post_fixpoint_sound_at:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
    and S :: "store set" and v0 :: pp
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  assumes combine_le:
    "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
       combine_collect_abs dst (env c) (env ex) \<le> env ret"
  assumes entry_le: "s0 \<le> env (cfg_entry g)"
  shows "ltr_collect g S v0 \<subseteq> \<lbrakk>env v0\<rbrakk>"
proof -
  interpret G: ltr_gamma g S "\<lambda>v _. \<lbrakk>env v\<rbrakk>" "\<lambda>_ _. ()" "()"
  proof (standard, goal_cases ROOT EDGE SEED COMB)
    case (ROOT s)
    then show ?case using S_sound gamma_state_mono[OF entry_le] by blast
  next
    case (EDGE u a v c s s')
    show ?case by (rule edge_of_bound[OF step_le[OF EDGE(1)] EDGE(3) EDGE(4)])
  next
    case (SEED u v c s s' xs es)
    show ?case by (rule edge_of_bound[OF step_le[OF SEED(1)] SEED(2) SEED(3)])
  next
    case (COMB cl ex v dst c1 s t es)
    have "combine_collect dst s t \<in> \<lbrakk>combine_collect_abs dst (env cl) (env ex)\<rbrakk>"
      using combine_collect_sound[OF COMB(2) COMB(3)] by simp
    then show ?case
      using gamma_state_mono[OF combine_le[OF COMB(1)]] by blast
  qed
  show ?thesis
  proof
    fix x assume "x \<in> ltr_collect g S v0"
    then obtain u where u: "u \<in> valid_ltr g S" "sink_node u = v0" "sink_store u = x"
      unfolding ltr_collect_def by blast
    have "u \<in> G.gamma_ltr" using G.valid_ltr_subset_gamma_ltr u(1) by blast
    then have "sink_store u \<in> \<lbrakk>env (sink_node u)\<rbrakk>" by (simp add: G.gamma_ltr_def)
    then show "x \<in> \<lbrakk>env v0\<rbrakk>" using u(2,3) by simp
  qed
qed

theorem unified_ltr_post_fixpoint_sound:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "ltr_collect g S v \<subseteq> \<lbrakk>env v\<rbrakk>"
proof -
  have step_le: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  proof -
    fix u a w assume e: "(u, a, w) \<in> edges g"
    have "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env w"
      by (rule apply_tf_le_rhs[OF fin finC e])
    also have "\<dots> \<le> env w" using post_fp unfolding is_post_fixpoint_def by simp
    finally show "apply_tf tf a (env u) \<le> env w" .
  qed
  have combine_le: "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
       combine_collect_abs dst (env c) (env ex) \<le> env ret"
  proof -
    fix c ex ret dst assume ce: "(c, ex, ret, dst) \<in> combines g"
    have "combine_collect_abs dst (env c) (env ex) \<le> rhs g tf (\<squnion>) bot s0 env ret"
      by (rule combine_collect_abs_le_rhs[OF fin finC ce])
    also have "\<dots> \<le> env ret" using post_fp unfolding is_post_fixpoint_def by simp
    finally show "combine_collect_abs dst (env c) (env ex) \<le> env ret" .
  qed
  have entry_le: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin finC]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  show ?thesis
  proof (rule ltr_post_fixpoint_sound_at)
    show "S \<le> \<lbrakk>s0\<rbrakk>" by (rule S_sound)
    show "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
      by (rule step_le)
    show "\<And>c ex ret dst. (c, ex, ret, dst) \<in> combines g \<Longrightarrow>
            combine_collect_abs dst (env c) (env ex) \<le> env ret"
      by (rule combine_le)
    show "s0 \<le> env (cfg_entry g)" by (rule entry_le)
  qed
qed

end

end
