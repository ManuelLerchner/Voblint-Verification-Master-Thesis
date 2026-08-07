theory LTR_Analysis_Sound
  imports Constraint_System_Sound "Voblint_CFG.LTR_Abstract"
begin

section \<open>Solver soundness against the stack-faithful semantics\<close>

text \<open>
  Monovariant solver soundness is stated directly against the stack-faithful local-trace collector
  \<^const>\<open>ltr_collect\<close>.  The bound is discharged through \<open>ltr_collect_semantic_postfix\<close> at the
  context-free candidate \<open>B v = \<lbrakk>env v\<rbrakk>\<close>: ROOT from the entry bound, EDGE from \<^const>\<open>apply_tf\<close>
  soundness, CALL from \<^const>\<open>tf_enter\<close> soundness, and COMB from \<^const>\<open>tf_combine_collect_abs\<close>
  soundness.  The three transfer sources are the intra predecessors, the callee-entry
  contributions over \<^const>\<open>calls\<close>, and the return combines over \<^const>\<open>calls\<close>.
\<close>



context sound_transfer_for
begin

lemma ltr_post_fixpoint_sound_at_for:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
    and S :: "store set" and v0 :: pp
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  assumes call_le:
    "\<And>c dst fs as p cont. (c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       tf_enter tf fs as (env c) \<le> env (FunctionEntry p)"
  assumes combine_le:
    "\<And>c dst fs as p cont. (c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       tf_combine_collect_abs tf dst (env c) (env (FunctionResult p)) \<le> env cont"
  assumes entry_le: "s0 \<le> env (cfg_entry g)"
  shows "ltr_collect gs g S v0 \<subseteq> \<lbrakk>env v0\<rbrakk>"
proof (rule ltr_collect_semantic_postfix)
  show "S \<subseteq> \<lbrakk>env (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
next
  fix u a w s s'
  assume "(u, a, w) \<in> intra g" and "s \<in> \<lbrakk>env u\<rbrakk>" and "s' \<in> edge_step a s"
  then show "s' \<in> \<lbrakk>env w\<rbrakk>" by (rule edge_of_bound[OF step_le])
next
  fix u dst pars args p cont s
  assume e: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and s: "s \<in> \<lbrakk>env u\<rbrakk>"
  show "call_enter gs (CallEdge dst pars args) s \<in> \<lbrakk>env (FunctionEntry p)\<rbrakk>"
    by (rule call_enter_of_bound_for[OF call_le[OF e] s])
next
  fix cl dst pars args p cont s t
  assume e: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and s: "s \<in> \<lbrakk>env cl\<rbrakk>" and t: "t \<in> \<lbrakk>env (FunctionResult p)\<rbrakk>"
  show "combine_collect gs dst s t \<in> \<lbrakk>env cont\<rbrakk>"
    by (rule combine_of_bound_for[OF combine_le[OF e] s t])
qed

theorem unified_ltr_post_fixpoint_sound_for:
  fixes g :: cfg and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes finI: "finite (intra g)"
  assumes finC: "finite (calls g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  shows "ltr_collect gs g S v \<subseteq> \<lbrakk>env v\<rbrakk>"
proof -
  have step_le: "\<And>u a w. (u, a, w) \<in> intra g \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  proof -
    fix u a w assume e: "(u, a, w) \<in> intra g"
    have "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env w"
      by (rule apply_tf_le_rhs[OF finI finC e])
    also have "\<dots> \<le> env w" using is_post_fixpointD[OF post_fp] .
    finally show "apply_tf tf a (env u) \<le> env w" .
  qed
  have call_le: "\<And>c dst fs as p cont. (c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       tf_enter tf fs as (env c) \<le> env (FunctionEntry p)"
  proof -
    fix c dst fs as p cont assume e: "(c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g"
    have "tf_enter tf fs as (env c) \<le> rhs g tf (\<squnion>) bot s0 env (FunctionEntry p)"
      by (rule tf_enter_le_rhs[OF finI finC e])
    also have "\<dots> \<le> env (FunctionEntry p)" using is_post_fixpointD[OF post_fp] .
    finally show "tf_enter tf fs as (env c) \<le> env (FunctionEntry p)" .
  qed
  have combine_le: "\<And>c dst fs as p cont. (c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g \<Longrightarrow>
       tf_combine_collect_abs tf dst (env c) (env (FunctionResult p)) \<le> env cont"
  proof -
    fix c dst fs as p cont assume e: "(c, CallEdge dst fs as, FunctionEntry p, cont) \<in> calls g"
    have "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p)) \<le> rhs g tf (\<squnion>) bot s0 env cont"
      by (rule tf_combine_le_rhs[OF finI finC e])
    also have "\<dots> \<le> env cont" using is_post_fixpointD[OF post_fp] .
    finally show "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p)) \<le> env cont" .
  qed
  have entry_le: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF finI finC]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  show ?thesis
    by (rule ltr_post_fixpoint_sound_at_for[OF S_sound step_le call_le combine_le entry_le])
qed

end

end
