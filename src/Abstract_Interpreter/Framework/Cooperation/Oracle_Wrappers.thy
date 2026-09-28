theory Oracle_Wrappers
  imports "Voblint_Framework.MCP_Spec"
begin

section \<open>Consulting the answers at an assignment\<close>

text \<open>
  A component that was written without queries can still use them through a
  wrapper around one transfer. At \<open>x = e\<close> it asks for the value of \<open>e\<close>; if the
  answer is a single integer \<open>n\<close>, the wrapper assigns the literal \<open>n\<close> instead
  of evaluating \<open>e\<close> itself. The component's own assignment of that literal
  then covers the concrete successor, because \<open>e\<close> evaluates to \<open>n\<close> at every
  store the answer holds at.
\<close>

definition assign_ask ::
  "(answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D) \<Rightarrow> answers \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D" where
  "assign_ask asn A x e d =
     (case answer_const (A (EvalInt e)) of
        Some n \<Rightarrow> asn A x (N n) d
      | None \<Rightarrow> asn A x e d)"

text \<open>The wrapper keeps an assignment's law: where it substitutes the literal, the
  answer holds at the store, so the literal evaluates to what \<open>e\<close> does.\<close>

lemma assign_ask_sound:
  assumes "assign_sound gm asn"
  shows "assign_sound gm (assign_ask asn)"
  unfolding assign_sound_def
proof (intro allI impI)
  fix A x s y e
  assume s: "s \<in> gm x" and o: "eval_query.oracle_holds A s"
  have base: "s(y := \<lbrakk>e'\<rbrakk>\<^sub>e s) \<in> gm (asn A y e' x)" for e'
    using assms s o unfolding assign_sound_def by blast
  show "s(y := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gm (assign_ask asn A y e x)"
  proof (cases "answer_const (A (EvalInt e))")
    case None
    then show ?thesis using base[of e] by (simp add: assign_ask_def)
  next
    case (Some n)
    have "\<lbrakk>e\<rbrakk>\<^sub>e s = n"
      by (rule eval_holds_constD[OF eval_query.oracle_holdsD[OF o] Some])
    then show ?thesis using Some base[of "N n"] by (simp add: assign_ask_def)
  qed
qed


section \<open>A component that asks at its assignments\<close>

text \<open>
  The same wrapper around a whole component: at every assignment it asks the
  channel for the value of the right-hand side and runs the assignment on the
  literal when the answer is a single integer. It changes neither the
  component's concretization nor its entry, so soundness, framing and a single
  entry carry over. Where every answer is \<^term>\<open>\<top>\<close>, as when no active
  analysis answers, it is the component itself.
\<close>

definition ask_assign :: "'s mcp_component \<Rightarrow> 's mcp_component" where
  "ask_assign c = c\<lparr>mc_assign := assign_ask (mc_assign c)\<rparr>"

lemma ask_assign_step_cases:
  "mc_step (ask_assign c) A a x = mc_step c A a x
   \<or> (\<exists>y e n. a = EA_Assign y e \<and> answer_const (A (EvalInt e)) = Some n
        \<and> mc_step (ask_assign c) A a x = mc_step c A (EA_Assign y (N n)) x)"
  by (cases a) (auto simp: ask_assign_def assign_ask_def split: option.splits)

lemma answer_const_top [simp]: "answer_const \<top> = None"
  by (simp add: top_query_lift_def)

lemma ask_assign_top:
  assumes "\<And>q. A q = \<top>"
  shows "mc_step (ask_assign c) A a x = mc_step c A a x"
  by (cases a) (simp_all add: ask_assign_def assign_ask_def assms)

lemma single_entry_ask_assign: "single_entry c \<Longrightarrow> single_entry (ask_assign c)"
  by (simp add: single_entry_def ask_assign_def)

theorem ask_assign_frame:
  assumes frame: "mcp_frame c g"
  shows "mcp_frame (ask_assign c) g"
proof -
  have st: "g (mc_step c A a x) = g x" for A a x
    using frame unfolding mcp_frame_def by blast
  have "g (mc_step (ask_assign c) A a x) = g x" for A a x
    using ask_assign_step_cases[of c A a x] st by metis
  then show ?thesis
    using frame unfolding mcp_frame_def by (simp add: ask_assign_def)
qed

theorem ask_assign_sound:
  assumes sound: "mcp_component_sound \<G> gm c"
  shows "mcp_component_sound \<G> gm (ask_assign c)"
proof -
  have "assign_sound gm (mc_assign c)"
    using sound unfolding mcp_component_sound_def mc_step_sound_iff by blast
  then show ?thesis
    unfolding ask_assign_def by (rule mcp_component_sound_update(2)[OF sound assign_ask_sound])
qed

end
