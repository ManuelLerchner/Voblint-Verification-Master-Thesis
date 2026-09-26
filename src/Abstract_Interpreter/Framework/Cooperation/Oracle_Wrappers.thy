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

text \<open>The question the wrapper needs, added to the ones the component already
  asks at an assignment.\<close>

definition assign_ask_qs ::
  "(edge_action \<Rightarrow> 'D \<Rightarrow> query list) \<Rightarrow> edge_action \<Rightarrow> 'D \<Rightarrow> query list" where
  "assign_ask_qs qs a d =
     (case a of
        EA_Assign x e \<Rightarrow> EvalInt e # qs a d
      | _ \<Rightarrow> qs a d)"

theorem sound_local_assign_ask:
  assumes "sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>"
  shows "sound_local_dg_spec qry sk (assign_ask asn) sp br bd rt en ev ce ca gammaD \<G>"
proof -
  interpret C: sound_local_dg_spec qry sk asn sp br bd rt en ev ce ca gammaD \<G>
    by (fact assms)
  have assign:
    "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gammaD (assign_ask asn A x e d)"
    if s: "s \<in> gammaD d" and o: "eval_query.oracle_holds A s" for s A x e d
  proof -
    have base: "s(x := \<lbrakk>e'\<rbrakk>\<^sub>e s) \<in> gammaD (asn A x e' d)" for e'
      using C.step_sound_local[of "EA_Assign x e'" d A] s o by auto
    show ?thesis
    proof (cases "answer_const (A (EvalInt e))")
      case None
      then show ?thesis using base[of e] by (simp add: assign_ask_def)
    next
      case (Some n)
      have "\<lbrakk>e\<rbrakk>\<^sub>e s = n"
        by (rule eval_holds_constD[OF eval_query.oracle_holdsD[OF o] Some])
      then show ?thesis
        using Some base[of "N n"] by (simp add: assign_ask_def)
    qed
  qed
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d')
    then show ?case by (rule C.gammaD_mono)
  next
    case (2 a d A)
    show ?case
    proof (cases a)
      case (EA_Assign x e)
      then show ?thesis using assign by auto
    qed (use C.step_sound_local[of a d A] in simp_all)
  next
    case (3 s d ci)
    then show ?case by (rule C.enter_sound_local)
  next
    case (4 s dc t de ci)
    then show ?case by (rule C.combine_sound_local)
  next
    case (5 s d q)
    then show ?case by (rule C.qry_sound)
  qed
qed


section \<open>A component that asks at its assignments\<close>

text \<open>
  The same wrapper around a whole component: it adds the question at every
  assignment and runs the assignment on the literal when the answer is a single
  integer. It changes neither the component's concretization nor its entry, so
  soundness, framing and a single entry carry over. Where every answer is
  \<^term>\<open>\<top>\<close>, as when no other active analysis answers, it is the component
  itself.
\<close>

definition ask_assign :: "'s mcp_component \<Rightarrow> 's mcp_component" where
  "ask_assign c = c\<lparr>
     mc_qs := assign_ask_qs (mc_qs c),
     mc_step := (\<lambda>A a x. case a of
        EA_Assign y e \<Rightarrow> assign_ask (\<lambda>A y e. mc_step c A (EA_Assign y e)) A y e x
      | _ \<Rightarrow> mc_step c A a x) \<rparr>"

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
  have "g (mc_step (ask_assign c) A a x) = g x" for A a x
    using ask_assign_step_cases[of c A a x] frame unfolding mcp_frame_def by auto
  then show ?thesis
    using frame unfolding mcp_frame_def by (simp add: ask_assign_def)
qed

theorem ask_assign_sound:
  assumes sound: "mcp_component_sound \<G> gm c"
  shows "mcp_component_sound \<G> gm (ask_assign c)"
proof -
  have base: "edge_collect a' (gm x \<inter> Collect (eval_query.oracle_holds A)) \<subseteq> gm (mc_step c A a' x)"
    for A a' x
    using sound unfolding mcp_component_sound_def by blast
  have step: "edge_collect a (gm x \<inter> Collect (eval_query.oracle_holds A))
                \<subseteq> gm (mc_step (ask_assign c) A a x)" for A a x
  proof (cases "mc_step (ask_assign c) A a x = mc_step c A a x")
    case True
    then show ?thesis using base by simp
  next
    case False
    then obtain y e n where a: "a = EA_Assign y e" and n: "answer_const (A (EvalInt e)) = Some n"
        and eq: "mc_step (ask_assign c) A a x = mc_step c A (EA_Assign y (N n)) x"
      using ask_assign_step_cases by metis
    have val: "\<lbrakk>e\<rbrakk>\<^sub>e s = n" if "eval_query.oracle_holds A s" for s
      by (rule eval_holds_constD[OF eval_query.oracle_holdsD[OF that] n])
    have "edge_collect a (gm x \<inter> Collect (eval_query.oracle_holds A))
            = edge_collect (EA_Assign y (N n)) (gm x \<inter> Collect (eval_query.oracle_holds A))"
      unfolding a using val by auto
    with base[of "EA_Assign y (N n)" x A] show ?thesis unfolding eq by argo
  qed
  have eqs: "mc_en (ask_assign c) = mc_en c" "mc_comb_env (ask_assign c) = mc_comb_env c"
    "mc_comb_assign (ask_assign c) = mc_comb_assign c" "mc_qry (ask_assign c) = mc_qry c"
    by (simp_all add: ask_assign_def)
  show ?thesis
    unfolding mcp_component_sound_def eqs
    using sound[unfolded mcp_component_sound_def] step
    by presburger
qed

end
