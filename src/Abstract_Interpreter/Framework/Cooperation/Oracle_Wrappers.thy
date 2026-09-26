theory Oracle_Wrappers
  imports "Voblint_Framework.DG_Spec_Sound"
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
     (case ivl_const (A (EvalInt e)) of
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
    proof (cases "ivl_const (A (EvalInt e))")
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

end
