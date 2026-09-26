theory Oracle_Wrappers
  imports Oracle_Local_Spec
begin

section \<open>Consulting the oracle at an assignment\<close>

text \<open>
  A component that was written without the oracle can still use it through a
  wrapper around one transfer. At \<open>x = e\<close>, if the oracle fixes the truth of
  \<open>e\<close>, the wrapper assigns the literal instead of evaluating \<open>e\<close> itself. An
  answer fixes only whether \<open>e\<close> is non-zero, so the wrapper applies only to
  expressions whose value is \<open>0\<close> or \<open>1\<close>: comparisons and logical operators.
  For \<open>z = x\<close> with \<open>x = 5\<close>, the answer \<open>{True}\<close> would wrongly give \<open>z = 1\<close>.
\<close>

fun bool_valued :: "exp \<Rightarrow> bool" where
  "bool_valued (Less a b) = True"
| "bool_valued (LessEq a b) = True"
| "bool_valued (Greater a b) = True"
| "bool_valued (GreaterEq a b) = True"
| "bool_valued (exp.Eq a b) = True"
| "bool_valued (NotEq a b) = True"
| "bool_valued (exp.Not b) = True"
| "bool_valued (And a b) = True"
| "bool_valued (Or a b) = True"
| "bool_valued _ = False"

lemma bool_valued_aval:
  "bool_valued e \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s = (if truthy (\<lbrakk>e\<rbrakk>\<^sub>e s) then 1 else 0)"
  by (cases e rule: bool_valued.cases) auto

definition assign_ask ::
  "((query \<Rightarrow> bool set) \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D)
   \<Rightarrow> (query \<Rightarrow> bool set) \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D" where
  "assign_ask asn ask x e d =
     (if bool_valued e \<and> ask (EvalBool e) = {True} then asn ask x (N 1) d
      else if bool_valued e \<and> ask (EvalBool e) = {False} then asn ask x (N 0) d
      else asn ask x e d)"

text \<open>
  The literal the wrapper assigns is the value \<open>e\<close> has at every store the
  oracle holds at, so the component's own assignment of that literal already
  covers the concrete successor.
\<close>

lemma assign_ask_value:
  assumes "truth_query.oracle_holds ask s"
    and "bool_valued e"
    and "ask (EvalBool e) = {b}"
  shows "\<lbrakk>e\<rbrakk>\<^sub>e s = \<lbrakk>N (if b then 1 else 0)\<rbrakk>\<^sub>e s"
  using truth_query.oracle_holdsD[OF assms(1), of "EvalBool e"] assms(3)
    bool_valued_aval[OF assms(2), of s]
  by simp

theorem oracle_component_assign_ask:
  assumes "oracle_component truth_holds sk asn sp br bd rt en ev ce ca gammaD \<G> qry"
  shows "oracle_component truth_holds sk (assign_ask asn) sp br bd rt en ev ce ca gammaD \<G> qry"
proof -
  interpret C: oracle_component truth_holds sk asn sp br bd rt en ev ce ca gammaD \<G> qry
    by (fact assms)
  have assign:
    "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gammaD (assign_ask asn ask x e d)"
    if s: "s \<in> gammaD d" and o: "truth_query.oracle_holds ask s" for s ask x e d
  proof -
    have base: "s(x := \<lbrakk>e'\<rbrakk>\<^sub>e s) \<in> gammaD (asn ask x e' d)" for e'
      using C.step_sound_oracle[of "EA_Assign x e'" d ask] s o by auto
    show ?thesis
    proof (cases "bool_valued e \<and> ask (EvalBool e) = {True}")
      case True
      then show ?thesis
        using base[of "N 1"] assign_ask_value[OF o, of e True] by (simp add: assign_ask_def)
    next
      case nt: False
      show ?thesis
      proof (cases "bool_valued e \<and> ask (EvalBool e) = {False}")
        case True
        then show ?thesis
          using nt base[of "N 0"] assign_ask_value[OF o, of e False]
          by (simp add: assign_ask_def)
      next
        case False
        then show ?thesis using nt base[of e] by (auto simp: assign_ask_def)
      qed
    qed
  qed
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d')
    then show ?case by (rule C.gammaD_mono)
  next
    case (2 a d ask)
    show ?case
    proof (cases a)
      case (EA_Assign x e)
      then show ?thesis using assign by auto
    qed (use C.step_sound_oracle[of a d ask] in simp_all)
  next
    case (3 s d ci)
    then show ?case by (rule C.enter_sound_local)
  next
    case (4 s dc t de ci)
    then show ?case by (rule C.combine_sound_local)
  qed
qed

end
