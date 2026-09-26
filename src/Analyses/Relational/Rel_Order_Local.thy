theory Rel_Order_Local
  imports Rel_Order_Domain "Voblint_Framework.Oracle_Local_Spec"
begin

section \<open>The order carrier as a component that asks\<close>

text \<open>
  \<^const>\<open>rel_order_spec\<close> reads and publishes the global channel, so it is not a
  local specification and cannot join a product of cooperating analyses. This
  theory gives the same carrier a local-only form. Intraprocedurally it is the
  order analysis of \<^theory>\<open>Voblint_Analysis_Relational.Rel_Order_Domain\<close>, with
  one addition: after an assignment it asks the oracle how the assigned value
  compares with the other variables, and records every order the answer fixes.
  At calls it is deliberately coarse, entering and returning with no facts, so
  that the component studies cooperation and not relational call boundaries.
\<close>

subsection \<open>Answering queries from the order\<close>

text \<open>
  A pair \<open>(x, y)\<close> means \<open>s x \<le> s y\<close>. It therefore decides \<open>x <= y\<close> and
  \<open>y >= x\<close> as true, \<open>y < x\<close> and \<open>x > y\<close> as false, and with the reverse pair
  also \<open>x == y\<close> as true and \<open>x != y\<close> as false. Every other query is answered
  with \<open>UNIV\<close>, the claim that holds of every store.
\<close>

fun rel_qry :: "relc \<Rightarrow> query \<Rightarrow> bool set" where
  "rel_qry d (EvalBool e) =
     (case e of
        LessEq (V x) (V y) \<Rightarrow> if relc_has x y d then {True} else UNIV
      | GreaterEq (V y) (V x) \<Rightarrow> if relc_has x y d then {True} else UNIV
      | Less (V y) (V x) \<Rightarrow> if relc_has x y d then {False} else UNIV
      | Greater (V x) (V y) \<Rightarrow> if relc_has x y d then {False} else UNIV
      | Eq (V x) (V y) \<Rightarrow>
          if relc_has x y d \<and> relc_has y x d then {True} else UNIV
      | NotEq (V x) (V y) \<Rightarrow>
          if relc_has x y d \<and> relc_has y x d then {False} else UNIV
      | _ \<Rightarrow> UNIV)"

lemma relc_has_sound: "s \<in> gamma_rel d \<Longrightarrow> relc_has x y d \<Longrightarrow> s x \<le> s y"
  by (cases d) auto

lemma rel_qry_sound: "s \<in> gamma_rel d \<Longrightarrow> truth_holds q (rel_qry d q) s"
  by (cases q; rename_tac e; case_tac e; simp split: exp.splits)
     (auto dest: relc_has_sound intro: order_antisym)

subsection \<open>Learning orders from the oracle\<close>

text \<open>
  At \<open>x = e\<close> the question is asked about the state before the assignment, where
  \<open>e\<close> evaluates to the new value of \<open>x\<close> and every other variable keeps its
  value. An answer \<open>{True}\<close> to \<open>e <= y\<close> therefore makes \<open>(x, y)\<close> true
  afterwards, and \<open>y <= e\<close> makes \<open>(y, x)\<close> true. The candidate partners are the
  variables in \<open>ys\<close>, a parameter so that the construction stays executable.
\<close>

definition rel_learn ::
  "(query \<Rightarrow> bool set) \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_learn ask ys x e d =
     (case d of
        Bot \<Rightarrow> Bot
      | RelC ps \<Rightarrow> RelC (ps
          \<union> set (map (\<lambda>y. (x, y))
                (filter (\<lambda>y. y \<noteq> x \<and> ask (EvalBool (LessEq e (V y))) = {True}) ys))
          \<union> set (map (\<lambda>y. (y, x))
                (filter (\<lambda>y. y \<noteq> x \<and> ask (EvalBool (LessEq (V y) e)) = {True}) ys))))"

lemma rel_learn_sound:
  assumes "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gamma_rel d"
    and "truth_query.oracle_holds ask s"
  shows "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gamma_rel (rel_learn ask ys x e d)"
proof (cases d)
  case Bot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  have up: "\<lbrakk>e\<rbrakk>\<^sub>e s \<le> s y" if "ask (EvalBool (LessEq e (V y))) = {True}" for y
    using truth_query.oracle_holdsD[OF assms(2), of "EvalBool (LessEq e (V y))"] that
    by (simp split: if_splits)
  have down: "s y \<le> \<lbrakk>e\<rbrakk>\<^sub>e s" if "ask (EvalBool (LessEq (V y) e)) = {True}" for y
    using truth_query.oracle_holdsD[OF assms(2), of "EvalBool (LessEq (V y) e)"] that
    by (simp split: if_splits)
  show ?thesis
    using assms(1) RelC up down by (auto simp: rel_learn_def)
qed

subsection \<open>The component\<close>

definition rel_ret :: "exp option \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_ret eo d = (case eo of None \<Rightarrow> d | Some a \<Rightarrow> forget_relc ret_var d)"

theorem rel_local_component:
  "oracle_component truth_holds
     (\<lambda>ask d. d)
     (\<lambda>ask x e d. rel_learn ask ys x e (forget_relc x d))
     (\<lambda>ask sc x d. forget_relc x d)
     (\<lambda>ask b pol d. branch_step_rel b pol d)
     (\<lambda>ask p d. d)
     (\<lambda>ask eo p d. rel_ret eo d)
     (\<lambda>ci d. [(d, top_relc)])
     (\<lambda>ask ev d. d)
     (\<lambda>ci dc de. dc)
     (\<lambda>ci d de. top_relc)
     gamma_rel \<G> rel_qry"
proof (unfold_locales, goal_cases)
  case (1 d d')
  then show ?case by (rule gamma_rel_mono)
next
  case (2 a d ask)
  show ?case
  proof (cases a)
    case (EA_Assign x e)
    then show ?thesis
      by (auto intro!: rel_learn_sound)
  next
    case (EA_Special sc x)
    then show ?thesis by (cases sc) auto
  next
    case (EA_Ret eo p)
    then show ?thesis by (cases eo) (auto simp: rel_ret_def)
  qed (auto simp: branch_step_rel_def)
next
  case (3 s d ci)
  then show ?case by (auto simp: entry_pairs_cover_def)
next
  case (4 s dc t de ci)
  then show ?case by simp
next
  case (5 s d q)
  then show ?case by (rule rel_qry_sound)
qed

end
