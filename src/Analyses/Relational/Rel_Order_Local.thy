theory Rel_Order_Local
  imports Rel_Order_Domain "Voblint_Framework.MCP_Spec"
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
  also \<open>x == y\<close> as true and \<open>x != y\<close> as false. A comparison evaluates to \<open>1\<close>
  when true and \<open>0\<close> when false, so the answers are the exact integers \<open>1\<close> and \<open>0\<close>. Every
  other query is answered with \<open>\<top>\<close>, the claim that holds of every store.
\<close>

text \<open>\<open>rel_le d a b\<close> holds when \<open>a\<close> and \<open>b\<close> are variables whose order \<open>d\<close> records.\<close>

fun var_of :: "exp \<Rightarrow> vname option" where
  "var_of (V x) = Some x"
| "var_of _ = None"

definition rel_le :: "relc \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool" where
  "rel_le d a b =
     (case (var_of a, var_of b) of (Some x, Some y) \<Rightarrow> relc_has x y d | _ \<Rightarrow> False)"

definition rel_eval :: "relc \<Rightarrow> exp \<Rightarrow> answer" where
  "rel_eval d e =
     (case e of
        LessEq a b \<Rightarrow> if rel_le d a b then answer_of_int 1 else \<top>
      | GreaterEq a b \<Rightarrow> if rel_le d b a then answer_of_int 1 else \<top>
      | Less a b \<Rightarrow> if rel_le d b a then answer_of_int 0 else \<top>
      | Greater a b \<Rightarrow> if rel_le d a b then answer_of_int 0 else \<top>
      | exp.Eq a b \<Rightarrow> if rel_le d a b \<and> rel_le d b a then answer_of_int 1 else \<top>
      | NotEq a b \<Rightarrow> if rel_le d a b \<and> rel_le d b a then answer_of_int 0 else \<top>
      | _ \<Rightarrow> \<top>)"

fun rel_qry :: "relc \<Rightarrow> answers" where
  "rel_qry d (EvalInt e) = rel_eval d e"

lemma relc_has_sound: "s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> relc_has x y d \<Longrightarrow> s x \<le> s y"
  by (cases d) auto

lemma var_of_SomeD: "var_of a = Some x \<Longrightarrow> a = V x"
  by (cases a) simp_all

lemma rel_le_sound: "s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> rel_le d a b \<Longrightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s \<le> \<lbrakk>b\<rbrakk>\<^sub>e s"
  by (auto simp: rel_le_def split: option.splits dest!: var_of_SomeD
      dest: relc_has_sound)

lemma rel_eval_sound:
  "s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_query_lift gamma_int_dom (rel_eval d e)"
  by (cases e) (auto simp: rel_eval_def
      dest: rel_le_sound intro: order_antisym)

lemma rel_qry_sound: "s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> eval_holds q (rel_qry d q) s"
  by (cases q) (simp add: rel_eval_sound)

subsection \<open>Learning orders from the oracle\<close>

text \<open>
  At \<open>x = e\<close> the question is asked about the state before the assignment, where
  \<open>e\<close> evaluates to the new value of \<open>x\<close> and every other variable keeps its
  value. The exact answer \<open>1\<close> to \<open>e <= y\<close> therefore makes \<open>(x, y)\<close> true
  afterwards, and \<open>y <= e\<close> makes \<open>(y, x)\<close> true. The candidate partners are the
  variables in \<open>ys\<close>, a parameter so that the construction stays executable.
\<close>

definition rel_learn :: "answers \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_learn ask ys x e d =
     (case d of
        RelBot \<Rightarrow> RelBot
      | RelC ps \<Rightarrow> RelC (ps
          \<union> set (map (\<lambda>y. (x, y))
                (filter (\<lambda>y. y \<noteq> x \<and> answer_const (ask (EvalInt (LessEq e (V y)))) = Some 1) ys))
          \<union> set (map (\<lambda>y. (y, x))
                (filter (\<lambda>y. y \<noteq> x \<and> answer_const (ask (EvalInt (LessEq (V y) e))) = Some 1) ys))))"

lemma rel_learn_sound:
  assumes "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> \<lbrakk>d\<rbrakk>"
    and "eval_query.oracle_holds ask s"
  shows "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> \<lbrakk>rel_learn ask ys x e d\<rbrakk>"
proof (cases d)
  case RelBot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  have up: "\<lbrakk>e\<rbrakk>\<^sub>e s \<le> s y" if "answer_const (ask (EvalInt (LessEq e (V y)))) = Some 1" for y
    using eval_holds_constD[OF eval_query.oracle_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  have down: "s y \<le> \<lbrakk>e\<rbrakk>\<^sub>e s" if "answer_const (ask (EvalInt (LessEq (V y) e))) = Some 1" for y
    using eval_holds_constD[OF eval_query.oracle_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  show ?thesis
    using assms(1) RelC up down by (auto simp: rel_learn_def)
qed

subsection \<open>The component\<close>

text \<open>
  The order analysis as a component of the combined state, over the variables
  \<open>ys\<close> it relates. It asks at assignments and answers comparisons. Its entry
  answers one alternative: the callee starts from the empty relation, and the
  return keeps nothing, which is sound and imprecise by design.
\<close>

definition rel_ret :: "exp option \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_ret eo d = (case eo of None \<Rightarrow> d | Some a \<Rightarrow> forget_relc ret_var d)"

definition order_component :: "vname list \<Rightarrow> relc mcp_component" where
  "order_component ys = \<lparr>
     mc_query = (\<lambda>A. rel_qry),
     mc_skip = (\<lambda>A d. d),
     mc_assign = (\<lambda>A x e d. rel_learn A ys x e (forget_relc x d)),
     mc_special = (\<lambda>A sc x d. forget_relc x d),
     mc_branch = (\<lambda>A b pol d. branch_step_rel b pol d),
     mc_body = (\<lambda>A p d. d),
     mc_return = (\<lambda>A eo p d. rel_ret eo d),
     mc_event = (\<lambda>A ev d. d),
     mc_enter = (\<lambda>A ci p. [(fst p, top_relc)]),
     mc_combine_env = (\<lambda>A B ci dc de. dc),
     mc_combine_assign = (\<lambda>B ci d de. top_relc) \<rparr>"

theorem order_component_sound: "mcp_component_sound \<G> gamma_rel (order_component ys)"
proof -
  have step: "edge_collect a (gamma_rel d \<inter> Collect (eval_query.oracle_holds ask))
                \<subseteq> gamma_rel (mc_step (order_component ys) ask a d)" for a d ask
  proof (cases a)
    case (EA_Assign x e)
    then show ?thesis by (auto simp: order_component_def intro!: rel_learn_sound)
  next
    case (EA_Special sc x)
    then show ?thesis by (cases sc) (auto simp: order_component_def)
  next
    case (EA_Ret eo p)
    then show ?thesis by (cases eo) (auto simp: order_component_def rel_ret_def)
  qed (auto simp: order_component_def branch_step_rel_def)
  show ?thesis
    unfolding mcp_component_sound_def
    using gamma_rel_mono step rel_qry_sound by (auto simp: order_component_def)
qed

lemma single_entry_order_component: "single_entry (order_component ys)"
  by (simp add: single_entry_def order_component_def)

end
