theory Rel_Order_Local
  imports Rel_Order_Domain "Voblint_Framework.MCP_Spec"
begin

section \<open>The order carrier as a component that asks\<close>

text \<open>
  \<^const>\<open>rel_order_spec\<close> reads and publishes the global channel, so it is not a
  local specification and cannot join the combination of cooperating analyses. This
  theory gives the same carrier a local-only form. Intraprocedurally it is the
  order analysis of \<^theory>\<open>Voblint_Analysis_Relational.Rel_Order_Domain\<close>, with
  one addition: after an assignment it asks the query channel how the assigned value
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

text \<open>
  \<open>relc_le d a b\<close> holds when \<open>a\<close> and \<open>b\<close> are variables whose order \<open>d\<close> records,
  or the same variable. The reflexive case lets a copy \<open>x = y\<close> learn both orders
  between \<open>x\<close> and \<open>y\<close> from the channel's own answer to \<open>y <= y\<close>.
\<close>

fun var_of :: "exp \<Rightarrow> vname option" where
  "var_of (V x) = Some x"
| "var_of _ = None"

definition relc_le :: "relc \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool" where
  "relc_le d a b =
     (case (var_of a, var_of b) of (Some x, Some y) \<Rightarrow> x = y \<or> relc_has x y d | _ \<Rightarrow> False)"

definition relc_eval :: "relc \<Rightarrow> exp \<Rightarrow> answer" where
  "relc_eval d e =
     (case e of
        LessEq a b \<Rightarrow> if relc_le d a b then answer_of_int 1 else \<top>
      | GreaterEq a b \<Rightarrow> if relc_le d b a then answer_of_int 1 else \<top>
      | Less a b \<Rightarrow> if relc_le d b a then answer_of_int 0 else \<top>
      | Greater a b \<Rightarrow> if relc_le d a b then answer_of_int 0 else \<top>
      | exp.Eq a b \<Rightarrow> if relc_le d a b \<and> relc_le d b a then answer_of_int 1 else \<top>
      | NotEq a b \<Rightarrow> if relc_le d a b \<and> relc_le d b a then answer_of_int 0 else \<top>
      | _ \<Rightarrow> \<top>)"

fun relc_qry :: "relc \<Rightarrow> channel" where
  "relc_qry d (EvalInt e) = relc_eval d e"

lemma relc_has_sound: "s \<in> \<gamma> d \<Longrightarrow> relc_has x y d \<Longrightarrow> s x \<le> s y"
  by (cases d) auto

lemma var_of_SomeD: "var_of a = Some x \<Longrightarrow> a = V x"
  by (cases a) simp_all

lemma relc_le_sound: "s \<in> \<gamma> d \<Longrightarrow> relc_le d a b \<Longrightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s \<le> \<lbrakk>b\<rbrakk>\<^sub>e s"
  by (auto simp: relc_le_def split: option.splits dest!: var_of_SomeD
      dest: relc_has_sound)

lemma relc_eval_sound:
  "s \<in> \<gamma> d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_answer (relc_eval d e)"
  by (cases e) (auto simp: relc_eval_def
      dest: relc_le_sound intro: order_antisym)

lemma relc_qry_sound: "s \<in> \<gamma> d \<Longrightarrow> eval_holds q (relc_qry d q) s"
  by (cases q) (simp add: relc_eval_sound)

subsection \<open>Learning orders from the query channel\<close>

text \<open>
  At \<open>x = e\<close> the question is asked about the state before the assignment, where
  \<open>e\<close> evaluates to the new value of \<open>x\<close> and every other variable keeps its
  value. The exact answer \<open>1\<close> to \<open>e <= y\<close> therefore makes \<open>(x, y)\<close> true
  afterwards, and \<open>y <= e\<close> makes \<open>(y, x)\<close> true. The candidate partners are the
  variables in \<open>ys\<close>, a parameter so that the construction stays executable.
\<close>

definition relc_learn :: "channel \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc" where
  "relc_learn ch ys x e d =
     (case d of
        RelBot \<Rightarrow> RelBot
      | RelC ps \<Rightarrow> RelC (ps
          \<union> set (map (\<lambda>y. (x, y))
                (filter (\<lambda>y. y \<noteq> x \<and> answer_const (ch (EvalInt (LessEq e (V y)))) = Some 1) ys))
          \<union> set (map (\<lambda>y. (y, x))
                (filter (\<lambda>y. y \<noteq> x \<and> answer_const (ch (EvalInt (LessEq (V y) e))) = Some 1) ys))))"

lemma relc_learn_sound:
  assumes "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> \<gamma> d"
    and "eval_query.channel_holds ch s"
  shows "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> \<gamma> (relc_learn ch ys x e d)"
proof (cases d)
  case RelBot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  have up: "\<lbrakk>e\<rbrakk>\<^sub>e s \<le> s y" if "answer_const (ch (EvalInt (LessEq e (V y)))) = Some 1" for y
    using eval_holds_constD[OF eval_query.channel_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  have down: "s y \<le> \<lbrakk>e\<rbrakk>\<^sub>e s" if "answer_const (ch (EvalInt (LessEq (V y) e))) = Some 1" for y
    using eval_holds_constD[OF eval_query.channel_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  show ?thesis
    using assms(1) RelC up down by (auto simp: relc_learn_def)
qed

subsection \<open>The component\<close>

text \<open>
  The order analysis as a component of the combined state, over the variables
  \<open>ys\<close> it relates. It starts from the conservative local specification: skip,
  body and events keep the relation, and the first return stage keeps the
  caller's. It supplies the operations without a default -- assignments ask and
  learn, the callee starts from the empty relation, and the return keeps
  nothing, which is sound and imprecise by design -- and overrides the handler
  and the branch, where it decides more than the default.
\<close>

definition relc_ret :: "exp option \<Rightarrow> relc \<Rightarrow> relc" where
  "relc_ret eo d = (case eo of None \<Rightarrow> d | Some a \<Rightarrow> forget_relc ret_var d)"

definition order_spec :: "vname list \<Rightarrow> relc local_spec" where
  "order_spec ys = (conservative_local_spec
       (\<lambda>ch x e d. relc_learn ch ys x e (forget_relc x d))
       (\<lambda>ch sc x d. forget_relc x d)
       (\<lambda>ch eo p d. relc_ret eo d)
       (\<lambda>ch ci p. [(fst p, \<top>)])
       (\<lambda>ch' ci d de. \<top>))
     \<lparr>ls_query := (\<lambda>ch. relc_qry), ls_branch := (\<lambda>ch b pol d. relc_branch_step b pol d)\<rparr>"

theorem order_spec_sound: "sound_local_spec \<G> gamma_relc (order_spec ys)"
proof -
  have special: "sound_special gamma_relc (\<lambda>ch sc x d. forget_relc x d)"
    unfolding sound_special_def
  proof (intro allI impI)
    fix ch d s sc x t
    assume "s \<in> \<gamma> (d :: relc)" "t \<in> special_step sc x s"
    then show "t \<in> \<gamma> (forget_relc x d)" by (cases sc) auto
  qed
  have base: "sound_local_spec \<G> gamma_relc (conservative_local_spec
       (\<lambda>ch x e d. relc_learn ch ys x e (forget_relc x d)) (\<lambda>ch sc x d. forget_relc x d)
       (\<lambda>ch eo p d. relc_ret eo d) (\<lambda>ch ci p. [(fst p, \<top>)]) (\<lambda>ch' ci d de. \<top>))"
    by (rule sound_conservative_local_spec[OF gamma_relc_mono _ special])
       (auto simp: sound_assign_def sound_return_def sound_enter_def relc_ret_def
          sound_combine_env_identity split: option.splits intro!: relc_learn_sound)
  show ?thesis
    unfolding order_spec_def
    by (intro sound_local_spec_update_branch[OF sound_local_spec_update_query[OF base]])
       (auto simp: sound_query_def sound_branch_def relc_branch_step_def relc_qry_sound)
qed

lemma single_entry_order_spec: "single_entry (order_spec ys)"
  by (simp add: single_entry_def order_spec_def conservative_local_spec_def)

end
