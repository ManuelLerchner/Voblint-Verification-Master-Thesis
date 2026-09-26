theory Rel_Order_Local
  imports Rel_Order_Domain
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
  when true and \<open>0\<close> when false, so the answers are \<open>[1,1]\<close> and \<open>[0,0]\<close>. Every
  other query is answered with \<open>\<top>\<close>, the claim that holds of every store.
\<close>

text \<open>\<open>rel_le d a b\<close> holds when \<open>a\<close> and \<open>b\<close> are variables whose order \<open>d\<close> records.\<close>

fun var_of :: "exp \<Rightarrow> vname option" where
  "var_of (V x) = Some x"
| "var_of _ = None"

definition rel_le :: "relc \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> bool" where
  "rel_le d a b =
     (case (var_of a, var_of b) of (Some x, Some y) \<Rightarrow> relc_has x y d | _ \<Rightarrow> False)"

definition rel_eval :: "relc \<Rightarrow> exp \<Rightarrow> ivl" where
  "rel_eval d e =
     (case e of
        LessEq a b \<Rightarrow> if rel_le d a b then ivl_of_int 1 else \<top>
      | GreaterEq a b \<Rightarrow> if rel_le d b a then ivl_of_int 1 else \<top>
      | Less a b \<Rightarrow> if rel_le d b a then ivl_of_int 0 else \<top>
      | Greater a b \<Rightarrow> if rel_le d a b then ivl_of_int 0 else \<top>
      | exp.Eq a b \<Rightarrow> if rel_le d a b \<and> rel_le d b a then ivl_of_int 1 else \<top>
      | NotEq a b \<Rightarrow> if rel_le d a b \<and> rel_le d b a then ivl_of_int 0 else \<top>
      | _ \<Rightarrow> \<top>)"

fun rel_qry :: "relc \<Rightarrow> answers" where
  "rel_qry d (EvalInt e) = rel_eval d e"

lemma relc_has_sound: "s \<in> gamma_rel d \<Longrightarrow> relc_has x y d \<Longrightarrow> s x \<le> s y"
  by (cases d) auto

lemma var_of_SomeD: "var_of a = Some x \<Longrightarrow> a = V x"
  by (cases a) simp_all

lemma rel_le_sound: "s \<in> gamma_rel d \<Longrightarrow> rel_le d a b \<Longrightarrow> \<lbrakk>a\<rbrakk>\<^sub>e s \<le> \<lbrakk>b\<rbrakk>\<^sub>e s"
  by (auto simp: rel_le_def split: option.splits dest!: var_of_SomeD
      dest: relc_has_sound)

lemma rel_eval_sound: "s \<in> gamma_rel d \<Longrightarrow> \<lbrakk>e\<rbrakk>\<^sub>e s \<in> gamma_ivl (rel_eval d e)"
  by (cases e) (auto simp: rel_eval_def top_ivl_def gamma_ivl_top
      dest: rel_le_sound intro: order_antisym)

lemma rel_qry_sound: "s \<in> gamma_rel d \<Longrightarrow> eval_holds q (rel_qry d q) s"
  by (cases q) (simp add: rel_eval_sound)

subsection \<open>Learning orders from the oracle\<close>

text \<open>
  At \<open>x = e\<close> the question is asked about the state before the assignment, where
  \<open>e\<close> evaluates to the new value of \<open>x\<close> and every other variable keeps its
  value. An answer \<open>[1,1]\<close> to \<open>e <= y\<close> therefore makes \<open>(x, y)\<close> true
  afterwards, and \<open>y <= e\<close> makes \<open>(y, x)\<close> true. The candidate partners are the
  variables in \<open>ys\<close>, a parameter so that the construction stays executable.
\<close>

definition rel_learn :: "answers \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> exp \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_learn ask ys x e d =
     (case d of
        Bot \<Rightarrow> Bot
      | RelC ps \<Rightarrow> RelC (ps
          \<union> set (map (\<lambda>y. (x, y))
                (filter (\<lambda>y. y \<noteq> x \<and> ivl_const (ask (EvalInt (LessEq e (V y)))) = Some 1) ys))
          \<union> set (map (\<lambda>y. (y, x))
                (filter (\<lambda>y. y \<noteq> x \<and> ivl_const (ask (EvalInt (LessEq (V y) e))) = Some 1) ys))))"

text \<open>The questions \<open>rel_learn\<close> consults at \<open>x = e\<close>, and nothing elsewhere.\<close>

definition rel_qs :: "vname list \<Rightarrow> edge_action \<Rightarrow> relc \<Rightarrow> query list" where
  "rel_qs ys a d =
     (case a of
        EA_Assign x e \<Rightarrow>
          concat (map (\<lambda>y. if y = x then []
                           else [EvalInt (LessEq e (V y)), EvalInt (LessEq (V y) e)]) ys)
      | _ \<Rightarrow> [])"

lemma rel_learn_sound:
  assumes "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gamma_rel d"
    and "eval_query.oracle_holds ask s"
  shows "s(x := \<lbrakk>e\<rbrakk>\<^sub>e s) \<in> gamma_rel (rel_learn ask ys x e d)"
proof (cases d)
  case Bot
  with assms(1) show ?thesis by simp
next
  case (RelC ps)
  have up: "\<lbrakk>e\<rbrakk>\<^sub>e s \<le> s y" if "ivl_const (ask (EvalInt (LessEq e (V y)))) = Some 1" for y
    using eval_holds_constD[OF eval_query.oracle_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  have down: "s y \<le> \<lbrakk>e\<rbrakk>\<^sub>e s" if "ivl_const (ask (EvalInt (LessEq (V y) e))) = Some 1" for y
    using eval_holds_constD[OF eval_query.oracle_holdsD[OF assms(2)] that]
    by (simp split: if_splits)
  show ?thesis
    using assms(1) RelC up down by (auto simp: rel_learn_def)
qed

subsection \<open>The component\<close>

definition rel_ret :: "exp option \<Rightarrow> relc \<Rightarrow> relc" where
  "rel_ret eo d = (case eo of None \<Rightarrow> d | Some a \<Rightarrow> forget_relc ret_var d)"

theorem rel_local_component:
  "sound_local_dg_spec rel_qry
     (\<lambda>A d. d)
     (\<lambda>A x e d. rel_learn A ys x e (forget_relc x d))
     (\<lambda>A sc x d. forget_relc x d)
     (\<lambda>A b pol d. branch_step_rel b pol d)
     (\<lambda>A p d. d)
     (\<lambda>A eo p d. rel_ret eo d)
     (\<lambda>ci d. [(d, top_relc)])
     (\<lambda>A ev d. d)
     (\<lambda>ci dc de. dc)
     (\<lambda>ci d de. top_relc)
     gamma_rel \<G>"
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
