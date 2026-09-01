theory Strategy_Tree_Program
  imports Strategy_Tree_Combinators
begin

section \<open>A typed frontend over the homogeneous vendor tree\<close>

text \<open>
  \<open>strategy_tree\<close> forces every query and the final answer to share one
  carrier \<open>'d\<close>, so a sequence of reads and writes threading an unrelated
  intermediate value has no natural encoding as a vendor tree directly.
  \<open>strategy_program\<close> is a continuation-passing frontend that fixes this:
  a program producing \<open>'a\<close>, given what to do with that \<open>'a\<close>, produces a
  vendor tree -- so \<open>'a\<close> can be anything (a record, a boolean, a manager's
  own local/global values) while only the very last step has to reach \<open>'d\<close>.
  \<open>sp_run_with\<close> is that last step; the vendor tree it produces is exactly
  what today's generators already build, unfolded one query/side at a time.
\<close>

type_synonym ('x,'g,'d,'a) strategy_program =
  "('a \<Rightarrow> ('x,'g,'d) strategy_tree) \<Rightarrow> ('x,'g,'d) strategy_tree"

definition sp_return :: "'a \<Rightarrow> ('x,'g,'d,'a) strategy_program" where
  "sp_return a = (\<lambda>k. k a)"

definition sp_bind ::
  "('x,'g,'d,'a) strategy_program \<Rightarrow> ('a \<Rightarrow> ('x,'g,'d,'b) strategy_program)
   \<Rightarrow> ('x,'g,'d,'b) strategy_program" where
  "sp_bind m f = (\<lambda>k. m (\<lambda>x. f x k))"

definition sp_local :: "'x \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_local x = (\<lambda>k. QueryL x k)"

definition sp_global :: "'g \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_global g = (\<lambda>k. QueryG g k)"

definition sp_sideg :: "'g \<Rightarrow> 'd \<Rightarrow> ('x,'g,'d,unit) strategy_program" where
  "sp_sideg g d = (\<lambda>k. Side g d (k ()))"

text \<open>
  \<open>sp_local\<close>/\<open>sp_global\<close>/\<open>sp_sideg\<close> build a program one effect at a time.
  \<open>sp_lift_tree\<close> instead embeds an already-built vendor tree -- the shape
  \<open>Strategy_Tree_Fold\<close>'s \<open>fold_rhs_trees\<close> and similar backend combinators
  hand back -- as the program that runs it and continues. \<open>seqcomp_tree\<close>
  (\<^theory>\<open>Voblint_Solver.Strategy_Tree_Sequencing\<close>) is exactly the right tool
  for this, since a vendor tree's own answer and query carrier already agree
  on \<open>'d\<close>: no new recursion over \<open>strategy_tree\<close>'s constructors is needed
  here, only the existing one.
\<close>

definition sp_lift_tree :: "('x,'g,'d) strategy_tree \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_lift_tree t = (\<lambda>k. seqcomp_tree t k)"

adhoc_overloading Monad_Syntax.bind == sp_bind

text \<open>
  \<open>sp_run\<close> only accepts a program whose answer is already \<open>'d\<close>.
  \<open>sp_run_with encode\<close> generalizes that to any \<open>'a\<close>, packing the final
  answer through \<open>encode\<close>; \<open>sp_run\<close> is its \<open>id\<close> specialization.
\<close>

definition sp_run_with ::
  "('a \<Rightarrow> 'd) \<Rightarrow> ('x,'g,'d,'a) strategy_program \<Rightarrow> ('x,'g,'d) strategy_tree" where
  "sp_run_with encode p = p (Answer o encode)"

definition sp_run :: "('x,'g,'d,'d) strategy_program \<Rightarrow> ('x,'g,'d) strategy_tree" where
  [simp]: "sp_run p = sp_run_with id p"

subsection \<open>Compile-down: a program reduces to exactly the vendor tree it stands for\<close>

lemma sp_run_with_bind_local [simp]:
  "sp_run_with encode ((sp_local x) \<bind> f) = QueryL x (\<lambda>d. sp_run_with encode (f d))"
  by (simp add: sp_run_with_def sp_bind_def sp_local_def)

lemma sp_run_with_bind_global [simp]:
  "sp_run_with encode ((sp_global g) \<bind> f) = QueryG g (\<lambda>d. sp_run_with encode (f d))"
  by (simp add: sp_run_with_def sp_bind_def sp_global_def)

lemma sp_run_with_bind_sideg [simp]:
  "sp_run_with encode ((sp_sideg g d) \<bind> f) = Side g d (sp_run_with encode (f ()))"
  by (simp add: sp_run_with_def sp_bind_def sp_sideg_def)

lemma sp_run_with_return [simp]:
  "sp_run_with encode (sp_return a) = Answer (encode a)"
  by (simp add: sp_run_with_def sp_return_def)

lemma sp_run_with_local [simp]:
  "sp_run_with encode (sp_local x) = QueryL x (Answer o encode)"
  by (simp add: sp_run_with_def sp_local_def)

lemma sp_run_with_global [simp]:
  "sp_run_with encode (sp_global g) = QueryG g (Answer o encode)"
  by (simp add: sp_run_with_def sp_global_def)

lemma sp_run_sp_lift_tree [simp]: "sp_run (sp_lift_tree t) = t"
  by (simp add: sp_run_with_def sp_lift_tree_def)

lemma sp_run_with_bind_lift_tree [simp]:
  "sp_run_with encode ((sp_lift_tree t) \<bind> f) = seqcomp_tree t (\<lambda>d. sp_run_with encode (f d))"
  by (simp add: sp_run_with_def sp_bind_def sp_lift_tree_def)

subsection \<open>Monad laws\<close>

lemma sp_bind_sp_return_left [simp]: "(sp_return a) \<bind> f = f a"
  by (simp add: sp_bind_def sp_return_def)

lemma sp_bind_sp_return_right [simp]: "m \<bind> sp_return = m"
  by (simp add: sp_bind_def sp_return_def)

lemma sp_bind_assoc:
  fixes m :: "('x, 'g, 'd, 'a) strategy_program"
    and f :: "'a \<Rightarrow> ('x, 'g, 'd, 'b) strategy_program"
    and g :: "'b \<Rightarrow> ('x, 'g, 'd, 'c) strategy_program"
  shows "(m \<bind> f) \<bind> g = m \<bind> (\<lambda>x. f x \<bind> g)"
  by (simp add: sp_bind_def)

end
