theory Strategy_Tree_Program
  imports "TD.Basics_side" "HOL-Library.Monad_Syntax" Strategy_Tree_Properties
begin

section \<open>A typed frontend over the homogeneous vendor tree\<close>

text \<open>
  \<open>strategy_tree\<close> fixes query results and terminal answers to the same
  carrier \<open>'d\<close> and therefore does not support a polymorphic bind.
  \<open>strategy_program\<close> supplies a continuation-based typed interface: a
  program may produce any result type \<open>'a\<close> while its generated vendor tree
  continues to use \<open>'d\<close> for solver values and side contributions.
  \<open>sp_compile_with\<close> encodes the final result into \<open>'d\<close> and produces the vendor
  tree consumed by the solver.
\<close>

type_synonym ('x,'g,'d,'a) strategy_program =
  "('a \<Rightarrow> ('x,'g,'d) strategy_tree) \<Rightarrow> ('x,'g,'d) strategy_tree"

definition sp_return :: "'a \<Rightarrow> ('x,'g,'d,'a) strategy_program" where
  "sp_return a k = k a"

definition sp_bind ::
  "('x,'g,'d,'a) strategy_program
   \<Rightarrow> ('a \<Rightarrow> ('x,'g,'d,'b) strategy_program)
   \<Rightarrow> ('x,'g,'d,'b) strategy_program" where
  "sp_bind m f k = m (\<lambda>v. f v k)"

definition sp_read_local :: "'x \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_read_local x k = QueryL x k"

definition sp_read_global :: "'g \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_read_global g k = QueryG g k"

definition sp_publish :: "'g \<Rightarrow> 'd \<Rightarrow> ('x,'g,'d,unit) strategy_program" where
  "sp_publish g d k = Side g d (k ())"

text \<open>
  \<open>sp_read_at\<close> reads an unknown in the solver's combined address space
  \<^typ>\<open>'x + 'g\<close>, dispatching \<^const>\<open>Inl\<close> to \<open>sp_read_local\<close> and \<^const>\<open>Inr\<close> to
  \<open>sp_read_global\<close> instead of fixing the constructor at the call site.
\<close>

fun sp_read_at :: "'x + 'g \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_read_at (Inl x) = sp_read_local x"
| "sp_read_at (Inr g) = sp_read_global g"

adhoc_overloading Monad_Syntax.bind == sp_bind

text \<open>
  \<open>sp_read_local\<close>/\<open>sp_read_global\<close>/\<open>sp_publish\<close> build a program one effect at a time.
  \<open>sp_lift_tree\<close> instead embeds an already-built vendor tree -- the shape a
  backend combinator produces by folding several contribution trees into one
  -- as the program that runs it and continues, by recursing over the tree's
  own constructors directly: an \<open>Answer\<close> becomes a pure result, a
  \<open>QueryL\<close>/\<open>QueryG\<close> becomes a read continuing into the lifted subtree, a
  \<open>Side\<close> becomes a published side contribution continuing into the lifted
  subtree. Defined directly against the constructors, its primitive-recursion
  equations are already the normal form needed by proofs about vendor trees.
\<close>

primrec sp_lift_tree :: "('x,'g,'d) strategy_tree \<Rightarrow> ('x,'g,'d,'d) strategy_program" where
  "sp_lift_tree (Answer d)   k = k d"
| "sp_lift_tree (QueryL x f) k = QueryL x (\<lambda>d. sp_lift_tree (f d) k)"
| "sp_lift_tree (QueryG g f) k = QueryG g (\<lambda>d. sp_lift_tree (f d) k)"
| "sp_lift_tree (Side g d t) k = Side g d (sp_lift_tree t k)"

lemma traverse_rhs_sp_lift_tree [simp]:
  "traverse_rhs (sp_lift_tree t k) \<sigma> = traverse_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"
  by (induction t arbitrary: k) (auto intro: rangeI)

lemma dep_aux_sp_lift_tree [simp]:
  "dep_aux \<sigma> (sp_lift_tree t k) = dep_aux \<sigma> t \<union> dep_aux \<sigma> (k (traverse_rhs t \<sigma>))"
  by (induction t arbitrary: k) (auto intro: rangeI)

lemma sides_of_rhs_sp_lift_tree [simp]:
  fixes t :: "('x, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree"
  shows "sides_of_rhs (sp_lift_tree t k) \<sigma>
         = sides_of_rhs t \<sigma> \<squnion> sides_of_rhs (k (traverse_rhs t \<sigma>)) \<sigma>"
  by (induction t arbitrary: k) (auto simp: Let_def sup_fun_def fun_upd_def ac_simps intro: rangeI)

text \<open>
  \<open>traverse_rhs_sp_lift_tree_mono\<close>: environment-monotonicity of the answer
  \<^const>\<open>sp_lift_tree\<close> produces, not of its dependency set -- if \<open>t\<close> is
  monotone in the environment, every continuation \<open>k v\<close> is monotone in the
  environment, and \<open>k\<close> is monotone in the value it receives, then
  \<open>sp_lift_tree t k\<close> is monotone in the environment.
\<close>

lemma traverse_rhs_sp_lift_tree_mono:
  fixes t :: "('x, 'g, 'd::{order,bot}) strategy_tree"
  assumes t_mono:
    "\<And>\<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> traverse_rhs t \<sigma>1 \<le> traverse_rhs t \<sigma>2"
  assumes k_mono_env:
    "\<And>v \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> traverse_rhs (k v) \<sigma>1 \<le> traverse_rhs (k v) \<sigma>2"
  assumes k_mono_val:
    "\<And>\<sigma> v1 v2. v1 \<le> v2 \<Longrightarrow> traverse_rhs (k v1) \<sigma> \<le> traverse_rhs (k v2) \<sigma>"
  assumes le: "\<sigma>1 \<le> \<sigma>2"
  shows "traverse_rhs (sp_lift_tree t k) \<sigma>1 \<le> traverse_rhs (sp_lift_tree t k) \<sigma>2"
proof -
  have "traverse_rhs (k (traverse_rhs t \<sigma>1)) \<sigma>1
      \<le> traverse_rhs (k (traverse_rhs t \<sigma>1)) \<sigma>2"
    by (rule k_mono_env[OF le])
  also have "\<dots>
      \<le> traverse_rhs (k (traverse_rhs t \<sigma>2)) \<sigma>2"
    by (rule k_mono_val[OF t_mono[OF le]])
  finally show ?thesis
    by simp
qed

text \<open>
  \<^const>\<open>mono_tree_deps\<close> gives the generally applicable composition rule: the
  continuation may query more unknowns as its received value grows.
  \<^const>\<open>env_indep_deps\<close> is also preserved, under the stronger condition that
  the continuation's dependency set is independent of both its argument and
  the environment.
\<close>

text \<open>
  \<open>sp_compile\<close> only accepts a program whose answer is already \<open>'d\<close>.
  \<open>sp_compile_with encode\<close> generalizes that to any \<open>'a\<close>, packing the final
  answer through \<open>encode\<close>; \<open>sp_compile\<close> is its \<open>id\<close> specialization.
\<close>

definition sp_compile_with ::
  "('a \<Rightarrow> 'd) \<Rightarrow> ('x,'g,'d,'a) strategy_program \<Rightarrow> ('x,'g,'d) strategy_tree" where
  "sp_compile_with encode p = p (Answer o encode)"

definition sp_compile :: "('x,'g,'d,'d) strategy_program \<Rightarrow> ('x,'g,'d) strategy_tree" where
  "sp_compile p = sp_compile_with id p"

subsection \<open>Compiling programs to vendor trees\<close>

lemma sp_compile_with_bind_read_local [simp]:
  "sp_compile_with encode ((sp_read_local x) \<bind> f) = QueryL x (\<lambda>d. sp_compile_with encode (f d))"
  by (simp add: sp_compile_with_def sp_bind_def sp_read_local_def)

lemma sp_compile_with_bind_read_global [simp]:
  "sp_compile_with encode ((sp_read_global g) \<bind> f) = QueryG g (\<lambda>d. sp_compile_with encode (f d))"
  by (simp add: sp_compile_with_def sp_bind_def sp_read_global_def)

lemma sp_compile_with_bind_publish [simp]:
  "sp_compile_with encode ((sp_publish g d) \<bind> f) = Side g d (sp_compile_with encode (f ()))"
  by (simp add: sp_compile_with_def sp_bind_def sp_publish_def)

lemma sp_compile_with_return [simp]:
  "sp_compile_with encode (sp_return a) = Answer (encode a)"
  by (simp add: sp_compile_with_def sp_return_def)

lemma sp_compile_with_read_local [simp]:
  "sp_compile_with encode (sp_read_local x) = QueryL x (Answer o encode)"
  by (simp add: sp_compile_with_def sp_read_local_def)

lemma sp_compile_with_read_global [simp]:
  "sp_compile_with encode (sp_read_global g) = QueryG g (Answer o encode)"
  by (simp add: sp_compile_with_def sp_read_global_def)

lemma sp_compile_with_publish [simp]:
  "sp_compile_with encode (sp_publish g d) = Side g d (Answer (encode ()))"
  by (simp add: sp_compile_with_def sp_publish_def)

lemma sp_compile_with_bind_read_at [simp]:
  "sp_compile_with encode ((sp_read_at src) \<bind> f) =
     (case src of Inl x \<Rightarrow> QueryL x (\<lambda>d. sp_compile_with encode (f d))
                | Inr g \<Rightarrow> QueryG g (\<lambda>d. sp_compile_with encode (f d)))"
  by (cases src) simp_all

lemma sp_compile_with_read_at [simp]:
  "sp_compile_with encode (sp_read_at src) =
     (case src of Inl x \<Rightarrow> QueryL x (Answer o encode) | Inr g \<Rightarrow> QueryG g (Answer o encode))"
  by (cases src) simp_all

lemma sp_compile_sp_lift_tree [simp]: "sp_compile (sp_lift_tree t) = t"
  by (induction t) (simp_all add: sp_compile_def sp_compile_with_def)

text \<open>
  The \<open>id\<close>-specialized counterparts of the \<open>sp_compile_with_*\<close> equations above,
  stated directly against \<open>sp_compile\<close> so a proof reasoning about compiled
  programs does not have to unfold \<open>sp_compile_def\<close> at every step.
\<close>

lemma sp_compile_bind_read_local [simp]:
  "sp_compile ((sp_read_local x) \<bind> f) = QueryL x (\<lambda>d. sp_compile (f d))"
  by (simp add: sp_compile_def)

lemma sp_compile_bind_read_global [simp]:
  "sp_compile ((sp_read_global g) \<bind> f) = QueryG g (\<lambda>d. sp_compile (f d))"
  by (simp add: sp_compile_def)

lemma sp_compile_bind_publish [simp]:
  "sp_compile ((sp_publish g d) \<bind> f) = Side g d (sp_compile (f ()))"
  by (simp add: sp_compile_def)

lemma sp_compile_return [simp]: "sp_compile (sp_return a) = Answer a"
  by (simp add: sp_compile_def)

lemma sp_compile_read_local [simp]: "sp_compile (sp_read_local x) = QueryL x Answer"
  by (simp add: sp_compile_def)

lemma sp_compile_read_global [simp]: "sp_compile (sp_read_global g) = QueryG g Answer"
  by (simp add: sp_compile_def)

lemma sp_compile_bind_read_at [simp]:
  "sp_compile ((sp_read_at src) \<bind> f) =
     (case src of Inl x \<Rightarrow> QueryL x (\<lambda>d. sp_compile (f d))
                | Inr g \<Rightarrow> QueryG g (\<lambda>d. sp_compile (f d)))"
  by (cases src) simp_all

lemma sp_compile_read_at [simp]:
  "sp_compile (sp_read_at src) =
     (case src of Inl x \<Rightarrow> QueryL x Answer | Inr g \<Rightarrow> QueryG g Answer)"
  by (cases src) simp_all

text \<open>
  Left bare rather than \<open>[simp]\<close>: using this equation on arbitrary binds
  exposes \<open>m\<close> as a raw CPS function application. The specialized equations
  above preserve the program abstraction and give the simplifier the
  vendor-tree constructors it needs.
\<close>

lemma sp_compile_with_bind: "sp_compile_with encode (m \<bind> f) = m (\<lambda>x. sp_compile_with encode (f x))"
  by (simp add: sp_compile_with_def sp_bind_def)

subsection \<open>Monad laws\<close>

lemma sp_bind_sp_return_left [simp]: "(sp_return a) \<bind> f = f a"
  by (rule ext) (simp add: sp_bind_def sp_return_def)

lemma sp_bind_sp_return_right [simp]: "m \<bind> sp_return = m"
  by (rule ext) (simp add: sp_bind_def sp_return_def)

lemma sp_bind_assoc:
  fixes m :: "('x, 'g, 'd, 'a) strategy_program"
    and f :: "'a \<Rightarrow> ('x, 'g, 'd, 'b) strategy_program"
    and g :: "'b \<Rightarrow> ('x, 'g, 'd, 'c) strategy_program"
  shows "(m \<bind> f) \<bind> g = m \<bind> (\<lambda>x. f x \<bind> g)"
  by (rule ext) (simp add: sp_bind_def)

end
