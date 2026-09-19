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

text \<open>One rewrite per program constructor, each \<open>simp\<close>, so compiling a concrete program is
  normalization rather than proof: the simplifier builds the tree from the program's own
  syntax, and a transfer written against the program layer never has to name a tree
  constructor.\<close>
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

subsection \<open>Programs that run their continuation once\<close>

text \<open>
  A \<^typ>\<open>('x,'g,'d,'a) strategy_program\<close> is any function from a continuation to a
  tree, so nothing stops one from ignoring its continuation, or from using it
  twice. Such a program has no semantics the tree vocabulary can describe: what
  it publishes and what it reads would depend on the continuation it is handed.

  \<open>sp_wf p\<close> names the programs that do not do this. It says \<open>p\<close> commutes with
  grafting: continuing into \<open>k\<close> and then grafting \<open>h\<close> onto every leaf of the
  result is the same as continuing into \<open>k\<close> already grafted. A program that
  dropped its continuation would lose \<open>h\<close> on the left and keep it on the
  right; one that used it twice would duplicate the grafting. Everything the
  generator builds runs its continuation once, and this is the condition under
  which asking a program what it publishes is a well-posed question at all.

  Stating it this way rather than as \<open>p = sp_lift_tree (sp_compile p)\<close> is what
  lets it apply to a transfer, whose answer type is the analysis' own \<open>'dl\<close>
  rather than the solver's \<open>'d\<close>: there is no tree whose leaves carry a \<open>'dl\<close>,
  so a transfer has no compilation to be recoverable from, but it commutes with
  grafting all the same. For a program that does answer \<open>'d\<close> the two agree, which
  is \<open>sp_wfD\<close>.
\<close>

lemma sp_lift_tree_sp_lift_tree:
  "sp_lift_tree (sp_lift_tree t g) k = sp_lift_tree t (\<lambda>v. sp_lift_tree (g v) k)"
  by (induction t) simp_all

definition sp_wf :: "('x,'g,'d,'a) strategy_program \<Rightarrow> bool" where
  "sp_wf p \<longleftrightarrow> (\<forall>k h. p (\<lambda>v. sp_lift_tree (k v) h) = sp_lift_tree (p k) h)"

lemma sp_wfI:
  "(\<And>k h. p (\<lambda>v. sp_lift_tree (k v) h) = sp_lift_tree (p k) h) \<Longrightarrow> sp_wf p"
  by (simp add: sp_wf_def)

lemma sp_wf_graft:
  "sp_wf p \<Longrightarrow> p (\<lambda>v. sp_lift_tree (k v) h) = sp_lift_tree (p k) h"
  by (simp add: sp_wf_def)

text \<open>
  The homogeneous reading: a program answering the solver's own value type is
  recoverable from the tree it compiles to. This is the form every consumer
  below uses, and \<open>sp_compile\<close> only accepts such a program in the first place.
\<close>

lemma sp_wfD:
  assumes "sp_wf p"
  shows "p k = sp_lift_tree (sp_compile p) k"
  using sp_wf_graft[OF assms, where k = Answer and h = k]
  by (simp add: sp_compile_def sp_compile_with_def)

text \<open>Closure under the constructors a generator actually builds with, so a
  well-formedness side condition discharges by \<open>simp\<close> at the use site instead
  of being threaded through as a hypothesis.\<close>

lemma sp_wf_lift_tree [intro, simp]: "sp_wf (sp_lift_tree t)"
  by (simp add: sp_wf_def sp_lift_tree_sp_lift_tree)

lemma sp_wf_return [intro, simp]: "sp_wf (sp_return a)"
  by (simp add: sp_wf_def sp_return_def)

lemma sp_wf_read_local [intro, simp]: "sp_wf (sp_read_local x)"
  by (simp add: sp_wf_def sp_read_local_def)

lemma sp_wf_read_global [intro, simp]: "sp_wf (sp_read_global g)"
  by (simp add: sp_wf_def sp_read_global_def)

lemma sp_wf_publish [intro, simp]: "sp_wf (sp_publish g d)"
  by (simp add: sp_wf_def sp_publish_def)

lemma sp_wf_read_at [intro, simp]: "sp_wf (sp_read_at src)"
  by (cases src) simp_all

lemma sp_wf_bind [intro]:
  assumes "sp_wf p" and "\<And>v. sp_wf (f v)"
  shows "sp_wf (p \<bind> f)"
proof (rule sp_wfI)
  fix k h
  have "(p \<bind> f) (\<lambda>v. sp_lift_tree (k v) h) = p (\<lambda>v. sp_lift_tree (f v k) h)"
    by (simp add: sp_bind_def sp_wf_graft[OF assms(2)])
  also have "\<dots> = sp_lift_tree (p (\<lambda>v. f v k)) h"
    by (rule sp_wf_graft[OF assms(1)])
  finally show "(p \<bind> f) (\<lambda>v. sp_lift_tree (k v) h) = sp_lift_tree ((p \<bind> f) k) h"
    by (simp add: sp_bind_def)
qed

text \<open>
  Post-composing a program's answer with an encoding, so a transfer answering
  \<open>'dl\<close> becomes a contribution answering the packed \<open>('dl,'dg) dg_state\<close> the
  generator folds. It is \<^const>\<open>sp_compile_with\<close>'s program-level counterpart:
  compiling it is compiling through the same encoding.
\<close>

definition sp_map ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('x,'g,'d,'a) strategy_program \<Rightarrow> ('x,'g,'d,'b) strategy_program"
where
  "sp_map e p = (\<lambda>k. p (\<lambda>v. k (e v)))"

lemma sp_map_apply [simp]: "sp_map e p k = p (\<lambda>v. k (e v))"
  by (simp add: sp_map_def)

lemma sp_compile_with_sp_map [simp]:
  "sp_compile_with e' (sp_map e p) = sp_compile_with (e' \<circ> e) p"
  by (simp add: sp_map_def sp_compile_with_def comp_def)

lemma sp_compile_sp_map [simp]: "sp_compile (sp_map e p) = sp_compile_with e p"
  by (simp add: sp_compile_def sp_compile_with_def comp_def)

lemma sp_wf_map [intro, simp]: "sp_wf p \<Longrightarrow> sp_wf (sp_map e p)"
  by (simp add: sp_wf_def)

lemma sp_compile_bind_wf:
  assumes "sp_wf p"
  shows "sp_compile (p \<bind> f) = sp_lift_tree (sp_compile p) (\<lambda>v. sp_compile (f v))"
  using sp_wfD[OF assms, where k = "\<lambda>v. sp_compile (f v)"]
  by (simp add: sp_bind_def sp_compile_def sp_compile_with_def)

text \<open>
  What a well-formed program answers, publishes and reads, asked of the program
  rather than of a tree. Each is the tree vocabulary applied to its compilation,
  so the three carry over unchanged --- and the point of stating them is that a
  characterization of a combinator can now speak one vocabulary on both sides,
  instead of a program on the left and its contributions' trees on the right.
\<close>

abbreviation traverse_program ::
  "('x,'g,'d::bot,'d) strategy_program \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'd"
  where "traverse_program p \<sigma> \<equiv> traverse_rhs (sp_compile p) \<sigma>"

abbreviation sides_of_program ::
  "('x,'g,'d::bounded_semilattice_sup_bot,'d) strategy_program
   \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x + 'g \<Rightarrow> 'd"
  where "sides_of_program p \<sigma> \<equiv> sides_of_rhs (sp_compile p) \<sigma>"

abbreviation dep_program ::
  "('x + 'g \<Rightarrow> 'd::bot) \<Rightarrow> ('x,'g,'d,'d) strategy_program \<Rightarrow> ('x + 'g) set"
  where "dep_program \<sigma> p \<equiv> dep_aux \<sigma> (sp_compile p)"

text \<open>Running a well-formed program under any continuation: its own effects
  happen, then the continuation runs on the value it answered.

  Left bare. Their left-hand sides are \<open>f (p k) \<sigma>\<close> with both \<open>p\<close> and \<open>k\<close>
  schematic, which is not a higher-order pattern: as \<open>simp\<close> rules they match any
  application under one of the three observers and spawn an \<open>sp_wf\<close> subgoal for
  it --- including their own right-hand sides, where \<open>sides_of_program p \<sigma>\<close>
  unfolds to \<open>sides_of_rhs (sp_compile p) \<sigma>\<close> and matches at \<open>?p := sp_compile\<close>.
  Nothing loops while \<open>sp_wf sp_compile\<close> is unprovable by the simpset, but that is
  an accident to rely on, so each use cites the rule.\<close>

lemma traverse_rhs_sp_wf:
  assumes "sp_wf p"
  shows "traverse_rhs (p k) \<sigma> = traverse_rhs (k (traverse_program p \<sigma>)) \<sigma>"
  by (subst sp_wfD[OF assms]) simp

lemma dep_aux_sp_wf:
  assumes "sp_wf p"
  shows "dep_aux \<sigma> (p k) = dep_program \<sigma> p \<union> dep_aux \<sigma> (k (traverse_program p \<sigma>))"
  by (subst sp_wfD[OF assms]) simp

lemma sides_of_rhs_sp_wf:
  fixes p :: "('x,'g,'d::bounded_semilattice_sup_bot,'d) strategy_program"
  assumes "sp_wf p"
  shows "sides_of_rhs (p k) \<sigma>
           = sides_of_program p \<sigma> \<squnion> sides_of_rhs (k (traverse_program p \<sigma>)) \<sigma>"
  by (subst sp_wfD[OF assms]) simp

text \<open>The three together: what a proof that has just exposed \<open>p k\<close> under an
  observer needs, cited as one name.\<close>

lemmas sp_wf_observes = traverse_rhs_sp_wf sides_of_rhs_sp_wf dep_aux_sp_wf

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

lemma sp_compile_bind: "sp_compile (m \<bind> f) = m (\<lambda>x. sp_compile (f x))"
  by (simp add: sp_compile_def sp_compile_with_def sp_bind_def)

lemma sp_compile_with_bind: "sp_compile_with encode (m \<bind> f) = m (\<lambda>x. sp_compile_with encode (f x))"
  by (simp add: sp_compile_with_def sp_bind_def)

subsection \<open>Monad laws\<close>

text \<open>The three laws, so a caller may rewrite a program before compiling it and know the
  tree is unchanged.  All three hold by function extensionality alone -- a program is a
  continuation transformer, and \<open>\<bind>\<close> is composition -- so no tree-level reasoning is
  involved.\<close>
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
