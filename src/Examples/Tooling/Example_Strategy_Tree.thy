theory Example_Strategy_Tree
  imports
    "Voblint_Solver.Strategy_Tree_Combinators"
    "Voblint_Solver.Strategy_Tree_Sequencing"
begin

section \<open>Strategy trees as a dependency/effect language\<close>

text \<open>
  A minimal, domain-independent demonstration that \<^type>\<open>strategy_tree\<close> is a
  small effect language on its own -- no abstract domain, CFG, or context
  involved. \<^const>\<open>answer\<close> gives a pure result, and \<^const>\<open>seqcomp_tree\<close>
  gives it monadic-style sequential composition, written below with \<open>do\<close>
  notation (\<open>Strategy_Tree_Sequencing\<close> registers it as this monad's bind, so
  \<open>do { x \<leftarrow> t; k x }\<close> parses to exactly \<open>seqcomp_tree t k\<close>). Its shape is
  \<open>tree d \<Rightarrow> (d \<Rightarrow> tree d) \<Rightarrow> tree d\<close> rather than a fully polymorphic
  \<open>m a \<Rightarrow> (a \<Rightarrow> m b) \<Rightarrow> m b\<close>, since \<open>'d\<close> is also the type \<open>QueryL\<close>/\<open>QueryG\<close>/
  \<open>Side\<close> read and publish -- so "monad" below means monadic in style, not a
  Haskell-style polymorphic \<open>Monad\<close> instance.

  \<open>fib_tree\<close> demonstrates pure sequencing: since it never reads or publishes,
  \<^const>\<open>seqcomp_tree\<close>'s own defining equation on \<open>Answer\<close> collapses it to
  \<open>answer (fib n)\<close> during construction (\<open>fib_tree_eq\<close> below) -- it never
  retains a genuine \<open>QueryL\<close>/\<open>QueryG\<close>/\<open>Side\<close> tree shape, so its purpose is
  only to show that strategy-tree bind reduces to ordinary sequential
  composition on pure computations. \<open>demo_tree\<close>, further down, is the other
  half of the API: it genuinely reads a local unknown and publishes a global
  contribution, so its \<^const>\<open>dep_aux\<close>, \<^const>\<open>sides_of_rhs\<close>, and
  \<^const>\<open>traverse_rhs\<close> all stay non-trivial.
\<close>

fun fib :: "nat \<Rightarrow> nat" where
  "fib 0 = 0"
| "fib (Suc 0) = 1"
| "fib (Suc (Suc n)) = fib (Suc n) + fib n"

fun fib_tree :: "nat \<Rightarrow> ('x, 'g, nat) strategy_tree" where
  "fib_tree 0 = answer 0"
| "fib_tree (Suc 0) = answer 1"
| "fib_tree (Suc (Suc n)) =
     do {
       a \<leftarrow> fib_tree (Suc n);
       b \<leftarrow> fib_tree n;
       answer (a + b)
     }"

text \<open>
  \<^type>\<open>strategy_tree\<close> itself gains no recursion primitive from \<open>fib_tree\<close> --
  the recursion lives in the Isabelle function that builds the term, exactly
  as every equation-authoring definition in this codebase builds a tree per
  unknown ahead of the solver run. Since \<open>fib_tree\<close> never issues a
  \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close>/\<^const>\<open>Side\<close>, though, the term it
  builds collapses immediately: \<^const>\<open>seqcomp_tree\<close>'s \<open>Answer\<close> equation
  fires at every step, so \<open>fib_tree n\<close> is definitionally \<open>answer (fib n)\<close>,
  not a retained tree shape.
\<close>

lemma fib_tree_eq: "fib_tree n = answer (fib n)"
  by (induct n rule: fib.induct) simp_all

lemma fib_tree_correct: "traverse_rhs (fib_tree n) \<sigma> = fib n"
  by (simp add: fib_tree_eq)

subsection \<open>Monad laws, demonstrated on the fib tree\<close>

text \<open>
  \<open>Answer\<close> is a right identity and \<open>seqcomp_tree\<close> is associative for any
  tree, not just \<^const>\<open>fib_tree\<close> -- these two concrete instances put both
  laws to use rather than only stating them abstractly.
\<close>

lemma fib_tree_seqcomp_Answer_right: "fib_tree n \<bind> Answer = fib_tree n"
  by (rule seqcomp_Answer_right)

lemma fib_tree_seqcomp_assoc:
  "fib_tree n \<bind> (\<lambda>a. answer (a + 1)) \<bind> (\<lambda>c. answer (c * 2))
     = fib_tree n \<bind> (\<lambda>a. answer (a + 1) \<bind> (\<lambda>c. answer (c * 2)))"
  by (rule seqcomp_assoc)

subsection \<open>Reading and publishing, demonstrated directly\<close>

text \<open>
  \<open>fib_tree\<close> never reads or publishes, so \<^const>\<open>dep_aux\<close> and
  \<^const>\<open>sides_of_rhs\<close> are trivial on it (shown below: \<open>{}\<close> and the
  everywhere-\<open>bot\<close> map). \<open>demo_tree\<close> is the other half of the API: it reads
  local unknown \<open>STR ''local''\<close> with \<^const>\<open>read_local\<close>, then publishes
  the result plus one as a \<^const>\<open>Side\<close> contribution to global key
  \<open>STR ''global''\<close> with \<^const>\<open>side_effect\<close> before answering with
  \<^const>\<open>answer\<close>.
\<close>

text \<open>
  \<^const>\<open>sides_of_rhs\<close> needs \<open>'d::bounded_semilattice_sup_bot\<close>. \<open>nat\<close> is
  mathematically one -- \<open>sup = max\<close> and \<open>bot = 0\<close>, both already proved from
  its standard library \<open>distrib_lattice\<close>/\<open>order_bot\<close> instances, so
  \<open>intro_classes\<close> discharges the combined class with no new axioms -- but
  the two were never bridged in HOL itself, so the sort has to be
  registered explicitly. This is deliberately scoped to this file: no
  domain in this codebase abstracts over plain \<open>nat\<close>, so nothing elsewhere
  depends on the sort staying unregistered, and a genuine future
  instantiation elsewhere would fail loudly at build time rather than
  silently conflict.
\<close>

instance nat :: bounded_semilattice_sup_bot ..

definition demo_tree :: "(String.literal, String.literal, nat) strategy_tree" where
  "demo_tree = do {
     x \<leftarrow> read_local (STR ''local'');
     side_effect (STR ''global'') (x + 1) (answer (x * 2))
   }"

lemma demo_tree_traverse_rhs: "traverse_rhs demo_tree \<sigma> = \<sigma> (Inl (STR ''local'')) * 2"
  by (simp add: demo_tree_def)

lemma demo_tree_dep_aux: "dep_aux \<sigma> demo_tree = {Inl (STR ''local'')}"
  by (simp add: demo_tree_def)

lemma demo_tree_sides_of_rhs:
  "sides_of_rhs demo_tree \<sigma> (Inr (STR ''global'')) = \<sigma> (Inl (STR ''local'')) + 1"
  by (simp add: demo_tree_def Let_def)

subsection \<open>Dependency properties, demonstrated on both trees\<close>

text \<open>
  \<open>fib_tree\<close> never issues a \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> -- no
  \<^const>\<open>read_local\<close>/\<^const>\<open>read_global\<close> appears in its definition -- so
  the set of unknowns it queries is always empty, for any environment: the
  strongest case of \<^const>\<open>env_indep_deps\<close>. \<^const>\<open>mono_tree_deps\<close> then
  follows for free through @{thm env_indep_deps_imp_mono_tree_deps},
  without a separate monotonicity argument.
\<close>

lemma fib_tree_dep_aux_empty: "dep_aux \<sigma> (fib_tree n) = {}"
  by (simp add: fib_tree_eq)

lemma fib_tree_env_indep_deps: "env_indep_deps (fib_tree n)"
  by (rule env_indep_depsI) (simp add: fib_tree_dep_aux_empty)

lemma fib_tree_mono_tree_deps: "mono_tree_deps (fib_tree n)"
  by (rule env_indep_deps_imp_mono_tree_deps[OF fib_tree_env_indep_deps])

text \<open>
  \<open>demo_tree\<close> reads the environment (\<^const>\<open>traverse_rhs\<close> and its
  published value both depend on \<open>\<sigma> (Inl (STR ''local''))\<close>), unlike
  \<open>fib_tree\<close>, but the *set* of unknowns it queries is still
  \<open>{Inl (STR ''local'')}\<close> for every \<open>\<sigma>\<close> -- every tree this codebase builds
  has that shape (fixed \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> skeleton, only
  \<^const>\<open>Side\<close>/\<^const>\<open>Answer\<close> values vary), so \<^const>\<open>env_indep_deps\<close>
  still holds, and \<^const>\<open>mono_tree_deps\<close> follows through the same bridge
  as for \<open>fib_tree\<close> -- just no longer vacuously, since the queried set here
  is non-empty.
\<close>

lemma demo_tree_env_indep_deps: "env_indep_deps demo_tree"
  by (rule env_indep_depsI) (simp add: demo_tree_dep_aux)

lemma demo_tree_mono_tree_deps: "mono_tree_deps demo_tree"
  by (rule env_indep_deps_imp_mono_tree_deps[OF demo_tree_env_indep_deps])

text \<open>
  \<^const>\<open>traverse_rhs\<close> is likewise constant in the environment
  (@{thm fib_tree_correct} already proves it equals \<open>fib n\<close> for every
  \<open>\<sigma>\<close>), so \<^const>\<open>seqcomp_tree\<close>'s own monotonicity lemma @{thm seqcomp_mono}
  applies to any continuation built on \<open>fib_tree\<close>, without needing the tree
  itself to read anything.
\<close>

lemma fib_tree_seqcomp_mono:
  fixes k :: "nat \<Rightarrow> ('x, 'g, nat) strategy_tree"
  assumes k_mono_env: "\<And>v \<sigma>1 \<sigma>2. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> traverse_rhs (k v) \<sigma>1 \<le> traverse_rhs (k v) \<sigma>2"
  assumes k_mono_val: "\<And>\<sigma> v1 v2. v1 \<le> v2 \<Longrightarrow> traverse_rhs (k v1) \<sigma> \<le> traverse_rhs (k v2) \<sigma>"
  assumes le: "\<sigma>1 \<le> \<sigma>2"
  shows "traverse_rhs (fib_tree n \<bind> k) \<sigma>1 \<le> traverse_rhs (fib_tree n \<bind> k) \<sigma>2"
  by (rule seqcomp_mono) (simp_all add: fib_tree_correct k_mono_env k_mono_val le)

end
