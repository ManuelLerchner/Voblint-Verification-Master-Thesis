theory Example_Strategy_Tree_Demo
  imports
    "Voblint_Core.Strategy_Tree_Combinators"
    "Voblint_Core.Strategy_Tree_Monad"
    "Voblint_Core.Strategy_Tree_Do"
begin

section \<open>Strategy trees as a dependency/effect language\<close>

text \<open>
  A minimal, domain-independent demonstration that \<^type>\<open>strategy_tree\<close> is a
  small effect language on its own -- no abstract domain, CFG, or context
  involved. \<^const>\<open>answer\<close> returns a value and \<^const>\<open>seqcomp_tree\<close> sequences
  two trees: exactly \<open>return\<close>/\<open>>>=\<close> for this monad
  (\<open>Strategy_Tree_Monad.thy\<close>), written below with \<open>do\<close> notation
  (\<open>Strategy_Tree_Do.thy\<close> registers \<^const>\<open>seqcomp_tree\<close> as this monad's
  bind, so \<open>do { x \<leftarrow> t; k x }\<close> parses to exactly \<open>seqcomp_tree t k\<close>).

  \<open>fib_tree n\<close> builds the whole finite computation tree for \<open>fib n\<close> before any
  evaluation. \<^type>\<open>strategy_tree\<close> itself gains no recursion primitive -- the
  recursion lives in the Isabelle function that builds the tree, exactly as
  every equation-authoring definition in this codebase builds a finite tree
  per unknown ahead of the solver run.
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
  \<open>fib_tree\<close> never reads a local or global unknown -- no \<^const>\<open>read_local\<close>,
  \<^const>\<open>read_global\<close>, or \<^const>\<open>depend_on\<close> appears above -- so its evaluation
  does not depend on the environment \<open>\<sigma>\<close> at all: \<open>traverse_rhs\<close> just runs the
  bind chain down to the leaves. A dependency-reading example would key
  \<^const>\<open>read_local\<close> by index and let the solver's fixpoint iteration do the
  recursion instead; this demo intentionally shows the other half of the
  API -- pure sequencing -- since \<^const>\<open>seqcomp_tree\<close> needs no solver at all.
\<close>

lemma fib_tree_correct: "traverse_rhs (fib_tree n) \<sigma> = fib n"
  by (induct n rule: fib.induct) auto

end
