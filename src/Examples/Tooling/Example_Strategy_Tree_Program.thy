theory Example_Strategy_Tree_Program
  imports
    "Voblint_Solver.Strategy_Tree_Program"
    Example_Strategy_Tree
begin

section \<open>The typed frontend, compiling to exactly the tree built by hand\<close>

text \<open>
  \<open>demo_tree\<close> (\<open>Example_Strategy_Tree\<close>) reads local unknown \<open>STR ''local''\<close>
  and publishes to global key \<open>STR ''global''\<close> by naming \<^const>\<open>read_local\<close>/
  \<^const>\<open>side_effect\<close> directly, at the vendor tree's own homogeneous carrier.
  \<open>demo_program\<close> below builds the identical effect through
  \<^type>\<open>strategy_program\<close>'s typed combinators instead; \<open>demo_program_eq\<close>
  proves the two compile to the same tree -- the frontend is not a parallel
  equation language, only a different surface over the one this codebase
  already solves with.
\<close>

definition demo_program :: "(String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program =
     do {
       x \<leftarrow> sp_local (STR ''local'');
       _ \<leftarrow> sp_sideg (STR ''global'') (x + 1);
       sp_return (x * 2)
     }"

lemma demo_program_eq: "sp_run demo_program = demo_tree"
  by (simp add: demo_program_def demo_tree_def)

section \<open>An intermediate value unrelated to the tree's own carrier\<close>

text \<open>
  \<open>strategy_tree\<close>'s own \<open>do\<close>-notation cannot express this directly: every
  \<^const>\<open>QueryL\<close>/\<^const>\<open>QueryG\<close> answer and the tree's own final answer share
  one carrier \<open>'d\<close>, so a step producing something else has no vendor-tree
  encoding until it is folded back into \<open>'d\<close>. \<open>strategy_program\<close>'s \<open>'a\<close> is
  free to be that something else -- here a plain \<open>bool\<close>, threaded through
  \<^const>\<open>sp_bind\<close> and used as live control flow -- for exactly as long as
  the computation needs it.
\<close>

definition demo_program_flag ::
  "bool \<Rightarrow> (String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program_flag publish =
     do {
       x \<leftarrow> sp_local (STR ''local'');
       keep \<leftarrow> sp_return publish;
       if keep
       then do { _ \<leftarrow> sp_sideg (STR ''global'') (x + 1); sp_return (x * 2) }
       else sp_return x
     }"

lemma demo_program_flag_true: "sp_run (demo_program_flag True) = demo_tree"
  by (simp add: demo_program_flag_def demo_tree_def)

lemma demo_program_flag_false:
  "sp_run (demo_program_flag False) = QueryL (STR ''local'') Answer"
  by (simp add: demo_program_flag_def)

text \<open>
  \<open>bool\<close> alone leaves open whether \<open>'a\<close> can be a compound value, not just
  another scalar. \<open>demo_ctx\<close> is a record with fields unrelated to \<open>'x\<close>,
  \<open>'g\<close>, or \<open>'d\<close>; \<open>demo_program_ctx\<close> builds one mid-program, reads both
  fields back out of it, and reaches the same \<open>demo_tree\<close> shape as
  \<open>demo_program\<close> -- the frontend threads whatever \<open>'a\<close> the caller chooses.
\<close>

record demo_ctx =
  ctx_count :: nat
  ctx_publish :: bool

definition demo_program_ctx :: "(String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program_ctx =
     do {
       x \<leftarrow> sp_local (STR ''local'');
       ctx \<leftarrow> sp_return \<lparr> ctx_count = x, ctx_publish = True \<rparr>;
       if ctx_publish ctx
       then do { _ \<leftarrow> sp_sideg (STR ''global'') (ctx_count ctx + 1); sp_return (ctx_count ctx * 2) }
       else sp_return (ctx_count ctx)
     }"

lemma demo_program_ctx_eq: "sp_run demo_program_ctx = demo_tree"
  by (simp add: demo_program_ctx_def demo_tree_def)

section \<open>Continuing from an already-built vendor tree\<close>

text \<open>
  \<open>sp_lift_tree\<close> embeds an already-built \<open>strategy_tree\<close> as the program
  that runs it and continues -- the shape a backend combinator like
  \<open>fold_rhs_trees\<close> (\<open>Strategy_Tree_Fold\<close>) hands back. \<open>demo_program_from_tree\<close>
  resumes exactly where \<open>demo_tree\<close> (\<open>Example_Strategy_Tree\<close>) leaves off,
  reading one more local unknown on top of its answer.
\<close>

definition demo_program_from_tree ::
    "(String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program_from_tree =
     do {
       v \<leftarrow> sp_lift_tree demo_tree;
       w \<leftarrow> sp_local (STR ''extra'');
       sp_return (v + w)
     }" 

lemma demo_program_from_tree_eq:
  "sp_run demo_program_from_tree =
     QueryL (STR ''local'')
       (\<lambda>x. Side (STR ''global'') (x + 1) (QueryL (STR ''extra'') (\<lambda>w. Answer (x * 2 + w))))"
  by (simp add: demo_program_from_tree_def demo_tree_def sp_bind_assoc)

end
