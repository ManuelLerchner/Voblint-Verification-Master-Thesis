theory Example_Strategy_Tree_Program
  imports
    "Voblint_Solver.Strategy_Tree_Program"
    Example_Strategy_Tree
begin

section \<open>A typed program compiling to exactly the tree built by hand\<close>

text \<open>
  \<open>read_decision\<close> reads local unknown \<open>STR ''local''\<close> and packages it into
  a \<open>demo_decision\<close> record together with whether it is positive --
  \<open>strategy_program\<close>'s intermediate type need not be the tree's own carrier
  \<open>'d\<close>, only the final answer does. \<open>demo_program\<close> consumes that record,
  conditionally publishes, and answers; \<open>demo_program_compiled\<close> shows the
  vendor tree this compiles to explicitly -- the record and the Boolean
  never reach the solver, only the \<^const>\<open>QueryL\<close>/\<^const>\<open>Side\<close>/
  \<^const>\<open>Answer\<close> shape they compile down to does.
  \<open>demo_program_matches_handwritten\<close> then identifies that shape with
  \<^const>\<open>demo_tree\<close> (\<open>Example_Strategy_Tree\<close>).
\<close>

record demo_decision =
  decision_value :: nat
  decision_publish :: bool

definition read_decision ::
  "(String.literal, String.literal, nat, demo_decision) strategy_program" where
  "read_decision =
     do {
       x \<leftarrow> sp_read_local (STR ''local'');
       sp_return \<lparr> decision_value = x, decision_publish = x > 0 \<rparr>
     }"

definition demo_program :: "(String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program =
     do {
       decision \<leftarrow> read_decision;
       if decision_publish decision
       then do {
              _ \<leftarrow> sp_publish (STR ''global'') (decision_value decision + 1);
              sp_return (decision_value decision * 2)
            }
       else sp_return (decision_value decision)
     }"

lemma demo_program_compiled:
  "sp_compile demo_program =
     QueryL (STR ''local'') (\<lambda>x.
       if x > 0
       then Side (STR ''global'') (x + 1) (Answer (x * 2))
       else Answer x)"
  by (auto simp: demo_program_def read_decision_def sp_compile_def sp_bind_assoc)

lemma demo_program_matches_handwritten: "sp_compile demo_program = demo_tree"
  by (simp add: demo_program_compiled demo_tree_def)

text \<open>
  \<open>decision_publish\<close> only ever chooses between publishing and not, never
  between different queries: the compiled query set is the fixed singleton
  \<open>{local}\<close>, for every environment.
\<close>

lemma demo_program_deps: "dep_aux \<sigma> (sp_compile demo_program) = {Inl (STR ''local'')}"
  by (simp add: demo_program_compiled)

lemma demo_program_env_indep_deps: "env_indep_deps (sp_compile demo_program)"
  by (rule env_indep_depsI) (simp add: demo_program_deps)

subsection \<open>Continuing from an already-built vendor tree\<close>

text \<open>
  \<^const>\<open>sp_lift_tree\<close> embeds an already-built \<open>strategy_tree\<close> as the
  program that runs it and continues -- the shape a backend combinator like
  \<open>fold_rhs_contributions\<close> (\<open>Strategy_Tree_Fold\<close>) folds one contribution tree at a
  time; \<open>fold_rhs_contributions\<close> itself returns a \<open>strategy_program\<close>, compiled to a
  vendor tree only at the solver boundary. \<open>demo_program_from_tree\<close>
  resumes exactly where \<^const>\<open>demo_tree\<close> leaves off, reading one more
  local unknown on top of its answer.
\<close>

definition demo_program_from_tree ::
    "(String.literal, String.literal, nat, nat) strategy_program" where
  "demo_program_from_tree =
     do {
       v \<leftarrow> sp_lift_tree demo_tree;
       w \<leftarrow> sp_read_local (STR ''extra'');
       sp_return (v + w)
     }"

lemma demo_program_from_tree_compiled:
  "sp_compile demo_program_from_tree =
     QueryL (STR ''local'') (\<lambda>x.
       if x > 0
       then Side (STR ''global'') (x + 1) (QueryL (STR ''extra'') (\<lambda>w. Answer (x * 2 + w)))
       else QueryL (STR ''extra'') (\<lambda>w. Answer (x + w)))"
proof -
  have step: "sp_compile demo_program_from_tree
      = sp_lift_tree demo_tree
          (\<lambda>v. sp_compile (sp_read_local (STR ''extra'') \<bind> (\<lambda>w. sp_return (v + w))))"
    unfolding demo_program_from_tree_def sp_compile_def
    by (rule sp_compile_with_bind)
  show ?thesis
    unfolding step by (auto simp: demo_tree_def sp_compile_def split: if_splits)
qed

section \<open>Value-dependent query structure\<close>

text \<open>
  A program's later queries may depend on values read earlier, so compiling
  a program does not by itself guarantee \<^const>\<open>env_indep_deps\<close>.
  \<open>branching_program\<close> queries only \<open>local\<close> when that value is \<open>0\<close>; when it is
  positive, it additionally queries the global unknown \<open>input\<close> before
  publishing and answering.
\<close>

definition branching_program ::
  "(String.literal, String.literal, nat, nat) strategy_program"
where
  "branching_program =
     do {
       x \<leftarrow> sp_read_local (STR ''local'');
       if x > 0
       then do {
              y \<leftarrow> sp_read_global (STR ''input'');
              _ \<leftarrow> sp_publish (STR ''output'') (x + y);
              sp_return (2 * (x + y))
            }
       else sp_return 0
     }"

lemma branching_program_compiled:
  "sp_compile branching_program =
     QueryL (STR ''local'') (\<lambda>x.
       if x > 0
       then QueryG (STR ''input'') (\<lambda>y. Side (STR ''output'') (x + y) (Answer (2 * (x + y))))
       else Answer 0)"
  by (auto simp: branching_program_def sp_compile_def split: if_splits)

text \<open>Two named environments distinguishing the two branches: \<open>zero_environment\<close>
  answers every unknown \<open>0\<close>, and \<open>positive_environment\<close> overrides only \<open>local\<close>.\<close>

definition zero_environment :: "String.literal + String.literal \<Rightarrow> nat" where
  "zero_environment = (\<lambda>_. 0)"

definition positive_environment :: "String.literal + String.literal \<Rightarrow> nat" where
  "positive_environment = zero_environment (Inl (STR ''local'') := 1)"

lemma branching_program_result_zero:
  "traverse_rhs (sp_compile branching_program) zero_environment = 0"
  by (simp add: branching_program_compiled zero_environment_def)

lemma branching_program_result_positive:
  "traverse_rhs (sp_compile branching_program) positive_environment = 2"
  by (simp add: branching_program_compiled positive_environment_def zero_environment_def)

lemma branching_program_deps_zero:
  "dep_aux zero_environment (sp_compile branching_program) = {Inl (STR ''local'')}"
  by (simp add: branching_program_compiled zero_environment_def)

lemma branching_program_deps_positive:
  "dep_aux positive_environment (sp_compile branching_program)
     = {Inl (STR ''local''), Inr (STR ''input'')}"
  by (simp add: branching_program_compiled positive_environment_def zero_environment_def)

lemma branching_program_not_env_indep_deps: "\<not> env_indep_deps (sp_compile branching_program)"
proof
  assume indep: "env_indep_deps (sp_compile branching_program)"
  have same: "dep_aux zero_environment (sp_compile branching_program)
      = dep_aux positive_environment (sp_compile branching_program)"
    using indep by blast
  show False
    using same branching_program_deps_zero branching_program_deps_positive by simp
qed

text \<open>
  \<open>branching_program\<close>'s query set is not fixed, but it only ever grows as
  \<open>local\<close> grows: exactly the case \<^const>\<open>mono_tree_deps\<close> exists for.
\<close>

lemma branching_program_mono_tree_deps: "mono_tree_deps (sp_compile branching_program)"
proof (rule mono_tree_depsI)
  fix \<sigma>1 \<sigma>2 :: "String.literal + String.literal \<Rightarrow> nat"
  assume "\<sigma>1 \<le> \<sigma>2"
  then have "\<sigma>1 (Inl (STR ''local'')) \<le> \<sigma>2 (Inl (STR ''local''))"
    by (simp add: le_fun_def)
  then show "dep_aux \<sigma>1 (sp_compile branching_program) \<subseteq> dep_aux \<sigma>2 (sp_compile branching_program)"
    by (auto simp add: branching_program_compiled)
qed

end
