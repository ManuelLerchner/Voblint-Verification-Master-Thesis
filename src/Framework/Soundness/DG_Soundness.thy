theory DG_Soundness
  imports DG_Spec_Sound DG_Keyed_Generator "Voblint_Domain.Nonrelational_State"
    "Voblint_Solver.Strategy_Tree_Post_Solution"
begin

section \<open>Generic D/G post-solution soundness\<close>

text \<open>
  The family-independent layer between a specification's soundness
  (\<open>DG_Spec_Sound\<close>) and a routed context's endpoints: order bounds for the
  generator's fold, and the \<open>vars_cover\<close> closure obligation every
  post-solution theorem states -- decidable executably as
  \<open>vars_cover_exec\<close> for a routed system, since a routed callee's entry is
  solved only once a caller publishes its seed, so coverage is a fact about
  the solver run rather than about graph reachability alone.
\<close>

subsection \<open>Fold bounds\<close>

text \<open>
  Order bounds for \<open>side_rhs_fold_dg\<close>/\<open>side_acc_dg\<close>: the accumulator and every
  folded Answer are below the folded result, and every tree's side
  contribution is below the fold's.
\<close>

lemma side_acc_dg_ge_acc:
  "acc \<le> side_acc_dg acc sigma ts"
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t ts)
  have "acc \<le> acc \<squnion> locals (traverse_rhs t sigma)" by simp
  also have "... \<le> side_acc_dg
      (acc \<squnion> locals (traverse_rhs t sigma)) sigma ts"
    by (rule Cons.IH)
  finally show ?case by simp
qed

lemma locals_traverse_le_side_acc_dg:
  assumes "t \<in> set ts"
  shows "locals (traverse_rhs t sigma) \<le> side_acc_dg acc sigma ts"
using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    have "locals (traverse_rhs t sigma)
        \<le> acc \<squnion> locals (traverse_rhs t' sigma)"
      using True by simp
    also have "... \<le> side_acc_dg
        (acc \<squnion> locals (traverse_rhs t' sigma)) sigma ts"
      by (rule side_acc_dg_ge_acc)
    finally show ?thesis by simp
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then show ?thesis using Cons.IH by simp
  qed
qed

lemma sides_le_side_rhs_fold_dg:
  assumes "t \<in> set ts"
  shows "sides_of_rhs t sigma k
    \<le> sides_of_rhs (sp_compile (side_rhs_fold_dg acc ts)) sigma k"
using assms
proof (induction ts arbitrary: acc)
  case Nil
  then show ?case by simp
next
  case (Cons t' ts)
  show ?case
  proof (cases "t = t'")
    case True
    then show ?thesis
      by (simp add: sp_compile_with_bind)
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "sides_of_rhs t sigma k
        \<le> sides_of_rhs
          (sp_compile (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts)) sigma k"
      by (rule Cons.IH)
    also have "... \<le> sides_of_rhs t' sigma k \<squnion>
        sides_of_rhs
          (sp_compile (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts)) sigma k"
      by simp
    also have "... =
        sides_of_rhs (sp_compile (side_rhs_fold_dg acc (t' # ts))) sigma k"
      by (simp add: sp_compile_with_bind)
    finally show ?thesis .
  qed
qed

text \<open>
  \<open>vars_cover g vars\<close> bundles the one recurring obligation every
  post-solution soundness theorem in this development needs: \<open>vars\<close> contains
  the CFG entry, every \<open>intra\<close> edge's target, and every call's callee entry
  and continuation. The four components are one semantic fact -- ``\<open>vars\<close> is
  a cover of \<open>g\<close>'s reachable nodes'' -- not four independent assumptions, so
  callers state and discharge it as a single premise instead of four
  positional ones. Global (not locale-local): every analysis instance and
  the executable pipeline cite it under the same name.
\<close>
definition vars_cover :: "cfg \<Rightarrow> (cfg_node \<times> unit) set \<Rightarrow> bool" where
  "vars_cover g vars \<longleftrightarrow>
     (cfg_entry g, ()) \<in> vars
   \<and> (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow> (v, ()) \<in> vars)
   \<and> (\<forall>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
        \<longrightarrow> (FunctionEntry q, ()) \<in> vars)
   \<and> (\<forall>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
        \<longrightarrow> (k, ()) \<in> vars)"

lemma vars_coverI [intro]:
  assumes "(cfg_entry g, ()) \<in> vars"
    and "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
    and "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
           \<Longrightarrow> (k, ()) \<in> vars"
  shows "vars_cover g vars"
  unfolding vars_cover_def using assms by blast

lemma vars_cover_entryD [dest]: "vars_cover g vars \<Longrightarrow> (cfg_entry g, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_edgeD [dest]:
  "vars_cover g vars \<Longrightarrow> (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
  unfolding vars_cover_def by blast

lemma vars_cover_enterD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (FunctionEntry q, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

lemma vars_cover_combineD [dest]:
  assumes cover: "vars_cover g vars"
  shows "\<And>c dst fs as q k. (c, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g
     \<Longrightarrow> (k, ()) \<in> vars"
  using cover unfolding vars_cover_def by blast

text \<open>
  Whether a solved key set covers a finite graph is decidable: walk the two edge
  enumerations and test membership. A routed system reads a callee's entry through
  its seed global rather than through the call site's unknown, so the callee's
  entry is solved only when some caller actually published a seed; coverage is
  therefore a fact about the solver run, not about graph connectivity, and this
  witness is how an executable run states it.
\<close>
definition vars_cover_exec :: "cfg \<Rightarrow> (cfg_node \<times> unit) set \<Rightarrow> bool" where
  "vars_cover_exec g vars \<longleftrightarrow>
     (cfg_entry g, ()) \<in> vars
   \<and> list_all (\<lambda>(u, a, v). (v, ()) \<in> vars) (cfg_intra_list g)
   \<and> list_all (\<lambda>(c, ca, ce, k). (ce, ()) \<in> vars \<and> (k, ()) \<in> vars) (cfg_calls_list g)"

lemma vars_cover_of_exec:
  assumes finE: "finite (intra g)" and finC: "finite (calls g)"
    and cover: "vars_cover_exec g vars"
  shows "vars_cover g vars"
  using cover unfolding vars_cover_exec_def vars_cover_def
  by (auto simp: list_all_iff set_cfg_intra_list[OF finE] set_cfg_calls_list[OF finC])


subsection \<open>combine_env algebra at the call boundary\<close>

text \<open>
  Every call site owns \<open>ret_var\<close> as its own compiler-internal name, never a
  user-declared global (\<^const>\<open>reserved_ret_var\<close>); that is what lets a
  combine step read the return value straight out of the callee exit instead
  of routing it through \<^const>\<open>combine_env\<close> a second time.
\<close>

lemma combine_env_combine_env_left [simp]:
  "combine_env gs (combine_env gs dc g) (combine_env gs de g) = combine_env gs dc g"
  by (auto simp: combine_env_def)

lemma combine_env_local_eq [simp]:
  "\<not> gs x \<Longrightarrow> combine_env gs sc se x = sc x"
  by (simp add: combine_env_def)

end

