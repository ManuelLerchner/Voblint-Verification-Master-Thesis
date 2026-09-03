theory DG_Soundness
  imports DG_Spec_Sound DG_Keyed_Generator
begin

section \<open>Generic D/G post-solution soundness\<close>

text \<open>
  The family-independent layer between a specification's soundness
  (\<open>DG_Spec_Sound\<close>) and a routed context's endpoints: order bounds for the
  generator's fold, the intersection concretization \<open>gamma_dg\<close>, the
  \<open>vars_cover\<close> closure obligation every post-solution theorem states, and
  the hook-parametric post-fixpoint spine \<open>sound_dg_hooks\<close>, which derives a
  structural post-fixpoint from any three tree-producing hooks whose
  observations are sound -- dependencies are handled as closure
  (\<open>dep\<^sub>L \<dots> \<subseteq> vars\<close>), never as an exact shape, so an effect-free and an
  effectful specification are both instances rather than cases.
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

subsection \<open>The intersection concretization\<close>

definition gamma_dg ::
  "'d::sound_domain abs_state \<Rightarrow> 'g::sound_domain abs_state \<Rightarrow> store set"
where
  "gamma_dg d g = \<lbrakk>d\<rbrakk> \<inter> \<lbrakk>g\<rbrakk>"

lemma gamma_dg_le_D: "gamma_dg d g \<subseteq> \<lbrakk>d\<rbrakk>"
  unfolding gamma_dg_def by blast

lemma gamma_dg_le_G: "gamma_dg d g \<subseteq> \<lbrakk>g\<rbrakk>"
  unfolding gamma_dg_def by blast

lemma gamma_dg_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_dg d g \<subseteq> gamma_dg d' g'"
  using gamma_state_mono[OF assms(1)] gamma_state_mono[OF assms(2)]
  unfolding gamma_dg_def by blast

(* Pointwise duals of gamma_dg_le_D / gamma_dg_le_G, for call sites that need
   the per-element fact rather than the set inclusion. *)
lemma gamma_dgD1 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>"
  using gamma_dg_le_D by blast

lemma gamma_dgD2 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>g\<rbrakk>"
  using gamma_dg_le_G by blast



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


subsection \<open>Hook-parametric D/G soundness\<close>

definition dg_hook_D ::
  "((pp \<times> unit + unit) \<Rightarrow> ('D::bounded_semilattice_sup_bot,
    'G::bounded_semilattice_sup_bot) dg_state) \<Rightarrow> pp \<Rightarrow> 'D"
where
  "dg_hook_D sigma v = locals (sigma (Inl (v, ())))"
definition dg_hook_G ::
  "((pp \<times> unit + unit) \<Rightarrow> ('D::bounded_semilattice_sup_bot,
    'G::bounded_semilattice_sup_bot) dg_state) \<Rightarrow> 'G"
where
  "dg_hook_G sigma = globs (sigma (Inr ()))"

definition dg_hook_gamma ::
  "('D::bounded_semilattice_sup_bot \<Rightarrow>
     'G::bounded_semilattice_sup_bot \<Rightarrow> store set)
   \<Rightarrow> ((pp \<times> unit + unit) \<Rightarrow> ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_hook_gamma gammaDG sigma v =
    gammaDG (dg_hook_D sigma v) (dg_hook_G sigma)"

locale sound_dg_hooks =
  fixes gammaDG :: "'D::bounded_semilattice_sup_bot \<Rightarrow>
      'G::bounded_semilattice_sup_bot \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
    and edge_tree :: "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and combine_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
    and enter_tree :: "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow>
      (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
  assumes gammaDG_mono:
      "\<And>d d' g g'. \<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and edge_hook_sound:
      "\<And>sigma source action destination.
        edge_collect action (dg_hook_gamma gammaDG sigma source) \<subseteq>
          gammaDG
            (locals (traverse_rhs
              (edge_tree source action destination) sigma))
            (globs (sides_of_rhs
              (edge_tree source action destination) sigma (Inr ())))"
    and enter_hook_sound:
      "\<And>sigma caller dst fs args callee s.
        s \<in> dg_hook_gamma gammaDG sigma caller \<Longrightarrow>
        call_enter gs (CallEdge dst fs args) s \<in>
          gammaDG
            (locals (traverse_rhs
              (enter_tree caller (CallEdge dst fs args)
                (FunctionEntry callee)) sigma))
            (globs (sides_of_rhs
              (enter_tree caller (CallEdge dst fs args)
                (FunctionEntry callee)) sigma (Inr ())))"
    and combine_hook_sound:
      "\<And>sigma caller dst fs args callee continuation s t.
        \<lbrakk>s \<in> dg_hook_gamma gammaDG sigma caller;
          t \<in> dg_hook_gamma gammaDG sigma (FunctionResult callee)\<rbrakk>
        \<Longrightarrow> combine_collect gs dst s t \<in>
          gammaDG
            (locals (traverse_rhs
              (combine_tree caller (CallEdge dst fs args)
                (FunctionResult callee) continuation) sigma))
            (globs (sides_of_rhs
              (combine_tree caller (CallEdge dst fs args)
                (FunctionResult callee) continuation) sigma (Inr ())))"
begin

definition hook_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree list"
where
  "hook_trees g v =
     map (\<lambda>(u, a). edge_tree u a v) (intra_predecessor_list g v)
     @ map (\<lambda>(c, ca, ex). combine_tree c ca ex v)
       (return_call_action_list g v)
     @ map (\<lambda>(c, ca). enter_tree c ca v)
       (entry_call_list g v)"

definition hook_gen ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G \<Rightarrow>
   (pp \<times> unit, unit, ('D, 'G) dg_state) eqsT"
where
  "hook_gen g bot0 s0d s0g =
    side_cfg_T_eff_keyed_seed_trees intra_predecessor_list (\<lambda>_. ())
      (\<lambda>_ u a v. edge_tree u a v)
      (\<lambda>_ c ca ex v. combine_tree c ca ex v)
      (\<lambda>_ c ca v. enter_tree c ca v)
      g bot0 s0d s0g"

definition hook_acc ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> pp \<Rightarrow> 'D"
where
  "hook_acc g bot0 s0d v =
    (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_hook_gen:
  "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (hook_acc g bot0 s0d v)
     sigma (hook_trees g v)) bot"
  unfolding hook_gen_def hook_trees_def hook_acc_def
  by (simp add: eq_side_cfg_T_eff_keyed_seed_trees)

lemma sides_fold_le_hook_gen:
  "sides_of_rhs
      (sp_compile (side_rhs_fold_dg (hook_acc g bot0 s0d v)
        (hook_trees g v))) sigma k
   \<le> sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma k"
  unfolding hook_gen_def hook_trees_def hook_acc_def
    side_cfg_T_eff_keyed_seed_trees_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

text \<open>
  \<open>hook_gen\<close> is one instantiation of the representation-neutral
  \<^const>\<open>side_cfg_T_eff_keyed_seed_trees\<close>, so its single-tree degeneracy at a
  node with exactly one incoming edge, call return, or call entry is the
  generic reduction proved once for that generator. An analysis instance
  cites the named tree constructor (\<open>edge_tree\<close>, \<open>enter_tree\<close>, or
  \<open>combine_tree\<close>) directly instead of re-unfolding \<open>hook_gen_def\<close> and the
  fold's single-element case at every node.
\<close>

lemma hook_gen_single_edge:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and pred: "intra_predecessor_list g v = [(u, a)]"
    and no_combine: "return_call_action_list g v = []"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (edge_tree u a v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (edge_tree u a v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_edge[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry pred no_combine no_enter bot0])

lemma hook_gen_single_enter:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "intra_predecessor_list g v = []"
    and no_combine: "return_call_action_list g v = []"
    and pred: "entry_call_list g v = [(caller, action)]"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (enter_tree caller action v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (enter_tree caller action v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_enter[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry no_edge no_combine pred bot0])

lemma hook_gen_single_combine:
  fixes bot0 :: 'D
  assumes not_entry: "v \<noteq> cfg_entry g"
    and no_edge: "intra_predecessor_list g v = []"
    and pred: "return_call_action_list g v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list g v = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma =
       DG (locals (traverse_rhs (combine_tree caller action callee_exit v) sigma)) bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()) =
       sides_of_rhs (combine_tree caller action callee_exit v) sigma (Inr ())"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_single_combine[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF not_entry no_edge pred no_enter bot0])

lemma hook_gen_entry:
  fixes bot0 :: 'D
  assumes no_edge: "intra_predecessor_list g (cfg_entry g) = []"
    and no_combine: "return_call_action_list g (cfg_entry g) = []"
    and no_enter: "entry_call_list g (cfg_entry g) = []"
    and bot0: "bot0 = bot"
  shows
    "eq (hook_gen g bot0 s0d s0g) (cfg_entry g, ()) sigma = DG s0d bot"
    "sides_of_rhs (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma (Inr ()) = DG bot s0g"
  unfolding hook_gen_def
  by (simp_all add: side_cfg_T_eff_keyed_seed_trees_entry[
        where pred_sel = intra_predecessor_list and gkey = "\<lambda>_. ()"
          and edge_tree = "\<lambda>_ u a v. edge_tree u a v"
          and combine_tree = "\<lambda>_ c ca ex v. combine_tree c ca ex v"
          and enter_tree = "\<lambda>_ c ca v. enter_tree c ca v",
        OF no_edge no_combine no_enter bot0])

definition hook_postfix ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow> ('D, 'G) dg_state)
   \<Rightarrow> bool"
where
  "hook_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_hook_D sigma (cfg_entry g) \<and>
     s0g \<le> dg_hook_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
       edge_collect a (dg_hook_gamma gammaDG sigma u)
         \<subseteq> dg_hook_gamma gammaDG sigma v) \<and>
     (\<forall>c dst fs args p k s.
       (c, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g \<longrightarrow>
       s \<in> dg_hook_gamma gammaDG sigma c \<longrightarrow>
       call_enter gs (CallEdge dst fs args) s \<in>
         dg_hook_gamma gammaDG sigma (FunctionEntry p)) \<and>
     (\<forall>c dst fs args p k s t.
       (c, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g \<longrightarrow>
       s \<in> dg_hook_gamma gammaDG sigma c \<longrightarrow>
       t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p) \<longrightarrow>
       combine_collect gs dst s t \<in> dg_hook_gamma gammaDG sigma k)"



lemma hook_tree_local_le:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
    and cover: "(v, ()) \<in> vars"
    and tree: "t \<in> set (hook_trees g v)"
  shows "locals (traverse_rhs t sigma) \<le> dg_hook_D sigma v"
proof -
  have eq_le:
      "eq (hook_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using tree_covered_at_local
      [OF part_post_solution_imp_tree_covered_at[OF pp]]
      cover
    by blast
  have "locals (traverse_rhs t sigma)
      \<le> side_acc_dg (hook_acc g bot0 s0d v)
        sigma (hook_trees g v)"
    by (rule locals_traverse_le_side_acc_dg[OF tree])
  also have "... = locals
      (eq (hook_gen g bot0 s0d s0g) (v, ()) sigma)"
    by (simp add: eq_hook_gen)
  also have "... \<le> dg_hook_D sigma v"
    using eq_le
    by (simp add: dg_hook_D_def less_eq_dg_state_def)
  finally show ?thesis .
qed

lemma hook_tree_side_le:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
    and cover: "(v, ()) \<in> vars"
    and tree: "t \<in> set (hook_trees g v)"
  shows "globs (sides_of_rhs t sigma (Inr ())) \<le> dg_hook_G sigma"
proof -
  have sides_le:
      "sides_of_rhs (hook_gen g bot0 s0d s0g (v, ())) sigma
        \<le> sigma"
    using tree_covered_at_sides
      [OF part_post_solution_imp_tree_covered_at[OF pp]]
      cover
    by blast
  have "globs (sides_of_rhs t sigma (Inr ()))
      \<le> globs (sides_of_rhs
        (sp_compile (side_rhs_fold_dg (hook_acc g bot0 s0d v)
          (hook_trees g v))) sigma (Inr ()))"
    using sides_le_side_rhs_fold_dg[OF tree, where k = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  also have "... \<le> globs (sides_of_rhs
      (hook_gen g bot0 s0d s0g (v, ())) sigma (Inr ()))"
    using sides_fold_le_hook_gen[where k = "Inr ()"]
    by (simp add: less_eq_dg_state_def)
  also have "... \<le> dg_hook_G sigma"
    using sides_le[THEN le_funD, of "Inr ()"]
    by (simp add: dg_hook_G_def less_eq_dg_state_def)
  finally show ?thesis .
qed



lemma hook_edge_tree_mem:
  assumes finI: "finite (intra g)"
    and edge: "(u, a, v) \<in> intra g"
  shows "edge_tree u a v \<in> set (hook_trees g v)"
proof -
  have "(u, a) \<in> set (intra_predecessor_list g v)"
    using edge
    by (simp add: set_intra_predecessor_list[OF finI] intra_predecessors_def)
  then show ?thesis
    by (auto simp: hook_trees_def)
qed

lemma hook_enter_tree_mem:
  assumes finC: "finite (calls g)"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
  shows "enter_tree caller (CallEdge dst fs args) (FunctionEntry p)
      \<in> set (hook_trees g (FunctionEntry p))"
proof -
  have "(caller, CallEdge dst fs args) \<in>
      set (entry_call_list g (FunctionEntry p))"
    using call
    by (auto simp: set_entry_call_list[OF finC] entry_calls_iff)
  then show ?thesis
    by (force simp: hook_trees_def image_iff)
qed

lemma hook_combine_tree_mem:
  assumes finC: "finite (calls g)"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
  shows "combine_tree caller (CallEdge dst fs args) (FunctionResult p) k
      \<in> set (hook_trees g k)"
proof -
  have "(caller, CallEdge dst fs args, FunctionResult p) \<in>
      set (return_call_action_list g k)"
    using call
    by (auto simp: set_return_call_action_list[OF finC]
      return_call_actions_iff)
  then show ?thesis
    by (force simp: hook_trees_def)
qed



theorem hook_post_solution_postfix:
  assumes pp:
      "part_post_solution (hook_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_enter:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>caller dst fs args p k.
        (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
        \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
  shows "hook_postfix g s0d s0g sigma"
proof -
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (hook_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using tree_covered_at_local
      [OF part_post_solution_imp_tree_covered_at[OF pp]]
    by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (hook_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using tree_covered_at_sides
      [OF part_post_solution_imp_tree_covered_at[OF pp]]
    by blast

  have entryD: "s0d \<le> dg_hook_D sigma (cfg_entry g)"
  proof -
    have "s0d \<le> hook_acc g bot0 s0d (cfg_entry g)"
      by (simp add: hook_acc_def)
    also have "... \<le> side_acc_dg
        (hook_acc g bot0 s0d (cfg_entry g))
        sigma (hook_trees g (cfg_entry g))"
      by (rule side_acc_dg_ge_acc)
    also have "... = locals
        (eq (hook_gen g bot0 s0d s0g)
          (cfg_entry g, ()) sigma)"
      by (simp add: eq_hook_gen)
    also have "... \<le> dg_hook_D sigma (cfg_entry g)"
      using eq_le[OF cover_entry]
      by (simp add: dg_hook_D_def less_eq_dg_state_def)
    finally show ?thesis .
  qed

  have entryG: "s0g \<le> dg_hook_G sigma"
  proof -
    have "DG bot s0g \<le>
       sides_of_rhs
         (hook_gen g bot0 s0d s0g (cfg_entry g, ()))
         sigma (Inr ())"
      unfolding hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: dg_hook_G_def less_eq_dg_state_def)
  qed

  have edge:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      edge_collect a (dg_hook_gamma gammaDG sigma u)
        \<subseteq> dg_hook_gamma gammaDG sigma v"
  proof -
    fix u a v
    assume intra: "(u, a, v) \<in> intra g"
    have d_le:
      "locals (traverse_rhs (edge_tree u a v) sigma)
        \<le> dg_hook_D sigma v"
      by (rule hook_tree_local_le
        [OF pp cover_edge[OF intra] hook_edge_tree_mem[OF finI intra]])
    have g_le:
      "globs (sides_of_rhs (edge_tree u a v) sigma (Inr ()))
        \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_edge[OF intra] hook_edge_tree_mem[OF finI intra]])
    have "gammaDG
        (locals (traverse_rhs (edge_tree u a v) sigma))
        (globs (sides_of_rhs (edge_tree u a v) sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma v"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "edge_collect a (dg_hook_gamma gammaDG sigma u)
        \<subseteq> dg_hook_gamma gammaDG sigma v"
      using edge_hook_sound by blast
  qed

  have enter:
    "\<And>caller dst fs args p k s.
      (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
      \<Longrightarrow> s \<in> dg_hook_gamma gammaDG sigma caller
      \<Longrightarrow> call_enter gs (CallEdge dst fs args) s \<in>
        dg_hook_gamma gammaDG sigma (FunctionEntry p)"
  proof -
    fix caller dst fs args p k s
    assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
      and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    have d_le:
      "locals (traverse_rhs
        (enter_tree caller (CallEdge dst fs args) (FunctionEntry p)) sigma)
        \<le> dg_hook_D sigma (FunctionEntry p)"
      by (rule hook_tree_local_le
        [OF pp cover_enter[OF call] hook_enter_tree_mem[OF finC call]])
    have g_le:
      "globs (sides_of_rhs
        (enter_tree caller (CallEdge dst fs args) (FunctionEntry p))
        sigma (Inr ())) \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_enter[OF call] hook_enter_tree_mem[OF finC call]])
    have "gammaDG
        (locals (traverse_rhs
          (enter_tree caller (CallEdge dst fs args) (FunctionEntry p)) sigma))
        (globs (sides_of_rhs
          (enter_tree caller (CallEdge dst fs args) (FunctionEntry p))
          sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma (FunctionEntry p)"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "call_enter gs (CallEdge dst fs args) s \<in>
        dg_hook_gamma gammaDG sigma (FunctionEntry p)"
      using enter_hook_sound[OF sin] by blast
  qed

  have combine:
    "\<And>caller dst fs args p k s t.
      (caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g
      \<Longrightarrow> s \<in> dg_hook_gamma gammaDG sigma caller
      \<Longrightarrow> t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)
      \<Longrightarrow> combine_collect gs dst s t \<in>
        dg_hook_gamma gammaDG sigma k"
  proof -
    fix caller dst fs args p k s t
    assume call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
      and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
      and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
    have d_le:
      "locals (traverse_rhs
        (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
        sigma) \<le> dg_hook_D sigma k"
      by (rule hook_tree_local_le
        [OF pp cover_combine[OF call] hook_combine_tree_mem[OF finC call]])
    have g_le:
      "globs (sides_of_rhs
        (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
        sigma (Inr ())) \<le> dg_hook_G sigma"
      by (rule hook_tree_side_le
        [OF pp cover_combine[OF call] hook_combine_tree_mem[OF finC call]])
    have "gammaDG
        (locals (traverse_rhs
          (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
          sigma))
        (globs (sides_of_rhs
          (combine_tree caller (CallEdge dst fs args) (FunctionResult p) k)
          sigma (Inr ())))
      \<subseteq> dg_hook_gamma gammaDG sigma k"
      unfolding dg_hook_gamma_def
      by (rule gammaDG_mono[OF d_le g_le])
    then show "combine_collect gs dst s t \<in>
        dg_hook_gamma gammaDG sigma k"
      using combine_hook_sound[OF sin tin] by blast
  qed

  show ?thesis
    unfolding hook_postfix_def
    using entryD entryG edge enter combine by blast
qed


lemma hook_postfix_entryD:
  assumes pf: "hook_postfix g s0d s0g sigma"
  shows "s0d \<le> dg_hook_D sigma (cfg_entry g)"
  using pf unfolding hook_postfix_def by blast

lemma hook_postfix_entryG:
  assumes pf: "hook_postfix g s0d s0g sigma"
  shows "s0g \<le> dg_hook_G sigma"
  using pf unfolding hook_postfix_def by blast

lemma hook_postfix_edge:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and edge: "(u, a, v) \<in> intra g"
  shows "edge_collect a (dg_hook_gamma gammaDG sigma u)
    \<subseteq> dg_hook_gamma gammaDG sigma v"
  using pf edge unfolding hook_postfix_def by blast

lemma hook_postfix_enter:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
  shows "call_enter gs (CallEdge dst fs args) s \<in>
    dg_hook_gamma gammaDG sigma (FunctionEntry p)"
  using pf call sin unfolding hook_postfix_def by blast

lemma hook_postfix_combine:
  assumes pf: "hook_postfix g s0d s0g sigma"
    and call:
      "(caller, CallEdge dst fs args, FunctionEntry p, k) \<in> calls g"
    and sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult p)"
  shows "combine_collect gs dst s t \<in>
    dg_hook_gamma gammaDG sigma k"
  using pf call sin tin unfolding hook_postfix_def by blast

subsection \<open>Generic post-solution assembly\<close>

text \<open>
  Turning a per-node dependency-closure fact (a @{const dep\<^sub>L} equation,
  obtained by unfolding @{const hook_gen} against the node's own CFG shape)
  and a per-node @{const tree_covered_at} fact into the single conjunct
  @{const part_post_solution} needs at that node -- and combining every
  node's conjunct with exit membership into @{const part_post_solution}
  itself -- is the same argument regardless of which CFG or domain
  instantiates this locale: only the node's own predecessor count (zero at
  entry, one at an ordinary edge, two at a join) and its concrete
  dependency/effect facts vary per call site. These lemmas fix that argument
  once, so an instance's own post-solution assembly reduces to a case split
  whose branches each cite one dependency fact, one membership fact, and one
  @{const tree_covered_at} fact.
\<close>

lemma hook_gen_dep_and_se_entry:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) = {}"
    and se: "tree_covered_at (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma
      (cfg_entry g, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) \<subseteq> vars \<and>
    tree_covered_at (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma (cfg_entry g, ())"
  using dep_eq se by auto

lemma hook_gen_dep_and_se_single:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u, ())}"
    and mem: "(u, ()) \<in> vars"
    and se: "tree_covered_at (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    tree_covered_at (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem se by auto

lemma hook_gen_dep_and_se_pair:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u1, ()), (u2, ())}"
    and mem1: "(u1, ()) \<in> vars"
    and mem2: "(u2, ()) \<in> vars"
    and se: "tree_covered_at (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    tree_covered_at (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem1 mem2 se by auto

text \<open>
  Assembling the whole node-indexed ball into @{const part_post_solution}
  itself needs only exit membership, via
  @{thm part_post_solution_iff_tree_covered_at}.
\<close>

lemma part_post_solution_of_ball:
  assumes exit_mem: "x \<in> vars"
    and ball: "\<forall>u \<in> vars. dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma u \<subseteq> vars \<and>
      tree_covered_at (hook_gen g bot0 s0d s0g u) sigma u"
  shows "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
  unfolding part_post_solution_iff_tree_covered_at using exit_mem ball by blast

end

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

