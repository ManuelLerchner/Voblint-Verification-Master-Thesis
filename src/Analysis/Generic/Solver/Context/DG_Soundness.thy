theory DG_Soundness
  imports DG_Framework Analysis_Sound
begin

section \<open>Native heterogeneous soundness\<close>

text \<open>
  Collecting soundness stated directly over an analysis's two domains \<open>D\<close> and
  \<open>G\<close>.  The analysis supplies \<open>gammaDG\<close>, the joint meaning of a per-point
  Answer and the shared Side fact.  Independent analyses use the intersection
  \<open>gamma_dg d g = [[d]] Int [[g]]\<close>; the homogeneous unit analysis uses
  \<open>gamma_unit d g = [[d Sup g]]\<close> because its transfer merges the slots.

  The locale \<open>sound_dg_spec\<close> assumes only monotonicity of \<open>gammaDG\<close> and
  semantic soundness of the analysis's edge and combine operations.  It derives
  the structural post-fixpoint from the heterogeneous generator, then applies
  the collecting-semantics post-fixpoint theorem directly.  No homogeneous
  equation system or representation transport appears in this proof.
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
    \<le> sides_of_rhs (side_rhs_fold_dg acc ts) sigma k"
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
      by (simp add: sides_of_rhs_seqcomp_at)
  next
    case False
    with Cons.prems have "t \<in> set ts" by simp
    then have "sides_of_rhs t sigma k
        \<le> sides_of_rhs
          (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts) sigma k"
      by (rule Cons.IH)
    also have "... \<le> sides_of_rhs t' sigma k \<squnion>
        sides_of_rhs
          (side_rhs_fold_dg
            (acc \<squnion> locals (traverse_rhs t' sigma)) ts) sigma k"
      by simp
    also have "... =
        sides_of_rhs (side_rhs_fold_dg acc (t' # ts)) sigma k"
      by (simp add: sides_of_rhs_seqcomp_at)
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

lemma cfg_collect_semantic_postfix:
  assumes entry: "S0 \<subseteq> B (cfg_entry g)"
    and edge:
      "\<And>u a v s. \<lbrakk>(u, a, v) \<in> edges g;
        s \<in> edge_collect a (B u)\<rbrakk> \<Longrightarrow> s \<in> B v"
    and combine:
      "\<And>cc ex v s t. \<lbrakk>(cc, ex, v) \<in> combines g;
        s \<in> B cc; t \<in> B ex\<rbrakk> \<Longrightarrow>
        combine_states s t \<in> B v"
  shows "cfg_collect g S0 v \<subseteq> B v"
proof (rule cfg_collect_post_fixpoint_sound)
  show "cfg_collect_F g S0 B \<le> B"
    unfolding cfg_collect_F_def collect_pp_def collect_combine_pp_def
      le_fun_def    using entry edge combine by auto
qed

subsection \<open>Analysis-parametric heterogeneous soundness\<close>

locale sound_dg_spec =
  fixes S :: "('d::sound_domain abs_state,
                'g::sound_domain abs_state) dg_spec"
    and gammaDG :: "'d abs_state \<Rightarrow> 'g abs_state \<Rightarrow> store set"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG d g) \<subseteq>
        (case dg_spec_step S a d g of
           (g', d') \<Rightarrow> gammaDG d' g')"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dc g; t \<in> gammaDG de g\<rbrakk> \<Longrightarrow>
        combine_states s t \<in>
          (case dgs_combine S dc de g of
             (g', d') \<Rightarrow> gammaDG d' g')"
begin

definition dg_cmb ::
  "unit \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
        ('d abs_state, 'g abs_state) dg_state) strategy_tree"
where
  "dg_cmb ctx cc ex =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree S cc ex))"

definition dg_gen ::
  "cfg \<Rightarrow> 'd abs_state \<Rightarrow> 'd abs_state \<Rightarrow> 'g abs_state
   \<Rightarrow> (pp \<times> unit, unit,
        ('d abs_state, 'g abs_state) dg_state) eqsT"
where
  "dg_gen g bot0 s0d s0g =
     side_cfg_T_eff_cmp_seed_dg (\<lambda>_. ()) dg_cmb
       (\<lambda>_. bot) g S bot0 s0d s0g"

definition dg_D ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('d abs_state, 'g abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> 'd abs_state"
where
  "dg_D sigma v = locals (sigma (Inl (v, ())))"

definition dg_G ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('d abs_state, 'g abs_state) dg_state)
   \<Rightarrow> 'g abs_state"
where
  "dg_G sigma = globs (sigma (Inr ()))"

definition dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('d abs_state, 'g abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_gamma sigma v = gammaDG (dg_D sigma v) (dg_G sigma)"

definition dg_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit,
      ('d abs_state, 'g abs_state) dg_state) strategy_tree list"
where
  "dg_trees g v =
     map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u)))
       (non_enter_predecessor_list g v)
     @ map (\<lambda>(cc, ex). dg_cmb () cc ex)
       (combine_predecessor_list g v)"

definition dg_acc ::
  "cfg \<Rightarrow> 'd abs_state \<Rightarrow> 'd abs_state \<Rightarrow> pp
   \<Rightarrow> 'd abs_state"
where
  "dg_acc g bot0 s0d v =
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_dg_gen:
  "eq (dg_gen g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (dg_acc g bot0 s0d v)
     sigma (dg_trees g v)) bot"
  unfolding dg_gen_def dg_trees_def dg_acc_def dg_cmb_def
  by (simp add: eq_side_cfg_T_eff_cmp_seed_dg)

lemma sides_fold_le_dg_gen:
  "sides_of_rhs
      (side_rhs_fold_dg (dg_acc g bot0 s0d v)
        (dg_trees g v)) sigma k
   \<le> sides_of_rhs (dg_gen g bot0 s0d s0g (v, ())) sigma k"
  unfolding dg_gen_def dg_trees_def dg_acc_def dg_cmb_def
    side_cfg_T_eff_cmp_seed_dg_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

definition dg_postfix ::
  "cfg \<Rightarrow> 'd abs_state \<Rightarrow> 'g abs_state
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        ('d abs_state, 'g abs_state) dg_state)
   \<Rightarrow> bool"
where
  "dg_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_D sigma (cfg_entry g) \<and>
     s0g \<le> dg_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_D sigma v) \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_G sigma) \<and>
     (\<forall>cc ex v. (cc, ex, v) \<in> combines g \<longrightarrow>
        snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
          (dg_G sigma)) \<le> dg_D sigma v) \<and>
     (\<forall>cc ex v. (cc, ex, v) \<in> combines g \<longrightarrow>
        fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
          (dg_G sigma)) \<le> dg_G sigma)"

lemma dg_edge_tree_local:
  "locals (traverse_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma)
   = snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (subst traverse_intra_cmp)
    (simp add: traverse_dg_edge_tree)

lemma dg_edge_tree_global:
  "globs (sides_of_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma (Inr ()))
   = fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (subst sides_map_gtree_unit_gen, subst sides_map_ltree_Inr)
    (simp add: sides_dg_edge_tree_Inr)

lemma dg_combine_tree_local:
  "locals (traverse_rhs (dg_cmb () cc ex) sigma)
   = snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
       (dg_G sigma))"
  unfolding dg_cmb_def dg_spec_combine_tree_def dg_D_def dg_G_def
  by (subst traverse_intra_cmp)
    (simp add: traverse_dg_combine_tree)

lemma dg_combine_tree_global:
  "globs (sides_of_rhs (dg_cmb () cc ex) sigma (Inr ()))
   = fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
       (dg_G sigma))"
  unfolding dg_cmb_def dg_spec_combine_tree_def dg_D_def dg_G_def
  by (subst sides_map_gtree_unit_gen, subst sides_map_ltree_Inr)
    (simp add: sides_dg_combine_tree_Inr)

theorem dg_post_solution_postfix:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow> (v, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter"
    and finC: "finite (combines g)"
  shows "dg_postfix g s0d s0g sigma"
proof -
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (dg_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using part_post_solution_imp_se_constraint_holds[OF pp]
    unfolding se_constraint_holds_def by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (dg_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using part_post_solution_imp_se_constraint_holds[OF pp]
    unfolding se_constraint_holds_def by blast

  have entryD: "s0d \<le> dg_D sigma (cfg_entry g)"
  proof -
    have "s0d \<le> dg_acc g bot0 s0d (cfg_entry g)"
      by (simp add: dg_acc_def)
    also have "... \<le> side_acc_dg
        (dg_acc g bot0 s0d (cfg_entry g)) sigma
        (dg_trees g (cfg_entry g))"
      by (rule side_acc_dg_ge_acc)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g)
          (cfg_entry g, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma (cfg_entry g)"
      using eq_le[OF cover_entry]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show ?thesis .
  qed

  have entryG: "s0g \<le> dg_G sigma"
  proof -
    have "DG bot s0g \<le>
       sides_of_rhs
         (dg_gen g bot0 s0d s0g (cfg_entry g, ()))
         sigma (Inr ())"
      unfolding dg_gen_def side_cfg_T_eff_cmp_seed_dg_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: dg_G_def less_eq_dg_state_def)
  qed

  have edge_tree_mem:
    "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
      map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> edges g"
    have "(u, a) \<in> set (non_enter_predecessor_list g v)"
      using edge no_enter[OF edge]
      by (simp add: non_enter_predecessor_list_def
          set_predecessor_list[OF finE] predecessors_def)
    then show "map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
      by (auto simp: dg_trees_def)
  qed

  have edgeD:
    "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
      snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma v"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> edges g"
    have "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d v)
          sigma (dg_trees g v)"
      using locals_traverse_le_side_acc_dg[OF edge_tree_mem[OF edge]]
      by (simp add: dg_edge_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (v, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma v"
      using eq_le[OF cover_edge[OF edge]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma v" .
  qed

  have edgeG:
    "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
      fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> edges g"
    have "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d v)
            (dg_trees g v)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF edge_tree_mem[OF edge], where k = "Inr ()"]
      by (simp add: dg_edge_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (v, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_edge[OF edge], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma" .
  qed

  have combine_tree_mem:
    "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow>
      dg_cmb () cc ex \<in> set (dg_trees g v)"
  proof -
    fix cc ex v
    assume comb: "(cc, ex, v) \<in> combines g"
    have "(cc, ex) \<in> set (combine_predecessor_list g v)"
      using comb
      by (simp add: set_combine_predecessor_list[OF finC]
          combine_predecessors_def)
    then show "dg_cmb () cc ex \<in> set (dg_trees g v)"
      by (auto simp: dg_trees_def)
  qed

  have combineD:
    "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow>
      snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_D sigma v"
  proof -
    fix cc ex v
    assume comb: "(cc, ex, v) \<in> combines g"
    have "snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
          (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d v)
          sigma (dg_trees g v)"
      using locals_traverse_le_side_acc_dg[OF combine_tree_mem[OF comb]]
      by (simp add: dg_combine_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (v, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma v"
      using eq_le[OF cover_combine[OF comb]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_D sigma v" .
  qed

  have combineG:
    "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow>
      fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_G sigma"
  proof -
    fix cc ex v
    assume comb: "(cc, ex, v) \<in> combines g"
    have "fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
          (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d v)
            (dg_trees g v)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF combine_tree_mem[OF comb], where k = "Inr ()"]
      by (simp add: dg_combine_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (v, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_combine[OF comb], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_G sigma" .
  qed

  show ?thesis
    unfolding dg_postfix_def
    using entryD entryG edgeD edgeG combineD combineG by blast
qed

theorem dg_postfix_collect_sound:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "cfg_collect g S0 v \<subseteq> dg_gamma sigma v"
proof (rule cfg_collect_semantic_postfix)
  show "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
  proof -
    have d_le: "s0d \<le> dg_D sigma (cfg_entry g)"
      and g_le: "s0g \<le> dg_G sigma"
      using pf unfolding dg_postfix_def by blast+
    have "gammaDG s0d s0g \<subseteq>
        gammaDG (dg_D sigma (cfg_entry g)) (dg_G sigma)"
      by (rule gammaDG_mono[OF d_le g_le])
    then show ?thesis
      using sound0 unfolding dg_gamma_def by blast
  qed
next
  fix u a w s
  assume edge: "(u, a, w) \<in> edges g"
    and sin: "s \<in> edge_collect a (dg_gamma sigma u)"
  obtain g' d' where step:
      "dg_spec_step S a (dg_D sigma u) (dg_G sigma) = (g', d')"
    by (cases "dg_spec_step S a (dg_D sigma u) (dg_G sigma)") blast
  have sin':
      "s \<in> edge_collect a (gammaDG (dg_D sigma u) (dg_G sigma))"
    using sin unfolding dg_gamma_def .
  have out0:
      "s \<in> (case dg_spec_step S a (dg_D sigma u) (dg_G sigma) of
          (g', d') \<Rightarrow> gammaDG d' g')"
    by (rule step_sound[THEN subsetD, OF sin'])
  have out: "s \<in> gammaDG d' g'"
    using out0 step by simp
  have stepD:
      "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma w"
    and stepG:
      "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma"
    using pf edge unfolding dg_postfix_def by blast+
  have d_le: "d' \<le> dg_D sigma w"
    and g_le: "g' \<le> dg_G sigma"
    using stepD stepG step by simp_all
  have "gammaDG d' g' \<subseteq>
      gammaDG (dg_D sigma w) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "s \<in> dg_gamma sigma w"
    using out unfolding dg_gamma_def by blast
next
  fix cc ex w s t
  assume comb: "(cc, ex, w) \<in> combines g"
    and sin: "s \<in> dg_gamma sigma cc"
    and tin: "t \<in> dg_gamma sigma ex"
  obtain g' d' where cmb:
      "dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma) = (g', d')"
    by (cases "dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
          (dg_G sigma)") blast
  have sin': "s \<in> gammaDG (dg_D sigma cc) (dg_G sigma)"
    using sin unfolding dg_gamma_def .
  have tin': "t \<in> gammaDG (dg_D sigma ex) (dg_G sigma)"
    using tin unfolding dg_gamma_def .
  have out0:
      "combine_states s t \<in>
        (case dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
            (dg_G sigma) of
          (g', d') \<Rightarrow> gammaDG d' g')"
    by (rule combine_sound[OF sin' tin'])
  have out: "combine_states s t \<in> gammaDG d' g'"
    using out0 cmb by simp
  have combineD:
      "snd (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_D sigma w"
    and combineG:
      "fst (dgs_combine S (dg_D sigma cc) (dg_D sigma ex)
        (dg_G sigma)) \<le> dg_G sigma"
    using pf comb unfolding dg_postfix_def by blast+
  have d_le: "d' \<le> dg_D sigma w"
    and g_le: "g' \<le> dg_G sigma"
    using combineD combineG cmb by simp_all
  have "gammaDG d' g' \<subseteq>
      gammaDG (dg_D sigma w) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "combine_states s t \<in> dg_gamma sigma w"
    using out unfolding dg_gamma_def by blast
qed

corollary dg_post_solution_collect_sound:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex w. (cc, ex, w) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter:
      "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "cfg_collect g S0 v \<subseteq> dg_gamma sigma v"
proof -
  have pf: "dg_postfix g s0d s0g sigma"
    by (rule dg_post_solution_postfix
          [OF pp cover_entry cover_edge cover_combine finE no_enter finC])
  show ?thesis
    by (rule dg_postfix_collect_sound
          [OF pf finE finC sound0])
qed

end

subsection \<open>The canonical independent-transfer spec\<close>

text \<open>
  The record an independent-transfer analysis denotes: every edge action
  advances each slot by its own transfer, the combine is structural in each
  slot.  Any two sound transfers yield a \<open>sound_dg_spec\<close> instance; at
  \<open>tfD = tfG\<close> this is the homogeneous single-domain analysis as the diagonal.
\<close>

definition indep_dg_spec ::
  "'d::sound_domain domain_transfer
   \<Rightarrow> 'g::sound_domain domain_transfer
   \<Rightarrow> ('d abs_state, 'g abs_state) dg_spec"
where
  "indep_dg_spec tfD tfG = \<lparr>
    dgs_nop        = (\<lambda>d g. (apply_tf tfG EA_Nop g, apply_tf tfD EA_Nop d)),
    dgs_assign     = (\<lambda>x e d g. (apply_tf tfG (EA_Assign x e) g,
                                 apply_tf tfD (EA_Assign x e) d)),
    dgs_assume     = (\<lambda>b d g. (apply_tf tfG (EA_Assume b) g,
                               apply_tf tfD (EA_Assume b) d)),
    dgs_assume_not = (\<lambda>b d g. (apply_tf tfG (EA_AssumeNot b) g,
                               apply_tf tfD (EA_AssumeNot b) d)),
    dgs_enter      = (\<lambda>d g. (apply_tf tfG EA_Enter g, apply_tf tfD EA_Enter d)),
    dgs_combine    = (\<lambda>dc de g. (combine_abs g g, combine_abs dc de))
  \<rparr>"

lemma dg_spec_step_indep [simp]:
  "dg_spec_step (indep_dg_spec tfD tfG) a d g
   = (apply_tf tfG a g, apply_tf tfD a d)"
  unfolding indep_dg_spec_def by (cases a) simp_all

lemma dgs_combine_indep [simp]:
  "dgs_combine (indep_dg_spec tfD tfG) dc de g
   = (combine_abs g g, combine_abs dc de)"
  unfolding indep_dg_spec_def by simp

lemma sound_dg_spec_indep:
  assumes soundD: "sound_transfer tfD"
    and soundG: "sound_transfer tfG"
  shows "sound_dg_spec (indep_dg_spec tfD tfG) gamma_dg"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_dg_mono)
  subgoal for a d g
  proof -
    have d_input:
        "edge_collect a (gamma_dg d g) \<subseteq> edge_collect a \<lbrakk>d\<rbrakk>"
      by (rule edge_collect_mono[OF gamma_dg_le_D])
    have d_transfer:
        "edge_collect a \<lbrakk>d\<rbrakk> \<subseteq> \<lbrakk>apply_tf tfD a d\<rbrakk>"
      by (rule sound_transfer.edge_collect_apply_tf_sound[OF soundD])
    have d_sound:
        "edge_collect a (gamma_dg d g) \<subseteq> \<lbrakk>apply_tf tfD a d\<rbrakk>"
      using d_input d_transfer by blast
    have g_input:
        "edge_collect a (gamma_dg d g) \<subseteq> edge_collect a \<lbrakk>g\<rbrakk>"
      by (rule edge_collect_mono[OF gamma_dg_le_G])
    have g_transfer:
        "edge_collect a \<lbrakk>g\<rbrakk> \<subseteq> \<lbrakk>apply_tf tfG a g\<rbrakk>"
      by (rule sound_transfer.edge_collect_apply_tf_sound[OF soundG])
    show ?thesis
      using d_sound g_input g_transfer
      unfolding gamma_dg_def by auto
  qed
  subgoal for s dc g t de
  proof -
    assume sin: "s \<in> gamma_dg dc g"
      and tin: "t \<in> gamma_dg de g"
    have d_sound:
        "combine_states s t \<in> \<lbrakk>combine_abs dc de\<rbrakk>"
      using combine_states_sound sin tin
      unfolding gamma_dg_def by blast
    have g_sound:
        "combine_states s t \<in> \<lbrakk>combine_abs g g\<rbrakk>"
      using combine_states_sound sin tin
      unfolding gamma_dg_def by blast
    show ?thesis
      using d_sound g_sound unfolding gamma_dg_def by simp
  qed
  done
subsection \<open>The homogeneous analysis as a diagonal interpretation\<close>

definition gamma_unit ::
  "'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_unit d g = \<lbrakk>d \<squnion> g\<rbrakk>"

lemma gamma_unit_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_unit d g \<subseteq> gamma_unit d' g'"
  unfolding gamma_unit_def
  by (rule gamma_state_mono) (rule sup_mono[OF assms])

lemma combine_abs_restrict:
  "combine_abs d e = restrict_local d \<squnion> restrict_global e"
  unfolding combine_abs_def restrict_local_def restrict_global_def sup_fun_def
  by (rule ext) simp

lemma sound_dg_spec_unit:
  assumes sound: "sound_transfer tf"
  shows "sound_dg_spec (unit_dg_spec tf) gamma_unit"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_unit_mono)
  subgoal for a d g
    unfolding gamma_unit_def dg_spec_step_unit unit_step_def
    using sound_transfer.edge_collect_apply_tf_sound[OF sound,
      where a = a]
    by (simp add: Let_def restrict_local_global_join)
  subgoal for s dc g t de
  proof -
    assume sin: "s \<in> gamma_unit dc g"
      and tin: "t \<in> gamma_unit de g"
    have "combine_states s t \<in>
        \<lbrakk>combine_abs (dc \<squnion> g) (de \<squnion> g)\<rbrakk>"
      using combine_states_sound sin tin
      unfolding gamma_unit_def by blast
    then show ?thesis
      unfolding unit_dg_spec_def unit_combine_step_def gamma_unit_def
      by (simp add: Let_def restrict_local_global_join
          combine_abs_restrict)
  qed
  done

context sound_transfer
begin

sublocale dg: sound_dg_spec "unit_dg_spec tf" gamma_unit
  by (rule sound_dg_spec_unit[OF sound_transfer_axioms])

end

end
