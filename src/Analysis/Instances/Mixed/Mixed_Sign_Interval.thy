theory Mixed_Sign_Interval
  imports
    "Voblint_Analysis.DG_Framework"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Ivl_Exec"
begin

section \<open>A flow-sensitive Sign analysis with a flow-insensitive Interval invariant\<close>

text \<open>
  The answer domain D is a flow-sensitive Sign store: every CFG point has its
  own Sign answer.  The side domain G is one flow-insensitive Interval invariant
  shared by every equation.  The name @{const globs} identifies the solver's
  side slot; it does not restrict G to IMP2 variables satisfying
  @{const is_global}.  The analysis chooses which facts G contains.

  Every edge advances the two abstractions independently.  Its Sign result
  becomes the successor's answer, while its Interval result is published to
  the shared side unknown.  Solver joins therefore close G under every
  reachable transfer.
\<close>

definition mixed_si_step ::
  "edge_action \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> ivl abs_state \<times> sign abs_state"
where
  "mixed_si_step a d g = (apply_tf ivl_tf a g, apply_tf sign_tf a d)"

definition mixed_si_combine ::
  "sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> ivl abs_state \<times> sign abs_state"
where
  "mixed_si_combine dc de g = (combine_abs g g, combine_abs dc de)"

definition mixed_si_spec :: "(sign abs_state, ivl abs_state) dg_spec" where
  "mixed_si_spec = \<lparr>
    dgs_nop        = mixed_si_step EA_Nop,
    dgs_assign     = (\<lambda>x e. mixed_si_step (EA_Assign x e)),
    dgs_assume     = (\<lambda>b. mixed_si_step (EA_Assume b)),
    dgs_assume_not = (\<lambda>b. mixed_si_step (EA_AssumeNot b)),
    dgs_enter      = mixed_si_step EA_Enter,
    dgs_combine    = mixed_si_combine
  \<rparr>"

lemma mixed_si_spec_step [simp]:
  "dg_spec_step mixed_si_spec a d g = mixed_si_step a d g"
  unfolding mixed_si_spec_def by (cases a) simp_all

definition mixed_si_cmb ::
  "unit \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
        (sign abs_state, ivl abs_state) dg_state) strategy_tree"
where
  "mixed_si_cmb ctx cc ex =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree mixed_si_spec cc ex))"

definition mixed_si_generator ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit, unit,
        (sign abs_state, ivl abs_state) dg_state) eqsT"
where
  "mixed_si_generator g bot0 s0d s0g =
     side_cfg_T_eff_cmp_seed_dg (\<lambda>_. ()) mixed_si_cmb
       (\<lambda>_. bot) g mixed_si_spec bot0 s0d s0g"

definition mixed_si_D ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> sign abs_state"
where
  "mixed_si_D sigma v = locals (sigma (Inl (v, ())))"

definition mixed_si_G ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> ivl abs_state"
where
  "mixed_si_G sigma = globs (sigma (Inr ()))"

definition mixed_si_gamma ::
  "(pp \<times> unit + unit \<Rightarrow>
      (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "mixed_si_gamma sigma v =
     \<lbrakk>mixed_si_D sigma v\<rbrakk> \<inter> \<lbrakk>mixed_si_G sigma\<rbrakk>"

text \<open>
  @{const mixed_si_D} reads the point-indexed @{term "Inl (v, ())"} answer.
  @{const mixed_si_G} always reads the one @{term "Inr ()"} side unknown.
  Consequently the concretisation at a point intersects its flow-sensitive
  Sign fact with the same flow-insensitive Interval invariant used at every
  point.
\<close>

definition mixed_si_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit,
      (sign abs_state, ivl abs_state) dg_state) strategy_tree list"
where
  "mixed_si_trees g v =
     map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec mixed_si_spec a u)))
       (non_enter_predecessor_list g v)
     @ map (\<lambda>(cc, ex). mixed_si_cmb () cc ex)
       (combine_predecessor_list g v)"

definition mixed_si_acc ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> pp
   \<Rightarrow> sign abs_state"
where
  "mixed_si_acc g bot0 s0d v =
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_mixed_si_generator:
  "eq (mixed_si_generator g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (mixed_si_acc g bot0 s0d v)
     sigma (mixed_si_trees g v)) bot"
  unfolding mixed_si_generator_def mixed_si_trees_def mixed_si_acc_def
    mixed_si_cmb_def
  by (simp add: eq_side_cfg_T_eff_cmp_seed_dg)

lemma sides_fold_le_mixed_si_generator:
  "sides_of_rhs
      (side_rhs_fold_dg (mixed_si_acc g bot0 s0d v)
        (mixed_si_trees g v)) sigma k
   \<le> sides_of_rhs (mixed_si_generator g bot0 s0d s0g (v, ())) sigma k"
  unfolding mixed_si_generator_def mixed_si_trees_def mixed_si_acc_def
    mixed_si_cmb_def side_cfg_T_eff_cmp_seed_dg_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

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

definition mixed_si_postfix ::
  "cfg \<Rightarrow> sign abs_state \<Rightarrow> ivl abs_state
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        (sign abs_state, ivl abs_state) dg_state)
   \<Rightarrow> bool"
where
  "mixed_si_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> mixed_si_D sigma (cfg_entry g) \<and>
     s0g \<le> mixed_si_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        apply_tf sign_tf a (mixed_si_D sigma u) \<le> mixed_si_D sigma v) \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        apply_tf ivl_tf a (mixed_si_G sigma) \<le> mixed_si_G sigma) \<and>
     (\<forall>cc ex v. (cc, ex, v) \<in> combines g \<longrightarrow>
        combine_abs (mixed_si_D sigma cc) (mixed_si_D sigma ex)
          \<le> mixed_si_D sigma v) \<and>
     (\<forall>cc ex v. (cc, ex, v) \<in> combines g \<longrightarrow>
        combine_abs (mixed_si_G sigma) (mixed_si_G sigma)
          \<le> mixed_si_G sigma)"

lemma mixed_si_edge_tree_local:
  "locals (traverse_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec mixed_si_spec a u))) sigma)
   = apply_tf sign_tf a (mixed_si_D sigma u)"
  unfolding apply_dg_spec_def mixed_si_D_def
  by (subst traverse_intra_cmp)
    (simp add: traverse_dg_edge_tree mixed_si_step_def)

lemma mixed_si_edge_tree_global:
  "globs (sides_of_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec mixed_si_spec a u))) sigma (Inr ()))
   = apply_tf ivl_tf a (mixed_si_G sigma)"
  unfolding apply_dg_spec_def mixed_si_G_def
  by (subst sides_map_gtree_unit_gen, subst sides_map_ltree_Inr)
    (simp add: sides_dg_edge_tree_Inr mixed_si_step_def)

lemma mixed_si_combine_tree_local:
  "locals (traverse_rhs (mixed_si_cmb () cc ex) sigma)
   = combine_abs (mixed_si_D sigma cc) (mixed_si_D sigma ex)"
  unfolding mixed_si_cmb_def dg_spec_combine_tree_def mixed_si_D_def
    mixed_si_spec_def
  by (subst traverse_intra_cmp)
    (simp add: traverse_dg_combine_tree mixed_si_combine_def)

lemma mixed_si_combine_tree_global:
  "globs (sides_of_rhs (mixed_si_cmb () cc ex) sigma (Inr ()))
   = combine_abs (mixed_si_G sigma) (mixed_si_G sigma)"
  unfolding mixed_si_cmb_def dg_spec_combine_tree_def mixed_si_G_def
    mixed_si_spec_def
  by (subst sides_map_gtree_unit_gen, subst sides_map_ltree_Inr)
    (simp add: sides_dg_combine_tree_Inr mixed_si_combine_def)

theorem mixed_si_post_solution_postfix:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow> (v, ()) \<in> vars"
    and finE: "finite (edges g)"
    and no_enter: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter"
    and finC: "finite (combines g)"
  shows "mixed_si_postfix g s0d s0g sigma"
proof -
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (mixed_si_generator g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using part_post_solution_imp_se_constraint_holds[OF pp]
    unfolding se_constraint_holds_def by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (mixed_si_generator g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using part_post_solution_imp_se_constraint_holds[OF pp]
    unfolding se_constraint_holds_def by blast

  have entryD: "s0d \<le> mixed_si_D sigma (cfg_entry g)"
  proof -
    have "s0d \<le> mixed_si_acc g bot0 s0d (cfg_entry g)"
      by (simp add: mixed_si_acc_def)
    also have "... \<le> side_acc_dg
        (mixed_si_acc g bot0 s0d (cfg_entry g)) sigma
        (mixed_si_trees g (cfg_entry g))"
      by (rule side_acc_dg_ge_acc)
    also have "... = locals
        (eq (mixed_si_generator g bot0 s0d s0g)
          (cfg_entry g, ()) sigma)"
      by (simp add: eq_mixed_si_generator)
    also have "... \<le> mixed_si_D sigma (cfg_entry g)"
      using eq_le[OF cover_entry]
      by (simp add: mixed_si_D_def less_eq_dg_state_def)
    finally show ?thesis .
  qed

  have entryG: "s0g \<le> mixed_si_G sigma"
  proof -
    have seed:
      "DG bot s0g \<le>
       sides_of_rhs
         (mixed_si_generator g bot0 s0d s0g (cfg_entry g, ()))
         sigma (Inr ())"
      unfolding mixed_si_generator_def side_cfg_T_eff_cmp_seed_dg_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: mixed_si_G_def less_eq_dg_state_def)
  qed

  have edgeD:
    "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
      apply_tf sign_tf a (mixed_si_D sigma u)
        \<le> mixed_si_D sigma v"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> edges g"
    have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
      using edge no_enter[OF edge]
      by (simp add: non_enter_predecessor_list_def
          set_predecessor_list[OF finE] predecessors_def)
    have tree_mem:
      "map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec mixed_si_spec a u))
       \<in> set (mixed_si_trees g v)"
      using mem by (auto simp: mixed_si_trees_def)
    have "apply_tf sign_tf a (mixed_si_D sigma u)
        \<le> side_acc_dg (mixed_si_acc g bot0 s0d v)
          sigma (mixed_si_trees g v)"
      using locals_traverse_le_side_acc_dg[OF tree_mem]
      by (simp add: mixed_si_edge_tree_local)
    also have "... = locals
        (eq (mixed_si_generator g bot0 s0d s0g) (v, ()) sigma)"
      by (simp add: eq_mixed_si_generator)
    also have "... \<le> mixed_si_D sigma v"
      using eq_le[OF cover_edge[OF edge]]
      by (simp add: mixed_si_D_def less_eq_dg_state_def)
    finally show "apply_tf sign_tf a (mixed_si_D sigma u)
        \<le> mixed_si_D sigma v" .
  qed

  have edgeG:
    "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
      apply_tf ivl_tf a (mixed_si_G sigma) \<le> mixed_si_G sigma"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> edges g"
    have mem: "(u, a) \<in> set (non_enter_predecessor_list g v)"
      using edge no_enter[OF edge]
      by (simp add: non_enter_predecessor_list_def
          set_predecessor_list[OF finE] predecessors_def)
    have tree_mem:
      "map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec mixed_si_spec a u))
       \<in> set (mixed_si_trees g v)"
      using mem by (auto simp: mixed_si_trees_def)
    have "apply_tf ivl_tf a (mixed_si_G sigma)
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (mixed_si_acc g bot0 s0d v)
            (mixed_si_trees g v)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg[OF tree_mem, where k = "Inr ()"]
      by (simp add: mixed_si_edge_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (mixed_si_generator g bot0 s0d s0g (v, ())) sigma (Inr ()))"
      using sides_fold_le_mixed_si_generator[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> mixed_si_G sigma"
      using sides_le[OF cover_edge[OF edge], THEN le_funD, of "Inr ()"]
      by (simp add: mixed_si_G_def less_eq_dg_state_def)
    finally show "apply_tf ivl_tf a (mixed_si_G sigma)
        \<le> mixed_si_G sigma" .
  qed

  have combineD:
    "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow>
      combine_abs (mixed_si_D sigma cc) (mixed_si_D sigma ex)
        \<le> mixed_si_D sigma v"
  proof -
    fix cc ex v
    assume comb: "(cc, ex, v) \<in> combines g"
    have mem: "(cc, ex) \<in> set (combine_predecessor_list g v)"
      using comb
      by (simp add: set_combine_predecessor_list[OF finC]
          combine_predecessors_def)
    have tree_mem: "mixed_si_cmb () cc ex \<in> set (mixed_si_trees g v)"
      using mem by (auto simp: mixed_si_trees_def)
    have "combine_abs (mixed_si_D sigma cc) (mixed_si_D sigma ex)
        \<le> side_acc_dg (mixed_si_acc g bot0 s0d v)
          sigma (mixed_si_trees g v)"
      using locals_traverse_le_side_acc_dg[OF tree_mem]
      by (simp add: mixed_si_combine_tree_local)
    also have "... = locals
        (eq (mixed_si_generator g bot0 s0d s0g) (v, ()) sigma)"
      by (simp add: eq_mixed_si_generator)
    also have "... \<le> mixed_si_D sigma v"
      using eq_le[OF cover_combine[OF comb]]
      by (simp add: mixed_si_D_def less_eq_dg_state_def)
    finally show "combine_abs (mixed_si_D sigma cc) (mixed_si_D sigma ex)
        \<le> mixed_si_D sigma v" .
  qed

  have combineG:
    "\<And>cc ex v. (cc, ex, v) \<in> combines g \<Longrightarrow>
      combine_abs (mixed_si_G sigma) (mixed_si_G sigma)
        \<le> mixed_si_G sigma"
  proof -
    fix cc ex v
    assume comb: "(cc, ex, v) \<in> combines g"
    have mem: "(cc, ex) \<in> set (combine_predecessor_list g v)"
      using comb
      by (simp add: set_combine_predecessor_list[OF finC]
          combine_predecessors_def)
    have tree_mem: "mixed_si_cmb () cc ex \<in> set (mixed_si_trees g v)"
      using mem by (auto simp: mixed_si_trees_def)
    have "combine_abs (mixed_si_G sigma) (mixed_si_G sigma)
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (mixed_si_acc g bot0 s0d v)
            (mixed_si_trees g v)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg[OF tree_mem, where k = "Inr ()"]
      by (simp add: mixed_si_combine_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (mixed_si_generator g bot0 s0d s0g (v, ())) sigma (Inr ()))"
      using sides_fold_le_mixed_si_generator[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> mixed_si_G sigma"
      using sides_le[OF cover_combine[OF comb], THEN le_funD, of "Inr ()"]
      by (simp add: mixed_si_G_def less_eq_dg_state_def)
    finally show "combine_abs (mixed_si_G sigma) (mixed_si_G sigma)
        \<le> mixed_si_G sigma" .
  qed

  show ?thesis
    unfolding mixed_si_postfix_def
    using entryD entryG edgeD edgeG combineD combineG by blast
qed

theorem mixed_si_postfix_collect_sound:
  assumes pf: "mixed_si_postfix g s0d s0g sigma"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and soundD: "S \<le> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<le> \<lbrakk>s0g\<rbrakk>"
  shows "cfg_collect g S v \<le> mixed_si_gamma sigma v"
proof -
  have d_sound: "cfg_collect g S v \<le> \<lbrakk>mixed_si_D sigma v\<rbrakk>"
    by (rule sound_transfer.post_fixpoint_sound_at
          [OF sign_is_sound_transfer finE finC soundD])
      (use pf in \<open>auto simp: mixed_si_postfix_def\<close>)
  have entryG: "s0g \<le> mixed_si_G sigma"
    using pf unfolding mixed_si_postfix_def by blast
  have stepG:
    "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow>
       apply_tf ivl_tf a (mixed_si_G sigma) \<le> mixed_si_G sigma"
    using pf unfolding mixed_si_postfix_def by blast
  have combineG:
    "\<And>cc ex w. (cc, ex, w) \<in> combines g \<Longrightarrow>
       combine_abs (mixed_si_G sigma) (mixed_si_G sigma)
         \<le> mixed_si_G sigma"
    using pf unfolding mixed_si_postfix_def by blast
  have g_sound: "cfg_collect g S v \<le> \<lbrakk>mixed_si_G sigma\<rbrakk>"
    by (rule sound_transfer.post_fixpoint_sound_at
          [where tf = ivl_tf and env = "\<lambda>_. mixed_si_G sigma",
           OF ivl_is_sound_transfer finE finC soundG stepG combineG entryG])
  show ?thesis
    using d_sound g_sound unfolding mixed_si_gamma_def by blast
qed

corollary mixed_si_post_solution_collect_sound:
  assumes pp:
      "part_post_solution (mixed_si_generator g bot0 s0d s0g)
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
    and soundD: "S \<subseteq> \<lbrakk>s0d\<rbrakk>"
    and soundG: "S \<subseteq> \<lbrakk>s0g\<rbrakk>"
  shows "cfg_collect g S v \<subseteq> mixed_si_gamma sigma v"
proof -
  have pf: "mixed_si_postfix g s0d s0g sigma"
    by (rule mixed_si_post_solution_postfix
          [OF pp cover_entry cover_edge cover_combine finE no_enter finC])
  show ?thesis
    by (rule mixed_si_postfix_collect_sound
          [OF pf finE finC soundD soundG])
qed

section \<open>Executable instance\<close>

instance st :: (bounded_warrowing) bounded_warrowing ..

instantiation dg_state :: (widening, widening) widening


begin

definition widen_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "widen_dg_state a b = DG (widen (locals a) (locals b)) (widen (globs a) (globs b))"

instance
  by standard
    (auto simp: widen_dg_state_def less_eq_dg_state_def
      intro: widen_ge1 widen_ge2)

end

instantiation dg_state :: (narrowing, narrowing) narrowing
begin

definition narrow_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "narrow_dg_state a b = DG (narrow (locals a) (locals b)) (narrow (globs a) (globs b))"

instance
  by standard
    (auto simp: narrow_dg_state_def less_eq_dg_state_def
      intro: narrow_ge narrow_le)

end

instance dg_state ::
  (bounded_warrowing, bounded_warrowing) bounded_warrowing ..

definition mixed_si_step_st ::
  "edge_action \<Rightarrow> sign st \<Rightarrow> ivl st \<Rightarrow> ivl st \<times> sign st"
where
  "mixed_si_step_st a d g = (ivl_tf_st a g, sign_tf_st a d)"

definition mixed_si_combine_st ::
  "sign st \<Rightarrow> sign st \<Rightarrow> ivl st \<Rightarrow> ivl st \<times> sign st"
where
  "mixed_si_combine_st dc de g =
     (combine_abs_st g g, combine_abs_st dc de)"

definition mixed_si_spec_st :: "(sign st, ivl st) dg_spec" where
  "mixed_si_spec_st = \<lparr>
    dgs_nop        = mixed_si_step_st EA_Nop,
    dgs_assign     = (\<lambda>x e. mixed_si_step_st (EA_Assign x e)),
    dgs_assume     = (\<lambda>b. mixed_si_step_st (EA_Assume b)),
    dgs_assume_not = (\<lambda>b. mixed_si_step_st (EA_AssumeNot b)),
    dgs_enter      = mixed_si_step_st EA_Enter,
    dgs_combine    = mixed_si_combine_st
  \<rparr>"

lemma mixed_si_spec_step_st [simp]:
  "dg_spec_step mixed_si_spec_st a d g = mixed_si_step_st a d g"
  unfolding mixed_si_spec_st_def by (cases a) simp_all

definition mixed_si_cmb_st ::
  "unit \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, (sign st, ivl st) dg_state) strategy_tree"
where
  "mixed_si_cmb_st ctx cc ex =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree mixed_si_spec_st cc ex))"

definition mixed_si_generator_st ::
  "cfg \<Rightarrow> sign st \<Rightarrow> sign st \<Rightarrow> ivl st
   \<Rightarrow> (pp \<times> unit, unit, (sign st, ivl st) dg_state) eqsT"
where
  "mixed_si_generator_st g bot0 s0d s0g =
     side_cfg_T_eff_cmp_seed_dg (\<lambda>_. ()) mixed_si_cmb_st
       (\<lambda>_. bot) g mixed_si_spec_st bot0 s0d s0g"

text \<open>
  The witness uses the local IMP2 variable @{text "''x''"}.  The Sign answer
  records its value at each control-flow point.  The Interval side invariant
  records every value of the same variable seen anywhere in the run.  Starting
  from zero, the program visits negative one and then two.  Thus the exit answer
  is positive, while the shared invariant spans @{text "[-1, 2]"}.
\<close>

definition mixed_si_example_cfg :: cfg where
  "mixed_si_example_cfg =
     mk_cfg 0 2
       {(0, EA_Assign ''x'' (IMP2_Syntax.N (-1)), 1),
        (1, EA_Assign ''x'' (IMP2_Syntax.N 2), 2)} {}"

definition mixed_si_example_sign_seed :: "sign st" where
  "mixed_si_example_sign_seed = update_st top_sign_st ''x'' SZero"

definition mixed_si_example_ivl_seed :: "ivl st" where
  "mixed_si_example_ivl_seed =
     update_st top_ivl_st ''x'' (Ivl (Fin 0) (Fin 0))"

definition mixed_si_example_eqs ::
  "(pp \<times> unit, unit, (sign st, ivl st) dg_state) eqsT"
where
  "mixed_si_example_eqs =
     mixed_si_generator_st mixed_si_example_cfg bot
       mixed_si_example_sign_seed mixed_si_example_ivl_seed"

definition mixed_si_example_solution ::
  "pp \<times> unit + unit \<Rightarrow> (sign st, ivl st) dg_state"
where
  "mixed_si_example_solution =
     snd (TD_side_always_join_Interp_solve mixed_si_example_eqs (2, ()))"

lemma mixed_si_example_terminates:
  "TD_side_always_join_Interp_solve_c mixed_si_example_eqs (2, ()) \<noteq> None"
  by eval

lemma mixed_si_example_x_is_local:
  "\<not> is_global ''x''"
  by (simp add: is_global_def)

lemma mixed_si_example_expected:
  "lookup_st (locals (mixed_si_example_solution (Inl (1, ())))) ''x'' = SNeg
   \<and> lookup_st (locals (mixed_si_example_solution (Inl (2, ())))) ''x'' = SPos
   \<and> lookup_st (globs (mixed_si_example_solution (Inr ()))) ''x''
       = Ivl (Fin (-1)) (Fin 2)"
  by eval

value "lookup_st (locals (mixed_si_example_solution (Inl (1, ())))) ''x''"
value "lookup_st (locals (mixed_si_example_solution (Inl (2, ())))) ''x''"
value "lookup_st (globs (mixed_si_example_solution (Inr ()))) ''x''"

end



