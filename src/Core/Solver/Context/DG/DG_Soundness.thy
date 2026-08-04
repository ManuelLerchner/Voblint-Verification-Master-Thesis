theory DG_Soundness
  imports DG_Framework Constraint_System_Sound
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

(* Pointwise duals of gamma_dg_le_D / gamma_dg_le_G, for call sites that need
   the per-element fact rather than the set inclusion. *)
lemma gamma_dgD1 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>"
  using gamma_dg_le_D by blast

lemma gamma_dgD2 [dest]: "s \<in> gamma_dg d g \<Longrightarrow> s \<in> \<lbrakk>g\<rbrakk>"
  using gamma_dg_le_G by blast



subsection \<open>Analysis-parametric heterogeneous soundness\<close>

locale sound_dg_spec =
  fixes S :: "('D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow>
        gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG d g) \<subseteq>
        (case dg_spec_step S a d g of
           (g', d') \<Rightarrow> gammaDG d' g')"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dc g; t \<in> gammaDG de g\<rbrakk> \<Longrightarrow>
        combine_collect gs dst s t \<in>
          (case dgs_combine S dst dc de g of
             (g', d') \<Rightarrow> gammaDG d' g')"
    and enter_sound:
      "s \<in> gammaDG dc g \<Longrightarrow>
        call_enter gs (CallEdge dst pars args) s \<in>
          (case dgs_enter S pars args dc g of
             (g', d') \<Rightarrow> gammaDG d' g')"
begin

text \<open>Fst/snd-shaped restatements of the three per-step soundness assumptions,
  so a caller comparing against dg_D/dg_G (which are always applied via fst/snd)
  does not need to obtain the case-split pair and its equation just to unpack a
  case-of-tuple result each time.\<close>
lemma step_sound_fs:
  "edge_collect a (gammaDG d g)
     \<subseteq> gammaDG (snd (dg_spec_step S a d g)) (fst (dg_spec_step S a d g))"
  using step_sound by (simp add: case_prod_beta)

lemma enter_sound_fs:
  assumes "s \<in> gammaDG dc g"
  shows "call_enter gs (CallEdge dst pars args) s \<in>
           gammaDG (snd (dgs_enter S pars args dc g)) (fst (dgs_enter S pars args dc g))"
  using enter_sound[OF assms] by (simp add: case_prod_beta)

lemma combine_sound_fs:
  assumes "s \<in> gammaDG dc g" and "t \<in> gammaDG de g"
  shows "combine_collect gs dst s t \<in>
           gammaDG (snd (dgs_combine S dst dc de g)) (fst (dgs_combine S dst dc de g))"
  using combine_sound[OF assms] by (simp add: case_prod_beta)

definition dg_cmb ::
  "(pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
        ('D, 'G) dg_state) strategy_tree"
where
  "dg_cmb route ctx ca cc ex =
     (case ca of CallEdge dst _ _ \<Rightarrow>
       map_gtree (\<lambda>_. ())
         (map_ltree (\<lambda>w. (w, ctx))
           (dg_spec_combine_tree S dst cc ex)))"

definition dg_enter ::
  "unit \<Rightarrow> vname list \<Rightarrow> aexp list \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_enter ctx fs as cl =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_edge_tree (dgs_enter S fs as) cl))"

definition dg_extra ::
  "cfg \<Rightarrow> (pp \<Rightarrow> unit \<Rightarrow> 'D \<Rightarrow> call_action \<Rightarrow> unit) \<Rightarrow> unit \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree list"
where
  "dg_extra g route ctx v =
     map (\<lambda>(cl, ca). case ca of CallEdge dst fs as \<Rightarrow> dg_enter ctx fs as cl)
         (entry_call_list g v)"

definition dg_gen ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit, unit,
        ('D, 'G) dg_state) eqsT"
where
  "dg_gen g bot0 s0d s0g =
     side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\<lambda>_. ())
       (\<lambda>_ _ _ _. ()) dg_cmb (dg_extra g) g S bot0 s0d s0g"

definition dg_D ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> 'D"
where
  "dg_D sigma v = locals (sigma (Inl (v, ())))"

definition dg_G ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> 'G"
where
  "dg_G sigma = globs (sigma (Inr ()))"

definition dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow>
      ('D, 'G) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_gamma sigma v = gammaDG (dg_D sigma v) (dg_G sigma)"

(* Dest/intro pair for the dg_gamma/gammaDG bridge, cited at the postfix
   soundness call sites below instead of re-unfolding dg_gamma_def at each. *)
lemma dg_gammaD [dest]: "s \<in> dg_gamma sigma v \<Longrightarrow> s \<in> gammaDG (dg_D sigma v) (dg_G sigma)"
  unfolding dg_gamma_def by simp

lemma dg_gammaI [intro]: "s \<in> gammaDG (dg_D sigma v) (dg_G sigma) \<Longrightarrow> s \<in> dg_gamma sigma v"
  unfolding dg_gamma_def by simp

definition dg_trees ::
  "cfg \<Rightarrow> pp \<Rightarrow>
   (pp \<times> unit, unit,
      ('D, 'G) dg_state) strategy_tree list"
where
  "dg_trees g v =
     map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u)))
       (intra_predecessor_list g v)
     @ map (\<lambda>(cc, ca, ex). dg_cmb (\<lambda>_ _ _ _. ()) () ca cc ex)
       (return_call_action_list g v)
     @ dg_extra g (\<lambda>_ _ _ _. ()) () v"

definition dg_acc ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> pp
   \<Rightarrow> 'D"
where
  "dg_acc g bot0 s0d v =
     (if v = cfg_entry g then bot0 \<squnion> s0d else bot0)"

lemma eq_dg_gen:
  "eq (dg_gen g bot0 s0d s0g) (v, ()) sigma =
   DG (side_acc_dg (dg_acc g bot0 s0d v)
     sigma (dg_trees g v)) bot"
  unfolding dg_gen_def dg_trees_def dg_acc_def dg_cmb_def
  by (simp add: eq_side_cfg_T_eff_keyed_seed_dg)

lemma sides_fold_le_dg_gen:
  "sides_of_rhs
      (side_rhs_fold_dg (dg_acc g bot0 s0d v)
        (dg_trees g v)) sigma k
   \<le> sides_of_rhs (dg_gen g bot0 s0d s0g (v, ())) sigma k"
  unfolding dg_gen_def dg_trees_def dg_acc_def dg_cmb_def
    side_cfg_T_eff_keyed_seed_dg_def
  by (cases "v = cfg_entry g") (simp_all add: Let_def)

text \<open>
  \<open>dg_postfix\<close> is the DG-specific instance of a semantic post-fixpoint:
  \<open>sigma\<close> dominates the seed on both projections, and every specification
  transfer --- \<open>dg_spec_step\<close> on an intra edge, \<open>dgs_enter\<close> on a call entry,
  \<open>dgs_combine\<close> on a call return --- is bounded on both projections by
  \<open>sigma\<close> at its target. The eight conjuncts are the two seed bounds plus a
  D/G pair for each of the three transfer kinds; each has its own named
  projection lemma below (\<open>dg_postfix_entryD\<close>, \<open>dg_postfix_edgeD\<close>, ...) so
  callers never navigate the conjunction positionally.
\<close>
definition dg_postfix ::
  "cfg \<Rightarrow> 'D \<Rightarrow> 'G
   \<Rightarrow> (pp \<times> unit + unit \<Rightarrow>
        ('D, 'G) dg_state)
   \<Rightarrow> bool"
where
  "dg_postfix g s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_D sigma (cfg_entry g) \<and>
     s0g \<le> dg_G sigma \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
        snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_D sigma v) \<and>
     (\<forall>u a v. (u, a, v) \<in> intra g \<longrightarrow>
        fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
          \<le> dg_G sigma) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        snd (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
          \<le> dg_D sigma (FunctionEntry p)) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        fst (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
          \<le> dg_G sigma) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        snd (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
          (dg_G sigma)) \<le> dg_D sigma k) \<and>
     (\<forall>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<longrightarrow>
        fst (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
          (dg_G sigma)) \<le> dg_G sigma)"

(* Stable, order-independent projections out of dg_postfix's 8-way conjunction; each
   pays the conjunct-navigation cost once here instead of at every call site via a
   positional [THEN conjunct2, THEN conjunct2, ...] chain that would silently misdirect
   if a conjunct were ever inserted or reordered. *)
lemma dg_postfix_entryD:
  assumes pf: "dg_postfix g s0d s0g sigma"
  shows "s0d \<le> dg_D sigma (cfg_entry g)"
  using pf unfolding dg_postfix_def by blast

lemma dg_postfix_entryG:
  assumes pf: "dg_postfix g s0d s0g sigma"
  shows "s0g \<le> dg_G sigma"
  using pf unfolding dg_postfix_def by blast

lemma dg_postfix_edgeD:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
  shows "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_D sigma w"
  using pf edge unfolding dg_postfix_def by auto

lemma dg_postfix_edgeG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
  shows "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
  using dg_postfix_def edge pf by fastforce

lemma dg_postfix_enterD:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "snd (dgs_enter S fs as (dg_D sigma cc) (dg_G sigma)) \<le> dg_D sigma (FunctionEntry p)"
  using pf ce unfolding dg_postfix_def by fastforce

lemma dg_postfix_enterG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "fst (dgs_enter S fs as (dg_D sigma cc) (dg_G sigma)) \<le> dg_G sigma"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_postfix_combineD:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "snd (dgs_combine S dst (dg_D sigma cc) (dg_D sigma (FunctionResult p)) (dg_G sigma))
           \<le> dg_D sigma k"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_postfix_combineG:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(cc, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
  shows "fst (dgs_combine S dst (dg_D sigma cc) (dg_D sigma (FunctionResult p)) (dg_G sigma))
           \<le> dg_G sigma"
  using pf ce unfolding dg_postfix_def by blast

lemma dg_edge_tree_local:
  "locals (traverse_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma)
   = snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (subst traverse_intra_keyed)
    (simp add: traverse_dg_edge_tree)

lemma dg_edge_tree_global:
  "globs (sides_of_rhs
      (map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ()))
          (apply_dg_spec S a u))) sigma (Inr ()))
   = fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding apply_dg_spec_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_edge_tree_Inr
      sum.map_comp o_def)

lemma dg_combine_tree_local:
  "locals (traverse_rhs (dg_cmb (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) cc ex) sigma)
   = snd (dgs_combine S dst (dg_D sigma cc) (dg_D sigma ex)
       (dg_G sigma))"
  unfolding dg_cmb_def dg_spec_combine_tree_def dg_D_def dg_G_def
  apply simp
  apply (subst traverse_intra_keyed)
  apply (simp add: traverse_dg_combine_tree)
  done

lemma dg_combine_tree_global:
  "globs (sides_of_rhs (dg_cmb (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) cc ex) sigma (Inr ()))
   = fst (dgs_combine S dst (dg_D sigma cc) (dg_D sigma ex)
       (dg_G sigma))"
  unfolding dg_cmb_def dg_spec_combine_tree_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_combine_tree_Inr
      sum.map_comp o_def)

lemma dg_enter_tree_local:
  "locals (traverse_rhs (dg_enter () fs as cl) sigma)
   = snd (dgs_enter S fs as (dg_D sigma cl) (dg_G sigma))"
  unfolding dg_enter_def dg_D_def dg_G_def
  by (subst traverse_intra_keyed)
    (simp add: traverse_dg_edge_tree)

lemma dg_enter_tree_global:
  "globs (sides_of_rhs (dg_enter () fs as cl) sigma (Inr ()))
   = fst (dgs_enter S fs as (dg_D sigma cl) (dg_G sigma))"
  unfolding dg_enter_def dg_D_def dg_G_def
  by (simp add: sides_map_gtree_unit_gen sides_map_ltree_Inr sides_dg_edge_tree_Inr
      sum.map_comp o_def)

theorem dg_post_solution_postfix:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g)
        x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow> (v, ()) \<in> vars"
    and cover_enter:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (FunctionEntry p, ()) \<in> vars"
    and cover_combine:
      "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g
         \<Longrightarrow> (k, ()) \<in> vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
  shows "dg_postfix g s0d s0g sigma"
proof -
  have eq_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      eq (dg_gen g bot0 s0d s0g) (v, ()) sigma
        \<le> sigma (Inl (v, ()))"
    using se_constraint_holds_local[OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (dg_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using se_constraint_holds_sides[OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast

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
      unfolding dg_gen_def side_cfg_T_eff_keyed_seed_dg_def
      by (simp add: Let_def less_eq_dg_state_def sup_dg_state_def)
    also have "... \<le> sigma (Inr ())"
      using sides_le[OF cover_entry] by (rule le_funD)
    finally show ?thesis
      by (simp add: dg_G_def less_eq_dg_state_def)
  qed

  have edge_tree_mem:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
    have "(u, a) \<in> set (intra_predecessor_list g v)"
      using edge
      by (simp add: set_intra_predecessor_list[OF finI] intra_predecessors_def)
    then show "map_gtree (\<lambda>_. ())
        (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))
      \<in> set (dg_trees g v)"
      by (auto simp: dg_trees_def)
  qed

  have edgeD:
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_D sigma v"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
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
    "\<And>u a v. (u, a, v) \<in> intra g \<Longrightarrow>
      fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))
        \<le> dg_G sigma"
  proof -
    fix u a v
    assume edge: "(u, a, v) \<in> intra g"
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

  have enter_tree_mem:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      dg_enter () fs as c \<in> set (dg_trees g (FunctionEntry p))"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "(c, CallEdge dst fs as) \<in> set (entry_call_list g (FunctionEntry p))"
      using ce by (auto simp: set_entry_call_list[OF finC] entry_calls_iff)
    then show "dg_enter () fs as c \<in> set (dg_trees g (FunctionEntry p))"
      by (force simp: dg_trees_def dg_extra_def image_iff)
  qed

  have enterD:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      snd (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> dg_D sigma (FunctionEntry p)"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "snd (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d (FunctionEntry p))
          sigma (dg_trees g (FunctionEntry p))"
      using locals_traverse_le_side_acc_dg[OF enter_tree_mem[OF ce]]
      by (simp add: dg_enter_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (FunctionEntry p, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma (FunctionEntry p)"
      using eq_le[OF cover_enter[OF ce]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> dg_D sigma (FunctionEntry p)" .
  qed

  have enterG:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      fst (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> dg_G sigma"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "fst (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d (FunctionEntry p))
            (dg_trees g (FunctionEntry p))) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF enter_tree_mem[OF ce], where k = "Inr ()"]
      by (simp add: dg_enter_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (FunctionEntry p, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_enter[OF ce], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dgs_enter S fs as (dg_D sigma c) (dg_G sigma))
        \<le> dg_G sigma" .
  qed

  have combine_tree_mem:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      dg_cmb (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c (FunctionResult p) \<in> set (dg_trees g k)"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "(c, CallEdge dst fs as, FunctionResult p) \<in> set (return_call_action_list g k)"
      using ce by (auto simp: set_return_call_action_list[OF finC] return_call_actions_iff)
    then show "dg_cmb (\<lambda>_ _ _ _. ()) () (CallEdge dst fs as) c (FunctionResult p)
        \<in> set (dg_trees g k)"
      by (force simp: dg_trees_def)
  qed

  have combineD:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      snd (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_D sigma k"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "snd (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
          (dg_G sigma))
        \<le> side_acc_dg (dg_acc g bot0 s0d k)
          sigma (dg_trees g k)"
      using locals_traverse_le_side_acc_dg[OF combine_tree_mem[OF ce]]
      by (simp add: dg_combine_tree_local)
    also have "... = locals
        (eq (dg_gen g bot0 s0d s0g) (k, ()) sigma)"
      by (simp add: eq_dg_gen)
    also have "... \<le> dg_D sigma k"
      using eq_le[OF cover_combine[OF ce]]
      by (simp add: dg_D_def less_eq_dg_state_def)
    finally show "snd (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_D sigma k" .
  qed

  have combineG:
    "\<And>c dst fs as p k. (c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g \<Longrightarrow>
      fst (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_G sigma"
  proof -
    fix c dst fs as p k
    assume ce: "(c, CallEdge dst fs as, FunctionEntry p, k) \<in> calls g"
    have "fst (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
          (dg_G sigma))
        \<le> globs (sides_of_rhs
          (side_rhs_fold_dg (dg_acc g bot0 s0d k)
            (dg_trees g k)) sigma (Inr ()))"
      using sides_le_side_rhs_fold_dg
        [OF combine_tree_mem[OF ce], where k = "Inr ()"]
      by (simp add: dg_combine_tree_global less_eq_dg_state_def)
    also have "... \<le> globs (sides_of_rhs
        (dg_gen g bot0 s0d s0g (k, ())) sigma (Inr ()))"
      using sides_fold_le_dg_gen[where k = "Inr ()"]
      by (simp add: less_eq_dg_state_def)
    also have "... \<le> dg_G sigma"
      using sides_le[OF cover_combine[OF ce], THEN le_funD, of "Inr ()"]
      by (simp add: dg_G_def less_eq_dg_state_def)
    finally show "fst (dgs_combine S dst (dg_D sigma c) (dg_D sigma (FunctionResult p))
        (dg_G sigma)) \<le> dg_G sigma" .
  qed

  show ?thesis
    unfolding dg_postfix_def
    using entryD entryG edgeD edgeG enterD enterG combineD combineG by blast
qed

text \<open>The three set-valued closure obligations of a \<^const>\<open>dg_postfix\<close> against
  \<^const>\<open>dg_gamma\<close> discharge the trace-native collecting endpoint.\<close>

lemma dg_postfix_gamma_entry:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
proof -
  have d_le: "s0d \<le> dg_D sigma (cfg_entry g)"
    and g_le: "s0g \<le> dg_G sigma"
    using dg_postfix_entryD[OF pf] dg_postfix_entryG[OF pf] .
  have "gammaDG s0d s0g \<subseteq>
      gammaDG (dg_D sigma (cfg_entry g)) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show ?thesis
    using sound0 dg_gammaI by blast
qed

lemma dg_postfix_gamma_edge:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and edge: "(u, a, w) \<in> intra g"
    and sin: "s \<in> edge_collect a (dg_gamma sigma u)"
  shows "s \<in> dg_gamma sigma w"
proof -
  have sin':
      "s \<in> edge_collect a (gammaDG (dg_D sigma u) (dg_G sigma))"
    using sin unfolding dg_gamma_def .
  have out: "s \<in> gammaDG (snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
                         (fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))"
    using step_sound_fs sin' by blast
  have d_le: "snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_D sigma w"
    using dg_postfix_edgeD[OF pf edge] .
  have g_le: "fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_edgeG[OF pf edge] .
  have "gammaDG (snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
                (fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma w) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "s \<in> dg_gamma sigma w"
    using out dg_gammaI by blast
qed

lemma dg_postfix_gamma_call:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_gamma sigma u"
  shows "call_enter gs (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
proof -
  have sin': "s \<in> gammaDG (dg_D sigma u) (dg_G sigma)"
    using dg_gammaD[OF sin] .
  have out: "call_enter gs (CallEdge dst pars args) s \<in>
               gammaDG (snd (dgs_enter S pars args (dg_D sigma u) (dg_G sigma)))
                       (fst (dgs_enter S pars args (dg_D sigma u) (dg_G sigma)))"
    using enter_sound_fs[OF sin'] .
  have d_le: "snd (dgs_enter S pars args (dg_D sigma u) (dg_G sigma))
                \<le> dg_D sigma (FunctionEntry p)"
    using dg_postfix_enterD[OF pf ce] .
  have g_le: "fst (dgs_enter S pars args (dg_D sigma u) (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_enterG[OF pf ce] .
  have "gammaDG (snd (dgs_enter S pars args (dg_D sigma u) (dg_G sigma)))
                (fst (dgs_enter S pars args (dg_D sigma u) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma (FunctionEntry p)) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "call_enter gs (CallEdge dst pars args) s \<in> dg_gamma sigma (FunctionEntry p)"
    using out dg_gammaI by blast
qed

lemma dg_postfix_gamma_combine:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and comb: "(cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and sin: "s \<in> dg_gamma sigma cl"
    and tin: "t \<in> dg_gamma sigma (FunctionResult p)"
  shows "combine_collect gs dst s t \<in> dg_gamma sigma cont"
proof -
  have sin': "s \<in> gammaDG (dg_D sigma cl) (dg_G sigma)"
    using dg_gammaD[OF sin] .
  have tin': "t \<in> gammaDG (dg_D sigma (FunctionResult p)) (dg_G sigma)"
    using dg_gammaD[OF tin] .
  have out: "combine_collect gs dst s t \<in>
      gammaDG (snd (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
              (fst (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p)) (dg_G sigma)))"
    using combine_sound_fs[OF sin' tin'] .
  have d_le: "snd (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p))
                (dg_G sigma)) \<le> dg_D sigma cont"
    using dg_postfix_combineD[OF pf comb] .
  have g_le: "fst (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p))
                (dg_G sigma)) \<le> dg_G sigma"
    using dg_postfix_combineG[OF pf comb] .
  have "gammaDG (snd (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
                (fst (dgs_combine S dst (dg_D sigma cl) (dg_D sigma (FunctionResult p)) (dg_G sigma)))
      \<subseteq> gammaDG (dg_D sigma cont) (dg_G sigma)"
    by (rule gammaDG_mono[OF d_le g_le])
  then show "combine_collect gs dst s t \<in> dg_gamma sigma cont"
    using out dg_gammaI by blast
qed

subsection \<open>Reduction to the hook-parametric shape\<close>

text \<open>
  \<open>dg_trees\<close>'s three tree constructors, restated as functions of exactly the
  shape the hook-parametric generator below fixes (\<open>edge_tree\<close>/\<open>combine_tree\<close>/
  \<open>enter_tree\<close>, each ignoring the destination/continuation position the same
  way \<open>dg_trees\<close> already does). \<open>dg_edge_tree_local\<close>/\<open>dg_combine_tree_local\<close>/
  \<open>dg_enter_tree_local\<close> (and their \<open>_global\<close> siblings) above already compute
  exactly what that generator's three soundness assumptions need, so this
  spec-record route is an instance of the hook route rather than a second,
  independent proof of the same per-step obligation.
\<close>

definition dg_edge_tree_hook ::
  "pp \<Rightarrow> edge_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_edge_tree_hook u a v =
     map_gtree (\<lambda>_. ()) (map_ltree (\<lambda>w. (w, ())) (apply_dg_spec S a u))"

definition dg_combine_tree_hook ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_combine_tree_hook cc ca ex k = dg_cmb (\<lambda>_ _ _ _. ()) () ca cc ex"

definition dg_enter_tree_hook ::
  "pp \<Rightarrow> call_action \<Rightarrow> pp \<Rightarrow> (pp \<times> unit, unit, ('D, 'G) dg_state) strategy_tree"
where
  "dg_enter_tree_hook cc ca p =
     (case ca of CallEdge dst fs as \<Rightarrow> dg_enter () fs as cc)"

lemma dg_edge_tree_hook_local:
  "locals (traverse_rhs (dg_edge_tree_hook u a v) sigma)
     = snd (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding dg_edge_tree_hook_def by (rule dg_edge_tree_local)

lemma dg_edge_tree_hook_global:
  "globs (sides_of_rhs (dg_edge_tree_hook u a v) sigma (Inr ()))
     = fst (dg_spec_step S a (dg_D sigma u) (dg_G sigma))"
  unfolding dg_edge_tree_hook_def by (rule dg_edge_tree_global)

lemma dg_combine_tree_hook_local:
  "locals (traverse_rhs (dg_combine_tree_hook cc (CallEdge dst fs as) ex k) sigma)
     = snd (dgs_combine S dst (dg_D sigma cc) (dg_D sigma ex) (dg_G sigma))"
  unfolding dg_combine_tree_hook_def by (rule dg_combine_tree_local)

lemma dg_combine_tree_hook_global:
  "globs (sides_of_rhs (dg_combine_tree_hook cc (CallEdge dst fs as) ex k) sigma (Inr ()))
     = fst (dgs_combine S dst (dg_D sigma cc) (dg_D sigma ex) (dg_G sigma))"
  unfolding dg_combine_tree_hook_def by (rule dg_combine_tree_global)

lemma dg_enter_tree_hook_local:
  "locals (traverse_rhs (dg_enter_tree_hook cc (CallEdge dst fs as) p) sigma)
     = snd (dgs_enter S fs as (dg_D sigma cc) (dg_G sigma))"
  unfolding dg_enter_tree_hook_def by (simp add: dg_enter_tree_local)

lemma dg_enter_tree_hook_global:
  "globs (sides_of_rhs (dg_enter_tree_hook cc (CallEdge dst fs as) p) sigma (Inr ()))
     = fst (dgs_enter S fs as (dg_D sigma cc) (dg_G sigma))"
  unfolding dg_enter_tree_hook_def by (simp add: dg_enter_tree_global)

end


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
      (side_rhs_fold_dg (hook_acc g bot0 s0d v)
        (hook_trees g v)) sigma k
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
    using se_constraint_holds_local
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
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
    using se_constraint_holds_sides
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
      cover
    by blast
  have "globs (sides_of_rhs t sigma (Inr ()))
      \<le> globs (sides_of_rhs
        (side_rhs_fold_dg (hook_acc g bot0 s0d v)
          (hook_trees g v)) sigma (Inr ()))"
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
    using se_constraint_holds_local
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
    by blast
  have sides_le:
    "\<And>v. (v, ()) \<in> vars \<Longrightarrow>
      sides_of_rhs (hook_gen g bot0 s0d s0g (v, ()))
        sigma \<le> sigma"
    using se_constraint_holds_sides
      [OF part_post_solution_imp_se_constraint_holds[OF pp]]
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
  and a per-node @{const se_constraint_holds} fact into the single conjunct
  @{const part_post_solution} needs at that node -- and combining every
  node's conjunct with exit membership into @{const part_post_solution}
  itself -- is the same argument regardless of which CFG or domain
  instantiates this locale: only the node's own predecessor count (zero at
  entry, one at an ordinary edge, two at a join) and its concrete
  dependency/effect facts vary per call site. These lemmas fix that argument
  once, so an instance's own post-solution assembly reduces to a case split
  whose branches each cite one dependency fact, one membership fact, and one
  @{const se_constraint_holds} fact.
\<close>

lemma hook_gen_dep_and_se_entry:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) = {}"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma
      (cfg_entry g, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (cfg_entry g, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (cfg_entry g, ())) sigma (cfg_entry g, ())"
  using dep_eq se by auto

lemma hook_gen_dep_and_se_single:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u, ())}"
    and mem: "(u, ()) \<in> vars"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem se by auto

lemma hook_gen_dep_and_se_pair:
  assumes dep_eq: "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) = {(u1, ()), (u2, ())}"
    and mem1: "(u1, ()) \<in> vars"
    and mem2: "(u2, ()) \<in> vars"
    and se: "se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  shows "dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma (v, ()) \<subseteq> vars \<and>
    se_constraint_holds (hook_gen g bot0 s0d s0g (v, ())) sigma (v, ())"
  using dep_eq mem1 mem2 se by auto

text \<open>
  Assembling the whole node-indexed ball into @{const part_post_solution}
  itself needs only exit membership, via
  @{thm part_post_solution_iff_se_constraint_holds}.
\<close>

lemma part_post_solution_of_ball:
  assumes exit_mem: "x \<in> vars"
    and ball: "\<forall>u \<in> vars. dep\<^sub>L (hook_gen g bot0 s0d s0g) sigma u \<subseteq> vars \<and>
      se_constraint_holds (hook_gen g bot0 s0d s0g u) sigma u"
  shows "part_post_solution (hook_gen g bot0 s0d s0g) x sigma vars"
  unfolding part_post_solution_iff_se_constraint_holds using exit_mem ball by blast

end

subsection \<open>The spec-record route as a hook instance\<close>

text \<open>
  \<open>sound_dg_spec\<close>'s per-step obligations (\<open>step_sound\<close>, \<open>combine_sound\<close>,
  \<open>enter_sound\<close>) are exactly \<open>sound_dg_hooks\<close>'s three hook obligations
  specialized at the tree instantiation \<open>dg_edge_tree_hook\<close>/
  \<open>dg_combine_tree_hook\<close>/\<open>dg_enter_tree_hook\<close>: \<open>dg_D\<close>/\<open>dg_G\<close> and
  \<open>dg_hook_D\<close>/\<open>dg_hook_G\<close> unfold to the same term, so \<open>dg_gamma\<close> and
  \<open>dg_hook_gamma\<close> agree pointwise, and each hook tree's local/global answer is
  the corresponding \<open>dg_spec_step\<close>/\<open>dgs_enter\<close>/\<open>dgs_combine\<close> component by
  \<open>dg_edge_tree_hook_local\<close>/\<open>_global\<close> and its combine/enter siblings. This
  makes every \<open>sound_dg_spec\<close> interpretation a \<open>sound_dg_hooks\<close> interpretation
  for free, with no change to any existing \<open>sound_dg_spec\<close> interpretation.
\<close>

text \<open>The target is interpreted under the \<open>hooks\<close> qualifier: both locales
  fix an assumption named \<open>gammaDG_mono\<close>, so an unqualified sublocale would
  make every concrete \<open>sound_dg_spec\<close> interpretation (\<open>sign_dg\<close>, \<open>ivl_dg\<close>,
  ...) export two facts under the same flattened name and fail to build.\<close>

sublocale sound_dg_spec \<subseteq> hooks: sound_dg_hooks gammaDG gs
  dg_edge_tree_hook dg_combine_tree_hook dg_enter_tree_hook
proof unfold_locales
  fix d d' g g' :: 'G and e e' :: 'D
  show "\<lbrakk>e \<le> e'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG e g \<subseteq> gammaDG e' g'"
    by (rule gammaDG_mono)
next
  fix sigma source action destination
  have dD: "dg_hook_D sigma source = dg_D sigma source"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  show "edge_collect action (dg_hook_gamma gammaDG sigma source) \<subseteq>
      gammaDG
        (locals (traverse_rhs (dg_edge_tree_hook source action destination) sigma))
        (globs (sides_of_rhs (dg_edge_tree_hook source action destination) sigma (Inr ())))"
    unfolding dg_hook_gamma_def dD dG
      dg_edge_tree_hook_local dg_edge_tree_hook_global
    by (rule step_sound_fs)
next
  fix sigma caller dst fs args callee s
  assume sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
  have dD: "dg_hook_D sigma caller = dg_D sigma caller"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  have sin': "s \<in> gammaDG (dg_D sigma caller) (dg_G sigma)"
    using sin unfolding dg_hook_gamma_def dD dG .
  show "call_enter gs (CallEdge dst fs args) s \<in>
      gammaDG
        (locals (traverse_rhs
          (dg_enter_tree_hook caller (CallEdge dst fs args) (FunctionEntry callee)) sigma))
        (globs (sides_of_rhs
          (dg_enter_tree_hook caller (CallEdge dst fs args) (FunctionEntry callee)) sigma (Inr ())))"
    unfolding dg_enter_tree_hook_local dg_enter_tree_hook_global
    by (rule enter_sound_fs[OF sin'])
next
  fix sigma caller dst fs args callee continuation s t
  assume sin: "s \<in> dg_hook_gamma gammaDG sigma caller"
    and tin: "t \<in> dg_hook_gamma gammaDG sigma (FunctionResult callee)"
  have dDc: "dg_hook_D sigma caller = dg_D sigma caller"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dDe: "dg_hook_D sigma (FunctionResult callee) = dg_D sigma (FunctionResult callee)"
    unfolding dg_hook_D_def dg_D_def by (rule refl)
  have dG: "dg_hook_G sigma = dg_G sigma"
    unfolding dg_hook_G_def dg_G_def by (rule refl)
  have sin': "s \<in> gammaDG (dg_D sigma caller) (dg_G sigma)"
    using sin unfolding dg_hook_gamma_def dDc dG .
  have tin': "t \<in> gammaDG (dg_D sigma (FunctionResult callee)) (dg_G sigma)"
    using tin unfolding dg_hook_gamma_def dDe dG .
  show "combine_collect gs dst s t \<in>
      gammaDG
        (locals (traverse_rhs
          (dg_combine_tree_hook caller (CallEdge dst fs args) (FunctionResult callee) continuation)
          sigma))
        (globs (sides_of_rhs
          (dg_combine_tree_hook caller (CallEdge dst fs args) (FunctionResult callee) continuation)
          sigma (Inr ())))"
    unfolding dg_combine_tree_hook_local dg_combine_tree_hook_global
    by (rule combine_sound_fs[OF sin' tin'])
qed

context sound_dg_spec
begin

text \<open>The two equation systems -- \<open>dg_gen\<close>, built directly off the
  spec-record, and \<open>hook_gen\<close>, inherited from the hook-route sublocale
  interpretation above at the instantiation just proved sound -- denote the
  same function, not merely a sound approximation of each other. Both unfold
  to the same \<open>side_rhs_fold_dg\<close> application over the same list of trees once
  the hook route's \<open>edge_tree\<close>/\<open>combine_tree\<close>/\<open>enter_tree\<close> are read back as
  \<open>dg_edge_tree_hook\<close>/\<open>dg_combine_tree_hook\<close>/\<open>dg_enter_tree_hook\<close>.\<close>
lemma dg_gen_eq_hook_gen: "dg_gen g bot0 s0d s0g = hooks.hook_gen g bot0 s0d s0g"
  unfolding dg_gen_def hooks.hook_gen_def
    side_cfg_T_eff_keyed_seed_dg_def side_cfg_T_eff_keyed_seed_trees_def
    dg_extra_def dg_edge_tree_hook_def dg_combine_tree_hook_def dg_enter_tree_hook_def
  by (rule ext) auto

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
    dgs_enter      = (\<lambda>xs es d g. (tf_enter tfG xs es g,
                                   tf_enter tfD xs es d)),
    dgs_combine_env    = (\<lambda>dc de g. (combine_abs is_global g g, combine_abs is_global dc de)),
    dgs_combine_assign = (\<lambda>dst de g merged.
      (combine_assign_abs dst (g ret_var) (fst merged),
       combine_assign_abs dst (de ret_var) (snd merged)))
  \<rparr>"

lemma dg_spec_step_indep [simp]:
  "dg_spec_step (indep_dg_spec tfD tfG) a d g
   = (apply_tf tfG a g, apply_tf tfD a d)"
  unfolding indep_dg_spec_def
  by (cases a) (simp_all add: apply_tf_EA_Ret_None apply_tf_EA_Ret_Some split: option.splits)

lemma dgs_combine_indep [simp]:
  "dgs_combine (indep_dg_spec tfD tfG) dst dc de g
   = (combine_collect_abs is_global dst g g, combine_collect_abs is_global dst dc de)"
  unfolding dgs_combine_def indep_dg_spec_def combine_collect_abs_def by simp

text \<open>The combine obligation of @{locale sound_dg_spec} for the independent
  product, as a named corollary: applied by @{method rule} at the interpretation
  boundary instead of positional \<open>for\<close> binders.\<close>
lemma gamma_dg_combine_sound:
  assumes sc: "s \<in> gamma_dg dc g" and tc: "t \<in> gamma_dg de g"
  shows "combine_collect is_global dst s t \<in>
           (case dgs_combine (indep_dg_spec tfD tfG) dst dc de g of (g', d') \<Rightarrow> gamma_dg d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc\<rbrakk>" using gamma_dgD1[OF sc] .
  have sg: "s \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF sc] .
  have tc': "t \<in> \<lbrakk>de\<rbrakk>" using gamma_dgD1[OF tc] .
  have tg: "t \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF tc] .
  have d_sound: "combine_collect is_global dst s t \<in> \<lbrakk>combine_collect_abs is_global dst dc de\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  have g_sound: "combine_collect is_global dst s t \<in> \<lbrakk>combine_collect_abs is_global dst g g\<rbrakk>"
    by (rule combine_collect_sound[OF sg tg])
  show ?thesis
    using d_sound g_sound unfolding gamma_dg_def by simp
qed

text \<open>The enter obligation of @{locale sound_dg_spec} for the independent product:
  each slot's callee-entry store lands in its own @{const tf_enter} image.\<close>
lemma gamma_dg_enter_sound:
  assumes soundD: "sound_transfer tfD" and soundG: "sound_transfer tfG"
    and sc: "s \<in> gamma_dg dc g"
  shows "call_enter is_global (CallEdge dst pars args) s \<in>
           (case dgs_enter (indep_dg_spec tfD tfG) pars args dc g of (g', d') \<Rightarrow> gamma_dg d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc\<rbrakk>" using gamma_dgD1[OF sc] .
  have sg: "s \<in> \<lbrakk>g\<rbrakk>" using gamma_dgD2[OF sc] .
  have d_sound: "call_enter is_global (CallEdge dst pars args) s \<in> \<lbrakk>tf_enter tfD pars args dc\<rbrakk>"
    using sound_transfer.tf_sound_enterD[OF soundD sc']
    by (simp add: call_enter_CallEdge)
  have g_sound: "call_enter is_global (CallEdge dst pars args) s \<in> \<lbrakk>tf_enter tfG pars args g\<rbrakk>"
    using sound_transfer.tf_sound_enterD[OF soundG sg]
    by (simp add: call_enter_CallEdge)
  show ?thesis
    unfolding indep_dg_spec_def gamma_dg_def by (simp add: d_sound g_sound)
qed

lemma sound_dg_spec_indep:
  assumes soundD: "sound_transfer tfD"
    and soundG: "sound_transfer tfG"
  shows "sound_dg_spec (indep_dg_spec tfD tfG) gamma_dg is_global"
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
  subgoal premises prems by (rule gamma_dg_combine_sound[OF prems])
  subgoal premises prems by (rule gamma_dg_enter_sound[OF soundD soundG prems])
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

lemma gamma_unitD [dest]: "s \<in> gamma_unit d g \<Longrightarrow> s \<in> \<lbrakk>d \<squnion> g\<rbrakk>"
  unfolding gamma_unit_def by simp

text \<open>The combine obligation of @{locale sound_dg_spec} for the diagonal (unit)
  interpretation, as a named corollary applied by @{method rule} at the
  interpretation boundary.\<close>
lemma gamma_unit_combine_sound:
  assumes sc: "s \<in> gamma_unit dc g" and tc: "t \<in> gamma_unit de g"
  shows "combine_collect is_global dst s t \<in>
           (case dgs_combine (unit_dg_spec tf) dst dc de g of (g', d') \<Rightarrow> gamma_unit d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_unitD[OF sc] .
  have tc': "t \<in> \<lbrakk>de \<squnion> g\<rbrakk>" using gamma_unitD[OF tc] .
  have "combine_collect is_global dst s t \<in> \<lbrakk>combine_collect_abs is_global dst (dc \<squnion> g) (de \<squnion> g)\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  then show ?thesis
    unfolding dgs_combine_unit_dg_spec gamma_unit_def
    by (simp add: Let_def restrict_local_global_join combine_abs_eq_restrict)
qed

text \<open>The enter obligation of @{locale sound_dg_spec} for the diagonal (unit)
  interpretation.\<close>
lemma gamma_unit_enter_sound:
  assumes sound: "sound_transfer tf"
    and sc: "s \<in> gamma_unit dc g"
  shows "call_enter is_global (CallEdge dst pars args) s \<in>
           (case dgs_enter (unit_dg_spec tf) pars args dc g of (g', d') \<Rightarrow> gamma_unit d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_unitD[OF sc] .
  have "call_enter is_global (CallEdge dst pars args) s \<in> \<lbrakk>tf_enter tf pars args (dc \<squnion> g)\<rbrakk>"
    using sound_transfer.tf_sound_enterD[OF sound sc']
    by (simp add: call_enter_CallEdge)
  then show ?thesis
    unfolding dgs_enter_unit_dg_spec unit_step_def gamma_unit_def
    by (simp add: Let_def restrict_local_global_join)
qed

lemma gamma_unit_combine_sound_for:
  assumes sc: "s \<in> gamma_unit dc g" and tc: "t \<in> gamma_unit de g"
  shows "combine_collect gs dst s t \<in>
           (case dgs_combine (unit_dg_spec_for gs tf) dst dc de g of (g', d') \<Rightarrow> gamma_unit d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_unitD[OF sc] .
  have tc': "t \<in> \<lbrakk>de \<squnion> g\<rbrakk>" using gamma_unitD[OF tc] .
  have "combine_collect gs dst s t \<in> \<lbrakk>combine_collect_abs gs dst (dc \<squnion> g) (de \<squnion> g)\<rbrakk>"
    by (rule combine_collect_sound[OF sc' tc'])
  then show ?thesis
    unfolding dgs_combine_unit_dg_spec_for gamma_unit_def
    by (simp add: Let_def restrict_local_for_global_join combine_abs_for_eq_restrict)
qed

lemma gamma_unit_enter_sound_for:
  assumes sound: "sound_transfer_for gs tf"
    and sc: "s \<in> gamma_unit dc g"
  shows "call_enter gs (CallEdge dst pars args) s \<in>
           (case dgs_enter (unit_dg_spec_for gs tf) pars args dc g of (g', d') \<Rightarrow> gamma_unit d' g')"
proof -
  have sc': "s \<in> \<lbrakk>dc \<squnion> g\<rbrakk>" using gamma_unitD[OF sc] .
  have "call_enter gs (CallEdge dst pars args) s \<in>
      \<lbrakk>tf_enter tf pars args (dc \<squnion> g)\<rbrakk>"
    using sound_transfer_for.tf_sound_enter_forD[OF sound sc']
    by (simp add: call_enter_CallEdge)
  then show ?thesis
    unfolding dgs_enter_unit_dg_spec_for unit_step_for_def gamma_unit_def
    by (simp add: Let_def restrict_local_for_global_join)
qed

lemma sound_dg_spec_unit_for:
  assumes sound: "sound_transfer_for gs tf"
  shows "sound_dg_spec (unit_dg_spec_for gs tf) gamma_unit gs"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_unit_mono)
  subgoal for a d g
    unfolding gamma_unit_def dg_spec_step_unit_for unit_step_for_def
    using sound_transfer_for.edge_collect_apply_tf_sound_for[OF sound, where a = a]
    by (simp add: Let_def restrict_local_for_global_join)
  subgoal premises prems
    by (rule gamma_unit_combine_sound_for[OF prems])
  subgoal premises prems
    by (rule gamma_unit_enter_sound_for[OF sound prems])
  done

lemma sound_dg_spec_unit:
  assumes sound: "sound_transfer tf"
  shows "sound_dg_spec (unit_dg_spec tf) gamma_unit is_global"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_unit_mono)
  subgoal for a d g
    unfolding gamma_unit_def dg_spec_step_unit unit_step_def
    using sound_transfer.edge_collect_apply_tf_sound[OF sound,
      where a = a]
    by (simp add: Let_def restrict_local_global_join)
  subgoal premises prems by (rule gamma_unit_combine_sound[OF prems])
  subgoal premises prems by (rule gamma_unit_enter_sound[OF sound prems])
  done

context sound_transfer
begin

sublocale dg: sound_dg_spec "unit_dg_spec tf" gamma_unit is_global
  by (rule sound_dg_spec_unit[OF sound_transfer_axioms])

end

end
