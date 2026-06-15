theory Constraint_System_Sound
  imports Constraint_System "Voblint_CFG.CFG_Collect_Core"
begin

section \<open>Constraint system: soundness theorem\<close>

text \<open>
  Main result: any post-fixpoint of the equation system overapproximates
  the CFG collecting semantics.

  Proof strategy:
    1. Define what it means for env to be a post-fixpoint.
    2. Prove: post-fixpoint ==> env(v) >= collecting(v) for all v.
       By lfp lower-bound: show gamma o env is itself a post-fixpoint.
    3. Conclude: every concrete state reachable at v is in \<gamma>(env(v)).

  This is the ''big bridge'' in the pipeline connecting the abstract
  constraint system back to concrete program behaviour.
\<close>

(* Global rhs-step lemmas (no \<gamma> needed). *)
lemma apply_tf_le_rhs:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  assumes uav: "(u, a, v) \<in> edges g"
  shows "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
proof -
  define P :: "(pp \<times> edge_action) set"
    where "P = {(u', a'). (u', a', v) \<in> edges g}"
  have Peq: "P = predecessors g v"
    by (simp add: P_def predecessors_def)
  have finP: "finite P"
    using Peq fin by (simp add: finite_predecessors)
  define f where "f \<equiv> \<lambda>(u', a'). apply_tf tf a' (env u')"
  have mem: "apply_tf tf a (env u) \<in> f ` P"
    unfolding f_def P_def using uav by force
  interpret j: comp_fun_idem "((\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _)"
    by (rule comp_fun_idem_sup)
  have le_fold: "apply_tf tf a (env u)
    \<le> Finite_Set.fold (\<squnion>) bot (f ` P)"
    by (rule mem_image_le_fold[OF finP comp_fun_commute_sup
            sup_ge1 sup_ge2, rule_format, OF mem])
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have rhs_eq: "rhs g tf (\<squnion>) bot s0 env v
      = Finite_Set.fold (\<squnion>) bot (insert s0 (f ` P))"
      unfolding rhs_def Let_def abs_join_set_def f_def using True
      by (simp add: P_def)
    show ?thesis
    proof (cases "s0 \<in> f ` P")
      case True
      then have "insert s0 (f ` P) = f ` P" by auto
      then show ?thesis using le_fold rhs_eq by simp
    next
      case False
      have "Finite_Set.fold (\<squnion>) bot (insert s0 (f ` P))
        = s0 \<squnion> (Finite_Set.fold (\<squnion>) bot (f ` P))"
        by (metis (no_types, lifting) Sup_fin.eq_fold Sup_fin.insert finP finite_imageI finite_insert
            insert_commute insert_not_empty)
      then show ?thesis
        using rhs_eq le_fold order_trans[OF _ sup_ge2] by simp
    qed
  next
    case False
    have rhs_eq: "rhs g tf (\<squnion>) bot s0 env v
      = Finite_Set.fold (\<squnion>) bot (f ` P)"
      unfolding rhs_def Let_def abs_join_set_def using False
      by (simp add: P_def f_def)
    then show ?thesis using le_fold by simp
  qed
qed

lemma s0_le_rhs_entry:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state"
  assumes fin: "finite (edges g)"
  shows "s0 \<le> rhs g tf (\<squnion>) bot s0 env (cfg_entry g)"
proof -
  define P :: "(pp \<times> edge_action) set"
    where "P = {(u', a'). (u', a', cfg_entry g) \<in> edges g}"
  have Peq: "P = predecessors g (cfg_entry g)"
    by (simp add: P_def predecessors_def)
  have finP: "finite P"
    using Peq fin by (simp add: finite_predecessors)
  define f where "f \<equiv> \<lambda>(u', a'). apply_tf tf a' (env u')"
  have fin_img: "finite (insert s0 (f ` P))"
    using finP by simp
  have mem: "s0 \<in> insert s0 (f ` P)" by simp
  have le_fold: "s0 \<le> Finite_Set.fold (\<squnion>) bot (insert s0 (f ` P))"
    by (metis Sup_fin.coboundedI Sup_fin.eq_fold fin_img finite_insert insert_iff)
  have rhs_eq: "rhs g tf (\<squnion>) bot s0 env (cfg_entry g)
    = Finite_Set.fold (\<squnion>) bot (insert s0 (f ` P))"
    unfolding rhs_def Let_def abs_join_set_def f_def
    using Peq predecessors_def by presburger
  show ?thesis using le_fold rhs_eq by simp
qed

context sound_transfer
begin

(* Per-edge soundness: edge_collect on concretisation factors through
   apply_tf in the abstract domain. *)
lemma edge_collect_apply_tf_sound:
  shows
    "edge_collect a (gamma_state \<sigma>) \<subseteq> gamma_state (apply_tf tf a \<sigma>)"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x ax)
  show ?thesis
    unfolding EA_Assign apply_tf.simps edge_collect.simps
    using tf_sound_assign by blast
next
  case (EA_Assume b)
  show ?thesis
    unfolding EA_Assume apply_tf.simps edge_collect.simps
    using tf_sound_assume by blast
next
  case (EA_AssumeNot b)
  show ?thesis
    unfolding EA_AssumeNot apply_tf.simps edge_collect.simps
    using tf_sound_assume_not by blast
next
  case EA_Enter
  then show ?thesis
    unfolding EA_Enter apply_tf.simps edge_collect.simps
    using tf_sound_enter by auto
qed

end

end
