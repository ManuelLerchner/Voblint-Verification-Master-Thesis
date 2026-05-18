theory Constraint_System_Sound
  imports Constraint_System CFG_Collecting
begin

(*
  Constraint System -- Soundness Theorem.

  Main result: any post-fixpoint of the equation system overapproximates
  the CFG collecting semantics.

  Proof strategy:
    1. Define what it means for env to be a post-fixpoint.
    2. Prove: post-fixpoint ==> env(v) >= cfg_collect(v) for all v.
       By induction on the CFG collecting semantics (or by lfp properties).
    3. Conclude: every concrete state reachable at v is in gamma(env(v)).

  This is the "big bridge" in the pipeline connecting the abstract
  constraint system back to concrete program behaviour.
*)

(* ── Post-Fixpoint Condition ──────────────────────────────────── *)
(* Defined in Constraint_System as is_post_fixpoint / is_post_fixpoint_def. *)

(* ── Overapproximation of Collecting Semantics ───────────────── *)
(*
  Informal sketch of the proof:
  By lfp.induct on cfg_collect: the collecting semantics is the least
  fixpoint of collect_pp.  We show that env also satisfies the fixpoint
  equation (because it is a post-fixpoint and transfer functions are sound).
  Then by minimality of lfp, env >= cfg_collect.
*)

context sound_domain
begin

(* Per-edge soundness: edge_collect on concretisation factors through
   apply_tf in the abstract domain. *)
lemma edge_collect_apply_tf_sound:
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  shows
    "edge_collect a (gamma_state sigma) \<subseteq> gamma_state (apply_tf tf a sigma)"
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
qed

(* join_state pointwise upper-bound lemmas. *)
lemma join_state_ub1: "sigma1 \<le> join_state sigma1 sigma2"
  unfolding join_state_def le_fun_def by (simp add: sup_ge1)

lemma join_state_ub2: "sigma2 \<le> join_state sigma1 sigma2"
  unfolding join_state_def le_fun_def by (simp add: sup_ge2)

(* Each predecessor's tf-image is below the rhs join.
   Uses mem_image_le_fold over the predecessor set. *)
lemma apply_tf_le_rhs:
  assumes fin: "finite (cfg_edges g)"
  assumes uav: "(u, a, v) \<in> cfg_edges g"
  shows "apply_tf tf a (env u) \<le> rhs g tf join_state bot_state s0 env v"
proof -
  define P :: "(pp \<times> edge_action) set"
    where "P = {(u', a'). (u', a', v) \<in> cfg_edges g}"
  have Peq: "P = predecessors g v"
    by (simp add: P_def predecessors_def)
  have finP: "finite P"
    using Peq fin by (simp add: finite_predecessors)
  define f where "f \<equiv> \<lambda>(u', a'). apply_tf tf a' (env u')"
  have mem: "apply_tf tf a (env u) \<in> f ` P"
    unfolding f_def P_def using uav by force
  have le_fold: "apply_tf tf a (env u)
    \<le> Finite_Set.fold join_state bot_state (f ` P)"
    by (rule mem_image_le_fold[OF finP join_state_comp_fun_commute
            join_state_ub1 join_state_ub2, rule_format, OF mem])
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have rhs_eq: "rhs g tf join_state bot_state s0 env v
      = Finite_Set.fold join_state bot_state (insert s0 (f ` P))"
      unfolding rhs_def Let_def abs_join_set_def f_def using True
      by (simp add: P_def)
    interpret jc: comp_fun_commute join_state
      by (rule join_state_comp_fun_commute)
    show ?thesis
    proof (cases "s0 \<in> f ` P")
      case True
      then have "insert s0 (f ` P) = f ` P" by auto
      then show ?thesis using le_fold rhs_eq by simp
    next
      case False
      have "Finite_Set.fold join_state bot_state (insert s0 (f ` P))
        = join_state s0 (Finite_Set.fold join_state bot_state (f ` P))"
        using finP False by (simp add: jc.fold_insert)
      then show ?thesis
        using rhs_eq le_fold order_trans[OF _ join_state_ub2] by simp
    qed
  next
    case False
    have rhs_eq: "rhs g tf join_state bot_state s0 env v
      = Finite_Set.fold join_state bot_state (f ` P)"
      unfolding rhs_def Let_def abs_join_set_def using False
      by (simp add: P_def f_def)
    then show ?thesis using le_fold by simp
  qed
qed

(* Step lemma for collect_pp abstract soundness. *)
lemma collect_pp_abstract_sound:
  assumes fin: "finite (cfg_edges g)"
  assumes post_fp: "is_post_fixpoint g tf join_state bot_state s0 env"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  shows
    "collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
proof
  fix x
  assume "x \<in> collect_pp g (\<lambda>v. gamma_state (env v)) v"
  then obtain u a where uav: "(u, a, v) \<in> cfg_edges g"
    and xin: "x \<in> edge_collect a (gamma_state (env u))"
    unfolding collect_pp_def by blast
  have step1: "x \<in> gamma_state (apply_tf tf a (env u))"
    using edge_collect_apply_tf_sound[OF tf_sound_assign tf_sound_assume tf_sound_assume_not] xin
    by blast
  have le_rhs: "apply_tf tf a (env u) \<le> rhs g tf join_state bot_state s0 env v"
    by (rule apply_tf_le_rhs[OF fin uav])
  have le_env: "rhs g tf join_state bot_state s0 env v \<le> env v"
    using post_fp unfolding is_post_fixpoint_def by simp
  have "apply_tf tf a (env u) \<le> env v"
    using le_rhs le_env by (rule order_trans)
  then have "gamma_state (apply_tf tf a (env u)) \<subseteq> gamma_state (env v)"
    by (rule gamma_state_mono)
  then show "x \<in> gamma_state (env v)" using step1 by blast
qed

(* Element of finite set is below the join_state-fold over that set. *)
lemma join_state_fold_ge:
  assumes "finite A" and "x \<in> A"
  shows "x \<le> Finite_Set.fold join_state bot_state A"
proof -
  have aux: "finite A \<Longrightarrow> \<forall>y\<in>A. y \<le> Finite_Set.fold join_state bot_state A"
  proof (induct A rule: finite_induct)
    case empty
    show ?case by simp
  next
    case (insert a F)
    interpret j: comp_fun_commute join_state
      by (rule join_state_comp_fun_commute)
    have fold_ins: "Finite_Set.fold join_state bot_state (insert a F) =
        join_state a (Finite_Set.fold join_state bot_state F)"
      using insert.hyps by (simp add: j.fold_insert)
    have IH: "\<forall>y\<in>F. y \<le> Finite_Set.fold join_state bot_state F"
      using insert.hyps(3) by blast
    show ?case unfolding fold_ins
    proof (intro ballI)
      fix y assume "y \<in> insert a F"
      then consider "y = a" | "y \<in> F" by blast
      then show "y \<le> join_state a (Finite_Set.fold join_state bot_state F)"
      proof cases
        case 1
        then show ?thesis by (simp add: join_state_ub1)
      next
        case 2
        then have "y \<le> Finite_Set.fold join_state bot_state F" using IH by simp
        also have "\<dots> \<le> join_state a (Finite_Set.fold join_state bot_state F)"
          by (rule join_state_ub2)
        finally show ?thesis .
      qed
    qed
  qed
  from assms aux show ?thesis by simp
qed

(* s0 ≤ rhs at entry: s0 is in the joined set, so below the fold. *)
lemma s0_le_rhs_entry:
  assumes fin: "finite (cfg_edges g)"
  shows "s0 \<le> rhs g tf join_state bot_state s0 env (cfg_entry g)"
proof -
  define P :: "(pp \<times> edge_action) set"
    where "P = {(u', a'). (u', a', cfg_entry g) \<in> cfg_edges g}"
  have Peq: "P = predecessors g (cfg_entry g)"
    by (simp add: P_def predecessors_def)
  have finP: "finite P"
    using Peq fin by (simp add: finite_predecessors)
  define f where "f \<equiv> \<lambda>(u', a'). apply_tf tf a' (env u')"
  have fin_img: "finite (insert s0 (f ` P))"
    using finP by simp
  have mem: "s0 \<in> insert s0 (f ` P)" by simp
  have le_fold: "s0 \<le> Finite_Set.fold join_state bot_state (insert s0 (f ` P))"
    by (rule join_state_fold_ge[OF fin_img mem])
  have rhs_eq: "rhs g tf join_state bot_state s0 env (cfg_entry g)
    = Finite_Set.fold join_state bot_state (insert s0 (f ` P))"
    unfolding rhs_def Let_def abs_join_set_def f_def
    by (simp add: P_def)
  show ?thesis using le_fold rhs_eq by simp
qed

lemma post_fixpoint_sound:
  assumes fin: "finite (cfg_edges g)"
  assumes post_fp: "is_post_fixpoint g tf join_state bot_state s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  shows
    "\<forall>v. cfg_collect g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound[OF fin post_fp
              tf_sound_assign tf_sound_assume tf_sound_assume_not])
  have s0_le_env: "s0 \<le> env (cfg_entry g)"
    using s0_le_rhs_entry[OF fin]
          post_fp[unfolded is_post_fixpoint_def, rule_format, of "cfg_entry g"]
    by (rule order_trans)
  have S_le_env: "S \<le> gamma_state (env (cfg_entry g))"
    using S_sound gamma_state_mono[OF s0_le_env] by blast
  have key: "cfg_collect_F g S (\<lambda>v. gamma_state (env v)) \<le> (\<lambda>v. gamma_state (env v))"
  proof (rule le_funI)
    fix v
    show "cfg_collect_F g S (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    proof (cases "v = cfg_entry g")
      case True
      show ?thesis unfolding cfg_collect_F_def
        using True S_le_env coll_le by simp
    next
      case False
      show ?thesis unfolding cfg_collect_F_def
        using False coll_le by simp
    qed
  qed
  have "cfg_collect g S \<le> (\<lambda>v. gamma_state (env v))"
    unfolding cfg_collect_def
    by (rule lfp_lowerbound[where f="cfg_collect_F g S", OF key])
  then show ?thesis by (auto simp: le_fun_def)
qed

end

context sound_domain
begin

(* ── Corollary: Exit-Point Soundness ─────────────────────────── *)
(*
  At the exit point, the abstract value covers all reachable output states.
*)

corollary exit_sound:
  assumes post_fp: "is_post_fixpoint (to_cfg c) tf join_state bot_state s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes s_in_S: "s \<in> S"
  assumes terminates: "big_step (c, s) t"
  shows   "t \<in> gamma_state (env (cfg_exit (to_cfg c)))"
proof -
  have fin: "finite (cfg_edges (to_cfg c))"
    by (rule to_cfg_finite)
  have pfp: "\<forall>v. cfg_collect (to_cfg c) S v \<le> gamma_state (env v)"
    by (rule post_fixpoint_sound[OF fin post_fp S_sound
            tf_sound_assign tf_sound_assume tf_sound_assume_not])
  have t_in_collect: "t \<in> collect c S"
    using s_in_S terminates unfolding collect_def by blast
  then have t_in_cfg: "t \<in> cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
    by (simp add: cfg_collect_exit_eq_collect)
  from pfp[rule_format, of "cfg_exit (to_cfg c)"] t_in_cfg
    show ?thesis by blast
qed

end

end
