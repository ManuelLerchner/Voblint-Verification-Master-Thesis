theory Constraint_System_Sound
  imports Constraint_System CFG_Runs_To_Bridge
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

(* Global rhs-step lemmas (no gamma needed). *)
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
next
  case EA_Enter
  then show ?thesis
    unfolding EA_Enter apply_tf.simps edge_collect.simps
    using tf_sound_enter by auto
qed

(* Step lemma for collect_pp abstract soundness. *)
lemma collect_pp_abstract_sound:
  assumes fin: "finite (edges g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  shows
    "collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
proof
  fix x
  assume "x \<in> collect_pp g (\<lambda>v. gamma_state (env v)) v"
  then obtain u a where uav: "(u, a, v) \<in> edges g"
    and xin: "x \<in> edge_collect a (gamma_state (env u))"
    unfolding collect_pp_def by blast
  have step1: "x \<in> gamma_state (apply_tf tf a (env u))"
    using edge_collect_apply_tf_sound xin
    by blast
  have le_rhs: "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
    by (rule apply_tf_le_rhs[OF fin uav])
  have le_env: "rhs g tf (\<squnion>) bot s0 env v \<le> env v"
    using post_fp unfolding is_post_fixpoint_def by simp
  have "apply_tf tf a (env u) \<le> env v"
    using le_rhs le_env by (rule order_trans)
  then have "gamma_state (apply_tf tf a (env u)) \<subseteq> gamma_state (env v)"
    by (rule gamma_state_mono)  then show "x \<in> gamma_state (env v)" using step1 by blast
qed

(* Per-pp variant: only the queried node's rhs bound is needed. *)
lemma collect_pp_abstract_sound_rhs_le:
  assumes fin: "finite (edges g)"
  assumes rhs_le: "rhs g tf (\<squnion>) bot s0 env v \<le> env v"
  shows
    "collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
proof
  fix x
  assume "x \<in> collect_pp g (\<lambda>v. gamma_state (env v)) v"
  then obtain u a where uav: "(u, a, v) \<in> edges g"
    and xin: "x \<in> edge_collect a (gamma_state (env u))"
    unfolding collect_pp_def by blast
  have step1: "x \<in> gamma_state (apply_tf tf a (env u))"
    using edge_collect_apply_tf_sound xin
    by blast
  have le_rhs: "apply_tf tf a (env u) \<le> rhs g tf (\<squnion>) bot s0 env v"
    by (rule apply_tf_le_rhs[OF fin uav])
  have le_env: "rhs g tf (\<squnion>) bot s0 env v \<le> env v"
    using rhs_le by simp
  have "apply_tf tf a (env u) \<le> env v"
    using le_rhs le_env by (rule order_trans)
  then have "gamma_state (apply_tf tf a (env u)) \<subseteq> gamma_state (env v)"
    by (rule gamma_state_mono)
  then show "x \<in> gamma_state (env v)" using step1 by blast
qed

lemma edges_collect_gamma_path_aux:
  assumes fin: "finite (edges g)"  assumes path: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  assumes step_le:
    "\<And>x b y es'. g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v \<Longrightarrow> apply_tf tf b (env x) \<le> env y"
  shows "edges_collect es (gamma_state (env u)) \<subseteq> gamma_state (env v)"
proof (insert path step_le, induction es arbitrary: u)
  case Nil
  then have uv: "u = v" by (cases rule: cfg_path.cases) simp_all
  then show ?case by simp
next
  case (Cons e es')
  assume p: "g \<turnstile> u \<longrightarrow>\<^bsub>(e # es')\<^esub> v"
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  from p ew obtain ed: "(u, a, w) \<in> edges g" and p2: "g \<turnstile> w \<longrightarrow>\<^bsub>es'\<^esub> v"
    by (cases rule: cfg_path.cases) auto
  have step_g: "edge_collect a (gamma_state (env u)) \<subseteq> gamma_state (env w)"
  proof
    fix x
    assume xin: "x \<in> edge_collect a (gamma_state (env u))"
    then obtain s where s: "s \<in> gamma_state (env u)" and xin': "x \<in> edge_collect a {s}"
      using edge_collect_member by blast    have tf_le: "apply_tf tf a (env u) \<le> env w"
      using step_le[OF p[unfolded ew]] .
    have s_in: "{s} \<subseteq> gamma_state (env u)" using s by simp
    have ec_sub: "edge_collect a {s} \<subseteq> gamma_state (apply_tf tf a (env u))"
      using edge_collect_apply_tf_sound s
        edge_collect_mono[OF s_in] subset_trans by blast
    have step1: "x \<in> gamma_state (apply_tf tf a (env u))"
      using xin' ec_sub by blast
    show "x \<in> gamma_state (env w)"
      using gamma_state_mono[OF tf_le] step1 by blast
  qed
  have IH: "edges_collect es' (gamma_state (env w)) \<subseteq> gamma_state (env v)"
    by (rule Cons.IH[OF p2 step_le])
  have "edges_collect es' (edge_collect a (gamma_state (env u))) \<subseteq> gamma_state (env v)"
  proof (rule subset_trans[OF _ IH])
    show "edges_collect es' (edge_collect a (gamma_state (env u)))
          \<subseteq> edges_collect es' (gamma_state (env w))"
      by (rule edges_collect_mono_strong[OF step_g])
  qed
  then show ?case unfolding ew edges_collect.simps .
qed

lemma edges_collect_gamma_path:
  assumes fin: "finite (edges g)"  assumes path: "g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> v"
  assumes step_le:
    "\<And>x b y es'. g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v \<Longrightarrow> apply_tf tf b (env x) \<le> env y"
  assumes u_gamma: "T \<subseteq> gamma_state (env u)"
  shows "edges_collect es T \<subseteq> gamma_state (env v)"
proof -
  have mono: "edges_collect es T \<subseteq> edges_collect es (gamma_state (env u))"
    by (rule edges_collect_mono_strong[OF u_gamma])
  also have "\<dots> \<subseteq> gamma_state (env v)"
    by (rule edges_collect_gamma_path_aux[OF fin path step_le])
  finally show ?thesis .
qed

lemma post_fixpoint_sound_at:
  assumes fin: "finite (edges g)"
  assumes rhs_le: "rhs g tf (\<squnion>) bot s0 env v0 \<le> env v0"  assumes step_le:
    "\<And>u a w es'. g \<turnstile> u \<longrightarrow>\<^bsub>(a, w) # es'\<^esub> v0 \<Longrightarrow> apply_tf tf a (env u) \<le> env w"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes entry_le: "s0 \<le> env (cfg_entry g)"
  shows "cfg_collect g S v0 \<le> gamma_state (env v0)"
proof -
  have paths: "cfg_collect g S v0 \<subseteq> cfg_collect_paths g S v0"
    by (rule cfg_collect_le_paths)
  show ?thesis
  proof
    fix t
    assume "t \<in> cfg_collect g S v0"
    with paths have "t \<in> cfg_collect_paths g S v0" by blast
    then obtain path_es where path_es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>path_es\<^esub> v0"
      and t_in: "t \<in> edges_collect path_es S"
      unfolding cfg_collect_paths_def by blast
    have S_env: "S \<subseteq> gamma_state (env (cfg_entry g))"
      using S_sound entry_le gamma_state_mono by blast
    have gamma_le: "edges_collect path_es S \<subseteq> gamma_state (env v0)"
    proof (rule edges_collect_gamma_path)
      show "finite (edges g)" by fact
      show "g \<turnstile> cfg_entry g \<longrightarrow>\<^bsub>path_es\<^esub> v0" using path_es .
      show "\<And>x b y es'. g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v0 \<Longrightarrow> apply_tf tf b (env x) \<le> env y"
        by (fact step_le)
      show "S \<subseteq> gamma_state (env (cfg_entry g))" using S_env .
    qed
    show "t \<in> gamma_state (env v0)" using gamma_le t_in by blast
  qed
qed

(* Lifted state version of sup_fold_ge; the global polymorphic lemma already
   covers 'a abs_state via the pointwise bounded_semilattice_sup_bot instance. *)
lemma sup_fold_ge_state:
  assumes "finite (A :: 'a abs_state set)" and "x \<in> A"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot A"
  using assms
  by (metis Sup_fin.coboundedI Sup_fin.eq_fold finite_insert insertCI)

lemma post_fixpoint_sound:
  assumes fin: "finite (edges g)"
  assumes post_fp: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  shows
    "\<forall>v. cfg_collect g S v \<le> gamma_state (env v)"
proof -
  have coll_le: "\<And>v. collect_pp g (\<lambda>v. gamma_state (env v)) v \<le> gamma_state (env v)"
    by (rule collect_pp_abstract_sound[OF fin post_fp])
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

context sound_transfer
begin

(* -- Corollary: Exit-Point Soundness ---------------------------- *)
(*
  At the exit point, the abstract value covers all reachable output states.
*)

corollary exit_sound:
  assumes post_fp: "is_post_fixpoint (to_cfg c) tf (\<squnion>) bot s0 env"
  assumes S_sound: "S \<le> gamma_state s0"
  assumes s_in_S: "s \<in> S"
  assumes exit_in_collect:
    "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
  shows   "t \<in> gamma_state (env (cfg_exit (to_cfg c)))"
proof -
  have fin: "finite (edges (to_cfg c))"
    by (rule to_cfg_finite)
  have pfp: "\<forall>v. cfg_collect (to_cfg c) S v \<le> gamma_state (env v)"
    by (rule post_fixpoint_sound[OF fin post_fp S_sound])
  have t_in_sing: "t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"
    using exit_in_collect .
  have t_in_cfg: "t \<in> cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
    using t_in_sing s_in_S cfg_collect_mono_S[of "{s}" S "to_cfg c"]
    by (auto simp: le_fun_def)
  from pfp[rule_format, of "cfg_exit (to_cfg c)"] t_in_cfg
    show ?thesis by blast
qed

end

end
