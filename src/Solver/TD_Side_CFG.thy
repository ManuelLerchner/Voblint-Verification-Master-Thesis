theory TD_Side_CFG
  imports Constraint_System_Sound IMP2_Globals "TD.TD_side"
begin

(*
  Side-effecting constraint system over a CFG, with a locals/globals split.

  Local unknowns are program points (flow-sensitive); a single global unknown
  (unit) holds the flow-insensitive abstract state of the global variables.

  For a program point v, the strategy tree folds over the incoming edges: for
  each predecessor (u, a) it queries u's local state (QueryL), reads the global
  state (QueryG), applies the edge transfer to the combined state, then splits
  the result -- the local component flows on to v, the global component is
  contributed to the global unknown by a side effect (Side).
*)

(* Keep only the local (resp. global) component of an abstract state; the other
   component is set to bot, so the join of the two recovers the original. *)
definition restrict_local ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local sigma = (\<lambda>x. if is_global x then bot else sigma x)"

definition restrict_global ::
  "'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global sigma = (\<lambda>x. if is_global x then sigma x else bot)"

lemma restrict_local_global_join:
  "restrict_local sigma \<squnion> restrict_global sigma = sigma"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

lemma restrict_local_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_local (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_local sigma2"
  unfolding restrict_local_def le_fun_def by (rule ext) auto

lemma restrict_global_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> restrict_global (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
     \<le> restrict_global sigma2"
  unfolding restrict_global_def le_fun_def by (rule ext) auto

(* Strategy tree for one program point: fold the incoming edges into a
   QueryL / QueryG / Side chain. *)
fun side_rhs_fold ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp * edge_action) list
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "side_rhs_fold tf join acc [] = Answer acc"
| "side_rhs_fold tf join acc ((u, a) # ps) =
     QueryL u (\<lambda>su. QueryG () (\<lambda>glob.
       let res = apply_tf tf a (join su glob)
       in Side () (restrict_global res)
            (side_rhs_fold tf join (join acc (restrict_local res)) ps)))"

definition make_side_rhs_tree ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state => pp
   => (pp, unit, 'a abs_state) strategy_tree"
where
  "make_side_rhs_tree g tf join bot0 s0 v =
     (let acc0 = (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
      in side_rhs_fold tf join acc0 (predecessor_list g v))"

(* The side-effecting equation system: one strategy tree per program point. *)
definition side_cfg_T ::
  "cfg => 'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => 'a abs_state
   => (pp, unit, 'a abs_state) eqsT"
where
  "side_cfg_T g tf join bot0 s0 = make_side_rhs_tree g tf join bot0 s0"

(* -- Denotation of the strategy tree --------------------------------- *)

(* The local value computed by traversing the tree: a left fold over the
   incoming edges, each contributing the local part of its transferred state
   (the predecessor's local value joined with the global value). *)
fun side_acc ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => 'a abs_state => (pp + unit => 'a abs_state)
   => (pp * edge_action) list => 'a abs_state"
where
  "side_acc tf join acc sigma [] = acc"
| "side_acc tf join acc sigma ((u, a) # ps) =
     side_acc tf join
       (join acc (restrict_local (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))))
       sigma ps"

(* traverse_rhs (= eq) of the fold is exactly side_acc: QueryL/QueryG resolve
   through sigma, Side is ignored by the answer traversal. *)
lemma traverse_side_rhs_fold:
  "traverse_rhs (side_rhs_fold tf join acc ps) sigma = side_acc tf join acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma eq_side_cfg_T:
  "eq (side_cfg_T g tf join bot0 s0) v sigma =
     side_acc tf join
       (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
       sigma (predecessor_list g v)"
  unfolding side_cfg_T_def make_side_rhs_tree_def
  by (simp add: traverse_side_rhs_fold Let_def)

(* The global contribution: the join over incoming edges of the global part of
   each transferred state.  (Independent of the local accumulator.) *)
fun side_glob ::
  "'a::bounded_semilattice_sup_bot domain_transfer
   => ('a abs_state => 'a abs_state => 'a abs_state)
   => (pp + unit => 'a abs_state) => (pp * edge_action) list => 'a abs_state"
where
  "side_glob tf join sigma [] = bot"
| "side_glob tf join sigma ((u, a) # ps) =
     side_glob tf join sigma ps
       \<squnion> restrict_global (apply_tf tf a (join (sigma (Inl u)) (sigma (Inr ()))))"
(* Monotonicity in the queried assignment (join = \<squnion>). *)
lemma side_acc_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc tf join acc sigma1 ps \<le> side_acc tf join acc sigma2 ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define su1 su2 where
    "su1 = join (sigma1 (Inl u)) (sigma1 (Inr ()))" and
    "su2 = join (sigma2 (Inl u)) (sigma2 (Inr ()))"
  have su_le: "su1 \<le> su2"
    using join_mono sigma_le unfolding su1_def su2_def le_fun_def by auto
  have tf_le: "apply_tf tf a su1 \<le> apply_tf tf a su2"
    by (rule tf_mono[OF su_le])
  have loc_le: "restrict_local (apply_tf tf a su1)
                 \<le> restrict_local (apply_tf tf a su2)"
    by (rule restrict_local_mono[OF tf_le])
  have acc_le: "join acc (restrict_local (apply_tf tf a su1))
                 \<le> join acc (restrict_local (apply_tf tf a su2))"
    by (rule join_mono[OF order_refl loc_le])
  show ?case unfolding ua using Cons.IH[OF acc_le] by (simp only: side_acc.simps)
qed

lemma side_acc_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_acc tf (\<squnion>) acc sigma1 ps \<le> side_acc tf (\<squnion>) acc sigma2 ps"
  using side_acc_mono[OF tf_mono _ sigma_le, where join="(\<squnion>)"]
  by (simp add: sup_mono)

lemma side_glob_mono:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes join_mono:
    "\<And>s1 s1' s2 s2'. s1 \<le> s1' \<Longrightarrow> s2 \<le> s2'
     \<Longrightarrow> join s1 s2 \<le> join s1' s2'"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob tf join sigma1 ps \<le> side_glob tf join sigma2 ps"
proof (induction ps)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  define su1 su2 where
    "su1 = join (sigma1 (Inl u)) (sigma1 (Inr ()))" and
    "su2 = join (sigma2 (Inl u)) (sigma2 (Inr ()))"
  have su_le: "su1 \<le> su2"
    using join_mono sigma_le unfolding su1_def su2_def le_fun_def by auto
  have glob_le: "restrict_global (apply_tf tf a su1)
                  \<le> restrict_global (apply_tf tf a su2)"
    by (rule restrict_global_mono[OF tf_mono[OF su_le]])
  show ?case unfolding ua
    using sup_mono[OF Cons.IH glob_le] by (simp only: side_glob.simps)
qed

lemma side_glob_mono_sup:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and sigma1 sigma2 :: "pp + unit \<Rightarrow> 'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  assumes sigma_le: "sigma1 \<le> sigma2"
  shows "side_glob tf (\<squnion>) sigma1 ps \<le> side_glob tf (\<squnion>) sigma2 ps"
  by (rule side_glob_mono[OF tf_mono _ sigma_le, where join="(\<squnion>)"])

(* Dependencies of side_rhs_fold trees depend only on the edge list, not sigma. *)
lemma dep_aux_side_rhs_fold_indep:
  "dep_aux sigma1 (side_rhs_fold tf join acc ps)
   = dep_aux sigma2 (side_rhs_fold tf join acc ps)"
proof (induction ps arbitrary: acc sigma1 sigma2)
  case Nil
  show ?case by simp
next
  case (Cons ua ps)
  obtain u a where ua: "ua = (u, a)" by (cases ua)
  show ?case unfolding ua by (simp add: Cons.IH)
qed


(* sides_of_rhs of the fold: all contributions land in the single global slot
   Inr (); the local slots receive nothing. *)
lemma sides_side_rhs_fold_Inr:
  "sides_of_rhs (side_rhs_fold tf join acc ps) sigma (Inr ()) = side_glob tf join sigma ps"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

lemma sides_side_rhs_fold_Inl:
  "sides_of_rhs (side_rhs_fold tf join acc ps) sigma (Inl u) = bot"
proof (induction ps arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons x ps)
  obtain w a where x: "x = (w, a)" by (cases x)
  show ?case unfolding x using Cons.IH by (simp add: Let_def)
qed

(* -- Monotonicity of side_cfg_T (TD_side solver precondition) ---------- *)

lemma side_cfg_T_is_mono_eq:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "is_mono_eq (side_cfg_T g tf (\<squnion>) bot0 s0)"
  unfolding is_mono_eq_def side_cfg_T_def
  apply clarify
  apply (subst eq_side_cfg_T)
  apply (rule side_acc_mono_sup[OF tf_mono])
  by simp

lemma side_cfg_T_mono_sides:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  assumes tf_mono:
    "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
  shows "mono_sides (side_cfg_T g tf (\<squnion>) bot0 s0)"
  unfolding mono_sides_def side_cfg_T_def make_side_rhs_tree_def Let_def
  apply clarify
  apply (rule le_funI)
  apply (case_tac x rule: sum.exhaust)
   apply (simp add: sides_side_rhs_fold_Inl)
  apply (simp add: sides_side_rhs_fold_Inr)
  apply (rule side_glob_mono_sup[OF tf_mono])
  apply simp

lemma side_cfg_T_mono_deps:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state"
  shows "mono_deps (side_cfg_T g tf (\<squnion>) bot0 s0)"
  unfolding mono_deps_def side_cfg_T_def make_side_rhs_tree_def Let_def dep_def
  apply clarify
  apply (subst (asm) dep_aux_side_rhs_fold_indep)
  by simp

(* -- Post-solution in usable form ------------------------------------ *)

(* Joining the local restriction of A with the global restriction of B is the
   abstract combine: locals from A, globals from B. *)
lemma restrict_combine:
  "restrict_local A \<squnion> restrict_global B = (\<lambda>x. if is_global x then B x else A x)"
  unfolding restrict_local_def restrict_global_def sup_fun_def by (rule ext) simp

(* A post-solution of side_cfg_T bounds, at every program point in scope, the
   local fold by the local unknown and the global contribution by the single
   global unknown. *)
lemma side_post_solution_le_local:
  assumes "part_post_solution (side_cfg_T g tf join bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_acc tf join
           (if v = cfg_entry g then join bot0 (restrict_local s0) else bot0)
           sigma (predecessor_list g v) \<le> sigma (Inl v)"
proof -
  from assms have "eq (side_cfg_T g tf join bot0 s0) v sigma \<le> sigma (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T)
qed

lemma side_post_solution_le_global:
  assumes "part_post_solution (side_cfg_T g tf join bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_glob tf join sigma (predecessor_list g v) \<le> sigma (Inr ())"
proof -
  from assms have "sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma \<le> sigma" by auto
  hence "sides_of_rhs (side_cfg_T g tf join bot0 s0 v) sigma (Inr ()) \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  thus ?thesis
    unfolding side_cfg_T_def make_side_rhs_tree_def
    by (simp add: sides_side_rhs_fold_Inr)
qed

(* -- Fold upper bounds (join = sup) ---------------------------------- *)

lemma side_acc_ge_acc:
  "acc \<le> side_acc tf (\<squnion>) acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x ps)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "acc \<le> side_acc tf (\<squnion>)
          (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma ps"
    by (meson Cons.IH sup_ge1 order_trans)
  then show ?case unfolding x by (simp only: side_acc.simps)
qed

(* Each incoming edge's local contribution is below the local fold. *)
lemma restrict_local_le_side_acc:
  "(u, a) \<in> set ps \<Longrightarrow>
   restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_acc tf (\<squnion>) acc sigma ps"
proof (induction ps arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x ps)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set ps" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_acc tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma ps"
      using side_acc_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x uw ab by (simp only: side_acc.simps)
  next
    case tl
    have "restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_acc tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma ps"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc.simps)
  qed
qed

(* Each incoming edge's global contribution is below the global join. *)
lemma restrict_global_le_side_glob:
  "(u, a) \<in> set ps \<Longrightarrow>
   restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_glob tf (\<squnion>) sigma ps"
proof (induction ps)
  case Nil thus ?case by simp
next
  case (Cons x ps)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set ps" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_glob tf (\<squnion>) sigma ps
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      by (rule sup_ge2)
    thus ?thesis unfolding x uw ab by (simp only: side_glob.simps)
  next
    case tl
    have "restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_glob tf (\<squnion>) sigma ps
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob.simps)
  qed
qed

(* -- Edge step: the combined env is closed under each edge transfer -- *)

(* The abstract state combined from the local unknown at v and the single
   global unknown. *)
definition side_env ::
  "(pp + unit => 'a::bounded_semilattice_sup_bot abs_state) => pp => 'a abs_state" where
  "side_env sigma v = sigma (Inl v) \<squnion> sigma (Inr ())"

(* For any CFG edge (u, a, v), a post-solution's combined env at u, transferred
   along a, is below the combined env at v.  This is the per-edge inductive step
   of the collecting-soundness bridge. *)
lemma apply_tf_combined_le:
  assumes pp:  "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> edges g"
      and fin: "finite (edges g)"
  shows "apply_tf tf a (side_env sigma u) \<le> side_env sigma v"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g v)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have loc: "restrict_local (apply_tf tf a (side_env sigma u)) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc[OF mem] side_post_solution_le_local[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (apply_tf tf a (side_env sigma u)) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob[OF mem] side_post_solution_le_global[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "apply_tf tf a (side_env sigma u)
        = restrict_local (apply_tf tf a (side_env sigma u))
          \<squnion> restrict_global (apply_tf tf a (side_env sigma u))"
    by (rule restrict_local_global_join[symmetric])
  also have "\<dots> \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* -- Collecting soundness of a side-effecting post-solution (M3) ------ *)

context sound_domain
begin

(*
  The combined env of a side_cfg_T post-solution soundly over-approximates the
  CFG collecting semantics at every program point reachable from the entry:
  along any path, the stores collected from S stay within the concretisation of
  the combined env.  Globals are tracked flow-insensitively (one global unknown,
  joined across all points), locals flow-sensitively.

  Assumptions: transfer-function soundness (assign/assume/assume-not); sigma is a
  partial post-solution over vars covering all program points; the initial set S
  is covered by the combined env at the entry.
*)
theorem side_collect_sound_path:
  fixes tf :: "'a domain_transfer"
    and sigma :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
  assumes vars_reach: "\<And>u es w. g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> w \<Longrightarrow> w \<in> vars"
  assumes fin: "finite (edges g)"
  assumes entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  assumes t_in: "t \<in> edges_collect es S"
  shows "t \<in> gamma_state (side_env sigma v)"
proof -
  have step_le: "\<And>x b y es'. g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v
     \<Longrightarrow> apply_tf tf b (side_env sigma x) \<le> side_env sigma y"
  proof -
    fix x b y es'
    assume p: "g \<turnstile> x \<longrightarrow>\<^bsub>(b, y) # es'\<^esub> v"
    obtain edge where edge: "(x, b, y) \<in> edges g"
      using p by (cases rule: cfg_stepE) auto
    have y_in: "y \<in> vars"
      using cfg_path_step_target[OF p] vars_reach by blast
    show "apply_tf tf b (side_env sigma x) \<le> side_env sigma y"
      by (rule apply_tf_combined_le[OF pp y_in edge fin])
  qed
  have collect: "edges_collect es (gamma_state (side_env sigma (cfg_entry g)))
                 \<subseteq> gamma_state (side_env sigma v)"
    by (rule edges_collect_gamma_path_aux[OF fin path step_le tf_sound_assign
          tf_sound_assume tf_sound_assume_not])
  have "edges_collect es S
        \<subseteq> edges_collect es (gamma_state (side_env sigma (cfg_entry g)))"
    by (rule edges_collect_mono_strong[OF entry])
  thus ?thesis using collect t_in by blast
qed

(* Subset form: any store collected at v lies in the side env at v. *)
corollary side_collect_sound_at:
  fixes tf :: "'a domain_transfer"
    and sigma :: "pp + unit => 'a abs_state"
    and bot0 s0 :: "'a abs_state"
  assumes tf_sound_assign:
    "\<forall>x a sg. \<forall>s \<in> gamma_state sg.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sg)"
  assumes tf_sound_assume:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sg)"
  assumes tf_sound_assume_not:
    "\<forall>b sg. \<forall>s \<in> gamma_state sg. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sg)"
  assumes pp: "part_post_solution (side_cfg_T g tf (\<squnion>) bot0 s0) x sigma vars"
  assumes vars_reach: "\<And>u es w. g \<turnstile> u \<longrightarrow>\<^bsub>es\<^esub> w \<Longrightarrow> w \<in> vars"
  assumes fin: "finite (edges g)"
  assumes entry: "S \<subseteq> gamma_state (side_env sigma (cfg_entry g))"
  assumes path: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>es\<^esub> v"
  shows "cfg_collect g S v \<le> gamma_state (side_env sigma v)"
proof -
  have paths: "cfg_collect g S v \<subseteq> cfg_collect_paths g S v"
    by (rule cfg_collect_le_paths)
  show ?thesis
  proof
    fix t
    assume "t \<in> cfg_collect g S v"
    with paths have "t \<in> cfg_collect_paths g S v" by blast
    then obtain path_es where path_es: "g \<turnstile> (cfg_entry g) \<longrightarrow>\<^bsub>path_es\<^esub> v"
      and t_in: "t \<in> edges_collect path_es S"
      unfolding cfg_collect_paths_def by blast
    show "t \<in> gamma_state (side_env sigma v)"
      by (rule side_collect_sound_path[OF tf_sound_assign tf_sound_assume
            tf_sound_assume_not pp vars_reach fin entry path_es t_in])
  qed
qed

end

end
