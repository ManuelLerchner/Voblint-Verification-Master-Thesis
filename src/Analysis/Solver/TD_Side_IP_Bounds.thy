theory TD_Side_IP_Bounds
  imports TD_Side_IP_Mono
begin

(*
  Post-solution bounds: the facts the soundness layer consumes.

  A post-solution of side_cfg_T_ip bounds, at every program point in scope, the
  local fold by the local unknown and the global contribution by the single
  global unknown.  Includes edge / combine closure (apply_tf_combined_le_ip,
  combine_combined_le_ip), dependency membership, and entry coverage
  (s0_le_side_env_entry_ip).  Construction: TD_Side_IP_Tree.  Monotonicity /
  solver preconditions: TD_Side_IP_Mono.
*)

(* -- Post-solution in usable form ------------------------------------- *)

(* A post-solution of side_cfg_T_ip bounds, at every program point in scope,
   the local fold by the local unknown and the global contribution by the
   single global unknown. *)
lemma side_post_solution_le_local_ip:
  assumes "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_acc_ip tf (\<squnion>)
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           sigma (predecessor_list g v) (combine_predecessor_list g v) \<le> sigma (Inl v)"
proof -
  from assms have "eq (side_cfg_T_ip g tf (\<squnion>) bot0 s0) v sigma \<le> sigma (Inl v)" by auto
  thus ?thesis by (simp add: eq_side_cfg_T_ip)
qed

lemma side_post_solution_le_global_ip:
  assumes "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and "v \<in> vars"
  shows "side_glob_ip tf (\<squnion>) sigma (predecessor_list g v) (combine_predecessor_list g v)
         \<le> sigma (Inr ())"
proof -
  from assms have "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma \<le> sigma" by auto
  hence le: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma (Inr ()) \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "side_glob_ip tf (\<squnion>) sigma (predecessor_list g v) (combine_predecessor_list g v)
        \<le> sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 v) sigma (Inr ())"
    unfolding side_cfg_T_ip_def
    by (simp add: sides_make_side_rhs_tree_ip_Inr)
  thus ?thesis using le by (rule order_trans)
qed

(* -- Fold upper bounds (join = sup) ----------------------------------- *)

lemma side_acc_ip_ge_acc:
  "acc \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc cs)
  case Nil
  show ?case
  proof (induction cs arbitrary: acc)
    case Nil show ?case by simp
  next
    case (Cons x cs)
    obtain cc ex where x: "x = (cc, ex)" by (cases x)
    have "acc \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))) sigma [] cs"
      by (meson Cons.IH sup_ge1 order_trans)
    then show ?case unfolding x by (simp only: side_acc_ip.simps)
  qed
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "acc \<le> side_acc_ip tf (\<squnion>)
          (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma es cs"
    by (meson Cons.IH sup_ge1 order_trans)
  then show ?case unfolding x by (simp only: side_acc_ip.simps)
qed

(* The local fold grows monotonically as more incoming edges are processed. *)
lemma side_acc_ip_es_mono:
  "side_acc_ip tf (\<squnion>) acc sigma [] cs \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "side_acc_ip tf (\<squnion>) acc sigma [] cs
        \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma [] cs"
    by (rule side_acc_ip_mono_acc[OF sup_mono sup_ge1])
  also have "... \<le> side_acc_ip tf (\<squnion>)
            (acc \<squnion> restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))) sigma es cs"
    by (rule Cons.IH)
  finally show ?case unfolding x by (simp only: side_acc_ip.simps)
qed

(* Each incoming edge's local contribution is below the local fold. *)
lemma restrict_local_le_side_acc_ip_edge:
  "(u, a) \<in> set es \<Longrightarrow>
   restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set es" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma es cs"
      using side_acc_ip_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x uw ab by (simp only: side_acc_ip.simps)
  next
    case tl
    have "restrict_local (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ()))))
               sigma es cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_ip.simps)
  qed
qed

(* Each incoming combine's local contribution (caller locals) is below the
   local fold (edge list exhausted). *)
lemma restrict_local_le_side_acc_ip_combine_nil:
  "(cc, ex) \<in> set cs \<Longrightarrow>
   restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
     \<le> side_acc_ip tf (\<squnion>) acc sigma [] cs"
proof (induction cs arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
  from Cons.prems x consider (hd) "(cc, ex) = (c2, e2)" | (tl) "(cc, ex) \<in> set cs" by auto
  then show ?case
  proof cases
    case hd
    then have cc2: "cc = c2" and exe2: "ex = e2" by auto
    have "restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))) sigma [] cs"
      using side_acc_ip_ge_acc sup_ge2 order_trans by blast
    thus ?thesis unfolding x cc2 exe2 by (simp only: side_acc_ip.simps)
  next
    case tl
    have "restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
          \<le> side_acc_ip tf (\<squnion>)
               (acc \<squnion> restrict_local (sigma (Inl c2) \<squnion> sigma (Inr ()))) sigma [] cs"
      by (rule Cons.IH[OF tl])
    thus ?thesis unfolding x by (simp only: side_acc_ip.simps)
  qed
qed

lemma restrict_local_le_side_acc_ip_combine:
  assumes "(cc, ex) \<in> set cs"
  shows "restrict_local (sigma (Inl cc) \<squnion> sigma (Inr ()))
         \<le> side_acc_ip tf (\<squnion>) acc sigma es cs"
  using restrict_local_le_side_acc_ip_combine_nil[OF assms] side_acc_ip_es_mono
  by (rule order_trans)

(* Global fold analogues. *)
lemma side_glob_ip_es_mono:
  "side_glob_ip tf (\<squnion>) sigma [] cs \<le> side_glob_ip tf (\<squnion>) sigma es cs"
proof (induction es)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain u a where x: "x = (u, a)" by (cases x)
  have "side_glob_ip tf (\<squnion>) sigma [] cs \<le> side_glob_ip tf (\<squnion>) sigma es cs"
    by (rule Cons.IH)
  also have "... \<le> side_glob_ip tf (\<squnion>) sigma es cs
                     \<squnion> restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))"
    by (rule sup_ge1)
  finally show ?case unfolding x by (simp only: side_glob_ip.simps)
qed

lemma restrict_global_le_side_glob_ip_edge:
  "(u, a) \<in> set es \<Longrightarrow>
   restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
     \<le> side_glob_ip tf (\<squnion>) sigma es cs"
proof (induction es)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  from Cons.prems x consider (hd) "(u, a) = (w, b)" | (tl) "(u, a) \<in> set es" by auto
  then show ?case
  proof cases
    case hd
    then have uw: "u = w" and ab: "a = b" by auto
    have "restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))
          \<le> side_glob_ip tf (\<squnion>) sigma es cs
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      by (rule sup_ge2)
    thus ?thesis unfolding x uw ab by (simp only: side_glob_ip.simps)
  next
    case tl
    have "restrict_global (apply_tf tf a (sigma (Inl u) \<squnion> sigma (Inr ())))
          \<le> side_glob_ip tf (\<squnion>) sigma es cs
               \<squnion> restrict_global (apply_tf tf b (sigma (Inl w) \<squnion> sigma (Inr ())))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob_ip.simps)
  qed
qed

lemma restrict_global_le_side_glob_ip_combine_nil:
  "(cc, ex) \<in> set cs \<Longrightarrow>
   restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
     \<le> side_glob_ip tf (\<squnion>) sigma [] cs"
proof (induction cs)
  case Nil thus ?case by simp
next
  case (Cons x cs)
  obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
  from Cons.prems x consider (hd) "(cc, ex) = (c2, e2)" | (tl) "(cc, ex) \<in> set cs" by auto
  then show ?case
  proof cases
    case hd
    then have exe2: "ex = e2" by auto
    have "restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))
          \<le> side_glob_ip tf (\<squnion>) sigma [] cs
               \<squnion> restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))"
      by (rule sup_ge2)
    thus ?thesis unfolding x exe2 by (simp only: side_glob_ip.simps)
  next
    case tl
    have "restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
          \<le> side_glob_ip tf (\<squnion>) sigma [] cs
               \<squnion> restrict_global (sigma (Inl e2) \<squnion> sigma (Inr ()))"
      using Cons.IH[OF tl] by (rule le_supI1)
    thus ?thesis unfolding x by (simp only: side_glob_ip.simps)
  qed
qed

lemma restrict_global_le_side_glob_ip_combine:
  assumes "(cc, ex) \<in> set cs"
  shows "restrict_global (sigma (Inl ex) \<squnion> sigma (Inr ()))
         \<le> side_glob_ip tf (\<squnion>) sigma es cs"
  using restrict_global_le_side_glob_ip_combine_nil[OF assms] side_glob_ip_es_mono
  by (rule order_trans)

(* -- Edge / combine closure of a side post-solution ------------------- *)

(* For any CFG edge (u, a, v), a post-solution's combined env at u, transferred
   along a, is below the combined env at v. *)
lemma apply_tf_combined_le_ip:
  assumes pp:  "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:   "v \<in> vars"
      and e:   "(u, a, v) \<in> edges g"
      and fin: "finite (edges g)"
  shows "apply_tf tf a (side_env sigma u) \<le> side_env sigma v"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g v)"
    using e by (simp add: set_predecessor_list[OF fin] predecessors_def)
  have loc: "restrict_local (apply_tf tf a (side_env sigma u)) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc_ip_edge[OF mem] side_post_solution_le_local_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (apply_tf tf a (side_env sigma u)) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob_ip_edge[OF mem] side_post_solution_le_global_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "apply_tf tf a (side_env sigma u)
        = restrict_local (apply_tf tf a (side_env sigma u))
          \<squnion> restrict_global (apply_tf tf a (side_env sigma u))"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* For any combine triple (c, ex, v), the abstract combine of the post-solution's
   combined envs at the caller c and the callee exit ex is below the combined env
   at the return point v. *)
lemma combine_combined_le_ip:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and bot0 s0 :: "'a abs_state" and sigma :: "pp + unit \<Rightarrow> 'a abs_state"
    and c ex v :: pp
  assumes pp:   "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and v:    "v \<in> vars"
      and e:    "(c, ex, v) \<in> combines g"
      and finC: "finite (combines g)"
  shows "combine_abs (side_env sigma c) (side_env sigma ex) \<le> side_env sigma v"
proof -
  have mem: "(c, ex) \<in> set (combine_predecessor_list g v)"
    using e by (simp add: set_combine_predecessor_list[OF finC] combine_predecessors_def)
  have loc: "restrict_local (side_env sigma c) \<le> sigma (Inl v)"
    using restrict_local_le_side_acc_ip_combine[OF mem] side_post_solution_le_local_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have glob: "restrict_global (side_env sigma ex) \<le> sigma (Inr ())"
    using restrict_global_le_side_glob_ip_combine[OF mem] side_post_solution_le_global_ip[OF pp v]
    unfolding side_env_def by (rule order_trans)
  have "combine_abs (side_env sigma c) (side_env sigma ex)
        = restrict_local (side_env sigma c) \<squnion> restrict_global (side_env sigma ex)"
    by (simp add: combine_abs_def restrict_combine)
  also have "... \<le> sigma (Inl v) \<squnion> sigma (Inr ())"
    using loc glob by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

(* -- Dependency membership (edges and combine endpoints) -------------- *)

lemma Inl_dep_aux_side_rhs_fold_ip_edge:
  assumes "(u, a) \<in> set es"
  shows "Inl u \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
  using assms
proof (induction es arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  show ?case
  proof (cases "x = (u, a)")
    case True
    thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
  next
    case False
    have mem: "(u, a) \<in> set es" using Cons.prems x False by auto
    show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
      using Cons.IH[OF mem] by simp
  qed
qed

(* The dependencies reachable after the edge list is exhausted (the combine
   queries) survive the edge prefix. *)
lemma dep_aux_side_rhs_fold_ip_nil_sub_es:
  "dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)
   \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof (induction es arbitrary: acc)
  case Nil show ?case by simp
next
  case (Cons x es)
  obtain w b where x: "x = (w, b)" by (cases x)
  let ?acc' = "join acc (restrict_local (apply_tf tf b (join (sigma (Inl w)) (sigma (Inr ())))))"
  have "dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)
        = dep_aux sigma (side_rhs_fold_ip tf join ?acc' [] cs)"
    by (rule dep_aux_side_rhs_fold_ip_acc_indep)
  also have "... \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join ?acc' es cs)"
    by (rule Cons.IH)
  also have "... \<subseteq> dep_aux sigma (side_rhs_fold_ip tf join acc (x # es) cs)"
    unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def by auto
  finally show ?case .
qed

lemma Inl_dep_aux_side_rhs_fold_ip_call:
  fixes c ex :: pp
  assumes "(c, ex) \<in> set cs"
  shows "Inl c \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof -
  have "Inl c \<in> dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)"
    using assms
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "x = (c, ex)")
      case True
      thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
    next
      case False
      have mem: "(c, ex) \<in> set cs" using Cons.prems x False by auto
      show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
        using Cons.IH[OF mem] by simp
    qed
  qed
  thus ?thesis using dep_aux_side_rhs_fold_ip_nil_sub_es by blast
qed

lemma Inl_dep_aux_side_rhs_fold_ip_exit:
  fixes c ex :: pp
  assumes "(c, ex) \<in> set cs"
  shows "Inl ex \<in> dep_aux sigma (side_rhs_fold_ip tf join acc es cs)"
proof -
  have "Inl ex \<in> dep_aux sigma (side_rhs_fold_ip tf join acc [] cs)"
    using assms
  proof (induction cs arbitrary: acc)
    case Nil thus ?case by simp
  next
    case (Cons x cs)
    obtain c2 e2 where x: "x = (c2, e2)" by (cases x)
    show ?case
    proof (cases "x = (c, ex)")
      case True
      thus ?thesis unfolding True side_rhs_fold_ip.simps dep_aux.simps Let_def by simp
    next
      case False
      have mem: "(c, ex) \<in> set cs" using Cons.prems x False by auto
      show ?thesis unfolding x side_rhs_fold_ip.simps dep_aux.simps Let_def
        using Cons.IH[OF mem] by simp
    qed
  qed
  thus ?thesis using dep_aux_side_rhs_fold_ip_nil_sub_es by blast
qed

(* -- Dependency at the eqsT level (edges and combine endpoints) ------- *)

lemma dep_side_rhs_tree_ip_edge:
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  shows "u \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using ed fin by (auto simp: predecessors_def set_predecessor_list)
  have "Inl u \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_edge[OF mem])
  thus ?thesis unfolding side_cfg_T_ip_def dep\<^sub>L_def dep_def by simp
qed

lemma dep_side_rhs_tree_ip_combine:
  fixes g :: cfg and c ex w :: pp
  assumes finC: "finite (combines g)"
  assumes ce: "(c, ex, w) \<in> combines g"
  shows "c \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w
       \<and> ex \<in> dep\<^sub>L (side_cfg_T_ip g tf join bot0 s0) sigma w"
proof -
  have mem: "(c, ex) \<in> set (combine_predecessor_list g w)"
    using ce finC by (simp add: combine_predecessors_def)
  have dc: "Inl c \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_call[OF mem])
  have de: "Inl ex \<in> dep_aux sigma (make_side_rhs_tree_ip g tf join bot0 s0 w)"
    unfolding dep_aux_make_side_rhs_tree_ip
    by (rule Inl_dep_aux_side_rhs_fold_ip_exit[OF mem])
  show ?thesis using dc de unfolding side_cfg_T_ip_def dep\<^sub>L_def dep_def by simp
qed

(* -- Entry coverage from an arbitrary initial state ------------------- *)

(* The entry node's wrapping Side () contributes restrict_global s0 to the
   single global unknown, so the initial globals are below it in any
   post-solution. *)
lemma restrict_global_s0_le_global_ip:
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot0 s0) x sigma vars"
      and entry_in: "cfg_entry g \<in> vars"
  shows "restrict_global s0 \<le> sigma (Inr ())"
proof -
  from pp entry_in have "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma \<le> sigma"
    by auto
  hence le: "sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())
             \<le> sigma (Inr ())"
    by (simp add: le_fun_def)
  have "restrict_global s0
        \<le> side_glob_ip tf (\<squnion>) sigma
             (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))
           \<squnion> restrict_global s0"
    by (rule sup_ge2)
  also have "... = sides_of_rhs (side_cfg_T_ip g tf (\<squnion>) bot0 s0 (cfg_entry g)) sigma (Inr ())"
    unfolding side_cfg_T_ip_def by (simp add: sides_make_side_rhs_tree_ip_Inr)
  also have "... \<le> sigma (Inr ())" by (rule le)
  finally show ?thesis .
qed

(* At the entry point the local fold seeds restrict_local s0 and the wrapping
   Side () seeds restrict_global s0, so s0 itself is below the combined env at
   the entry -- for an arbitrary initial state, no globals-free hypothesis. *)
lemma s0_le_side_env_entry_ip:
  assumes pp: "part_post_solution (side_cfg_T_ip g tf (\<squnion>) bot s0) v0 sigma vars"
  assumes entry_in: "cfg_entry g \<in> vars"
  shows "s0 \<le> side_env sigma (cfg_entry g)"
proof -
  have acc_le: "side_acc_ip tf (\<squnion>) (bot \<squnion> restrict_local s0) sigma
                  (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))
                \<le> sigma (Inl (cfg_entry g))"
    using side_post_solution_le_local_ip[OF pp entry_in] by simp
  have "restrict_local s0 \<le> bot \<squnion> restrict_local s0" by simp
  also have "... \<le> side_acc_ip tf (\<squnion>) (bot \<squnion> restrict_local s0) sigma
                     (predecessor_list g (cfg_entry g)) (combine_predecessor_list g (cfg_entry g))"
    by (rule side_acc_ip_ge_acc)
  also have "... \<le> sigma (Inl (cfg_entry g))" by (rule acc_le)
  finally have rl: "restrict_local s0 \<le> sigma (Inl (cfg_entry g))" .
  have rg: "restrict_global s0 \<le> sigma (Inr ())"
    by (rule restrict_global_s0_le_global_ip[OF pp entry_in])
  have "s0 = restrict_local s0 \<squnion> restrict_global s0"
    by (rule restrict_local_global_join[symmetric])
  also have "... \<le> sigma (Inl (cfg_entry g)) \<squnion> sigma (Inr ())"
    using rl rg by (rule sup_mono)
  finally show ?thesis unfolding side_env_def .
qed

end
