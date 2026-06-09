theory TD_CFG_IP_Core
  imports TD_CFG_Core
begin

(*
  Interprocedural TD bridge (M1 slice 4).

  Extends make_rhs_tree with combine_predecessor_list queries so traverse_rhs
  matches rhs_ip.  Solver stays TD_plain.
*)

definition make_rhs_ip ::
    "cfg
     => 'a::ord domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => (pp => 'a abs_state) => 'a abs_state"
where
  "make_rhs_ip g tf join_abs bot_abs s0 v env =
     rhs_ip g tf join_abs bot_abs s0 env v"

fun ip_rhs_tree ::
    "'a::bounded_semilattice_sup_bot domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => (pp * edge_action) list
     => (pp * pp) list
     => (pp, 'a abs_state) strategy_tree"
where
  "ip_rhs_tree tf join comb acc [] [] = Answer acc"
| "ip_rhs_tree tf join comb acc ((u, a) # es) cs =
     Query u (\<lambda>su. ip_rhs_tree tf join comb (join acc (apply_tf tf a su)) es cs)"
| "ip_rhs_tree tf join comb acc [] ((c, e) # cs) =
     Query c (\<lambda>sc. Query e (\<lambda>se.
       ip_rhs_tree tf join comb (join acc (comb sc se)) [] cs))"

definition make_rhs_tree_ip ::
    "cfg
     => 'a::bounded_semilattice_sup_bot domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp
     => (pp, 'a abs_state) strategy_tree"
where
  "make_rhs_tree_ip g tf join_abs bot_abs s0 v =
     (let acc0 = (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)
      in ip_rhs_tree tf join_abs combine_abs acc0
           (predecessor_list g v) (combine_predecessor_list g v))"

lemma ip_rhs_tree_traverse_env_map:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join comb :: "'a abs_state => 'a abs_state => 'a abs_state"
    and env :: "pp => 'a abs_state" and acc :: "'a abs_state"
  shows "traverse_rhs (ip_rhs_tree tf join comb acc es cs) (env_map env) =
         fold (\<lambda>(c, e) st. join st (comb (env c) (env e))) cs
           (fold (\<lambda>(u, a) st. join st (apply_tf tf a (env u))) es acc)"
proof (induct es arbitrary: acc cs)
  case Nil
  show ?case proof (induct cs arbitrary: acc)
    case Nil
    show ?case by (simp add: ip_rhs_tree.simps)
  next
    case (Cons ce cs')
    obtain c e where ce: "ce = (c, e)" by (cases ce) auto
    have ih: "traverse_rhs (ip_rhs_tree tf join comb (join acc (comb (env c) (env e))) [] cs')
            (env_map env) =
           fold (\<lambda>(c', e') st. join st (comb (env c') (env e'))) cs'
             (join acc (comb (env c) (env e)))"
      using Cons by simp
    show ?case
    proof -
      have "traverse_rhs (ip_rhs_tree tf join comb acc [] (ce # cs')) (env_map env) =
            traverse_rhs (ip_rhs_tree tf join comb (join acc (comb (env c) (env e))) [] cs')
             (env_map env)"
        by (simp add: ce ip_rhs_tree.simps)
      also have "\<dots> = fold (\<lambda>(c', e') st. join st (comb (env c') (env e'))) cs'
             (join acc (comb (env c) (env e)))"
        using ih by simp
      also have "\<dots> = fold (\<lambda>(c', e') st. join st (comb (env c') (env e'))) (ce # cs') acc"
        by (simp add: ce)
      finally show ?case by simp
    qed
  qed
next
  case (Cons p ps)
  obtain u a where p: "p = (u, a)" by (cases p) auto
  have ih: "traverse_rhs (ip_rhs_tree tf join comb (join acc (apply_tf tf a (env u))) ps cs)
            (env_map env) =
           fold (\<lambda>(c, e) st. join st (comb (env c) (env e))) cs
             (fold (\<lambda>(u', a') st. join st (apply_tf tf a' (env u'))) ps
               (join acc (apply_tf tf a (env u))))"
    using Cons by simp
  show ?case
  proof -
    have "traverse_rhs (ip_rhs_tree tf join comb acc (p # ps) cs) (env_map env) =
          traverse_rhs (ip_rhs_tree tf join comb (join acc (apply_tf tf a (env u))) ps cs)
           (env_map env)"
      by (simp add: p ip_rhs_tree.simps)
    also have "\<dots> = fold (\<lambda>(c, e) st. join st (comb (env c) (env e))) cs
             (fold (\<lambda>(u', a') st. join st (apply_tf tf a' (env u'))) ps
               (join acc (apply_tf tf a (env u))))"
      using ih by simp
    also have "\<dots> = fold (\<lambda>(c, e) st. join st (comb (env c) (env e))) cs
             (fold (\<lambda>(u', a') st. join st (apply_tf tf a' (env u'))) (p # ps) acc)"
      by (simp add: p)
    finally show ?case by simp
  qed
qed

lemma fold_join_abs_swap_combine_steps:
  fixes join :: "'a::bounded_semilattice_sup_bot abs_state => _ => _"
    and comb :: "'a abs_state => 'a abs_state => 'a abs_state"
    and env :: "pp => 'a abs_state"
  assumes join_sym: "\<And>x y. join x y = join y x"
  shows "fold (\<lambda>(c, e) st. join st (comb (env c) (env e))) cs acc =
         fold (\<lambda>(c, e) st. join (comb (env c) (env e)) st) cs acc"
proof (induct cs arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons ce cs)
  obtain c e where ce: "ce = (c, e)" by (cases ce) auto
  show ?case
    unfolding ce
    using Cons[of "join acc (comb (env c) (env e))"] join_sym by simp
qed

lemma rhs_ip_eq_fold_predecessor_lists:
  fixes g v tf join_abs bot_abs s0
  fixes env :: "pp => 'a::bounded_semilattice_sup_bot abs_state"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a abs_state => 'a abs_state => 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "rhs_ip g tf join_abs bot_abs s0 env v =
         fold (\<lambda>(c, e) acc. join_abs (combine_abs (env c) (env e)) acc)
              (combine_predecessor_list g v)
              (fold (\<lambda>(u, a) acc. join_abs (apply_tf tf a (env u)) acc)
                    (predecessor_list g v)
                    (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs))"
proof -
  define acc0 where
    "acc0 = (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
  define edge_acc where
    "edge_acc = fold (\<lambda>(u, a) acc. join_abs (apply_tf tf a (env u)) acc)
                      (predecessor_list g v) acc0"
  define P where "P = predecessors g v"
  define C where "C = combine_predecessors g v"
  define fv where "fv = image (\<lambda>(u, a). apply_tf tf a (env u)) P"
  define cv where "cv = image (\<lambda>(c, e). combine_abs (env c) (env e)) C"
  have finP: "finite P" using fin by (simp add: P_def finite_predecessors)
  have finCset: "finite C" using finC by (simp add: C_def finite_combine_predecessors)
  have set_edge: "set (predecessor_list g v) = P"
    using set_predecessor_list[OF fin] unfolding P_def predecessors_def by auto
  have set_comb: "set (combine_predecessor_list g v) = C"
    using set_combine_predecessor_list[OF finC] unfolding C_def by simp
  have edge_acc_eq: "edge_acc = rhs g tf join_abs bot_abs s0 env v"
    unfolding edge_acc_def acc0_def
    using rhs_eq_fold_predecessor_list[OF fin cfi join_sym] by simp
  have edge_abs: "edge_acc = abs_join_set join_abs bot_abs
        (if v = cfg_entry g then insert s0 fv else fv)"
    unfolding edge_acc_eq rhs_def Let_def P_def fv_def predecessors_def by simp
  interpret j: comp_fun_idem join_abs by (fact cfi)
  have comb_fold: "fold (\<lambda>(c, e) acc. join_abs (combine_abs (env c) (env e)) acc)
        (combine_predecessor_list g v) edge_acc =
        abs_join_set join_abs edge_acc cv"
  proof -
    have set_map:
      "set (map (\<lambda>(c, e). combine_abs (env c) (env e)) (combine_predecessor_list g v)) = cv"
      using set_comb unfolding cv_def C_def by auto
    show ?thesis
    proof -
      have list_fold:
        "fold (\<lambda>(c, e) acc. join_abs (combine_abs (env c) (env e)) acc)
          (combine_predecessor_list g v) edge_acc =
         fold (\<lambda>x acc. join_abs x acc)
          (map (\<lambda>(c, e). combine_abs (env c) (env e)) (combine_predecessor_list g v))
          edge_acc"
        by (metis (mono_tags, lifting) List.fold_cong fold_join_apply_edges_eq_fold_join_over_map
            old.prod.case prod.exhaust)
      also have "\<dots> = Finite_Set.fold join_abs edge_acc cv"
        unfolding abs_join_set_def cv_def C_def set_map
        by (metis C_def cv_def j.fold_set_fold local.set_map)
      finally show ?thesis unfolding abs_join_set_def .
    qed
  qed
  have rhs_ip_abs: "rhs_ip g tf join_abs bot_abs s0 env v =
        abs_join_set join_abs bot_abs
          (if v = cfg_entry g then insert s0 (fv \<union> cv) else fv \<union> cv)"
    unfolding rhs_ip_def Let_def abs_join_set_def P_def C_def fv_def cv_def
      combine_predecessors_def predecessors_def by simp
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have fin_fv: "finite fv"
      by (simp add: finP fv_def)
    have fin_cv: "finite cv" using finCset unfolding cv_def by simp
    have edge_entry: "edge_acc = abs_join_set join_abs bot_abs (insert s0 fv)"
      using edge_abs True by simp
    have union_fold:
      "abs_join_set join_abs bot_abs (insert s0 (fv \<union> cv)) =
       abs_join_set join_abs edge_acc cv"
      unfolding edge_entry abs_join_set_def comb_fold[symmetric]
      by (metis Un_insert_left abs_join_set_def abs_join_set_union cfi fin_cv fin_fv(1)
          finite.insertI)
    show ?thesis unfolding rhs_ip_abs comb_fold edge_acc_def acc0_def True
      using union_fold
      using True acc0_def comb_fold edge_acc_def rhs_ip_abs by argo 
  next
    case False
    have fin_fv: "finite fv" using finP unfolding fv_def by simp
    have fin_cv: "finite cv" using finCset unfolding cv_def by simp
    have edge_none: "edge_acc = abs_join_set join_abs bot_abs fv"
      using edge_abs False by simp
    have union_fold:
      "abs_join_set join_abs bot_abs (fv \<union> cv) =
       abs_join_set join_abs edge_acc cv"
      unfolding edge_none abs_join_set_def comb_fold[symmetric]
      using cfi comp_fun_idem_fold_union fin_cv fin_fv by blast
    show ?thesis unfolding rhs_ip_abs comb_fold edge_acc_def acc0_def False
      using union_fold
      using False acc0_def comb_fold edge_acc_def by fastforce  
  qed
qed

lemma make_rhs_tree_ip_correspondence:
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a::bounded_semilattice_sup_bot abs_state => _ => _)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v) (env_map env) =
         make_rhs_ip g tf join_abs bot_abs s0 v env"
proof -
  have tr: "traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v) (env_map env) =
        fold (\<lambda>(c, e) st. join_abs st (combine_abs (env c) (env e)))
             (combine_predecessor_list g v)
             (fold (\<lambda>(u, a) st. join_abs st (apply_tf tf a (env u)))
               (predecessor_list g v)
               (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs))"
    unfolding make_rhs_tree_ip_def Let_def
    by (simp add: ip_rhs_tree_traverse_env_map)
  also have "\<dots> =
        fold (\<lambda>(c, e) acc. join_abs (combine_abs (env c) (env e)) acc)
             (combine_predecessor_list g v)
             (fold (\<lambda>(u, a) acc. join_abs (apply_tf tf a (env u)) acc)
               (predecessor_list g v)
               (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs))"
  proof -
    show ?thesis
      apply (subst fold_join_abs_swap_combine_steps[OF join_sym])
      apply (subst fold_join_abs_swap_edge_steps[OF join_sym])
      apply(auto)
      done
  qed
  also have "\<dots> = rhs_ip g tf join_abs bot_abs s0 env v"
  proof (cases "v = cfg_entry g")
    case True
    then show ?thesis
      using rhs_ip_eq_fold_predecessor_lists[OF fin finC cfi join_sym] by simp
  next
    case False
    then show ?thesis
      using rhs_ip_eq_fold_predecessor_lists[OF fin finC cfi join_sym] by simp
  qed
  finally show ?thesis unfolding make_rhs_ip_def by simp
qed

lemma rhs_ip_make_rhs_tree_ip_traverse_mlup:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs bot_abs s0 v
    and \<sigma> :: "(pp, 'a abs_state) map"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a abs_state => 'a abs_state => 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v =
         traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma>"
proof -
  have "traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma> =
        traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v)
         (env_map (\<lambda>w. mlup \<sigma> w))"
    by (rule traverse_rhs_mlup_eq) (simp add: mlup_env_map_of_mlup)
  also have "\<dots> = make_rhs_ip g tf join_abs bot_abs s0 v (\<lambda>w. mlup \<sigma> w)"
    by (rule make_rhs_tree_ip_correspondence[OF fin finC cfi join_sym])
  also have "\<dots> = rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v"
    by (simp add: make_rhs_ip_def)
  finally show ?thesis ..
qed

lemma eq_le_mlup_imp_rhs_ip_le:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state => 'a abs_state => 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
    and T :: "pp => (pp, 'a abs_state) strategy_tree"
    and \<sigma> :: "(pp, 'a abs_state) map" and v :: pp
  assumes T_mk: "\<And>w. T w = make_rhs_tree_ip g tf join_abs bot_abs s0 w"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes le: "(eq T) v \<sigma> \<le> mlup \<sigma> v"
  shows "rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. lookup_bot \<sigma> w) v
         \<le> lookup_bot \<sigma> v"
proof -
  have "rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. lookup_bot \<sigma> w) v =
        rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v"
    by (simp add: fun_eq_iff lookup_bot_mlup)
  also have "\<dots> = traverse_rhs (T v) \<sigma>"
  proof -
    have "rhs_ip g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v =
          traverse_rhs (make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma>"
      by (rule rhs_ip_make_rhs_tree_ip_traverse_mlup[OF fin finC cfi join_sym])
    thus ?thesis unfolding T_mk by simp
  qed
  also have "traverse_rhs (T v) \<sigma> = (eq T) v \<sigma>"
    by (simp add: eq_def)
  also have "\<dots> \<le> mlup \<sigma> v"
    using le by simp
  finally show ?thesis by (simp add: lookup_bot_mlup)
qed

lemma cfg_env_post_fixpoint_ip:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state => 'a abs_state => 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
    and T :: "pp => (pp, 'a abs_state) strategy_tree"
    and env :: "pp => 'a abs_state" and \<sigma> :: "(pp, 'a abs_state) map"
  assumes T_mk: "\<And>w. T w = make_rhs_tree_ip g tf join_abs bot_abs s0 w"
  assumes fin: "finite (edges g)"
  assumes finC: "finite (combines g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes env_def: "\<And>w. env w = lookup_bot \<sigma> w"
  assumes eq_le: "\<And>v. (eq T) v \<sigma> \<le> mlup \<sigma> v"
  shows "is_post_fixpoint_ip g tf join_abs bot_abs s0 env"
  unfolding is_post_fixpoint_ip_def
proof (intro allI)
  fix v
  show "rhs_ip g tf join_abs bot_abs s0 env v \<le> env v"
  proof -
    have "rhs_ip g tf join_abs bot_abs s0 env v \<le> lookup_bot \<sigma> v"
      using eq_le_mlup_imp_rhs_ip_le[OF T_mk fin finC cfi join_sym eq_le] env_def by presburger
    thus ?thesis using env_def by simp
  qed
qed

lemma dep_ip_rhs_tree_pred:
  shows "(u, a) \<in> set es \<Longrightarrow> u \<in> dep_aux \<sigma> (ip_rhs_tree tf join comb acc es cs)"
  by (induct es arbitrary: acc cs; auto simp: ip_rhs_tree.simps dep_aux.simps split: prod.splits)

lemma cfg_edges_list_edges_cong:
  assumes fin: "finite (edges g1)"
  assumes eq: "edges g1 = edges g2"
  shows "cfg_edges_list g1 = cfg_edges_list g2"
  unfolding cfg_edges_list_def using fin eq by simp

lemma predecessor_list_edges_cong:
  assumes fin: "finite (edges g1)"
  assumes eq: "edges g1 = edges g2"
  shows "predecessor_list g1 v = predecessor_list g2 v"
proof -
  have list_eq: "cfg_edges_list g1 = cfg_edges_list g2"
    by (rule cfg_edges_list_edges_cong[OF fin eq])
  show ?thesis
    unfolding predecessor_list_def list_eq by simp
qed

lemma cfg_combines_list_combines_cong:
  assumes fin: "finite (combines g1)"
  assumes eq: "combines g1 = combines g2"
  shows "cfg_combines_list g1 = cfg_combines_list g2"
  unfolding cfg_combines_list_def using fin eq by simp

lemma combine_predecessor_list_combines_cong:
  assumes fin: "finite (combines g1)"
  assumes eq: "combines g1 = combines g2"
  shows "combine_predecessor_list g1 v = combine_predecessor_list g2 v"
proof -
  have list_eq: "cfg_combines_list g1 = cfg_combines_list g2"
    by (rule cfg_combines_list_combines_cong[OF fin eq])
  show ?thesis
    unfolding combine_predecessor_list_def list_eq by simp
qed

lemma make_rhs_tree_ip_cong:
  assumes entry: "cfg_entry g1 = cfg_entry g2"
  assumes edges: "edges g1 = edges g2"
  assumes comb: "combines g1 = combines g2"
  assumes fin: "finite (edges g1)"
  assumes finC: "finite (combines g1)"
  shows "make_rhs_tree_ip g1 tf join_abs bot_abs s0 v = make_rhs_tree_ip g2 tf join_abs bot_abs s0 v"
proof (cases "v = cfg_entry g2")
  case True
  then show ?thesis
    by (simp add: entry edges comb fin finC
         predecessor_list_edges_cong[OF fin edges]
         combine_predecessor_list_combines_cong[OF finC comb]
         make_rhs_tree_ip_def Let_def)
next
  case False
  then show ?thesis
    by (simp add: False entry edges comb fin finC
         predecessor_list_edges_cong[OF fin edges]
         combine_predecessor_list_combines_cong[OF finC comb]
         make_rhs_tree_ip_def Let_def)
qed

lemma dep_ip_rhs_tree_edge:
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  shows "u \<in> dep (\<lambda>v. make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma> w"
proof -
  define acc0 where
    "acc0 = (if w = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using ed fin by (auto simp: predecessors_def set_predecessor_list)
  have "u \<in> dep_aux \<sigma> (ip_rhs_tree tf join_abs combine_abs acc0 (predecessor_list g w)
        (combine_predecessor_list g w))"
    by (rule dep_ip_rhs_tree_pred[OF mem])
  then show ?thesis
    unfolding make_rhs_tree_ip_def Let_def dep_def acc0_def by simp
qed

lemma cfg_path_node_in_reach_ip_tree:
  assumes fin: "finite (edges g)"
  assumes path: "cfg_path g u es v0"
  shows "u \<in> reach (\<lambda>v. make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma> v0"
proof (insert path, induction es arbitrary: u)
  case Nil
  then have "u = v0" by (cases rule: cfg_path.cases) simp_all
  then show ?case by (simp add: reach.base)
next
  case (Cons e es')
  assume p: "cfg_path g u (e # es') v0"
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  from p ew obtain ed: "(u, a, w) \<in> edges g" and p2: "cfg_path g w es' v0"
    by (cases rule: cfg_path.cases) auto
  have w_reach: "w \<in> reach (\<lambda>v. make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma> v0"
    by (rule Cons.IH[OF p2])
  have u_dep: "u \<in> dep (\<lambda>v. make_rhs_tree_ip g tf join_abs bot_abs s0 v) \<sigma> w"
    using dep_ip_rhs_tree_edge[OF fin ed] .
  show ?case using reach.step[OF w_reach u_dep] .
qed

locale td_cfg_ip_core = td_cfg_core +
  assumes fin: "finite (edges g)"
  and fin_combines: "finite (combines g)"
begin

definition cfg_T_ip :: "pp => (pp, 'a abs_state) strategy_tree"
where
  "cfg_T_ip v = make_rhs_tree_ip g tf join_abs bot_abs s0 v"

lemma cfg_T_ip_eq[simp]:
  "cfg_T_ip v = make_rhs_tree_ip g tf join_abs bot_abs s0 v"
  unfolding cfg_T_ip_def by rule

lemma cfg_path_node_in_reach_ip:
  fixes \<sigma> :: "(pp, 'a abs_state) map" and v0 u :: pp
  assumes path: "cfg_path g u es v0"
  shows "u \<in> reach cfg_T_ip \<sigma> v0"
  using cfg_path_node_in_reach_ip_tree[OF fin path]
  unfolding cfg_T_ip_def
  by blast  

lemma cfg_env_post_fixpoint_ip_solver:
  fixes env :: "pp => 'a abs_state" and \<sigma> :: "(pp, 'a abs_state) map"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes env_def: "\<And>w. env w = lookup_bot \<sigma> w"
  assumes eq_le: "\<And>v. (eq cfg_T_ip) v \<sigma> \<le> mlup \<sigma> v"
  shows "is_post_fixpoint_ip g tf join_abs bot_abs s0 env"
  using cfg_env_post_fixpoint_ip[where T=cfg_T_ip, OF cfg_T_ip_eq fin fin_combines cfi join_sym
        env_def eq_le]
  by simp

end

end
