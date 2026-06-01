theory TD_CFG_Core
  imports Constraint_System CFG_Runs_To_Bridge "TD.Basics"
begin

(*
  Top-Down Solver Interface.

  We connect our function-style RHS
    rhs :: pp => (pp => 'a abs_state) => 'a abs_state
  to AFP's strategy-tree interface
    T   :: pp => (pp, 'a abs_state) strategy_tree.
*)

(* -- Monotone RHS wrapper (reused in downstream proofs) -- *)

definition make_rhs ::
    "cfg
     => 'a::ord domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => (pp => 'a abs_state) => 'a abs_state"
where
  "make_rhs g tf join_abs bot_abs s0 v env =
     rhs g tf join_abs bot_abs s0 env v"

lemma make_rhs_mono:
  assumes fin: "finite (edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::preorder abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_ub1: "\<And>x y::'a abs_state. x \<le> join_abs x y"
  assumes join_ub2: "\<And>x y::'a abs_state. y \<le> join_abs x y"
  assumes join_mono:
      "\<And>x1 y1 x2 y2::'a abs_state. x1 \<le> y1 \<Longrightarrow> x2 \<le> y2 \<Longrightarrow> join_abs x1 x2 \<le> join_abs y1 y2"
  assumes join_least:
      "\<And>x y z::'a abs_state. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> join_abs x y \<le> z"
  assumes tf_mono:
      "\<And>a \<sigma>1 \<sigma>2::'a abs_state. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> apply_tf tf a \<sigma>1 \<le> apply_tf tf a \<sigma>2"
  shows "monotone (\<le>) (\<le>) (make_rhs g tf join_abs bot_abs s0 v)"
proof (rule monotoneI)
  fix env1 env2 :: "pp \<Rightarrow> 'a abs_state"
  assume "env1 \<le> env2"
  then have env_le: "\<forall>v. env1 v \<le> env2 v"
    by (simp add: le_fun_def)
  show "make_rhs g tf join_abs bot_abs s0 v env1 \<le> make_rhs g tf join_abs bot_abs s0 v env2"
    unfolding make_rhs_def
    by (rule rhs_mono[OF fin cfu join_ub1 join_ub2 join_mono join_least tf_mono env_le])
qed

(* -- Strategy-tree bridge to AFP TD_plain -- *)

fun rhs_tree_fold ::
    "'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => (pp * edge_action) list
     => (pp, 'a abs_state) strategy_tree"
where
  "rhs_tree_fold tf join_abs acc [] = Answer acc"
| "rhs_tree_fold tf join_abs acc ((u,a)#ps) =
     Query u (\<lambda>su. rhs_tree_fold tf join_abs (join_abs acc (apply_tf tf a su)) ps)"

definition make_rhs_tree ::
    "cfg
     => 'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp
     => (pp, 'a abs_state) strategy_tree"
where
  "make_rhs_tree g tf join_abs bot_abs s0 v =
     (let acc0 = (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)
      in rhs_tree_fold tf join_abs acc0 (predecessor_list g v))"

definition env_map :: "(pp => 'a abs_state) => (pp, 'a abs_state) map" where
  "env_map env = (\<lambda>x. Some (env x))"

definition lookup_bot :: "('x, 'd::bot) map => 'x => 'd" where
  "lookup_bot m x = (case m x of None => bot | Some d => d)"

lemma lookup_bot_env_map[simp]:
  "lookup_bot (env_map env) x = env x"
  unfolding lookup_bot_def env_map_def
  by simp

lemma mlup_env_map[simp]:
  fixes env :: "pp \<Rightarrow> ('a::{bot}) abs_state"
  shows "mlup (env_map env) x = env x"
  unfolding mlup_def env_map_def by simp

lemma rhs_tree_fold_traverse_env_map:
  fixes env :: "pp \<Rightarrow> ('a::bounded_semilattice_sup_bot) abs_state"
  shows "traverse_rhs (rhs_tree_fold tf join_abs acc ps) (env_map env)
     = fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps acc"
proof (induct ps arbitrary: acc)
  case Nil
  show ?case
    by simp
next
  case (Cons p ps)
  obtain u a where p: "p = (u, a)"
    by (cases p) auto
  have "traverse_rhs (rhs_tree_fold tf join_abs acc (p # ps)) (env_map env) =
        traverse_rhs (Query u (\<lambda>su. rhs_tree_fold tf join_abs (join_abs acc (apply_tf tf a su)) ps))
         (env_map env)"
    by (simp add: p)
  also have "\<dots> =
        traverse_rhs (rhs_tree_fold tf join_abs (join_abs acc (apply_tf tf a (env u))) ps)
         (env_map env)"
    by simp
  also have "\<dots> =
        fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps
         (join_abs acc (apply_tf tf a (env u)))"
    using Cons[of "join_abs acc (apply_tf tf a (env u))"] by simp
  also have "\<dots> =
        fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) (p # ps) acc"
    by (simp add: p)
  finally show ?case .
qed

(* Avoid simp turning @{text "set xs = {}"} inside @{text SOME} into @{text "xs = []"} the wrong way. *)
lemma SOME_list_distinct_set_empty_eq_Nil:
  "(SOME xs :: ('a::type) list. distinct xs \<and> set xs = {}) = []"
proof (rule some_equality)
  show "distinct ([] :: 'a list) \<and> set [] = {}"
    by simp
next
  fix xs :: "'a list"
  assume H: "distinct xs \<and> set xs = {}"
  then show "xs = []"
    by simp
qed

lemma SOME_distinct_list_if_set_empty:
  fixes P :: "'a set"
  assumes hp: "P = {}"
  shows "(SOME xs :: 'a list. distinct xs \<and> set xs = P) = []"
  unfolding hp by (rule SOME_list_distinct_set_empty_eq_Nil)

(* Special case: no edges into v and v is not the entry tree is Answer bot, same as rhs. *)
lemma make_rhs_tree_eq_Answer_bot_if_no_preds_not_entry:
  assumes not_e: "v \<noteq> cfg_entry g"
  assumes no_in: "\<And>u a. (u, a, v) \<notin> edges g"
  shows "make_rhs_tree g tf join_abs bot_abs s0 v = Answer bot_abs"
  unfolding make_rhs_tree_def Let_def
  using no_in not_e predecessor_list_Nil_if_no_in
  by simp

lemma make_rhs_tree_correspondence_not_entry_no_predecessors:
  fixes env :: "pp \<Rightarrow> ('a::bounded_semilattice_sup_bot) abs_state"
  assumes not_e: "v \<noteq> cfg_entry g"
  assumes no_in: "\<And>u a. (u, a, v) \<notin> edges g"
  shows "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map env) =
         make_rhs g tf join_abs bot_abs s0 v env"
proof -
  have tr: "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map env) = bot_abs"
    unfolding make_rhs_tree_eq_Answer_bot_if_no_preds_not_entry[OF not_e no_in] by simp
  have mk: "make_rhs g tf join_abs bot_abs s0 v env = bot_abs"
    unfolding make_rhs_def by (simp add: rhs_no_predecessors_not_entry not_e no_in)
  from tr mk show ?thesis
    by simp
qed

lemma finite_predecessor_pairs:
  assumes fin: "finite (edges g)"
  shows "finite {(u,a). (u,a,v) \<in> edges g}"
proof (rule finite_subset)
  show "{(u,a). (u,a,v) \<in> edges g} \<subseteq> (\<lambda>(u, a, w). (u, a)) ` edges g"
    by force
  show "finite ((\<lambda>(u, a, w). (u, a)) ` edges g)"
    by (simp add: fin)
qed

lemma fold_join_apply_edges_eq_fold_join_over_map:
  fixes join :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and F :: "('b \<times> 'c) \<Rightarrow> 'a"
  shows "fold (\<lambda>p acc. join (F p) acc) ps acc =
         fold (\<lambda>x acc. join x acc) (map F ps) acc"
proof (induct ps arbitrary: acc)
  case Nil
  show ?case
    by simp
next
  case (Cons p ps)
  have "fold (\<lambda>p acc. join (F p) acc) (p # ps) acc =
        fold (\<lambda>p acc. join (F p) acc) ps (join (F p) acc)"
    by simp
  also have "\<dots> = fold (\<lambda>x acc. join x acc) (map F ps) (join (F p) acc)"
    using Cons[of "join (F p) acc"] by simp
  also have "\<dots> = fold (\<lambda>x acc. join x acc) (map F (p # ps)) acc"
    by simp
  finally show ?case .
qed

lemma rhs_eq_fold_predecessors:
  fixes g v tf join_abs bot_abs s0
  fixes env :: "pp \<Rightarrow> ('a::bounded_semilattice_sup_bot) abs_state"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes dist: "distinct ps"
  assumes setps: "set ps = {(u,a). (u,a,v) \<in> edges g}"
  defines "preds \<equiv> {(u,a). (u,a,v) \<in> edges g}"
  defines "F \<equiv> (\<lambda>(u,a). apply_tf tf a (env u))"
  defines "vals \<equiv> F ` preds"
  defines "acc0 \<equiv> (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
  shows "rhs g tf join_abs bot_abs s0 env v =
         fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps acc0"
proof -
  interpret j: comp_fun_idem join_abs
    by (fact cfi)
  have fin_preds: "finite preds"
    unfolding preds_def by (rule finite_predecessor_pairs[OF fin])
  have setps': "set ps = preds"
    unfolding preds_def using setps by simp
  have vals_eq: "vals = set (map F ps)"
    unfolding vals_def using setps' by simp
  have fold_map:
    "fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps acc0 =
     fold (\<lambda>x acc. join_abs x acc) (map F ps) acc0"
  proof -
    have H: "(\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) = (\<lambda>p acc. join_abs (F p) acc)"
      by (rule ext)+ (simp add: F_def split: prod.split)
    show ?thesis
      unfolding H by (rule fold_join_apply_edges_eq_fold_join_over_map)
  qed
  have fold_set:
    "Finite_Set.fold join_abs acc0 (set (map F ps)) =
     fold (\<lambda>x acc. join_abs x acc) (map F ps) acc0"
    by (rule j.fold_set_fold)
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    have rhsv: "rhs g tf join_abs bot_abs s0 env v = abs_join_set join_abs bot_abs (insert s0 vals)"
      unfolding rhs_def preds_def vals_def F_def using True by (simp add: Let_def)
    have fin_vals: "finite vals"
      unfolding vals_def using fin_preds by simp
    have ins_fold:
      "Finite_Set.fold join_abs bot_abs (insert s0 vals) =
       Finite_Set.fold join_abs (join_abs s0 bot_abs) vals"
      by (simp only: j.fold_insert_idem2 fin_vals)
    also have "join_abs s0 bot_abs = join_abs bot_abs s0"
      by (simp add: join_sym)
    also have "Finite_Set.fold join_abs (join_abs bot_abs s0) vals =
               Finite_Set.fold join_abs acc0 (set (map F ps))"
      unfolding vals_eq acc0_def using True by simp
    also have "\<dots> = fold (\<lambda>x acc. join_abs x acc) (map F ps) acc0"
      by (simp add: fold_set[symmetric])
    also have "\<dots> = fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps acc0"
      by (simp add: fold_map[symmetric])
    finally show ?thesis
      unfolding rhsv abs_join_set_def by simp
  next
    case False
    then have ne: "v \<noteq> cfg_entry g"
      by simp
    have rhsv: "rhs g tf join_abs bot_abs s0 env v = abs_join_set join_abs bot_abs vals"
      unfolding rhs_def preds_def vals_def F_def using False by (simp add: Let_def)
    have "Finite_Set.fold join_abs bot_abs vals =
          Finite_Set.fold join_abs acc0 (set (map F ps))"
      unfolding vals_eq acc0_def using ne by simp
    also have "\<dots> = fold (\<lambda>x acc. join_abs x acc) (map F ps) acc0"
      by (simp add: fold_set[symmetric])
    also have "\<dots> = fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps acc0"
      by (simp add: fold_map[symmetric])
    finally show ?thesis
      unfolding rhsv abs_join_set_def by simp
  qed
qed

lemma rhs_eq_fold_predecessor_list:
  fixes g v tf join_abs bot_abs s0
  fixes env :: "pp \<Rightarrow> ('a::bounded_semilattice_sup_bot) abs_state"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "rhs g tf join_abs bot_abs s0 env v =
         fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc)
              (predecessor_list g v)
              (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
proof -
  have setps: "set (predecessor_list g v) = {(u,a). (u,a,v) \<in> edges g}"
    using set_predecessor_list[OF fin] unfolding predecessors_def by auto
  show ?thesis
    using rhs_eq_fold_predecessors[OF fin cfi join_sym
        distinct_predecessor_list[OF fin] setps]
    by simp
qed

lemma fold_join_abs_swap_edge_steps:
  fixes join_abs :: "'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and tf :: "'a domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps acc =
         fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps acc"
proof (induct ps arbitrary: acc)
  case Nil
  show ?case
    by simp
next
  case (Cons p ps)
  obtain u a where pa: "p = (u, a)"
    by (cases p) auto
  have "fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) (p # ps) acc =
        fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps (join_abs acc (apply_tf tf a (env u)))"
    by (simp add: pa)
  also have "join_abs acc (apply_tf tf a (env u)) = join_abs (apply_tf tf a (env u)) acc"
    by (simp add: join_sym)
  also have "fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u))) ps (join_abs (apply_tf tf a (env u)) acc) =
             fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) ps (join_abs (apply_tf tf a (env u)) acc)"
    using Cons.hyps by simp
  also have "\<dots> = fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc) (p # ps) acc"
    by (simp add: pa)
  finally show ?case .
qed

lemma make_rhs_tree_correspondence:
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map (env :: pp \<Rightarrow> 'a abs_state)) =
         make_rhs g tf join_abs bot_abs s0 v env"
proof -
  have "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map env) =
        fold (\<lambda>(u,a) st. join_abs st (apply_tf tf a (env u)))
             (predecessor_list g v)
             (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
    unfolding make_rhs_tree_def Let_def
    by (simp add: rhs_tree_fold_traverse_env_map)
  also have "\<dots> =
        fold (\<lambda>(u,a) acc. join_abs (apply_tf tf a (env u)) acc)
             (predecessor_list g v)
             (if v = cfg_entry g then join_abs bot_abs s0 else bot_abs)"
    by (rule fold_join_abs_swap_edge_steps[OF join_sym])
  also have "\<dots> = rhs g tf join_abs bot_abs s0 env v"
    by (simp add: rhs_eq_fold_predecessor_list[OF fin cfi join_sym])
  finally show ?thesis
    unfolding make_rhs_def by (simp split: if_splits)
qed

lemma mlup_env_map_of_mlup:
  fixes \<sigma> :: "(pp, ('a::bounded_semilattice_sup_bot) abs_state) map"
  shows "mlup (env_map (\<lambda>w. mlup \<sigma> w)) x = mlup \<sigma> x"
  by (simp add: mlup_env_map)

lemma lookup_bot_mlup:
  fixes \<sigma> :: "(pp, ('a::bounded_semilattice_sup_bot) abs_state) map"
  shows "lookup_bot \<sigma> x = mlup \<sigma> x"
  unfolding lookup_bot_def mlup_def by (cases "\<sigma> x") simp_all

lemma traverse_rhs_mlup_eq:
  fixes t :: "(pp, ('a::bounded_semilattice_sup_bot) abs_state) strategy_tree"
    and \<sigma> \<sigma>' :: "(pp, ('a::bounded_semilattice_sup_bot) abs_state) map"
  assumes mlup_ag: "\<And>z. mlup \<sigma> z = mlup \<sigma>' z"
  shows "traverse_rhs t \<sigma> = traverse_rhs t \<sigma>'"
  apply (rule solution_sufficient_t)
  using mlup_ag by simp

lemma rhs_make_rhs_tree_traverse_mlup:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs bot_abs s0 v and \<sigma> :: "(pp, ('a::bounded_semilattice_sup_bot) abs_state) map"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem (join_abs :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  shows "rhs g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v =
         traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma>"
proof -
  have "traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> =
        traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) (env_map (\<lambda>w. mlup \<sigma> w))"
    by (rule traverse_rhs_mlup_eq) (simp add: mlup_env_map_of_mlup)
  also have "\<dots> =
        make_rhs g tf join_abs bot_abs s0 v (\<lambda>w. mlup \<sigma> w)"
    by (simp add: make_rhs_tree_correspondence[OF fin cfi join_sym])
  also have "\<dots> = rhs g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v"
    by (simp add: make_rhs_def)
  finally show ?thesis ..
qed


lemma dep_rhs_tree_fold:
  shows "(u, a) \<in> set ps \<Longrightarrow> u \<in> dep_aux \<sigma> (rhs_tree_fold tf join_abs acc ps)"
  by (induct ps arbitrary: acc; auto simp: rhs_tree_fold.simps dep_aux.simps split: prod.splits)

lemma dep_make_rhs_tree_pred:
  assumes fin: "finite (edges g)"
  assumes pred: "(u, a) \<in> predecessors g w"
  shows "u \<in> dep (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> w"
proof -
  have mem: "(u, a) \<in> set (predecessor_list g w)"
    using pred fin by (auto simp: predecessors_def set_predecessor_list)
  have "u \<in> dep_aux \<sigma> (make_rhs_tree g tf join_abs bot_abs s0 w)"
    unfolding make_rhs_tree_def Let_def dep_def
    by (metis dep_rhs_tree_fold mem)
  then show ?thesis unfolding dep_def by simp
qed

lemma dep_make_rhs_tree_edge:
  assumes fin: "finite (edges g)"
  assumes ed: "(u, a, w) \<in> edges g"
  shows "u \<in> dep (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> w"
  using dep_make_rhs_tree_pred[OF fin, unfolded predecessors_def] ed by auto



lemma eq_le_mlup_imp_rhs_le:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
    and T :: "pp \<Rightarrow> (pp, 'a abs_state) strategy_tree"
    and \<sigma> :: "(pp, 'a abs_state) map" and v :: pp
  assumes T_mk: "\<And>w. T w = make_rhs_tree g tf join_abs bot_abs s0 w"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes le: "(eq T) v \<sigma> \<le> mlup \<sigma> v"
  shows "rhs g tf join_abs bot_abs s0 (\<lambda>w. lookup_bot \<sigma> w) v \<le> lookup_bot \<sigma> v"
proof -
  have "rhs g tf join_abs bot_abs s0 (\<lambda>w. lookup_bot \<sigma> w) v =
        rhs g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v"
    by (simp add: fun_eq_iff lookup_bot_mlup)
  also have "\<dots> = traverse_rhs (T v) \<sigma>"
  proof -
    have "rhs g tf join_abs bot_abs s0 (\<lambda>w. mlup \<sigma> w) v =
          traverse_rhs (make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma>"
      by (rule rhs_make_rhs_tree_traverse_mlup[OF fin cfi join_sym])
    thus ?thesis unfolding T_mk by simp
  qed
  also have "traverse_rhs (T v) \<sigma> = (eq T) v \<sigma>"
    by (simp add: eq_def)
  also have "\<dots> \<le> mlup \<sigma> v"
    using le by simp
  finally show ?thesis
    by (simp add: lookup_bot_mlup)
qed

lemma cfg_env_post_fixpoint:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
    and T :: "pp \<Rightarrow> (pp, 'a abs_state) strategy_tree"
    and env :: "pp \<Rightarrow> 'a abs_state" and \<sigma> :: "(pp, 'a abs_state) map"
  assumes T_mk: "\<And>w. T w = make_rhs_tree g tf join_abs bot_abs s0 w"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes env_def: "\<And>w. env w = lookup_bot \<sigma> w"
  assumes eq_le: "\<And>v. (eq T) v \<sigma> \<le> mlup \<sigma> v"
  shows "is_post_fixpoint g tf join_abs bot_abs s0 env"
  unfolding is_post_fixpoint_def
proof (intro allI)
  fix v
  show "rhs g tf join_abs bot_abs s0 env v \<le> env v"
  proof -
    have "rhs g tf join_abs bot_abs s0 env v \<le> lookup_bot \<sigma> v"
      using eq_le_mlup_imp_rhs_le[OF T_mk fin cfi join_sym eq_le] env_def by presburger
    thus ?thesis using env_def by simp
  qed
qed

lemma cfg_path_node_in_reach_tree:
  assumes fin: "finite (edges g)"
    and path: "cfg_path g u es v0"
  shows "u \<in> reach (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> v0"
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
  have w_reach: "w \<in> reach (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> v0"
    by (rule Cons.IH[OF p2])
  have u_dep: "u \<in> dep (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> w"
    using dep_make_rhs_tree_edge[OF fin ed] .
  show ?case using reach.step[OF w_reach u_dep] .
qed

locale td_cfg_core =
  fixes g :: cfg and
  tf :: "'a::bounded_semilattice_sup_bot domain_transfer" and
  join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" and
  bot_abs s0 :: "'a abs_state"
begin

definition cfg_T :: "pp \<Rightarrow> (pp, 'a abs_state) strategy_tree"
where
  "cfg_T v = make_rhs_tree g tf join_abs bot_abs s0 v"

lemma cfg_T_eq[simp]:
  "cfg_T v = make_rhs_tree g tf join_abs bot_abs s0 v"
  unfolding cfg_T_def by rule

lemma cfg_env_post_fixpoint:
  fixes env :: "pp \<Rightarrow> 'a abs_state" and \<sigma> :: "(pp, 'a abs_state) map"
  assumes fin: "finite (edges g)"
  assumes cfi: "comp_fun_idem join_abs"
  assumes join_sym: "\<And>x y. join_abs x y = join_abs y x"
  assumes env_def: "\<And>w. env w = lookup_bot \<sigma> w"
  assumes eq_le: "\<And>v. (eq cfg_T) v \<sigma> \<le> mlup \<sigma> v"
  shows "is_post_fixpoint g tf join_abs bot_abs s0 env"
  using cfg_env_post_fixpoint[where T=cfg_T, OF cfg_T_eq fin cfi join_sym env_def eq_le]
  by simp

lemma cfg_path_node_in_reach:
  fixes \<sigma> :: "(pp, 'a abs_state) map" and v0 u :: pp
  assumes fin: "finite (edges g)"
  assumes path: "cfg_path g u es v0"
  shows "u \<in> reach cfg_T \<sigma> v0"
proof -
  have main: "u \<in> reach (\<lambda>v. make_rhs_tree g tf join_abs bot_abs s0 v) \<sigma> v0"
    using cfg_path_node_in_reach_tree[OF fin path] .
  show ?thesis unfolding cfg_T_def using main by simp
qed

end

end
