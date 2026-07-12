theory Exec_Ctx_Bridge
  imports Exec_Bridge TD_Side_Tree
begin

section \<open>Executable context-indexed equation-system generator\<close>

text \<open>
  Executable \<open>_st\<close> mirrors of the proven-sound abstract context generator in
  \<^theory>\<open>Voblint_Analysis.TD_Side_Tree\<close>: \<^const>\<open>side_cfg_T_eff_ctx\<close> and
  \<^const>\<open>unit_combine_tree_ctx\<close>.  The payload moves from the abstract
  \<^typ>\<open>'a abs_state\<close> to the executable \<^typ>\<open>'a st\<close> finite-map state, and the
  abstract \<^const>\<open>restrict_local\<close> / \<^const>\<open>restrict_global\<close> become their
  executable counterparts \<^const>\<open>restrict_local_st\<close> / \<^const>\<open>restrict_global_st\<close>.

  The unknown is reindexed \<^typ>\<open>pp\<close> to \<^typ>\<open>pp \<times> 'c\<close>; intra per-edge trees keep
  the context (a uniform \<^const>\<open>map_ltree\<close> relabel \<open>u \<mapsto> (u, c)\<close>), and the
  combine trees are supplied by an instance combine builder \<open>cmb\<close>.  For the
  semantic entry-state context, \<open>unit_combine_tree_ctx_st\<close> routes the
  callee-exit query value-dependently through the context \<open>ec ctx (sc \<squnion> g)\<close>.

  These run through the real vendored side solver on a compiled CFG.
\<close>

subsection \<open>Context fold over a list of per-point executable trees\<close>

text \<open>
  Executable counterpart of \<^const>\<open>side_rhs_fold_ctx\<close>: fold the already-assembled
  context-indexed trees for one unknown with \<^const>\<open>seqcomp_tree\<close>, joining the
  local Answers.
\<close>

fun side_rhs_fold_ctx_st ::
  "'a::bounded_semilattice_sup_bot st
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree list
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree"
where
  "side_rhs_fold_ctx_st acc [] = Answer acc"
| "side_rhs_fold_ctx_st acc (t # ts) =
     seqcomp_tree t (\<lambda>res. side_rhs_fold_ctx_st (acc \<squnion> res) ts)"

subsection \<open>Value-dependent semantic combine (unit global, executable)\<close>

text \<open>
  Executable mirror of \<^const>\<open>unit_combine_tree_ctx\<close>: query the caller \<open>(cc, ctx)\<close>
  for its local \<open>sc\<close>, compute the callee context \<open>ec ctx (sc \<squnion> g)\<close> from the
  queried value, then query \<open>(ex, ec ctx (sc \<squnion> g))\<close> for the callee exit \<open>se\<close>.
  Locals flow from the caller, globals from the callee exit.
\<close>

definition unit_combine_tree_ctx_st ::
  "('c \<Rightarrow> 'a st \<Rightarrow> 'c) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c, unit, 'a::bounded_semilattice_sup_bot st) strategy_tree"
where
  "unit_combine_tree_ctx_st ec cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG () (\<lambda>g. QueryL (ex, ec ctx (sc \<squnion> g)) (\<lambda>se.
       let res = restrict_local_st (sc \<squnion> g) \<squnion> restrict_global_st (se \<squnion> g) in
       Side () (restrict_global_st res)
         (Answer (restrict_local_st res)))))"



subsection \<open>Bridge to the abstract context equation system\<close>

text \<open>
  The abstract context combine receives an abstract state, while the executable
  combine keys contexts by the finite-map state that produced that abstraction.
  This inverse is only used in bridge proofs, on values known to come from
  \<^const>\<open>fun_of_st\<close>.
\<close>

definition st_of_abs :: "'a::bot abs_state \<Rightarrow> 'a st" where
  "st_of_abs a = (SOME s. fun_of_st s = a)"

lemma st_of_abs_fun_of_st [simp]:
  "st_of_abs (fun_of_st s) = s"
  unfolding st_of_abs_def
  by (rule some_equality) (simp_all add: fun_of_st_inject)

lemma sides_of_rhs_Inl_bot [simp]:
  "sides_of_rhs t \<sigma> (Inl x) = bot"
  by (induction t arbitrary: \<sigma>) (simp_all add: Let_def)

lemma sides_map_ltree_Inr:
  "sides_of_rhs (map_ltree h t) \<sigma> (Inr g)
   = sides_of_rhs t (\<lambda>z. \<sigma> (map_sum h id z)) (Inr g)"
  by (induction t arbitrary: \<sigma>) (auto simp: Let_def fun_upd_apply)

lemma dep_aux_map_ltree:
  "dep_aux \<sigma> (map_ltree h t)
   = map_sum h id ` dep_aux (\<lambda>z. \<sigma> (map_sum h id z)) t"
  by (induction t arbitrary: \<sigma>) auto

lemma traverse_unit_combine_tree_ctx_st_fun_of_st:
  "fun_of_st (traverse_rhs (unit_combine_tree_ctx_st ec cc ex ctx) \<sigma>_st)
   = traverse_rhs (unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)
       (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding unit_combine_tree_ctx_st_def unit_combine_tree_ctx_def
  by (simp del: fun_of_st_sup
      add: Let_def o_def restrict_local_combine_eq fun_of_st_sup[symmetric])
lemma sides_unit_combine_tree_ctx_st_fun_of_st:
  "fun_of_st (sides_of_rhs (unit_combine_tree_ctx_st ec cc ex ctx) \<sigma>_st k)
   = sides_of_rhs (unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (cases k)
  case (Inl x)
  then show ?thesis
    unfolding unit_combine_tree_ctx_st_def unit_combine_tree_ctx_def
    by (simp add: bot_fun_def)
next
  case (Inr g)
  then show ?thesis
    unfolding unit_combine_tree_ctx_st_def unit_combine_tree_ctx_def
    by (simp del: fun_of_st_sup
        add: Let_def o_def restrict_global_combine_eq fun_of_st_sup[symmetric])
qed


lemma dep_aux_unit_combine_tree_ctx_st:
  "dep_aux \<sigma>_st (unit_combine_tree_ctx_st ec cc ex ctx)
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)"
  unfolding unit_combine_tree_ctx_st_def unit_combine_tree_ctx_def
  by (simp del: fun_of_st_sup add: Let_def o_def fun_of_st_sup[symmetric])

lemma traverse_map_ltree_st_fun_of_st:
  assumes tr:
    "\<And>\<sigma>_st. fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  shows "fun_of_st (traverse_rhs (map_ltree h t_st) \<sigma>_st)
       = traverse_rhs (map_ltree h t_abs) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding traverse_rhs_map_ltree
  by (simp add: tr o_def)

lemma sides_map_ltree_st_fun_of_st:
  assumes sd:
    "\<And>\<sigma>_st k. fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  shows "fun_of_st (sides_of_rhs (map_ltree h t_st) \<sigma>_st k)
       = sides_of_rhs (map_ltree h t_abs) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (cases k)
  case (Inl x)
  then show ?thesis by (simp add: bot_fun_def)
next
  case (Inr g)
  then show ?thesis
    by (simp add: sides_map_ltree_Inr sd o_def)
qed

lemma dep_aux_map_ltree_st_eq:
  assumes dep:
    "\<And>\<sigma>_st. dep_aux \<sigma>_st t_st
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  shows "dep_aux \<sigma>_st (map_ltree h t_st)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (map_ltree h t_abs)"
  by (simp add: dep_aux_map_ltree dep o_def)

lemma side_rhs_fold_ctx_st_traverse_fun_of_st:
  assumes rel:
    "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip ts_st ts_abs) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes len: "length ts_st = length ts_abs"
  shows "fun_of_st (traverse_rhs (side_rhs_fold_ctx_st acc_st ts_st) \<sigma>_st)
       = traverse_rhs (side_rhs_fold_ctx (fun_of_st acc_st) ts_abs)
           (\<lambda>k. fun_of_st (\<sigma>_st k))"
  using rel len
proof (induction ts_st arbitrary: ts_abs acc_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st)
  then obtain t_abs ts_abs' where ts_abs: "ts_abs = t_abs # ts_abs'"
    by (cases ts_abs) auto
  have hd_rel: "\<And>\<sigma>_st. fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(1)[of t_st t_abs] ts_abs by auto
  have tl_rel: "\<And>u_st u_abs \<sigma>_st. (u_st, u_abs) \<in> set (zip ts_st ts_abs') \<Longrightarrow>
       fun_of_st (traverse_rhs u_st \<sigma>_st)
       = traverse_rhs u_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(1) ts_abs by auto
  have len_tl: "length ts_st = length ts_abs'"
    using Cons.prems(2) ts_abs by simp
  show ?case
    unfolding ts_abs side_rhs_fold_ctx_st.simps side_rhs_fold_ctx.simps traverse_seqcomp
    by (simp add: hd_rel Cons.IH[OF tl_rel len_tl] fun_of_st_sup sup_fun_def)
qed

lemma side_rhs_fold_ctx_st_sides_fun_of_st:
  assumes rel:
    "\<And>t_st t_abs \<sigma>_st k. (t_st, t_abs) \<in> set (zip ts_st ts_abs) \<Longrightarrow>
       fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes tr:
    "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip ts_st ts_abs) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes len: "length ts_st = length ts_abs"
  shows "fun_of_st (sides_of_rhs (side_rhs_fold_ctx_st acc_st ts_st) \<sigma>_st k)
       = sides_of_rhs (side_rhs_fold_ctx (fun_of_st acc_st) ts_abs)
           (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  using rel tr len
proof (induction ts_st arbitrary: ts_abs acc_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st)
  then obtain t_abs ts_abs' where ts_abs: "ts_abs = t_abs # ts_abs'"
    by (cases ts_abs) auto
  have hd_sd: "\<And>\<sigma>_st k. fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using Cons.prems(1)[of t_st t_abs] ts_abs by auto
  have hd_tr: "\<And>\<sigma>_st. fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(2)[of t_st t_abs] ts_abs by auto
  have tl_sd: "\<And>u_st u_abs \<sigma>_st k. (u_st, u_abs) \<in> set (zip ts_st ts_abs') \<Longrightarrow>
       fun_of_st (sides_of_rhs u_st \<sigma>_st k)
       = sides_of_rhs u_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using Cons.prems(1) ts_abs by auto
  have tl_tr: "\<And>u_st u_abs \<sigma>_st. (u_st, u_abs) \<in> set (zip ts_st ts_abs') \<Longrightarrow>
       fun_of_st (traverse_rhs u_st \<sigma>_st)
       = traverse_rhs u_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(2) ts_abs by auto
  have len_tl: "length ts_st = length ts_abs'"
    using Cons.prems(3) ts_abs by simp
  show ?case
    unfolding ts_abs side_rhs_fold_ctx_st.simps side_rhs_fold_ctx.simps
    by (simp add: hd_sd hd_tr Cons.IH[OF tl_sd tl_tr len_tl]
                  fun_of_st_sup sup_fun_def sides_of_rhs_seqcomp_at)
qed

lemma dep_aux_side_rhs_fold_ctx_st_eq:
  assumes rel:
    "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip ts_st ts_abs) \<Longrightarrow>
       dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  assumes tr:
    "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip ts_st ts_abs) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes len: "length ts_st = length ts_abs"
  shows "dep_aux \<sigma>_st (side_rhs_fold_ctx_st acc_st ts_st)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
           (side_rhs_fold_ctx (fun_of_st acc_st) ts_abs)"
  using rel tr len
proof (induction ts_st arbitrary: ts_abs acc_st)
  case Nil
  then show ?case by simp
next
  case (Cons t_st ts_st)
  then obtain t_abs ts_abs' where ts_abs: "ts_abs = t_abs # ts_abs'"
    by (cases ts_abs) auto
  have hd_dep: "\<And>\<sigma>_st. dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
    using Cons.prems(1)[of t_st t_abs] ts_abs by auto
  have hd_tr: "\<And>\<sigma>_st. fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(2)[of t_st t_abs] ts_abs by auto
  have tl_dep: "\<And>u_st u_abs \<sigma>_st. (u_st, u_abs) \<in> set (zip ts_st ts_abs') \<Longrightarrow>
       dep_aux \<sigma>_st u_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) u_abs"
    using Cons.prems(1) ts_abs by auto
  have tl_tr: "\<And>u_st u_abs \<sigma>_st. (u_st, u_abs) \<in> set (zip ts_st ts_abs') \<Longrightarrow>
       fun_of_st (traverse_rhs u_st \<sigma>_st)
       = traverse_rhs u_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using Cons.prems(2) ts_abs by auto
  have len_tl: "length ts_st = length ts_abs'"
    using Cons.prems(3) ts_abs by simp
  show ?case
    unfolding ts_abs side_rhs_fold_ctx_st.simps side_rhs_fold_ctx.simps
    by (simp add: hd_dep hd_tr Cons.IH[OF tl_dep tl_tr len_tl]
                  fun_of_st_sup dep_aux_seqcomp sup_fun_def)
qed



end

