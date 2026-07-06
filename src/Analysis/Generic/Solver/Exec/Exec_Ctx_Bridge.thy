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

subsection \<open>General context-indexed executable equation system\<close>

text \<open>
  Executable mirror of \<^const>\<open>side_cfg_T_eff_ctx\<close>: at every unknown \<open>(v, c)\<close>, the
  intra per-edge trees are relabelled \<open>u \<mapsto> (u, c)\<close> via \<^const>\<open>map_ltree\<close> (the
  context is unchanged along an intra edge), the combine trees come from the
  instance builder \<open>cmb\<close>, and both are folded by \<^const>\<open>side_rhs_fold_ctx_st\<close>.
  The program-entry seed and the \<^const>\<open>Side\<close> wrapper match the monovariant
  \<^const>\<open>side_cfg_T_eff_st\<close>.
\<close>

definition side_cfg_T_eff_ctx_st ::
  "('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_ctx_st cmb g etf bot0_st s0_st gseed =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st);
            intra = map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, c)) (apply_etf_st etf a u))
                        (predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ comb)
        in if v = cfg_entry g then Side gseed (restrict_global_st s0_st) t else t)"


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



context
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st :: "'a st"
  fixes ec :: "'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
       = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
begin

private abbreviation cmb_st where
  "cmb_st \<equiv> (\<lambda>ctx cc ex. unit_combine_tree_ctx_st ec cc ex ctx)"

private abbreviation cmb_abs where
  "cmb_abs \<equiv> (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)"

private lemma ctx_tree_traverse_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  using mem
  by (auto intro: traverse_map_ltree_st_fun_of_st[OF tr_edge]
           simp: traverse_unit_combine_tree_ctx_st_fun_of_st in_set_zip
           split: prod.splits)

private lemma ctx_tree_sides_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  using mem
  by (auto intro: sides_map_ltree_st_fun_of_st[OF sd_edge]
           simp: sides_unit_combine_tree_ctx_st_fun_of_st in_set_zip
           split: prod.splits)

private lemma ctx_tree_dep_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  using mem
  by (auto simp: dep_aux_map_ltree_st_eq[OF dep_edge]
                 dep_aux_unit_combine_tree_ctx_st in_set_zip
           split: prod.splits)

private lemma ctx_fold_traverse_rel:
  "fun_of_st (traverse_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st)
   = traverse_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k))"
proof (rule side_rhs_fold_ctx_st_traverse_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)"
    by simp
qed

private lemma ctx_fold_sides_rel:
  "fun_of_st (sides_of_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st k)
   = sides_of_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (rule side_rhs_fold_ctx_st_sides_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st k.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    by (rule ctx_tree_sides_rel)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)"
    by simp
qed

private lemma ctx_fold_dep_rel:
  "dep_aux \<sigma>_st
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
proof (rule dep_aux_side_rhs_fold_ctx_st_eq)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
    by (rule ctx_tree_dep_rel)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)"
    by simp
qed

lemma fun_of_st_eq_side_cfg_T_eff_ctx_st:
  "fun_of_st
     (eq (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st ()) (v, ctx) \<sigma>_st)
   = eq (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
       (v, ctx) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding eq_side_cfg_T_eff_ctx side_cfg_T_eff_ctx_st_def
  by (simp add: Let_def traverse_side_rhs_fold_ctx ctx_fold_traverse_rel fun_of_st_sup)

lemma fun_of_st_sides_side_cfg_T_eff_ctx_st:
  "fun_of_st
     (sides_of_rhs (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st () (v, ctx)) \<sigma>_st k)
   = sides_of_rhs
       (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () (v, ctx))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  unfolding side_cfg_T_eff_ctx_st_def side_cfg_T_eff_ctx_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def ctx_fold_sides_rel fun_of_st_sup)

lemma dep_aux_side_cfg_T_eff_ctx_st_eq:
  "dep_aux \<sigma>_st (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st () (v, ctx))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () (v, ctx))"
  unfolding side_cfg_T_eff_ctx_st_def side_cfg_T_eff_ctx_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def ctx_fold_dep_rel)

theorem part_post_solution_ctx_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st ()) x sigma_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof (rule part_post_solution_st_to_abs_transport[OF _ _ _ pp_st])
  fix v \<sigma>
  show "fun_of_st (eq (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st ()) v \<sigma>)
        = eq (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
            v (\<lambda>k. fun_of_st (\<sigma> k))"
    using fun_of_st_eq_side_cfg_T_eff_ctx_st[where v="fst v" and ctx="snd v"]
    by (cases v) simp
next
  fix v \<sigma> k
  show "fun_of_st (sides_of_rhs (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st () v) \<sigma> k)
        = sides_of_rhs (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () v)
            (\<lambda>k. fun_of_st (\<sigma> k)) k"
    using fun_of_st_sides_side_cfg_T_eff_ctx_st[where v="fst v" and ctx="snd v" and k=k]
    by (cases v) simp
next
  fix v \<sigma>
  show "dep_aux \<sigma> (side_cfg_T_eff_ctx_st cmb_st g etf_st bot0_st s0_st () v)
        = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (side_cfg_T_eff_ctx cmb_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () v)"
    using dep_aux_side_cfg_T_eff_ctx_st_eq[where v="fst v" and ctx="snd v"]
    by (cases v) simp
qed

end

lemma part_post_solution_ctx_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st :: "'a st"
  fixes ec :: "'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes pp_st:
    "part_post_solution
       (side_cfg_T_eff_ctx_st (\<lambda>ctx cc ex. unit_combine_tree_ctx_st ec cc ex ctx)
          g etf_st bot0_st s0_st ()) x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_ctx
          (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)
          g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have tr_edge:
    "\<And>a u sigma_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) sigma_st)
     = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (sigma_st k))"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute Let_def)
  have sd_edge:
    "\<And>a u sigma_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) sigma_st k)
     = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (sigma_st k)) k"
    using sides_apply_etf_st_unit_transfer[OF edge_st edge comb comb_st commute]
    by (simp add: o_def)
  have dep_edge:
    "\<And>a u sigma_st. dep_aux sigma_st (apply_etf_st etf_st a u)
     = dep_aux (\<lambda>k. fun_of_st (sigma_st k)) (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  show ?thesis
    by (rule part_post_solution_ctx_st_to_abs_eff[OF tr_edge sd_edge dep_edge pp_st])
qed


section \<open>Frame-entry context seeding (executable mirror)\<close>

text \<open>
  Executable mirror of \<^const>\<open>side_cfg_T_eff_ctx_seeded\<close>: a separate generator
  (not a modification of \<^const>\<open>side_cfg_T_eff_ctx_st\<close>) that, at a frame-entry
  node, drops every \<^const>\<open>EA_Enter\<close> predecessor from the ordinary intra fold and
  replaces it by a single context-derived seed \<^term>\<open>combine_abs_st (ent c) s\<close> --
  locals from the context (via \<open>ent\<close>), globals from the queried predecessor state.
  Non-\<^const>\<open>EA_Enter\<close> predecessors (e.g. a loop backedge into the same node)
  still flow through \<^const>\<open>apply_etf_st\<close> unchanged.
\<close>

definition side_cfg_T_eff_ctx_seeded_st ::
  "('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> ('c \<Rightarrow> 'a st)
   \<Rightarrow> cfg \<Rightarrow> ('g, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_ctx_seeded_st cmb ent g etf bot0_st s0_st gseed =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st);
            intra = map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, c)) (apply_etf_st etf a u))
                        (non_enter_predecessor_list g v);
            enter = map (\<lambda>(u, a). QueryL (u, c) (\<lambda>s. Answer (combine_abs_st (ent c) s)))
                        (enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ enter @ comb)
        in if v = cfg_entry g then Side gseed (restrict_global_st s0_st) t else t)"

lemma eq_side_cfg_T_eff_ctx_seeded_st:
  "eq (side_cfg_T_eff_ctx_seeded_st cmb ent g etf bot0_st s0_st gseed) (v, ctx) \<sigma> =
     traverse_rhs
       (side_rhs_fold_ctx_st
          (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
          (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf a u))
               (non_enter_predecessor_list g v)
           @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent ctx) s)))
                 (enter_predecessor_list g v)
           @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))) \<sigma>"
  unfolding side_cfg_T_eff_ctx_seeded_st_def
  by (simp add: Let_def)


subsection \<open>Bridge for the seeded context equation system\<close>

context
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st :: "'a st"
  fixes ec :: "'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  fixes ent_st :: "'c \<Rightarrow> 'a st"
  fixes ent_abs :: "'c \<Rightarrow> 'a abs_state"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
       = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
  assumes ent_commute:
    "\<And>c. fun_of_st (ent_st c) = ent_abs c"
begin

private abbreviation scmb_st where
  "scmb_st \<equiv> (\<lambda>ctx cc ex. unit_combine_tree_ctx_st ec cc ex ctx)"

private abbreviation scmb_abs where
  "scmb_abs \<equiv> (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx)"

private lemma enter_tree_traverse_rel:
  "fun_of_st (traverse_rhs (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) \<sigma>_st)
   = traverse_rhs (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s)))
       (\<lambda>k. fun_of_st (\<sigma>_st k))"
  by (simp add: ent_commute)

private lemma enter_tree_sides_rel:
  "fun_of_st (sides_of_rhs (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) \<sigma>_st k)
   = sides_of_rhs (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s)))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  by (simp add: bot_fun_def)

private lemma enter_tree_dep_rel:
  "dep_aux \<sigma>_st (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s)))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s)))"
  by simp

private lemma ctx_tree_traverse_rel_seeded:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
  shows "fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
proof -
  have split: "set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))
    = set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
      \<union> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
      \<union> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by (simp add: zip_append Un_assoc)
  from mem split have
    "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by auto
  then show ?thesis
  proof (elim disjE)
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))"
    then show ?thesis
      by (auto intro: traverse_map_ltree_st_fun_of_st[OF tr_edge]
               simp: in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))"
    then show ?thesis
      by (auto simp: enter_tree_traverse_rel ent_commute in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    then show ?thesis
      by (auto simp: traverse_unit_combine_tree_ctx_st_fun_of_st in_set_zip split: prod.splits)
  qed
qed

private lemma ctx_tree_sides_rel_seeded:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
  shows "fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof -
  have split: "set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))
    = set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
      \<union> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
      \<union> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by (simp add: zip_append Un_assoc)
  from mem split have
    "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by auto
  then show ?thesis
  proof (elim disjE)
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))"
    then show ?thesis
      by (auto intro: sides_map_ltree_st_fun_of_st[OF sd_edge]
               simp: in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))"
    then show ?thesis
      by (auto simp: enter_tree_sides_rel in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    then show ?thesis
      by (auto simp: sides_unit_combine_tree_ctx_st_fun_of_st in_set_zip split: prod.splits)
  qed
qed

private lemma ctx_tree_dep_rel_seeded:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
  shows "dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
proof -
  have split: "set (zip
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
       @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
       @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))
    = set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
      \<union> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
      \<union> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by (simp add: zip_append Un_assoc)
  from mem split have
    "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))
   \<or> (t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    by auto
  then show ?thesis
  proof (elim disjE)
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps)
               (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps))"
    then show ?thesis
      by (auto simp: dep_aux_map_ltree_st_eq[OF dep_edge] in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs)
                 (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs))"
    then show ?thesis
      by (auto simp: enter_tree_dep_rel in_set_zip split: prod.splits)
  next
    assume "(t_st, t_abs) \<in> set (zip (map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
                 (map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
    then show ?thesis
      by (auto simp: dep_aux_unit_combine_tree_ctx_st in_set_zip split: prod.splits)
  qed
qed

private lemma ctx_fold_traverse_rel_seeded:
  "fun_of_st (traverse_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)) \<sigma>_st)
   = traverse_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k))"
proof (rule side_rhs_fold_ctx_st_traverse_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel_seeded)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)"
    by simp
qed

private lemma ctx_fold_sides_rel_seeded:
  "fun_of_st (sides_of_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)) \<sigma>_st k)
   = sides_of_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (rule side_rhs_fold_ctx_st_sides_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st k.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (sides_of_rhs t_st \<sigma>_st k)
       = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    by (rule ctx_tree_sides_rel_seeded)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel_seeded)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)"
    by simp
qed

private lemma ctx_fold_dep_rel_seeded:
  "dep_aux \<sigma>_st
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
         @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
         @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs))"
proof (rule dep_aux_side_rhs_fold_ctx_st_eq)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)) \<Longrightarrow>
       dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
    by (rule ctx_tree_dep_rel_seeded)
  show "\<And>t_st t_abs \<sigma>_st.
       (t_st, t_abs) \<in> set (zip
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
         (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
          @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
          @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st)
       = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule ctx_tree_traverse_rel_seeded)
  show "length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs_st (ent_st ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_st ctx cc ex) cs)
      = length
       (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)) ps
        @ map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. Answer (combine_abs (ent_abs ctx) s))) qs
        @ map (\<lambda>(cc, ex). scmb_abs ctx cc ex) cs)"
    by simp
qed

lemma fun_of_st_eq_side_cfg_T_eff_ctx_seeded_st:
  "fun_of_st
     (eq (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st ()) (v, ctx) \<sigma>_st)
   = eq (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
       (v, ctx) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding eq_side_cfg_T_eff_ctx_seeded side_cfg_T_eff_ctx_seeded_st_def
  by (simp add: Let_def traverse_side_rhs_fold_ctx ctx_fold_traverse_rel_seeded fun_of_st_sup)

lemma fun_of_st_sides_side_cfg_T_eff_ctx_seeded_st:
  "fun_of_st
     (sides_of_rhs (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st () (v, ctx)) \<sigma>_st k)
   = sides_of_rhs
       (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () (v, ctx))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  unfolding side_cfg_T_eff_ctx_seeded_st_def side_cfg_T_eff_ctx_seeded_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def ctx_fold_sides_rel_seeded fun_of_st_sup)

lemma dep_aux_side_cfg_T_eff_ctx_seeded_st_eq:
  "dep_aux \<sigma>_st (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st () (v, ctx))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () (v, ctx))"
  unfolding side_cfg_T_eff_ctx_seeded_st_def side_cfg_T_eff_ctx_seeded_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def ctx_fold_dep_rel_seeded)

theorem part_post_solution_ctx_seeded_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st ()) x sigma_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof (rule part_post_solution_st_to_abs_transport[OF _ _ _ pp_st])
  fix v \<sigma>
  show "fun_of_st (eq (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st ()) v \<sigma>)
        = eq (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
            v (\<lambda>k. fun_of_st (\<sigma> k))"
    using fun_of_st_eq_side_cfg_T_eff_ctx_seeded_st[where v="fst v" and ctx="snd v"]
    by (cases v) simp
next
  fix v \<sigma> k
  show "fun_of_st (sides_of_rhs (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st () v) \<sigma> k)
        = sides_of_rhs (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () v)
            (\<lambda>k. fun_of_st (\<sigma> k)) k"
    using fun_of_st_sides_side_cfg_T_eff_ctx_seeded_st[where v="fst v" and ctx="snd v" and k=k]
    by (cases v) simp
next
  fix v \<sigma>
  show "dep_aux \<sigma> (side_cfg_T_eff_ctx_seeded_st scmb_st ent_st g etf_st bot0_st s0_st () v)
        = dep_aux (\<lambda>k. fun_of_st (\<sigma> k)) (side_cfg_T_eff_ctx_seeded scmb_abs ent_abs g etf (fun_of_st bot0_st) (fun_of_st s0_st) () v)"
    using dep_aux_side_cfg_T_eff_ctx_seeded_st_eq[where v="fst v" and ctx="snd v"]
    by (cases v) simp
qed

end

lemma part_post_solution_ctx_seeded_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st :: "'a st"
  fixes ec :: "'c \<Rightarrow> 'a st \<Rightarrow> 'c"
  fixes ent_st :: "'c \<Rightarrow> 'a st"
  fixes ent_abs :: "'c \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes ent_commute: "\<And>c. fun_of_st (ent_st c) = ent_abs c"
  assumes pp_st:
    "part_post_solution
       (side_cfg_T_eff_ctx_seeded_st (\<lambda>ctx cc ex. unit_combine_tree_ctx_st ec cc ex ctx) ent_st
          g etf_st bot0_st s0_st ()) x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_ctx_seeded
          (\<lambda>ctx cc ex. unit_combine_tree_ctx (\<lambda>ctx a. ec ctx (st_of_abs a)) cc ex ctx) ent_abs
          g etf (fun_of_st bot0_st) (fun_of_st s0_st) ())
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have tr_edge:
    "\<And>a u sigma_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) sigma_st)
     = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (sigma_st k))"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute Let_def)
  have sd_edge:
    "\<And>a u sigma_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) sigma_st k)
     = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (sigma_st k)) k"
    using sides_apply_etf_st_unit_transfer[OF edge_st edge comb comb_st commute]
    by (simp add: o_def)
  have dep_edge:
    "\<And>a u sigma_st. dep_aux sigma_st (apply_etf_st etf_st a u)
     = dep_aux (\<lambda>k. fun_of_st (sigma_st k)) (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  show ?thesis
    by (rule part_post_solution_ctx_seeded_st_to_abs_eff
          [OF tr_edge sd_edge dep_edge ent_commute pp_st])
qed

end

