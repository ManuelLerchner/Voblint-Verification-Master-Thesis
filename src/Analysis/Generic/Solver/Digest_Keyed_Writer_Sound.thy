theory Digest_Keyed_Writer_Sound
  imports Digest_Keyed_Writer
begin

section \<open>Abstract digest-keyed generator and executable transport\<close>

text \<open>
  The abstract image of \<^const>\<open>side_cfg_T_eff_digest_st\<close>: intra global writes are routed to the
  slot keyed by the digest \<open>dg\<close> of the queried predecessor state, read on \<^typ>\<open>'a abs_state\<close>.
  This is the transport target for the executable \<open>_st\<close> generator, mirroring the pair
  \<^const>\<open>side_cfg_T_eff_cmp\<close> / \<^const>\<open>side_cfg_T_eff_cmp_st\<close>.
\<close>

definition side_cfg_T_eff_digest ::
  "('a abs_state \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, 'a::bounded_semilattice_sup_bot) effectful_domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) eqsT"
where
  "side_cfg_T_eff_digest dg cmb g etf fresh_frame bot0 s0 =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                   \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>);
            intra = map (\<lambda>(u, a).
                          QueryL (u, c) (\<lambda>s.
                            map_gtree (\<lambda>_. dg s)
                              (map_ltree (\<lambda>w. (w, c)) (apply_etf etf a u))))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx acc0 (intra @ comb)
        in if v = cfg_entry g then Side (dg s0) (restrict_global s0) t else t)"

text \<open>Denotation at \<open>(v, ctx)\<close>: the entry \<open>Side\<close> is traverse-transparent, so \<open>eq\<close> is the
  \<^const>\<open>side_rhs_fold_ctx\<close> traversal over the intra query trees and the combine trees.\<close>

lemma eq_side_cfg_T_eff_digest_st:
  "eq (side_cfg_T_eff_digest_st dg cmb g etf fresh_frame_st bot0_st s0_st) (v, ctx) \<sigma> =
     traverse_rhs
       (side_rhs_fold_ctx_st
          ((if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
           \<squnion> (if is_frame_entry g v then fresh_frame_st else \<bottom>))
          (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg s)
                          (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf a u))))
               (non_enter_predecessor_list g v)
           @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))) \<sigma>"
  unfolding side_cfg_T_eff_digest_st_def
  by (simp add: Let_def)

lemma eq_side_cfg_T_eff_digest:
  "eq (side_cfg_T_eff_digest dg cmb g etf fresh_frame bot0 s0) (v, ctx) \<sigma> =
     side_acc_ctx
       ((if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
        \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)) \<sigma>
       (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))))
            (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v))"
  unfolding side_cfg_T_eff_digest_def
  by (simp add: traverse_side_rhs_fold_ctx Let_def)

section \<open>Transport: executable digest post-solution maps to the abstract generator\<close>

text \<open>
  Parametric in the digest generator's data: the executable/abstract edge transfers (related
  by the three edge bridges), the combine builders (three combine bridges), and the digest
  projection \<open>dg\<close> --- executable \<open>dg_st\<close> and abstract \<open>dg_abs\<close> related by \<open>dg_compat\<close>,
  \<open>dg_abs (fun_of_st s) = dg_st s\<close>.  Under these the query-then-side intra tree of the digest
  writer transports exactly as the fixed-key map_gtree of \<^const>\<open>side_cfg_T_eff_cmp\<close> does: the
  \<^const>\<open>QueryL\<close> reduces the state-dependent key to a value at which \<open>dg_compat\<close> aligns the two
  keys, and the residual is the proven \<^const>\<open>map_gtree\<close> / \<^const>\<open>map_ltree\<close> bridge.
\<close>

context
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes bot0_st s0_st fresh_frame_st :: "'a st"
  fixes dg_st :: "'a st \<Rightarrow> 'g"
  fixes dg_abs :: "'a abs_state \<Rightarrow> 'g"
  fixes cmb_st :: "'c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree"
  fixes cmb_abs :: "'c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a abs_state) strategy_tree"
  assumes tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
       = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
       = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
  assumes tr_comb:
    "\<And>ctx cc ex \<sigma>_st. fun_of_st (traverse_rhs (cmb_st ctx cc ex) \<sigma>_st)
       = traverse_rhs (cmb_abs ctx cc ex) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  assumes sd_comb:
    "\<And>ctx cc ex \<sigma>_st k. fun_of_st (sides_of_rhs (cmb_st ctx cc ex) \<sigma>_st k)
       = sides_of_rhs (cmb_abs ctx cc ex) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  assumes dep_comb:
    "\<And>ctx cc ex \<sigma>_st. dep_aux \<sigma>_st (cmb_st ctx cc ex)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (cmb_abs ctx cc ex)"
  assumes dg_compat: "\<And>s. dg_abs (fun_of_st s) = dg_st s"
begin

private lemma digest_intra_traverse_rel:
  "fun_of_st (traverse_rhs (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) \<sigma>_st)
   = traverse_rhs (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) (\<lambda>k. fun_of_st (\<sigma>_st k))"
  by (simp add: dg_compat
        traverse_map_gtree_st_fun_of_st[OF traverse_map_ltree_st_fun_of_st[OF tr_edge]])

private lemma digest_intra_dep_rel:
  "dep_aux \<sigma>_st (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))))"
  by (simp add: dg_compat
        dep_map_gtree_st_fun_of_st[OF dep_aux_map_ltree_st_eq[OF dep_edge]])

private lemma digest_intra_sides_rel:
  "fun_of_st (sides_of_rhs (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) \<sigma>_st k)
   = sides_of_rhs (QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) ) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof -
  let ?K = "dg_st (\<sigma>_st (Inl (u, ctx)))"
  have keyeq: "dg_abs (fun_of_st (\<sigma>_st (Inl (u, ctx)))) = ?K" by (rule dg_compat)
  show ?thesis
  proof (cases k)
    case (Inl x)
    then show ?thesis by (simp add: bot_fun_def)
  next
    case (Inr h)
    show ?thesis
    proof (cases "h = ?K")
      case True
      have st: "sides_of_rhs (map_gtree (\<lambda>_. ?K)
                   (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st (Inr ?K)
                = sides_of_rhs (apply_etf_st etf_st a u)
                    (\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. ?K) z)) (Inr ())"
        by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. ?K"] sides_map_ltree_Inr
              sum.map_comp o_def)
      have abs: "sides_of_rhs (map_gtree (\<lambda>_. ?K)
                   (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k)) (Inr ?K)
                = sides_of_rhs (apply_etf etf a u)
                    (\<lambda>z. fun_of_st (\<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. ?K) z))) (Inr ())"
        by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. ?K"] sides_map_ltree_Inr
              sum.map_comp o_def)
      show ?thesis
        unfolding Inr True using keyeq st abs
          sd_edge[where a=a and u=u
              and \<sigma>_st="\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. ?K) z)" and k="Inr ()"]
        by (simp add: o_def)
    next
      case False
      then have "h \<notin> range (\<lambda>_::unit. ?K)" by simp
      then show ?thesis
        using Inr keyeq by (simp add: sides_map_gtree_off_gen bot_fun_def)
    qed
  qed
qed

private lemma digest_tree_traverse_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
  using mem
  by (auto simp: tr_comb dg_compat in_set_zip
        traverse_map_gtree_st_fun_of_st[OF traverse_map_ltree_st_fun_of_st[OF tr_edge]]
        split: prod.splits)

private lemma digest_sides_map_key:
  "fun_of_st (sides_of_rhs (map_gtree (\<lambda>_. K)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st k)
   = sides_of_rhs (map_gtree (\<lambda>_. K)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (cases k)
  case (Inl x)
  then show ?thesis by (simp add: bot_fun_def)
next
  case (Inr h)
  show ?thesis
  proof (cases "h = K")
    case True
    have st: "sides_of_rhs (map_gtree (\<lambda>_. K)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))) \<sigma>_st (Inr K)
              = sides_of_rhs (apply_etf_st etf_st a u)
                  (\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. K) z)) (Inr ())"
      by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. K"] sides_map_ltree_Inr
            sum.map_comp o_def)
    have abs: "sides_of_rhs (map_gtree (\<lambda>_. K)
                 (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))) (\<lambda>k. fun_of_st (\<sigma>_st k)) (Inr K)
              = sides_of_rhs (apply_etf etf a u)
                  (\<lambda>z. fun_of_st (\<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. K) z))) (Inr ())"
      by (simp add: sides_map_gtree_unit_gen[where r="\<lambda>_. K"] sides_map_ltree_Inr
            sum.map_comp o_def)
    show ?thesis
      unfolding Inr True st abs
      using sd_edge[where a=a and u=u
              and \<sigma>_st="\<lambda>z. \<sigma>_st (map_sum (\<lambda>w. (w, ctx)) (\<lambda>_. K) z)" and k="Inr ()"]
      by (simp add: o_def)
  next
    case False
    then have "h \<notin> range (\<lambda>_::unit. K)" by simp
    then show ?thesis
      using Inr by (simp add: sides_map_gtree_off_gen bot_fun_def)
  qed
qed

private lemma digest_tree_sides_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "fun_of_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  using mem
  by (auto simp: sd_comb dg_compat in_set_zip digest_sides_map_key split: prod.splits)

private lemma digest_tree_dep_rel:
  assumes mem: "(t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
  shows "dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
  using mem
  by (auto simp: dep_comb dg_compat in_set_zip
        dep_map_gtree_st_fun_of_st[OF dep_aux_map_ltree_st_eq[OF dep_edge]]
        split: prod.splits)

private lemma digest_fold_traverse_rel:
  "fun_of_st (traverse_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st)
   = traverse_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k))"
proof (rule side_rhs_fold_ctx_st_traverse_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule digest_tree_traverse_rel)
qed simp

private lemma digest_fold_sides_rel:
  "fun_of_st (sides_of_rhs
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)) \<sigma>_st k)
   = sides_of_rhs
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))
      (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof (rule side_rhs_fold_ctx_st_sides_fun_of_st)
  show "\<And>t_st t_abs \<sigma>_st k. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (sides_of_rhs t_st \<sigma>_st k) = sides_of_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    by (rule digest_tree_sides_rel)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule digest_tree_traverse_rel)
qed simp

private lemma digest_fold_dep_rel:
  "dep_aux \<sigma>_st
      (side_rhs_fold_ctx_st acc_st
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
      (side_rhs_fold_ctx (fun_of_st acc_st)
        (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
                (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
         @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs))"
proof (rule dep_aux_side_rhs_fold_ctx_st_eq)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       dep_aux \<sigma>_st t_st = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) t_abs"
    by (rule digest_tree_dep_rel)
  show "\<And>t_st t_abs \<sigma>_st. (t_st, t_abs) \<in> set (zip
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_st s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_st ctx cc ex) cs)
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg_abs s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))) ps
       @ map (\<lambda>(cc, ex). cmb_abs ctx cc ex) cs)) \<Longrightarrow>
       fun_of_st (traverse_rhs t_st \<sigma>_st) = traverse_rhs t_abs (\<lambda>k. fun_of_st (\<sigma>_st k))"
    by (rule digest_tree_traverse_rel)
qed simp

lemma fun_of_st_eq_side_cfg_T_eff_digest_st:
  "fun_of_st
     (eq (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st) (v, ctx) \<sigma>_st)
   = eq (side_cfg_T_eff_digest dg_abs cmb_abs g etf
           (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st)) (v, ctx)
       (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding eq_side_cfg_T_eff_digest_st eq_side_cfg_T_eff_digest
  by (simp add: Let_def traverse_side_rhs_fold_ctx digest_fold_traverse_rel
        bot_fun_def[symmetric])

lemma fun_of_st_sides_side_cfg_T_eff_digest_st:
  "fun_of_st
     (sides_of_rhs (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st (v, ctx)) \<sigma>_st k)
   = sides_of_rhs
       (side_cfg_T_eff_digest dg_abs cmb_abs g etf
          (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))
       (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
  unfolding side_cfg_T_eff_digest_st_def side_cfg_T_eff_digest_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def dg_compat digest_fold_sides_rel bot_fun_def[symmetric])

lemma dep_aux_side_cfg_T_eff_digest_st_eq:
  "dep_aux \<sigma>_st (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st (v, ctx))
   = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k))
       (side_cfg_T_eff_digest dg_abs cmb_abs g etf
          (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) (v, ctx))"
  unfolding side_cfg_T_eff_digest_st_def side_cfg_T_eff_digest_def
  by (cases "v = cfg_entry g")
     (simp_all add: Let_def digest_fold_dep_rel bot_fun_def[symmetric])

theorem part_post_solution_digest_st_to_abs_eff:
  assumes pp_st:
    "part_post_solution (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
           (side_cfg_T_eff_digest dg_abs cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
           x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have x_in: "x \<in> vars" using pp_st by simp
  show ?thesis
  proof (intro conjI x_in ballI conjI)
    fix v assume v_in: "v \<in> vars"
    show "dep\<^sub>L (side_cfg_T_eff_digest dg_abs cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
            (\<lambda>k. fun_of_st (sigma_st k)) v \<subseteq> vars"
    proof -
      have "dep\<^sub>L (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st) sigma_st v
        = dep\<^sub>L (side_cfg_T_eff_digest dg_abs cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
            (\<lambda>k. fun_of_st (sigma_st k)) v"
        using dep_aux_side_cfg_T_eff_digest_st_eq[where v="fst v" and ctx="snd v"]
        by (cases v) (simp add: dep\<^sub>L_def dep_def)
      then show ?thesis using pp_st v_in by auto
    qed
    show "eq (side_cfg_T_eff_digest dg_abs cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st)) v
            (\<lambda>k. fun_of_st (sigma_st k)) \<le> (\<lambda>k. fun_of_st (sigma_st k)) (Inl v)"
    proof -
      have le_st: "eq (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st) v sigma_st
                   \<le> sigma_st (Inl v)"
        using pp_st v_in by simp
      show ?thesis
        using fun_of_st_mono[OF le_st]
          fun_of_st_eq_side_cfg_T_eff_digest_st[where v="fst v" and ctx="snd v"]
        by (cases v) simp
    qed
    show "sides_of_rhs (side_cfg_T_eff_digest dg_abs cmb_abs g etf
              (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v)
            (\<lambda>k. fun_of_st (sigma_st k)) \<le> (\<lambda>k. fun_of_st (sigma_st k))"
    proof (rule le_funI)
      fix k
      have le_st: "sides_of_rhs (side_cfg_T_eff_digest_st dg_st cmb_st g etf_st fresh_frame_st bot0_st s0_st v) sigma_st k
                   \<le> sigma_st k"
        using pp_st v_in by (simp add: le_fun_def)
      show "sides_of_rhs (side_cfg_T_eff_digest dg_abs cmb_abs g etf
                (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st) v)
              (\<lambda>k. fun_of_st (sigma_st k)) k
            \<le> (\<lambda>k. fun_of_st (sigma_st k)) k"
        using fun_of_st_mono[OF le_st]
          fun_of_st_sides_side_cfg_T_eff_digest_st[where v="fst v" and ctx="snd v" and k=k]
        by (cases v) simp
    qed
  qed
qed

end

section \<open>Abstract digest-consistent switching combine and its bridges\<close>

text \<open>
  The abstract image of \<^const>\<open>switching_combine_digest_st\<close>: the caller's global contribution is
  read at the digest key \<open>dg sc\<close>, and both \<^const>\<open>Side\<close> writes publish to the callee digest
  \<open>dg caller\<close>.  These are the combine bridges the transport context above consumes, so the digest
  generator's combine can be threaded through \<open>part_post_solution_digest_st_to_abs_eff\<close>.
\<close>

definition abs_switching_combine_digest ::
  "('a abs_state \<Rightarrow> 'g) \<Rightarrow> (pp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'g, 'g, ('a::bounded_semilattice_sup_bot) abs_state) strategy_tree"
where
  "abs_switching_combine_digest dg prep cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG (dg sc) (\<lambda>g.
       let caller = prep cc (sc \<squnion> g);
           callee_dg = dg caller in
       Side callee_dg (restrict_global caller)
         (QueryL (ex, callee_dg) (\<lambda>se.
           let res = restrict_local caller \<squnion> restrict_global se in
           Side callee_dg (restrict_global res)
             (Answer (restrict_local res))))))"

lemma traverse_switching_combine_digest_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes dgc: "\<And>s. dg_abs (fun_of_st s) = dg_st s"
  shows "fun_of_st (traverse_rhs (switching_combine_digest_st dg_st prep_st cc ex ctx) \<sigma>_st)
         = traverse_rhs (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)
             (\<lambda>k. fun_of_st (\<sigma>_st k))"
  unfolding switching_combine_digest_st_def abs_switching_combine_digest_def
  by (simp del: fun_of_st_sup
      add: Let_def o_def prep dgc restrict_local_combine_eq fun_of_st_sup[symmetric])

lemma sides_switching_combine_digest_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes dgc: "\<And>s. dg_abs (fun_of_st s) = dg_st s"
  shows "fun_of_st (sides_of_rhs (switching_combine_digest_st dg_st prep_st cc ex ctx) \<sigma>_st k)
         = sides_of_rhs (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)
             (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
proof -
  have dgprep2: "\<And>cc a b. dg_abs (prep_abs cc (fun_of_st a \<squnion> fun_of_st b)) = dg_st (prep_st cc (a \<squnion> b))"
  proof -
    fix cc a b
    have "dg_abs (prep_abs cc (fun_of_st a \<squnion> fun_of_st b)) = dg_abs (prep_abs cc (fun_of_st (a \<squnion> b)))"
      by (simp add: fun_of_st_sup)
    also have "\<dots> = dg_abs (fun_of_st (prep_st cc (a \<squnion> b)))" by (simp add: prep)
    also have "\<dots> = dg_st (prep_st cc (a \<squnion> b))" by (rule dgc)
    finally show "dg_abs (prep_abs cc (fun_of_st a \<squnion> fun_of_st b)) = dg_st (prep_st cc (a \<squnion> b))" .
  qed
  show ?thesis
  proof (cases k)
    case (Inl x)
    then show ?thesis
      unfolding switching_combine_digest_st_def abs_switching_combine_digest_def
      by (simp add: Let_def o_def prep dgc bot_fun_def)
  next
    case (Inr h)
    then show ?thesis
      unfolding switching_combine_digest_st_def abs_switching_combine_digest_def
      by (simp add: Let_def o_def prep dgc dgprep2 restrict_global_combine_eq bot_fun_def[symmetric])
  qed
qed

lemma dep_switching_combine_digest_st_fun_of_st:
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes dgc: "\<And>s. dg_abs (fun_of_st s) = dg_st s"
  shows "dep_aux \<sigma>_st (switching_combine_digest_st dg_st prep_st cc ex ctx)
         = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)"
proof -
  have dgprep: "\<And>cc s. dg_abs (prep_abs cc (fun_of_st s)) = dg_st (prep_st cc s)"
    by (simp add: prep[symmetric] dgc)
  show ?thesis
    unfolding switching_combine_digest_st_def abs_switching_combine_digest_def
    by (simp del: fun_of_st_sup add: Let_def o_def prep dgc dgprep fun_of_st_sup[symmetric])
qed

section \<open>Unit-transfer transport for the digest switching generator\<close>

text \<open>
  The self-contained transport an instance applies: given the domain's edge/combine trees as
  unit trees (\<open>edge\<close> / \<open>comb\<close> / \<open>edge_st\<close> / \<open>comb_st\<close> / \<open>commute\<close> --- the standard framed-transfer
  bundle every \<open>_st\<close> domain supplies), the call-state transform bridge (\<open>prep\<close>), and the digest
  compatibility (\<open>dgc\<close>), a post-solution of the executable digest generator maps to a post-solution
  of its abstract image.  Mirrors \<^theory_text>\<open>part_post_solution_cmp_switching_st_to_abs_eff_unit_transfer\<close>
  with the context selector replaced by the digest projection.
\<close>

lemma part_post_solution_digest_switching_st_to_abs_eff_unit_transfer:
  fixes g :: cfg
  fixes etf_st :: "(unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer"
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  fixes F_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  fixes bot0_st s0_st fresh_frame_st :: "'a st"
  fixes dg_st :: "'a st \<Rightarrow> 'g"
  fixes dg_abs :: "'a abs_state \<Rightarrow> 'g"
  fixes prep_st :: "pp \<Rightarrow> 'a st \<Rightarrow> 'a st"
  fixes prep_abs :: "pp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes edge: "\<And>a u. apply_etf etf a u = unit_edge_tree (F a) u"
  assumes comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
  assumes edge_st: "\<And>a u. apply_etf_st etf_st a u = unit_edge_tree_st (F_st a) u"
  assumes comb_st: "\<And>cc ex. etf_combine_st etf_st cc ex = unit_combine_tree_st cc ex"
  assumes commute: "\<And>a s. fun_of_st (F_st a s) = F a (fun_of_st s)"
  assumes prep: "\<And>cc s. fun_of_st (prep_st cc s) = prep_abs cc (fun_of_st s)"
  assumes dgc: "\<And>s. dg_abs (fun_of_st s) = dg_st s"
  assumes pp_st:
    "part_post_solution
       (side_cfg_T_eff_digest_st dg_st
          (\<lambda>ctx cc ex. switching_combine_digest_st dg_st prep_st cc ex ctx)
          g etf_st fresh_frame_st bot0_st s0_st) x sigma_st vars"
  shows "part_post_solution
       (side_cfg_T_eff_digest dg_abs
          (\<lambda>ctx cc ex. abs_switching_combine_digest dg_abs prep_abs cc ex ctx)
          g etf (fun_of_st fresh_frame_st) (fun_of_st bot0_st) (fun_of_st s0_st))
       x (\<lambda>k. fun_of_st (sigma_st k)) vars"
proof -
  have tr_edge:
    "\<And>a u \<sigma>_st. fun_of_st (traverse_rhs (apply_etf_st etf_st a u) \<sigma>_st)
     = traverse_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k))"
    unfolding edge_st edge traverse_unit_edge_tree_st traverse_unit_edge_tree
    by (simp add: commute Let_def)
  have sd_edge:
    "\<And>a u \<sigma>_st k. fun_of_st (sides_of_rhs (apply_etf_st etf_st a u) \<sigma>_st k)
     = sides_of_rhs (apply_etf etf a u) (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using sides_apply_etf_st_unit_transfer[OF edge_st edge comb comb_st commute]
    by (simp add: o_def)
  have dep_edge:
    "\<And>a u \<sigma>_st. dep_aux \<sigma>_st (apply_etf_st etf_st a u)
     = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (apply_etf etf a u)"
    by (simp add: edge_st edge dep_aux_unit_edge_tree_st)
  have tr_comb:
    "\<And>ctx cc ex \<sigma>_st.
       fun_of_st (traverse_rhs (switching_combine_digest_st dg_st prep_st cc ex ctx) \<sigma>_st)
       = traverse_rhs (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k))"
    using prep dgc by (rule traverse_switching_combine_digest_st_fun_of_st)
  have sd_comb:
    "\<And>ctx cc ex \<sigma>_st k.
       fun_of_st (sides_of_rhs (switching_combine_digest_st dg_st prep_st cc ex ctx) \<sigma>_st k)
       = sides_of_rhs (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)
           (\<lambda>k. fun_of_st (\<sigma>_st k)) k"
    using prep dgc by (rule sides_switching_combine_digest_st_fun_of_st)
  have dep_comb:
    "\<And>ctx cc ex \<sigma>_st.
       dep_aux \<sigma>_st (switching_combine_digest_st dg_st prep_st cc ex ctx)
       = dep_aux (\<lambda>k. fun_of_st (\<sigma>_st k)) (abs_switching_combine_digest dg_abs prep_abs cc ex ctx)"
    using prep dgc by (rule dep_switching_combine_digest_st_fun_of_st)
  show ?thesis
    by (rule part_post_solution_digest_st_to_abs_eff
          [OF tr_edge sd_edge dep_edge tr_comb sd_comb dep_comb dgc pp_st])
qed
end
