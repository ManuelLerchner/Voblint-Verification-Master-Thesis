theory Digest_Keyed_Writer
  imports Exec_Cmp_Bridge
begin

section \<open>Generic digest-keyed side-effecting generator\<close>

text \<open>
  The executable generator missing from \<^const>\<open>side_cfg_T_eff_cmp_st\<close> (context-keyed) and
  \<^const>\<open>side_cfg_T_eff_cmp_site_st\<close> (site-keyed): each intra global write is routed to the
  slot \<^emph>\<open>keyed by a digest of the write-point abstract state\<close>, \<open>dg s\<close>.  This is Goblint's
  \<open>sideg\<close>-with-digest --- the write key is a projection of the local state at the write
  (\<open>Digest.compute man.local\<close>), so two writes to one global that differ in their digest land
  in different partitions even inside one function under one context.

  The shape reuses the query-then-side idiom already proven for \<^const>\<open>switching_combine_st\<close>:
  each intra edge \<open>(u, a)\<close> first queries the predecessor state \<open>s = \<sigma> (Inl (u, c))\<close>, then
  relabels the transfer tree's globals to \<open>dg s\<close> via \<^const>\<open>map_gtree\<close>.  For an equality
  digest the same key filters reads, so the read at \<open>(u, c)\<close> already sees exactly its own
  digest partition.
\<close>

definition side_cfg_T_eff_digest_st ::
  "('a st \<Rightarrow> 'g) \<Rightarrow> ('c \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> (pp \<times> 'c, 'g, 'a st) strategy_tree)
   \<Rightarrow> cfg \<Rightarrow> (unit, ('a::bounded_semilattice_sup_bot) st) effectful_st_transfer
   \<Rightarrow> 'a st \<Rightarrow> 'a st \<Rightarrow> 'a st
   \<Rightarrow> (pp \<times> 'c, 'g, 'a st) eqsT"
where
  "side_cfg_T_eff_digest_st dg cmb g etf fresh_frame_st bot0_st s0_st =
     (\<lambda>(v, c).
        let acc0 = (if v = cfg_entry g then bot0_st \<squnion> restrict_local_st s0_st else bot0_st)
                   \<squnion> (if is_frame_entry g v then fresh_frame_st else \<bottom>);
            intra = map (\<lambda>(u, a).
                          QueryL (u, c) (\<lambda>s.
                            map_gtree (\<lambda>_. dg s)
                              (map_ltree (\<lambda>w. (w, c)) (apply_etf_st etf a u))))
                        (non_enter_predecessor_list g v);
            comb  = map (\<lambda>(cc, ex). cmb c cc ex) (combine_predecessor_list g v);
            t = side_rhs_fold_ctx_st acc0 (intra @ comb)
        in if v = cfg_entry g then Side (dg s0_st) (restrict_global_st s0_st) t else t)"

text \<open>Right-goingness: the generator's rhs is a valid side-effecting strategy tree, so the
  vendored always-join solver accepts it.  The intra digest wrapper is a \<^const>\<open>QueryL\<close> over
  the same unit-edge tree the context generator uses.\<close>

lemma side_rg_side_cfg_T_eff_digest_st_unit:
  assumes edge_st: "\<And>a u. \<exists>f. apply_etf_st etf_st a u = unit_edge_tree_st f u"
  assumes comb: "\<And>ctx cc ex. side_rg (cmb ctx cc ex)"
  shows "side_rg (side_cfg_T_eff_digest_st dg cmb g etf_st fresh_frame_st bot0_st s0_st z)"
proof (cases z)
  case (Pair v ctx)
  have intra: "\<And>u a K. side_rg (map_gtree (\<lambda>_. K)
      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))"
  proof -
    fix u a K
    obtain f where f: "apply_etf_st etf_st a u = unit_edge_tree_st f u"
      using edge_st by blast
    show "side_rg (map_gtree (\<lambda>_. K)
      (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u)))"
      unfolding f
      by (simp add: side_rg_map_gtree side_rg_map_ltree side_rg_unit_edge_tree_st)
  qed
  have fold: "\<And>acc v. side_rg (side_rhs_fold_ctx_st acc
      (map (\<lambda>(u, a). QueryL (u, ctx) (\<lambda>s. map_gtree (\<lambda>_. dg s)
              (map_ltree (\<lambda>w. (w, ctx)) (apply_etf_st etf_st a u))))
          (non_enter_predecessor_list g v)
       @ map (\<lambda>(cc, ex). cmb ctx cc ex) (combine_predecessor_list g v)))"
    by (rule side_rg_side_rhs_fold_ctx_st) (auto simp: intra comb split: prod.splits)
  show ?thesis
    unfolding Pair side_cfg_T_eff_digest_st_def
    by (simp add: Let_def fold)
qed

section \<open>Digest-consistent switching combine\<close>

text \<open>
  The combine sibling of \<^const>\<open>side_cfg_T_eff_digest_st\<close>: it reads the caller's global
  contribution through the \<^emph>\<open>same digest\<close> the writer uses (\<open>QueryG (dg sc)\<close>, not the context
  slot), so the value published to the callee lands in --- and is read from --- one consistent
  partition.  The callee context is the digest of the (prepared) caller, so a call switches to
  the caller's digest partition exactly as \<^const>\<open>switching_combine_st\<close> switches on \<open>ec\<close>.
\<close>

definition switching_combine_digest_st ::
  "('a st \<Rightarrow> 'g) \<Rightarrow> (pp \<Rightarrow> 'a st \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> 'g
   \<Rightarrow> (pp \<times> 'g, 'g, ('a::bounded_semilattice_sup_bot) st) strategy_tree"
where
  "switching_combine_digest_st dg prep cc ex ctx =
     QueryL (cc, ctx) (\<lambda>sc. QueryG (dg sc) (\<lambda>g.
       let caller = prep cc (sc \<squnion> g);
           callee_dg = dg caller in
       Side callee_dg (restrict_global_st caller)
         (QueryL (ex, callee_dg) (\<lambda>se.
           let res = restrict_local_st caller \<squnion> restrict_global_st se in
           Side callee_dg (restrict_global_st res)
             (Answer (restrict_local_st res))))))"

lemma side_rg_switching_combine_digest_st:
  "side_rg (switching_combine_digest_st dg prep cc ex ctx)"
  unfolding switching_combine_digest_st_def by (simp add: Let_def)

end
