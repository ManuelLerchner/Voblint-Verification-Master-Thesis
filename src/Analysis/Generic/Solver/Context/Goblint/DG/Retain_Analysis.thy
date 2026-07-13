theory Retain_Analysis
  imports DG_Soundness
begin

section \<open>The retain analysis\<close>

text \<open>
  An ordinary analysis on the D/G framework of \<^theory>\<open>Voblint_Analysis.DG_Framework\<close>:
  its \<open>D\<close> is locals \<times> flow-sensitive global snapshot, its \<open>G\<close> the global state.
  The framework transports \<open>Answer : D\<close> and \<open>Side : G\<close> and never copies \<open>G\<close>
  into \<open>D\<close>; the snapshot in the Answer is written by this analysis's own
  transfer.  The homogeneous \<open>retain_edge_tree\<close> (one \<open>'a abs_state\<close> value type,
  Answer keeps the full result) is this analysis's homogeneous form; everything
  retain-specific --- the tree, its transfer factory, its soundness, its keyed
  exactness reduction, and its executable mirror --- lives here, not in the
  framework.
\<close>

subsection \<open>The homogeneous retain tree\<close>

text \<open>
  The retain-globals edge tree keeps the full result in the local Answer (globals
  retained) instead of \<^const>\<open>restrict_local\<close>; the Side publication of
  \<^term>\<open>restrict_global res\<close> is unchanged.  It differs from \<^const>\<open>unit_edge_tree\<close>
  only in the Answer payload, which \<^const>\<open>sides_of_rhs\<close> ignores, so their side maps
  coincide (\<open>sides_retain_eq_unit\<close>) and \<^const>\<open>etf_full\<close> is preserved
  (\<open>etf_full_retain_eq_unit_edge_tree\<close>).  Only the local slot changes, now carrying
  the flow-sensitive global.
\<close>

definition retain_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> (unit, 'a) edge_tf_tree"
where
  "retain_edge_tree f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global res) (Answer res)))"

lemma traverse_retain_edge_tree:
  "traverse_rhs (retain_edge_tree f u) \<sigma> = f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding retain_edge_tree_def by (simp add: Let_def)

lemma sides_retain_eq_unit:
  "sides_of_rhs (retain_edge_tree f u) \<sigma> = sides_of_rhs (unit_edge_tree f u) \<sigma>"
  unfolding retain_edge_tree_def unit_edge_tree_def by (simp add: Let_def)

lemma sides_retain_edge_tree_Inr:
  "sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ()) =
   restrict_global (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  by (simp add: sides_retain_eq_unit sides_unit_edge_tree_Inr)

lemma all_sides_retain_edge_tree:
  "all_sides (retain_edge_tree f u) \<sigma> = restrict_global (f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())))"
  by (simp add: all_sides_eq_sides_Inr_unit sides_retain_edge_tree_Inr)

lemma etf_full_retain_edge_tree:
  "etf_full (retain_edge_tree f u) \<sigma> = f (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ()))"
  unfolding etf_full_def traverse_retain_edge_tree all_sides_retain_edge_tree
    restrict_global_def sup_fun_def
  by (rule ext) simp

text \<open>
  The reassembled result is unchanged with respect to the unit tree, so soundness
  proved for \<^const>\<open>unit_edge_tree\<close> holds for \<^const>\<open>retain_edge_tree\<close> unchanged.
\<close>

lemma etf_full_retain_eq_unit_edge_tree:
  "etf_full (retain_edge_tree f u) \<sigma> = etf_full (unit_edge_tree f u) \<sigma>"
  by (simp add: etf_full_retain_edge_tree etf_full_unit_edge_tree)

lemma etf_collecting_full_retain_eq_unit_edge_tree:
  "etf_collecting_full (retain_edge_tree f u) \<sigma> =
   etf_collecting_full (unit_edge_tree f u) \<sigma>"
  by (simp add: etf_collecting_full_def etf_full_retain_eq_unit_edge_tree)

lemma sides_inr_local_bot_retain_edge_tree:
  "local_bot_on_locals (sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr g))"
  by (simp add: sides_retain_eq_unit sides_inr_local_bot_unit_edge_tree)



subsection \<open>The retain transfer factory and its soundness\<close>

definition retain_etf_of_transfer ::
  "'a::sound_domain domain_transfer \<Rightarrow> (unit, 'a) effectful_domain_transfer"
where
  "retain_etf_of_transfer tf = \<lparr>
    etf_nop        = (\<lambda>u. retain_edge_tree (apply_tf tf EA_Nop) u),
    etf_assign     = (\<lambda>x e u. retain_edge_tree (apply_tf tf (EA_Assign x e)) u),
    etf_assume     = (\<lambda>b u. retain_edge_tree (apply_tf tf (EA_Assume b)) u),
    etf_assume_not = (\<lambda>b u. retain_edge_tree (apply_tf tf (EA_AssumeNot b)) u),
    etf_enter      = (\<lambda>u. retain_edge_tree (apply_tf tf EA_Enter) u),
    etf_combine    = unit_combine_tree
  \<rparr>"

lemma apply_etf_retain_of_transfer:
  "apply_etf (retain_etf_of_transfer tf) a u = retain_edge_tree (apply_tf tf a) u"
  unfolding retain_etf_of_transfer_def by (cases a) simp_all

lemma etf_combine_retain_of_transfer:
  "etf_combine (retain_etf_of_transfer tf) cc ex = unit_combine_tree cc ex"
  unfolding retain_etf_of_transfer_def by simp

lemma sound_effectful_transfer_retain_of_transfer:
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes st: "sound_transfer tf"
  shows "sound_effectful_transfer (retain_etf_of_transfer tf)"
proof -
  interpret sound_transfer tf using st .
  show ?thesis
  proof (unfold_locales; unfold glob_env_unit)
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s \<in> \<lbrakk>etf_collecting_full (etf_nop (retain_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: retain_etf_of_transfer_def glob_env_unit
          etf_collecting_full_retain_eq_unit_edge_tree
          intro: in_gamma_unit_edge_tree_nop)
  next
    show "\<forall>x e u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              s(x := aval e s) \<in> \<lbrakk>etf_collecting_full
                (etf_assign (retain_etf_of_transfer tf) x e u) \<sigma>\<rbrakk>)"
      by (auto simp add: retain_etf_of_transfer_def glob_env_unit
          etf_collecting_full_retain_eq_unit_edge_tree
          intro: in_gamma_unit_edge_tree_assign)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume (retain_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: retain_etf_of_transfer_def glob_env_unit
          etf_collecting_full_retain_eq_unit_edge_tree
          intro: in_gamma_unit_edge_tree_assume)
  next
    show "\<forall>(b::bexp) u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>. \<not> bval b s
            \<longrightarrow> s \<in> \<lbrakk>etf_collecting_full
                  (etf_assume_not (retain_etf_of_transfer tf) b u) \<sigma>\<rbrakk>)"
      by (auto simp add: retain_etf_of_transfer_def glob_env_unit
          etf_collecting_full_retain_eq_unit_edge_tree
          intro: in_gamma_unit_edge_tree_assume_not)
  next
    show "\<forall>u \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              enter_state s \<in> \<lbrakk>etf_collecting_full
                (etf_enter (retain_etf_of_transfer tf) u) \<sigma>\<rbrakk>)"
      by (auto simp add: retain_etf_of_transfer_def glob_env_unit
          etf_collecting_full_retain_eq_unit_edge_tree
          intro: in_gamma_unit_edge_tree_enter)
  next
    show "\<forall>cc ex \<sigma>. inr_slot_locals_bot \<sigma> \<longrightarrow>
            (\<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())\<rbrakk>.
            \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())\<rbrakk>.
              <s|t> \<in> \<lbrakk>etf_full (etf_combine (retain_etf_of_transfer tf) cc ex) \<sigma>\<rbrakk>)"
      by (auto simp add: etf_combine_retain_of_transfer etf_full_unit_combine_tree
           intro: combine_states_sound)
  qed
qed

subsection \<open>The keyed snapshot invariant is derivable from an exact solution\<close>

text \<open>
  \<^const>\<open>inl_glob_le_keyed_ctx\<close> is not an axiom for this analysis: it is the
  globals-projection of the exact-fixpoint property.  At an exact
  \<^const>\<open>part_solution\<close> each retain edge publishes its written global to the keyed
  slot (the intra tree's \<open>Side\<close>), while its full result --- globals included ---
  is the local Answer.  So the local slot's globals are a sub-join of what the
  keyed slot accumulates, hence dominated by it.  A mere
  \<^const>\<open>part_post_solution\<close> is insufficient: it bounds the equation \<^emph>\<open>below\<close>
  the local slot but leaves the local slot itself unbounded \<^emph>\<open>above\<close>, so an
  adversarial post-solution can inflate a local global past the keyed slot.  The
  vendored always-join side solver returns an exact \<^const>\<open>part_solution\<close> (no
  widening), so the invariant holds at every reachable slot.
\<close>

text \<open>Per-tree domination for a keyed retain intra edge: traverse-global \<^emph>\<open>equals\<close> the keyed side.\<close>
lemma restrict_global_traverse_retain_intra:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma>)
         = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
              (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma> (Inr (gkey ctx))"
proof -
  have "restrict_global (traverse_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma>)
        = restrict_global (traverse_rhs (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>))"
    by (simp add: traverse_intra_pull_gk)
  also have "\<dots> = all_sides (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>)"
    by (simp add: traverse_retain_edge_tree all_sides_retain_edge_tree)
  also have "\<dots> = sides_of_rhs (retain_edge_tree f u) (pull_gk gkey ctx \<sigma>) (Inr ())"
    by (rule all_sides_eq_sides_Inr_unit)
  also have "\<dots> = sides_of_rhs (map_gtree (\<lambda>_. gkey ctx)
             (map_ltree (\<lambda>w. (w, ctx)) (retain_edge_tree f u))) \<sigma> (Inr (gkey ctx))"
    by (rule sides_intra_pull_gk[symmetric])
  finally show ?thesis .
qed

theorem part_solution_imp_inl_glob_le_keyed_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes retain_edge: "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and retain_comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and bot0_glob: "restrict_global bot0 = \<bottom>"
    and frame_glob: "restrict_global fresh_frame = \<bottom>"
    and ps: "part_solution (side_cfg_T_eff_cmp gkey
                (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                    (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                g etf fresh_frame bot0 s0) x \<sigma> vars"
    and v: "(v, ctx) \<in> vars"
    and y: "is_global y"
  shows "\<sigma> (Inl (v, ctx)) y \<le> \<sigma> (Inr (gkey ctx)) y"
proof -
  let ?cmb = "\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c) (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex))"
  let ?T = "side_cfg_T_eff_cmp gkey ?cmb g etf fresh_frame bot0 s0"
  let ?acc0 = "(if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
                \<squnion> (if is_frame_entry g v then fresh_frame else \<bottom>)"
  let ?intra = "map (\<lambda>(u, a). map_gtree (\<lambda>_. gkey ctx)
                        (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u)))
                    (non_enter_predecessor_list g v)"
  let ?comb = "map (\<lambda>(cc, ex). ?cmb ctx cc ex) (combine_predecessor_list g v)"
  have exact: "eq ?T (v, ctx) \<sigma> = \<sigma> (Inl (v, ctx))" using ps v by auto
  have hyp: "\<And>t. t \<in> set (?intra @ ?comb)
             \<Longrightarrow> restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr (gkey ctx))"
  proof -
    fix t assume t: "t \<in> set (?intra @ ?comb)"
    show "restrict_global (traverse_rhs t \<sigma>) \<le> sides_of_rhs t \<sigma> (Inr (gkey ctx))"
    proof (cases "t \<in> set ?intra")
      case True
      then obtain u a where
        "t = map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))"
        by auto
      thus ?thesis
        by (simp add: retain_edge restrict_global_traverse_retain_intra)
    next
      case False
      with t have "t \<in> set ?comb" by simp
      then obtain cc ex where
        "t = map_gtree (\<lambda>_. gkey ctx) (map_ltree (\<lambda>w. (w, ctx)) (etf_combine etf cc ex))"
        by auto
      thus ?thesis
        by (simp add: retain_comb restrict_global_traverse_unit_combine_intra)
    qed
  qed
  have acc0_glob: "restrict_global ?acc0 = \<bottom>"
    using bot0_glob frame_glob
    by (simp add: restrict_global_sup restrict_global_restrict_local_bot restrict_global_bot
          split: if_split)
  have fold_eq: "traverse_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> = eq ?T (v, ctx) \<sigma>"
    by (simp add: eq_side_cfg_T_eff_cmp traverse_side_rhs_fold_ctx)
  have sides_le: "sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))
                    \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))
            \<le> sides_of_rhs (?T (v, ctx)) \<sigma> (Inr (gkey ctx))"
      by (rule sides_fold_le_side_cfg_T_eff_cmp)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))"
      by (rule side_post_solution_le_global_cmp[OF _ v]) (use ps in auto)
    finally show ?thesis .
  qed
  have fun_le: "restrict_global (eq ?T (v, ctx) \<sigma>) \<le> \<sigma> (Inr (gkey ctx))"
  proof -
    have "restrict_global (eq ?T (v, ctx) \<sigma>)
            \<le> restrict_global ?acc0
              \<squnion> sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))"
      by (metis (no_types, lifting) fold_eq hyp restrict_global_traverse_side_rhs_fold_ctx_le)
    also have "\<dots> = sides_of_rhs (side_rhs_fold_ctx ?acc0 (?intra @ ?comb)) \<sigma> (Inr (gkey ctx))"
      by (simp add: acc0_glob)
    also have "\<dots> \<le> \<sigma> (Inr (gkey ctx))" by (rule sides_le)
    finally show ?thesis .
  qed
  have "\<sigma> (Inl (v, ctx)) y = restrict_global (eq ?T (v, ctx) \<sigma>) y"
    using y exact by (simp add: restrict_global_def)
  also have "\<dots> \<le> \<sigma> (Inr (gkey ctx)) y" using fun_le by (rule le_funD)
  finally show ?thesis .
qed

text \<open>
  Packaged as the invariant on a covering variable set: on any \<open>vars\<close> closed under the
  reachable slots, the exact retain solution satisfies \<^const>\<open>inl_glob_le_keyed_ctx\<close>
  pointwise.  (The full unconditional \<^const>\<open>inl_glob_le_keyed_ctx\<close> additionally needs
  the solver's \<open>\<bottom>\<close>-default outside \<open>vars\<close>, where both sides are \<open>\<bottom>\<close>.)
\<close>
lemma inl_glob_le_keyed_ctx_on_vars:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and "restrict_global bot0 = \<bottom>" and "restrict_global fresh_frame = \<bottom>"
    and "part_solution (side_cfg_T_eff_cmp gkey
           (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
               (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
           g etf fresh_frame bot0 s0) x \<sigma> vars"
    and "\<And>v ctx. (v, ctx) \<in> vars"
  shows "inl_glob_le_keyed_ctx gkey \<sigma>"
  unfolding inl_glob_le_keyed_ctx_def
  using part_solution_imp_inl_glob_le_keyed_ctx[OF assms(1-5)] assms(6) by blast

text \<open>
  The realistic full form.  Exactness gives the invariant on the solved set
  \<open>vars\<close>; the solver's \<open>\<bottom>\<close>-init default gives it outside \<open>vars\<close> --- an unsolved
  local slot keeps the initial \<open>\<bottom>\<close>, dominated by anything.  Together they discharge
  the full \<^const>\<open>inl_glob_le_keyed_ctx\<close> from the fixpoint shape alone, with no
  standalone slot-relating assumption.  Both inputs are intrinsic properties of the
  solver output (exact fixpoint, \<open>\<bottom>\<close> default), not semantic assertions about the
  analysis.
\<close>
lemma inl_glob_le_keyed_ctx_full:
  fixes \<sigma> :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
    and F :: "edge_action \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes retain_edge: "\<And>a u. apply_etf etf a u = retain_edge_tree (F a) u"
    and retain_comb: "\<And>cc ex. etf_combine etf cc ex = unit_combine_tree cc ex"
    and bot0_glob: "restrict_global bot0 = \<bottom>"
    and frame_glob: "restrict_global fresh_frame = \<bottom>"
    and ps: "part_solution (side_cfg_T_eff_cmp gkey
                (\<lambda>c cc ex. map_gtree (\<lambda>_. gkey c)
                    (map_ltree (\<lambda>w. (w, c)) (etf_combine etf cc ex)))
                g etf fresh_frame bot0 s0) x \<sigma> vars"
    and outside: "\<And>v ctx. (v, ctx) \<notin> vars \<Longrightarrow> \<sigma> (Inl (v, ctx)) = \<bottom>"
  shows "inl_glob_le_keyed_ctx gkey \<sigma>"
  unfolding inl_glob_le_keyed_ctx_def
proof (intro allI impI)
  fix v ctx x assume glob: "is_global x"
  show "\<sigma> (Inl (v, ctx)) x \<le> \<sigma> (Inr (gkey ctx)) x"
  proof (cases "(v, ctx) \<in> vars")
    case True
    show ?thesis
      by (rule part_solution_imp_inl_glob_le_keyed_ctx
            [OF retain_edge retain_comb bot0_glob frame_glob ps True glob])
  next
    case False
    then have "\<sigma> (Inl (v, ctx)) = \<bottom>" by (rule outside)
    then show ?thesis by simp
  qed
qed

subsection \<open>Executable retain edge tree\<close>

text \<open>
  The executable counterpart of @{const retain_edge_tree}: the local Answer keeps
  the full result (globals retained).  It differs from @{const unit_edge_tree_st}
  only in the Answer payload, which @{const sides_of_rhs} ignores --- so its side
  map is the publish tree's, while its traverse carries the full transfer result.
  The two commutation lemmas transport traverse and sides through @{const fun_of_st}
  to the kernel @{const retain_edge_tree}, so a runnable retain transfer discharges
  the hypotheses of the generic executable fold.
\<close>

definition retain_edge_tree_st ::
  "('a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st) \<Rightarrow> (unit, 'a st) st_edge_tf_tree"
where
  "retain_edge_tree_st f u =
     QueryL u (\<lambda>su. QueryG () (\<lambda>g.
       let res = f (su \<squnion> g) in
       Side () (restrict_global_st res) (Answer res)))"

lemma traverse_retain_edge_tree_st:
  "traverse_rhs (retain_edge_tree_st f u) \<sigma>_st =
   f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ()))"
  unfolding retain_edge_tree_st_def by (simp add: Let_def)

lemma sides_retain_edge_tree_st_Inr:
  "sides_of_rhs (retain_edge_tree_st f u) \<sigma>_st (Inr ()) =
   restrict_global_st (f (\<sigma>_st (Inl u) \<squnion> \<sigma>_st (Inr ())))"
  unfolding retain_edge_tree_st_def by (simp add: Let_def)

lemma sides_retain_edge_tree_st_Inl:
  "sides_of_rhs (retain_edge_tree_st f u) \<sigma> (Inl u') = bot"
  unfolding retain_edge_tree_st_def Let_def by simp

lemma side_rg_retain_edge_tree_st: "side_rg (retain_edge_tree_st f u)"
  unfolding retain_edge_tree_st_def by (simp add: Let_def)

lemma dep_aux_retain_edge_tree_st:
  fixes f :: "'a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  shows "dep_aux \<sigma>1 (retain_edge_tree_st f u) = dep_aux \<sigma>2 (retain_edge_tree g u)"
  unfolding retain_edge_tree_st_def retain_edge_tree_def Let_def by simp

lemma traverse_retain_edge_tree_st_commute:
  fixes f :: "'a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes commute: "\<And>s. fun_of_st (f s) = g (fun_of_st s)"
  shows "fun_of_st (traverse_rhs (retain_edge_tree_st f u) \<sigma>_st)
       = traverse_rhs (retain_edge_tree g u) (fun_of_st \<circ> \<sigma>_st)"
  by (simp add: traverse_retain_edge_tree_st traverse_retain_edge_tree
                commute fun_of_st_sup o_def)

lemma sides_retain_edge_tree_st_commute:
  fixes f :: "'a::bounded_semilattice_sup_bot st \<Rightarrow> 'a st"
    and g :: "'a abs_state \<Rightarrow> 'a abs_state"
  assumes commute: "\<And>s. fun_of_st (f s) = g (fun_of_st s)"
  shows "fun_of_st (sides_of_rhs (retain_edge_tree_st f u) \<sigma>_st k)
       = sides_of_rhs (retain_edge_tree g u) (fun_of_st \<circ> \<sigma>_st) k"
proof (cases k)
  case (Inl u')
  then show ?thesis
    by (simp add: sides_retain_edge_tree_st_Inl sides_retain_eq_unit
                  sides_unit_edge_tree_Inl fun_of_st_bot bot_fun_def)
next
  case (Inr g')
  then show ?thesis
    by (simp add: sides_retain_edge_tree_st_Inr sides_retain_edge_tree_Inr
                  commute fun_of_st_sup o_def)
qed



subsection \<open>Retain on the heterogeneous framework: the expressiveness witness\<close>

text \<open>
  Retain is an ordinary \<open>D\<close>/\<open>G\<close>/step analysis on
  \<^const>\<open>dg_edge_tree\<close>.  Its local domain is
  \<open>D = ('a abs_state, 'a abs_state) dg_state\<close>, carrying locals and a
  flow-sensitive snapshot; its published domain is \<open>G = 'a abs_state\<close>.
  The framework sees only the analysis-agnostic \<open>dg_spec\<close> interface.
\<close>

definition retain_hetero_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> ('a abs_state, 'a abs_state) dg_state"
where
  "retain_hetero_step f d g =
     (let res = f (merge_dg d \<squnion> g)
      in (restrict_global res, split_dg res))"


subsection \<open>The heterogeneous retain spec\<close>

definition retain_hetero_combine ::
  "('a::bounded_semilattice_sup_bot abs_state, 'a abs_state) dg_state
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state
   \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> ('a abs_state, 'a abs_state) dg_state"
where
  "retain_hetero_combine dc de g =
     (let res = restrict_local (merge_dg dc \<squnion> g)
                \<squnion> restrict_global (merge_dg de \<squnion> g)
      in (restrict_global res, split_dg (restrict_local res)))"



definition retain_dg_spec ::
  "'a::sound_domain domain_transfer
   \<Rightarrow> (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_spec"
where
  "retain_dg_spec tf = \<lparr>
    dgs_nop        = retain_hetero_step (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. retain_hetero_step (apply_tf tf (EA_Assign x e))),
    dgs_assume     = (\<lambda>b. retain_hetero_step (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. retain_hetero_step (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = retain_hetero_step (apply_tf tf EA_Enter),    dgs_combine    = retain_hetero_combine
  \<rparr>"


subsection \<open>Native heterogeneous soundness\<close>

text \<open>
  Retain interprets \<^locale>\<open>sound_dg_spec\<close> \<^emph>\<open>directly\<close> at its product local
  carrier \<open>D = ('a abs_state, 'a abs_state) dg_state\<close> and global carrier
  \<open>G = 'a abs_state\<close> --- no homogeneous transport.  This is the witness that the
  \<^locale>\<open>sound_dg_spec\<close> carrier generalization is real: an \<open>abs_state\<close>-only
  soundness locale could not accept this product \<open>D\<close>.  The joint concretization
  merges the two local slots before intersecting with the globals, matching how
  \<^const>\<open>retain_hetero_step\<close> reads its inputs (\<open>f (merge_dg d \<squnion> g)\<close>).
\<close>

definition gamma_retain ::
  "('a::sound_domain abs_state, 'a abs_state) dg_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_retain d g = \<lbrakk>merge_dg d \<squnion> g\<rbrakk>"

lemma merge_dg_mono:
  "d \<le> d' \<Longrightarrow> merge_dg d \<le> merge_dg d'"
  unfolding merge_dg_def pair_of_dg_def
  by (rule merge_state_mono) (auto simp: less_eq_dg_state_def)

lemma gamma_retain_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_retain d g \<subseteq> gamma_retain d' g'"
  unfolding gamma_retain_def
  by (rule gamma_state_mono) (rule sup_mono[OF merge_dg_mono[OF assms(1)] assms(2)])

lemma dg_spec_step_retain:
  "dg_spec_step (retain_dg_spec tf) a d g = retain_hetero_step (apply_tf tf a) d g"
  by (cases a) (simp_all add: retain_dg_spec_def)

lemma sound_dg_spec_retain:
  assumes sound: "sound_transfer tf"
  shows "sound_dg_spec (retain_dg_spec tf) gamma_retain"
  apply unfold_locales
  subgoal for d d' g g'
    by (rule gamma_retain_mono)
  subgoal for a d g
  proof -
    have "edge_collect a (gamma_retain d g)
          \<subseteq> \<lbrakk>apply_tf tf a (merge_dg d \<squnion> g)\<rbrakk>"
      unfolding gamma_retain_def
      by (rule sound_transfer.edge_collect_apply_tf_sound[OF sound])
    also have "... \<subseteq> \<lbrakk>apply_tf tf a (merge_dg d \<squnion> g)
                       \<squnion> restrict_global (apply_tf tf a (merge_dg d \<squnion> g))\<rbrakk>"
      by (rule gamma_state_mono) simp
    finally show ?thesis
      by (simp add: dg_spec_step_retain retain_hetero_step_def Let_def
            gamma_retain_def merge_split_dg)
  qed
  subgoal for s dc g t de
  proof -
    assume sin: "s \<in> gamma_retain dc g" and tin: "t \<in> gamma_retain de g"
    have "combine_states s t
          \<in> \<lbrakk>combine_abs (merge_dg dc \<squnion> g) (merge_dg de \<squnion> g)\<rbrakk>"
      using combine_states_sound sin tin unfolding gamma_retain_def by blast
    then show ?thesis
      unfolding retain_dg_spec_def retain_hetero_combine_def gamma_retain_def
      by (simp add: Let_def merge_split_dg restrict_local_global_join
            combine_abs_restrict)
  qed
  done

text \<open>
  The layered public endpoint, instantiated for Retain: a solver post-solution
  of the framework generator for \<^const>\<open>retain_dg_spec\<close> soundly
  over-approximates the CFG collecting semantics at every program point.
\<close>

lemmas retain_post_solution_collect_sound =
  sound_dg_spec.dg_post_solution_collect_sound[OF sound_dg_spec_retain]








end
