theory Retain_Analysis
  imports DG_Framework
begin

section \<open>The retain analysis\<close>

text \<open>
  An ordinary analysis on the D/G framework of \<^theory>\<open>Voblint_Analysis.DG_Framework\<close>:
  its \<open>D\<close> is locals \<times> flow-sensitive global snapshot, its \<open>G\<close> the global state.
  The framework transports \<open>Answer : D\<close> and \<open>Side : G\<close> and never copies \<open>G\<close>
  into \<open>D\<close>; the snapshot in the Answer is written by this analysis's own
  transfer.  The homogeneous \<open>retain_edge_tree\<close> (one \<open>'a abs_state\<close> value type,
  Answer keeps the full result) is this analysis's legacy form; everything
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

text \<open>The legacy tree factors through the framework shape: retain is a step.\<close>

definition retain_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state"
where
  "retain_step f d g = (let res = f (d \<squnion> g) in (restrict_global res, res))"

theorem step_edge_tree_retain:
  "step_edge_tree (retain_step f) u = retain_edge_tree f u"
  unfolding step_edge_tree_def retain_step_def retain_edge_tree_def
  by (simp add: Let_def)

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

subsection \<open>Retain on the flat dg carrier\<close>

text \<open>
  The analysis's domain choice made explicit on the solver value type:
  \<open>D = ('a abs_state, 'a abs_state) dg_state\<close>, locals in the \<open>locals\<close> field, the
  flow-sensitive global snapshot in the \<open>globs\<close> field; global slots carry
  \<^const>\<open>emb_glob\<close>-embedded values.
\<close>

definition retain_dg_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<Rightarrow> ('a abs_state, 'a abs_state) dg_state
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<times> ('a abs_state, 'a abs_state) dg_state"
where
  "retain_dg_step f d g =
     (let res = f (merge_dg d \<squnion> globs g)
      in (emb_glob (restrict_global res), split_dg res))"

definition retain_dg_edge_tree ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> pp \<Rightarrow> (pp, unit, ('a abs_state, 'a abs_state) dg_state) strategy_tree"
where
  "retain_dg_edge_tree f u = step_edge_tree (retain_dg_step f) u"

lemma retain_dg_traverse_wf:
  "wf_dg (traverse_rhs (retain_dg_edge_tree f u) \<tau>)"
  unfolding retain_dg_edge_tree_def retain_dg_step_def
  by (simp add: traverse_step_edge_tree Let_def wf_dg_split_dg)

lemma retain_dg_sides_locals_bot:
  "locals (sides_of_rhs (retain_dg_edge_tree f u) \<tau> (Inr ())) = bot"
  unfolding retain_dg_edge_tree_def retain_dg_step_def emb_glob_def
  by (simp add: sides_step_edge_tree_Inr Let_def)

definition dg_rep ::
  "(pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> pp + unit \<Rightarrow> ('a abs_state, 'a abs_state) dg_state"
where
  "dg_rep \<sigma> =
     (\<lambda>k. case k of Inl v \<Rightarrow> split_dg (\<sigma> (Inl v)) | Inr g \<Rightarrow> emb_glob (\<sigma> (Inr g)))"

theorem retain_dg_traverse:
  "traverse_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>)
   = split_dg (traverse_rhs (retain_edge_tree f u) \<sigma>)"
  unfolding retain_dg_edge_tree_def retain_dg_step_def dg_rep_def emb_glob_def
  by (simp add: traverse_step_edge_tree traverse_retain_edge_tree Let_def)

corollary retain_dg_traverse_merge:
  "merge_dg (traverse_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>))
   = traverse_rhs (retain_edge_tree f u) \<sigma>"
  by (simp add: retain_dg_traverse)

theorem retain_dg_sides_Inr:
  "sides_of_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>) (Inr ())
   = emb_glob (sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ()))"
  unfolding retain_dg_edge_tree_def retain_dg_step_def dg_rep_def emb_glob_def
  by (simp add: sides_step_edge_tree_Inr sides_retain_edge_tree_Inr Let_def)

corollary retain_dg_sides_Inr_globs:
  "globs (sides_of_rhs (retain_dg_edge_tree f u) (dg_rep \<sigma>) (Inr ()))
   = sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ())"
  by (simp add: retain_dg_sides_Inr emb_glob_def)

subsection \<open>Retain on the heterogeneous framework: the expressiveness witness\<close>

text \<open>
  Retain as an ordinary \<open>D\<close>/\<open>G\<close>/step analysis on \<^const>\<open>dg_edge_tree\<close>:
  \<open>D = ('a abs_state, 'a abs_state) dg_state\<close> (locals \<times> snapshot),
  \<open>G = 'a abs_state\<close>.  The framework tree is the same analysis-agnostic
  \<^const>\<open>dg_edge_tree\<close> every analysis uses --- no retain knowledge anywhere in
  \<^theory>\<open>Voblint_Analysis.DG_Framework\<close> --- and under the slot embedding the
  behaviour is exactly the homogeneous retain tree's.
\<close>

definition retain_hetero_step ::
  "('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('a abs_state, 'a abs_state) dg_state \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> ('a abs_state, 'a abs_state) dg_state"
where
  "retain_hetero_step f d g =
     (let res = f (merge_dg d \<squnion> g)
      in (restrict_global res, split_dg res))"

definition retain_hetero_rep ::
  "('x + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> 'x + unit \<Rightarrow> (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_state"
where
  "retain_hetero_rep \<sigma> =
     (\<lambda>k. case k of Inl v \<Rightarrow> DG (split_dg (\<sigma> (Inl v))) bot
                  | Inr g \<Rightarrow> DG bot (\<sigma> (Inr g)))"

theorem retain_hetero_traverse:
  "traverse_rhs (dg_edge_tree (retain_hetero_step f) u) (retain_hetero_rep \<sigma>)
   = DG (split_dg (traverse_rhs (retain_edge_tree f u) \<sigma>)) bot"
  unfolding retain_hetero_step_def retain_hetero_rep_def
  by (simp add: traverse_dg_edge_tree traverse_retain_edge_tree Let_def)

theorem retain_hetero_sides:
  "sides_of_rhs (dg_edge_tree (retain_hetero_step f) u) (retain_hetero_rep \<sigma>) (Inr ())
   = DG bot (sides_of_rhs (retain_edge_tree f u) \<sigma> (Inr ()))"
  unfolding retain_hetero_step_def retain_hetero_rep_def
  by (simp add: sides_dg_edge_tree_Inr sides_retain_edge_tree_Inr Let_def)

text \<open>
  With @{thm [source] dg_edge_tree_answer_pure_D} and
  @{thm [source] dg_edge_tree_side_pure_G} holding
  for every step, retain needs no framework-specific support: the snapshot lives
  inside this analysis's \<open>D\<close>, published globals are pure \<open>G\<close>, and the legacy
  homogeneous behaviour is recovered exactly.
\<close>

subsection \<open>Retain's representation transport\<close>

primrec retain_pack_tree ::
  "('x, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> ('x, unit,
       (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_state)
      strategy_tree"
where
  "retain_pack_tree (Answer d) = Answer (DG (split_dg d) bot)"
| "retain_pack_tree (QueryL x f) =
     QueryL x (\<lambda>d. retain_pack_tree (f (merge_dg (locals d))))"
| "retain_pack_tree (QueryG g f) =
     QueryG g (\<lambda>d. retain_pack_tree (f (globs d)))"
| "retain_pack_tree (Side g d t) =
     Side g (DG bot d) (retain_pack_tree t)"

lemma traverse_retain_pack_tree:
  "traverse_rhs (retain_pack_tree t) (retain_hetero_rep \<sigma>) =
   DG (split_dg (traverse_rhs t \<sigma>)) bot"
  by (induction t)
    (simp_all add: retain_hetero_rep_def bot_fun_def)

lemma sides_retain_pack_tree:
  "sides_of_rhs (retain_pack_tree t) (retain_hetero_rep \<sigma>) =
   retain_hetero_rep (sides_of_rhs t \<sigma>)"
  unfolding fun_eq_iff
proof (intro allI)
  fix k
  show "sides_of_rhs (retain_pack_tree t) (retain_hetero_rep \<sigma>) k =
        retain_hetero_rep (sides_of_rhs t \<sigma>) k"
  proof (cases k)
    case (Inl x)
    then show ?thesis
      by (simp add: retain_hetero_rep_def sides_of_rhs_Inl_any
            bot_dg_state_def)
  next
    case (Inr g)
    then show ?thesis
      by (induction t)
        (auto simp: retain_hetero_rep_def Let_def sup_dg_state_def
          bot_dg_state_def)
  qed
qed

lemma dep_aux_retain_pack_tree:
  "dep_aux (retain_hetero_rep \<sigma>) (retain_pack_tree t) = dep_aux \<sigma> t"
  by (induction t) (simp_all add: retain_hetero_rep_def)

lemma retain_pack_tree_seqcomp:
  "retain_pack_tree (seqcomp_tree t f) =
   seqcomp_tree (retain_pack_tree t)
     (\<lambda>d. retain_pack_tree (f (merge_dg (locals d))))"
  by (induction t arbitrary: f) simp_all

lemma retain_pack_tree_map_ltree:
  "retain_pack_tree (map_ltree h t) = map_ltree h (retain_pack_tree t)"
  by (induction t) simp_all

lemma retain_pack_tree_map_gtree:
  "retain_pack_tree (map_gtree h t) = map_gtree h (retain_pack_tree t)"
  by (induction t) simp_all

lemma dg_edge_tree_retain_pack:
  "dg_edge_tree (retain_hetero_step f) u =
   retain_pack_tree (retain_edge_tree f u)"
  unfolding dg_edge_tree_def retain_hetero_step_def retain_edge_tree_def
  by (simp add: Let_def fun_eq_iff)

subsection \<open>Retain through the heterogeneous CMP generator\<close>

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

lemma dg_combine_tree_retain_pack:
  "dg_combine_tree retain_hetero_combine cc ex =
   retain_pack_tree (unit_combine_tree cc ex)"
  unfolding dg_combine_tree_def retain_hetero_combine_def
    unit_combine_tree_def
  by (simp add: Let_def fun_eq_iff)
lemma retain_hetero_rep_bot [simp]:
  "retain_hetero_rep
     (bot :: 'x + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) = bot"
  unfolding fun_eq_iff
  by (intro allI; case_tac x; rule dg_state.expand)
    (simp_all add: retain_hetero_rep_def bot_dg_state_def)

lemma retain_hetero_rep_sup [simp]:
  "retain_hetero_rep (\<sigma> \<squnion> \<tau>) =
   retain_hetero_rep \<sigma> \<squnion> retain_hetero_rep \<tau>"
  unfolding fun_eq_iff
  by (intro allI; case_tac x; rule dg_state.expand)
    (simp_all add: retain_hetero_rep_def sup_dg_state_def)


lemma traverse_retain_pack_fold:
  "traverse_rhs
     (side_rhs_fold_dg (split_dg acc) (map retain_pack_tree ts))
     (retain_hetero_rep \<sigma>) =
   DG (split_dg (traverse_rhs (side_rhs_fold_ctx acc ts) \<sigma>)) bot"
proof (induction ts arbitrary: acc)
  case Nil
  show ?case by (simp add: bot_fun_def)
next
  case (Cons t ts)
  have acc_eq:
    "split_dg acc \<squnion> split_dg (traverse_rhs t \<sigma>) =
     split_dg (acc \<squnion> traverse_rhs t \<sigma>)"
    by (rule split_dg_sup[symmetric])
  show ?case
    by (simp only: list.map side_rhs_fold_dg.simps side_rhs_fold_ctx.simps
          traverse_seqcomp traverse_retain_pack_tree dg_state.sel acc_eq Cons.IH)
qed

lemma sides_retain_pack_fold:
  "sides_of_rhs
     (side_rhs_fold_dg (split_dg acc) (map retain_pack_tree ts))
     (retain_hetero_rep \<sigma>) =
   retain_hetero_rep
     (sides_of_rhs (side_rhs_fold_ctx acc ts) \<sigma>)"
proof (induction ts arbitrary: acc)
  case Nil
  show ?case
    by (rule ext; case_tac x; rule dg_state.expand)
      (simp_all add: retain_hetero_rep_def bot_dg_state_def bot_fun_def split_dg_def dg_of_pair_def split_state_def)
next
  case (Cons t ts)
  have acc_eq:
    "split_dg acc \<squnion> split_dg (traverse_rhs t \<sigma>) =
     split_dg (acc \<squnion> traverse_rhs t \<sigma>)"
    by (rule split_dg_sup[symmetric])
  show ?case
    by (simp only: list.map side_rhs_fold_dg.simps side_rhs_fold_ctx.simps
          sides_of_rhs_seqcomp sides_retain_pack_tree
          traverse_retain_pack_tree dg_state.sel acc_eq Cons.IH
          retain_hetero_rep_sup)
qed

lemma dep_aux_retain_pack_fold:
  "dep_aux (retain_hetero_rep \<sigma>)
     (side_rhs_fold_dg (split_dg acc) (map retain_pack_tree ts)) =
   dep_aux \<sigma> (side_rhs_fold_ctx acc ts)"
proof (induction ts arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons t ts)
  have acc_eq:
    "split_dg acc \<squnion> split_dg (traverse_rhs t \<sigma>) =
     split_dg (acc \<squnion> traverse_rhs t \<sigma>)"
    by (rule split_dg_sup[symmetric])
  show ?case
    by (simp only: list.map side_rhs_fold_dg.simps side_rhs_fold_ctx.simps
          dep_aux_seqcomp dep_aux_retain_pack_tree
          traverse_retain_pack_tree dg_state.sel acc_eq Cons.IH)
qed

definition retain_dg_spec ::
  "'a::sound_domain domain_transfer
   \<Rightarrow> (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_spec"
where
  "retain_dg_spec tf = \<lparr>
    dgs_nop        = retain_hetero_step (apply_tf tf EA_Nop),
    dgs_assign     = (\<lambda>x e. retain_hetero_step (apply_tf tf (EA_Assign x e))),
    dgs_assume     = (\<lambda>b. retain_hetero_step (apply_tf tf (EA_Assume b))),
    dgs_assume_not = (\<lambda>b. retain_hetero_step (apply_tf tf (EA_AssumeNot b))),
    dgs_enter      = retain_hetero_step (apply_tf tf EA_Enter),
    dgs_combine    = retain_hetero_combine
  \<rparr>"

lemma dg_spec_step_retain:
  "dg_spec_step (retain_dg_spec tf) a =
   retain_hetero_step (apply_tf tf a)"
  unfolding retain_dg_spec_def by (cases a) simp_all

lemma apply_retain_dg_spec:
  "apply_dg_spec (retain_dg_spec tf) a u =
   dg_edge_tree (retain_hetero_step (apply_tf tf a)) u"
  by (simp add: apply_dg_spec_def dg_spec_step_retain)

lemma combine_retain_dg_spec:
  "dg_spec_combine_tree (retain_dg_spec tf) cc ex =
   dg_combine_tree retain_hetero_combine cc ex"
  by (simp add: dg_spec_combine_tree_def retain_dg_spec_def)

definition retain_dg_cmb ::
  "'a::sound_domain domain_transfer \<Rightarrow> unit \<Rightarrow> pp \<Rightarrow> pp
   \<Rightarrow> (pp \<times> unit, unit,
       (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_state)
      strategy_tree"
where
  "retain_dg_cmb tf ctx cc ex =
     map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx))
         (dg_spec_combine_tree (retain_dg_spec tf) cc ex))"

lemma apply_retain_dg_spec_pack:
  "apply_dg_spec (retain_dg_spec tf) a u =
   retain_pack_tree (apply_etf (retain_etf_of_transfer tf) a u)"
  by (simp add: apply_retain_dg_spec dg_edge_tree_retain_pack
        apply_etf_retain_of_transfer)

lemma retain_dg_cmb_pack:
  "retain_dg_cmb tf ctx cc ex =
   retain_pack_tree
     (map_gtree (\<lambda>_. ())
       (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))"
  unfolding retain_dg_cmb_def combine_retain_dg_spec
    dg_combine_tree_retain_pack
  by (simp add: retain_pack_tree_map_ltree retain_pack_tree_map_gtree)

definition retain_generator ::
  "cfg \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> unit, unit, 'a abs_state) eqsT"
where
  "retain_generator g tf fresh_frame bot0 s0 =
     side_cfg_T_eff_cmp_seed (\<lambda>_. ())
       (\<lambda>ctx cc ex. map_gtree (\<lambda>_. ())
         (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))
       (\<lambda>_. fresh_frame) g (retain_etf_of_transfer tf) bot0 s0"

definition retain_dg_generator ::
  "cfg \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state
   \<Rightarrow> (pp \<times> unit, unit,
       (('a abs_state, 'a abs_state) dg_state, 'a abs_state) dg_state) eqsT"
where
  "retain_dg_generator g tf fresh_frame bot0 s0 =
     side_cfg_T_eff_cmp_seed_dg (\<lambda>_. ()) (retain_dg_cmb tf)
       (\<lambda>_. split_dg fresh_frame) g (retain_dg_spec tf)
       (split_dg bot0) (split_dg (restrict_local s0)) (restrict_global s0)"

lemma eq_retain_dg_generator:
  "eq (retain_dg_generator g tf fresh_frame bot0 s0) (v, ctx) \<tau> =
   DG (side_acc_dg
     ((if v = cfg_entry g
       then split_dg bot0 \<squnion> split_dg (restrict_local s0)
       else split_dg bot0)
      \<squnion> (if is_frame_entry g v then split_dg fresh_frame else bot))
     \<tau>
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
              (map_ltree (\<lambda>w. (w, ctx))
                (apply_dg_spec (retain_dg_spec tf) a u)))
           (non_enter_predecessor_list g v)
      @ map (\<lambda>(cc, ex). retain_dg_cmb tf ctx cc ex)
            (combine_predecessor_list g v))) bot"
  unfolding retain_dg_generator_def
  by (rule eq_side_cfg_T_eff_cmp_seed_dg)

lemma retain_dg_tree_list_pack:
  "map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
          (map_ltree (\<lambda>w. (w, ctx))
            (apply_dg_spec (retain_dg_spec tf) a u)))
       (non_enter_predecessor_list g v)
   @ map (\<lambda>(cc, ex). retain_dg_cmb tf ctx cc ex)
       (combine_predecessor_list g v) =
   map retain_pack_tree
     (map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
            (map_ltree (\<lambda>w. (w, ctx))
              (apply_etf (retain_etf_of_transfer tf) a u)))
         (non_enter_predecessor_list g v)
      @ map (\<lambda>(cc, ex). map_gtree (\<lambda>_. ())
              (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))
          (combine_predecessor_list g v))"
  by (simp add: apply_retain_dg_spec_pack retain_dg_cmb_pack
        retain_pack_tree_map_ltree[symmetric]
        retain_pack_tree_map_gtree[symmetric] split: prod.splits)

lemma retain_dg_acc0_pack:
  fixes a b d :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "((if P then split_dg a \<squnion> split_dg b else split_dg a)
      \<squnion> (if Q then split_dg d else bot)) =
   split_dg ((if P then a \<squnion> b else a)
      \<squnion> (if Q then d else bot))"
  by simp

lemma traverse_retain_dg_tree_list:
  "traverse_rhs
     (side_rhs_fold_dg (split_dg acc)
       (map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
          (map_ltree (\<lambda>w. (w, ctx))
            (apply_dg_spec (retain_dg_spec tf) a u)))
        (non_enter_predecessor_list g v)
      @ map (\<lambda>(cc, ex). retain_dg_cmb tf ctx cc ex)
          (combine_predecessor_list g v)))
     (retain_hetero_rep \<sigma>) =
   DG (split_dg
     (traverse_rhs
       (side_rhs_fold_ctx acc
         (map (\<lambda>(u, a). map_gtree (\<lambda>_. ())
            (map_ltree (\<lambda>w. (w, ctx))
              (apply_etf (retain_etf_of_transfer tf) a u)))
          (non_enter_predecessor_list g v)
        @ map (\<lambda>(cc, ex). map_gtree (\<lambda>_. ())
            (map_ltree (\<lambda>w. (w, ctx)) (unit_combine_tree cc ex)))
          (combine_predecessor_list g v)))
       \<sigma>)) bot"
by (simp only: retain_dg_tree_list_pack traverse_retain_pack_fold)

lemma eq_retain_dg_generator_rep:
  "eq (retain_dg_generator g tf fresh_frame bot0 s0) (v, ctx)
      (retain_hetero_rep \<sigma>) =
   DG (split_dg
     (eq (retain_generator g tf fresh_frame bot0 s0) (v, ctx) \<sigma>)) bot"
  unfolding retain_dg_generator_def retain_generator_def
    side_cfg_T_eff_cmp_seed_dg_def side_cfg_T_eff_cmp_seed_def
  by (cases "v = cfg_entry g"; cases "is_frame_entry g v")
    (simp_all only: Let_def if_True if_False prod.case
      retain_dg_acc0_pack traverse_retain_dg_tree_list
      traverse_rhs.simps refl sup_bot_right)

lemma retain_hetero_rep_update_global:
  fixes d :: "'a::bounded_semilattice_sup_bot abs_state"
  shows "(retain_hetero_rep \<sigma>)
           (Inr () := (retain_hetero_rep \<sigma>) (Inr ()) \<squnion> DG bot d) =
         retain_hetero_rep (\<sigma> (Inr () := \<sigma> (Inr ()) \<squnion> d))"
  by (rule ext; case_tac x; rule dg_state.expand)
    (simp_all add: retain_hetero_rep_def sup_dg_state_def bot_dg_state_def)

lemma sides_retain_dg_generator_rep:
  "sides_of_rhs
     (retain_dg_generator g tf fresh_frame bot0 s0 (v, ctx))
     (retain_hetero_rep \<sigma>) =
   retain_hetero_rep
     (sides_of_rhs
       (retain_generator g tf fresh_frame bot0 s0 (v, ctx)) \<sigma>)"
  unfolding retain_dg_generator_def retain_generator_def
    side_cfg_T_eff_cmp_seed_dg_def side_cfg_T_eff_cmp_seed_def
  by (cases "v = cfg_entry g"; cases "is_frame_entry g v")
    (simp_all only: Let_def if_True if_False prod.case
      retain_dg_acc0_pack retain_dg_tree_list_pack
      sides_retain_pack_fold sides_of_rhs.simps
      retain_hetero_rep_sup retain_hetero_rep_update_global
      refl sup_bot_right)

lemma dep_aux_retain_dg_generator_rep:
  "dep_aux (retain_hetero_rep \<sigma>)
     (retain_dg_generator g tf fresh_frame bot0 s0 (v, ctx)) =
   dep_aux \<sigma> (retain_generator g tf fresh_frame bot0 s0 (v, ctx))"
  unfolding retain_dg_generator_def retain_generator_def
    side_cfg_T_eff_cmp_seed_dg_def side_cfg_T_eff_cmp_seed_def
  by (cases "v = cfg_entry g"; cases "is_frame_entry g v")
    (simp_all only: Let_def if_True if_False prod.case
      retain_dg_acc0_pack retain_dg_tree_list_pack
      dep_aux_retain_pack_fold dep_aux.simps refl sup_bot_right)

lemma retain_hetero_rep_le_iff [simp]:
  "retain_hetero_rep \<sigma> \<le> retain_hetero_rep \<tau> \<longleftrightarrow> \<sigma> \<le> \<tau>"
proof
  assume h: "retain_hetero_rep \<sigma> \<le> retain_hetero_rep \<tau>"
  show "\<sigma> \<le> \<tau>"
  proof (rule le_funI)
    fix k
    show "\<sigma> k \<le> \<tau> k"

    proof (cases k)
      case (Inl x)
      have outer:
          "(retain_hetero_rep \<sigma>) (Inl x) \<le>
           (retain_hetero_rep \<tau>) (Inl x)"
        using le_funD[OF h, of "Inl x"] .
      have inner:
          "split_dg (\<sigma> (Inl x)) \<le> split_dg (\<tau> (Inl x))"
        using outer
        by (simp add: retain_hetero_rep_def)
      show ?thesis
        using Inl split_dg_le_iff[THEN iffD1, OF inner] by simp
    next
      case (Inr g)
      have outer:
          "(retain_hetero_rep \<sigma>) (Inr g) \<le>
           (retain_hetero_rep \<tau>) (Inr g)"
        using le_funD[OF h, of "Inr g"] .
      have global: "\<sigma> (Inr g) \<le> \<tau> (Inr g)"
        using outer
        by (simp add: retain_hetero_rep_def sup.absorb_iff2 sup_dg_state_def)
      show ?thesis using Inr global by simp
    qed
  qed
next
  assume h: "\<sigma> \<le> \<tau>"
  show "retain_hetero_rep \<sigma> \<le> retain_hetero_rep \<tau>"
  proof (rule le_funI)
    fix k
    have hk: "\<sigma> k \<le> \<tau> k" using le_funD[OF h, of k] .
    show "(retain_hetero_rep \<sigma>) k \<le> (retain_hetero_rep \<tau>) k"
    proof (cases k)
      case (Inl x)
      have split_le:
          "split_dg (\<sigma> (Inl x)) \<le> split_dg (\<tau> (Inl x))"
        using hk Inl split_dg_le_iff[THEN iffD2] by simp
      show ?thesis
        using Inl split_le
        by (simp add: retain_hetero_rep_def)
    next
      case (Inr g)
      show ?thesis
        using hk Inr
        by (simp add: retain_hetero_rep_def sup.absorb_iff2 sup_dg_state_def)
    qed
  qed
qed

lemma eq_retain_dg_generator_rep_any:
  "eq (retain_dg_generator g tf fresh_frame bot0 s0) x
      (retain_hetero_rep \<sigma>) =
   DG (split_dg
     (eq (retain_generator g tf fresh_frame bot0 s0) x \<sigma>)) bot"
  by (cases x) (simp add: eq_retain_dg_generator_rep)

lemma sides_retain_dg_generator_rep_any:
  "sides_of_rhs
     (retain_dg_generator g tf fresh_frame bot0 s0 x)
     (retain_hetero_rep \<sigma>) =
   retain_hetero_rep
     (sides_of_rhs (retain_generator g tf fresh_frame bot0 s0 x) \<sigma>)"
  by (cases x) (simp add: sides_retain_dg_generator_rep)

lemma dep_aux_retain_dg_generator_rep_any:
  "dep_aux (retain_hetero_rep \<sigma>)
     (retain_dg_generator g tf fresh_frame bot0 s0 x) =
   dep_aux \<sigma> (retain_generator g tf fresh_frame bot0 s0 x)"
  by (cases x) (simp add: dep_aux_retain_dg_generator_rep)

lemma retain_answer_le_rep_Inl [simp]:
  "DG (split_dg d) bot \<le> (retain_hetero_rep \<sigma>) (Inl x)
   \<longleftrightarrow> d \<le> \<sigma> (Inl x)"
  by (simp add: retain_hetero_rep_def)

theorem part_post_solution_retain_dg_iff:
  "part_post_solution
     (retain_dg_generator g tf fresh_frame bot0 s0)
     x (retain_hetero_rep \<sigma>) vars
   \<longleftrightarrow>
   part_post_solution
     (retain_generator g tf fresh_frame bot0 s0) x \<sigma> vars"
  by (simp add: eq_retain_dg_generator_rep_any
        sides_retain_dg_generator_rep_any dep_aux_retain_dg_generator_rep_any
        dep\<^sub>L_def dep_def split: prod.splits)

theorem retain_dg_generator_uses_standard_framework:
  "apply_dg_spec (retain_dg_spec tf) a u =
   dg_edge_tree (retain_hetero_step (apply_tf tf a)) u"
  by (rule apply_retain_dg_spec)

text \<open>
  The complete generator sees only the standard \<open>dg_spec\<close> interface.  The
  snapshot occurs solely in Retain's choice of \<open>D\<close>; \<open>side_cfg_T_eff_cmp_seed_dg\<close>
  remains independent of Retain.
\<close>

end
