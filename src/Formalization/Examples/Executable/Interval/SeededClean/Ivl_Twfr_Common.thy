theory Ivl_Twfr_Common
  imports
    Twfr_Reach_Read
    Exec_Ivl_Cmp_Seed_Rehydrate_Run
    Exec_Ivl_Seed_EnterMono
begin

section \<open>Reusable interval seeded-clean twfr plumbing\<close>

text \<open>
  The run-independent obligations shared by every executable interval seeded-clean example.
  Each example fixes only its own \<open>cfg\<close> and abstract post-fixpoint; the routing, the
  combine-tree dependency set, the backward query-membership dischargers (\<open>q_caller\<close> /
  \<open>q_callee\<close>) and the return combine bound are proved here once, generic in the solution and
  the graph.  The activation routing \<open>ivl_enterc\<close> is the same executable \<^typ>\<open>ivl st\<close>
  key the generator's \<^const>\<open>ivl_combine_rehydrate_abs\<close> reads --- no reconstruction of a key
  from an abstract value, no \<^const>\<open>fun_of_st\<close> inverse.
\<close>

subsection \<open>The shared activation routing and its correspondence to the generator key\<close>

text \<open>Keep the entered store's globals, abstract them to point intervals, and take the
  executable global-restricted key.  A function of the concrete store alone; the caller
  context \<open>kc\<close> is not read.\<close>

definition ivl_enterc :: "ivl st \<Rightarrow> store \<Rightarrow> ivl st" where
  "ivl_enterc kc s = ivl_abs_route_st (\<lambda>x. ivl_of_int (s x))"

text \<open>On an inhabited caller slot whose globals are point intervals, the routing computed
  from the concrete store equals the routing the generator computes from the abstract caller
  slot: point-exactness collapses \<^const>\<open>restrict_global\<close> of the pointwise abstraction to
  \<^const>\<open>restrict_global\<close> of the slot, and \<^const>\<open>ivl_abs_route_st\<close> is a function of that.\<close>

lemma ivl_route_correspondence:
  fixes sg :: "(pp \<times> ivl st) + ivl st \<Rightarrow> ivl abs_state"
  assumes s: "s \<in> \<lbrakk>sg (Inl (cl, kc))\<rbrakk>"
    and pts: "\<And>x. IMP2_Globals.is_global x \<Longrightarrow> point_ivl (sg (Inl (cl, kc)) x)"
  shows "ivl_enterc kc s = ivl_abs_route_st (sg (Inl (cl, kc)))"
proof -
  have "restrict_global (\<lambda>x. ivl_of_int (s x)) = restrict_global (sg (Inl (cl, kc)))"
  proof (rule ext)
    fix x
    show "restrict_global (\<lambda>x. ivl_of_int (s x)) x = restrict_global (sg (Inl (cl, kc))) x"
    proof (cases "IMP2_Globals.is_global x")
      case True
      have g: "s x \<in> gamma_ivl (sg (Inl (cl, kc)) x)"
        using s unfolding gamma_state_def by simp
      have "ivl_of_int (s x) = sg (Inl (cl, kc)) x"
        by (rule point_ivl_gamma_exact[OF pts[OF True] g])
      thus ?thesis unfolding restrict_global_def using True by simp
    next
      case False
      thus ?thesis unfolding restrict_global_def by simp
    qed
  qed
  thus ?thesis unfolding ivl_enterc_def ivl_abs_route_st_def by simp
qed

subsection \<open>The rehydrate combine tree's dependency set\<close>

text \<open>\<^const>\<open>dep_aux\<close> of the rehydrating combine is exactly the caller call node and the
  routed callee exit; \<^const>\<open>Side\<close> targets and the \<^const>\<open>Answer\<close> carry no dependency.\<close>

lemma dep_aux_ivl_combine_rehydrate_abs:
  "dep_aux sg (ivl_combine_rehydrate_abs cc ex ctx)
     = {Inl (cc, ctx), Inl (ex, ivl_abs_route_st (sg (Inl (cc, ctx))))}"
  by (simp add: ivl_combine_rehydrate_abs_def Let_def)

subsection \<open>Backward query-membership dischargers (q_caller / q_callee)\<close>

text \<open>The caller call node and routed callee exit of a solved return node are solved.  Both
  are \<open>combine_edge_dep_in_vars\<close> of the combine tree's two dependencies.\<close>

lemma ivl_q_caller:
  assumes finC: "finite (combines g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey (\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c)
                  frame_seed g etf bot0 s0) x sg vars"
    and c: "(cl, ex, v) \<in> combines g" and cov: "(v, kc) \<in> vars"
  shows "(cl, kc) \<in> vars"
proof -
  have "Inl (cl, kc)
          \<in> dep_aux sg ((\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c) kc cl ex)"
    by (simp add: dep_aux_ivl_combine_rehydrate_abs)
  thus ?thesis by (rule combine_edge_dep_in_vars[OF finC pp cov c])
qed

lemma ivl_q_callee:
  assumes finC: "finite (combines g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey (\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c)
                  frame_seed g etf bot0 s0) x sg vars"
    and c: "(cl, ex, v) \<in> combines g" and cov: "(v, kc) \<in> vars"
  shows "(ex, ivl_abs_route_st (sg (Inl (cl, kc)))) \<in> vars"
proof -
  have "Inl (ex, ivl_abs_route_st (sg (Inl (cl, kc))))
          \<in> dep_aux sg ((\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c) kc cl ex)"
    by (simp add: dep_aux_ivl_combine_rehydrate_abs)
  thus ?thesis by (rule combine_edge_dep_in_vars[OF finC pp cov c])
qed

subsection \<open>The return combine bound (COMB_BOUND)\<close>

text \<open>\<open>seeded_clean_comb_bound\<close> dominates the rehydrate combine tree by the return slot;
  \<open>traverse_ivl_combine_rehydrate_abs\<close> exposes it as the \<^const>\<open>combine_abs\<close> continuation
  at the routed callee exit; the routing correspondence rewrites the witness routing
  \<^const>\<open>ivl_enterc\<close> to that executable key.\<close>

lemma ivl_comb_bound:
  fixes sg :: "(pp \<times> ivl st) + ivl st \<Rightarrow> ivl abs_state"
  assumes finC: "finite (combines g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey (\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c)
                  frame_seed g etf bot0 s0) x sg vars"
    and c: "(cl, ex, v) \<in> combines g" and cov: "(v, kc) \<in> vars"
    and s: "s \<in> \<lbrakk>sg (Inl (cl, kc))\<rbrakk>"
    and pts: "\<And>x. IMP2_Globals.is_global x \<Longrightarrow> point_ivl (sg (Inl (cl, kc)) x)"
  shows "\<langle>sg (Inl (cl, kc))|sg (Inl (ex, ivl_enterc kc s))\<rangle> \<le> sg (Inl (v, kc))"
proof -
  have route: "ivl_enterc kc s = ivl_abs_route_st (sg (Inl (cl, kc)))"
    by (rule ivl_route_correspondence[where sg = sg and cl = cl and kc = kc and s = s,
          OF s pts])
  have "traverse_rhs ((\<lambda>c cc ex. ivl_combine_rehydrate_abs cc ex c) kc cl ex) sg
          \<le> sg (Inl (v, kc))"
    by (rule seeded_clean_comb_bound[OF finC pp cov c])
  thus ?thesis unfolding route by (simp add: traverse_ivl_combine_rehydrate_abs)
qed

end
