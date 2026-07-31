theory Solver_Side_RG
  imports Exec_Bridge "TD.TD_side_upd_rule"
begin

section \<open>Side-effecting solver keeps \<open>Inr\<close> slots globally restricted\<close>

text \<open>If every reachable side contribution is fixed by
  @{const restrict_global_st}, the solver keeps every global slot in that image: slots
  start at bottom, joins preserve the image, and only such contributions reach them.
  This yields \<open>inr_slot_locals_bot\<close> without a least-solution argument. The proof is
  domain-generic but intentionally phrased at the executable bridge's state projection.\<close>

definition rg_val :: "('a::bot) st \<Rightarrow> bool" where
  "rg_val d \<longleftrightarrow> restrict_global_st d = d"

lemma rg_val_bot [simp]: "rg_val (bot :: ('a::bounded_semilattice_sup_bot) st)"
  unfolding rg_val_def by (rule restrict_global_st_eq_when_lookup_local_bot) simp

lemma rg_val_sup:
  assumes "rg_val a" and "rg_val b"
  shows "rg_val (a \<squnion> b)"
  using assms unfolding rg_val_def
  by (metis restrict_global_st_sup_restrict_global_st)

abbreviation rg_state :: "(pp, unit, ('a::bot) st) state \<Rightarrow> bool" where
  "rg_state s \<equiv> (\<forall>g. rg_val (state.\<sigma> s (Inr g)))"

abbreviation rg_sides :: "(unit \<Rightarrow> ('a::bot) st) \<Rightarrow> bool" where
  "rg_sides sa \<equiv> (\<forall>g. rg_val (sa g))"

lemma TD_side_always_join_rg_ind:
  fixes T :: "(pp, unit, ('a::bounded_warrowing) st) eqsT"
  assumes sr: "\<And>z. side_rg (T z)"
  shows
  "TD_side_always_join_Interp.query_dom T x y state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_always_join_Interp.query T x y state ug_state
    \<Longrightarrow> rg_state state \<Longrightarrow> rg_state state'"
  and
  "TD_side_always_join_Interp.iterate_dom T x state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_always_join_Interp.iterate T x state ug_state
    \<Longrightarrow> rg_state state \<Longrightarrow> rg_state state'"
  and
  "TD_side_always_join_Interp.repeat_dom T x state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_always_join_Interp.repeat T x state ug_state
    \<Longrightarrow> rg_state state \<Longrightarrow> rg_state state'"
  and
  "TD_side_always_join_Interp.eval_dom T x t sides_acc state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_always_join_Interp.eval T x t sides_acc state ug_state
    \<Longrightarrow> rg_state state \<Longrightarrow> rg_sides sides_acc \<Longrightarrow> side_rg t \<Longrightarrow> rg_state state'"
proof (induction x y state ug_state and x state ug_state and x state ug_state
         and x t sides_acc state ug_state
       arbitrary: xd state' ug_state' and xd state' ug_state' and xd state' ug_state'
         and xd state' ug_state'
       rule: TD_side_always_join_Interp.query_iterate_repeat_eval_pinduct)
  case (Query x y state ug_state)
  show ?case
    using Query.IH(1) Query.prems(1)
  proof (cases rule: TD_side_always_join_Interp.query_iterate_lookup_cases_basic)
    case (Iterate state1 xd1 ug_state1)
    have rgc: "rg_state (state\<lparr>c := insert y (c state)\<rparr>)" using Query.prems(2) by simp
    have "rg_state state1"
      by (rule Query.IH(2)[OF Iterate(4) Iterate(2) rgc])
    then show ?thesis using Iterate(3) by simp
  next
    case Lookup
    show ?thesis using Query.prems(2) Lookup(2) by simp
  qed
next
  case (Iterate x state ug_state)
  show ?case
    using Iterate.IH(1) Iterate.prems(1)
  proof (cases rule: TD_side_always_join_Interp.iterate_continue_fixpoint_cases)
    case Stable
    show ?thesis using Iterate.prems(2) Stable(1) by simp
  next
    case (Fixpoint state1 xd_new ug_state1)
    have rg1: "rg_state state1"
      by (rule Iterate.IH(2)[OF Fixpoint(5) refl Fixpoint(2) Iterate.prems(2)])
    show ?thesis using rg1 Fixpoint(6) by simp
  next
    case (Continue state1 xd_new xd_new' infl2 stabl2 ug_state1)
    have rg1: "rg_state state1"
      by (rule Iterate.IH(2)[OF Continue(8) refl Continue(2) Iterate.prems(2)])
    have rg1': "rg_state (state1\<lparr>infl := infl2, stabl := stabl2,
                            \<sigma> := (\<sigma> state1)(Inl x := xd_new')\<rparr>)"
      using rg1 by simp
    show ?thesis
      by (rule Iterate.IH(3)[OF Continue(8) refl Continue(2) refl refl Continue(3)
                                Continue(4) Continue(5) refl Continue(7) rg1'])
  qed
next
  case (Repeat x state ug_state)
  have sb: "rg_sides (\<lambda>_. (\<bottom> :: 'a st))" by simp
  show ?case
    using Repeat.IH(1) Repeat.prems(1)
  proof (cases rule: TD_side_always_join_Interp.repeat_unstable_stable_cases)
    case (Unstable state1 d1 ug_state1)
    have rgst: "rg_state (state\<lparr>stabl := insert x (stabl state)\<rparr>)"
      using Repeat.prems(2) by simp
    have rg1: "rg_state state1"
      by (rule Repeat.IH(2)[OF Unstable(2) rgst sb sr])
    show ?thesis
      by (rule Repeat.IH(3)[OF Unstable(2) refl refl Unstable(3) Unstable(5) rg1])
  next
    case Stable
    have rgst: "rg_state (state\<lparr>stabl := insert x (stabl state)\<rparr>)"
      using Repeat.prems(2) by simp
    show ?thesis
      by (rule Repeat.IH(2)[OF Stable(2) rgst sb sr])
  qed
next
  case (Eval x t sides_acc state ug_state)
  show ?case
    using Eval.IH(1) Eval.prems(1)
  proof (cases rule: TD_side_always_join_Interp.eval_query_answer_cases_basic)
    case (QueryL y g yd state1 ug_state1)
    have rg1: "rg_state state1"
      by (rule Eval.IH(2)[OF QueryL(1) QueryL(3) Eval.prems(2)])
    have sgt: "side_rg (g yd)" using Eval.prems(4) by (simp add: QueryL(1))
    show ?thesis
      by (rule Eval.IH(3)[OF QueryL(1) QueryL(3) refl refl QueryL(5) rg1 Eval.prems(3) sgt])
  next
    case (QueryG y g yd)
    have rgI: "rg_state (state\<lparr>infl := fminsert (infl state) (Inr y) x\<rparr>)"
      using Eval.prems(2) by simp
    have sgt: "side_rg (g yd)" using Eval.prems(4) by (simp add: QueryG(1))
    show ?thesis
      by (rule Eval.IH(4)[OF QueryG(1) QueryG(2) QueryG(4) rgI Eval.prems(3) sgt])
  next
    case (Side_Subsumed y yd t1 sides_acc' d' ug_state1)
    have sd: "restrict_global_st yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Subsumed(1))
    have rgy: "rg_val yd" using sd by (simp add: rg_val_def)
    have rgd: "rg_val d'"
      using Side_Subsumed(2) rg_val_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Subsumed(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    show ?thesis
      by (rule Eval.IH(5)[OF Side_Subsumed(1) Side_Subsumed(2) Side_Subsumed(3) refl
                              Side_Subsumed(4) refl Side_Subsumed(6) Eval.prems(2) rgsa' sg1])
  next
    case (Side_Effect y yd t1 d' sides_acc' d'' ug_state1 infl1 stabl1)
    have sd: "restrict_global_st yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Effect(1))
    have rgy: "rg_val yd" using sd by (simp add: rg_val_def)
    have rgd: "rg_val d'"
      using Side_Effect(2) rg_val_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Effect(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    have d''eq: "d'' = \<sigma> state (Inr y) \<squnion> d'"
      using Side_Effect(4)
      by (auto simp: update_global_always_join_def Let_def split: if_splits)
    have rgd'': "rg_val d''"
      using d''eq rg_val_sup[OF Eval.prems(2)[THEN spec] rgd] by simp
    have rgE: "rg_state (state\<lparr>infl := infl1, stabl := stabl1,
                          \<sigma> := (\<sigma> state)(Inr y := d'')\<rparr>)"
      using Eval.prems(2) rgd'' by (auto simp: fun_upd_apply)
    show ?thesis
      by (rule Eval.IH(6)[OF Side_Effect(1) Side_Effect(2) Side_Effect(3) refl
                              Side_Effect(4) refl refl Side_Effect(5) Side_Effect(7)
                              rgE rgsa' sg1])
  next
    case Answer
    show ?thesis using Eval.prems(2) Answer(2) by simp
  qed
qed

text \<open>
  Specialising the induction to the top-level @{const TD_side_always_join_Interp_solve}:
  the solver starts from @{const TD_side_always_join_Interp.init_state} (every slot
  @{term \<bottom>}), so the \<open>Inr\<close>-globally-restricted invariant holds initially and is
  preserved to the result.
\<close>

lemma TD_side_always_join_solve_Inr_rg:
  fixes T :: "(pp, unit, ('a::bounded_warrowing) st) eqsT"
  assumes dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE('a st) T v"
  assumes sr: "\<And>z. side_rg (T z)"
  assumes sol: "TD_side_always_join_Interp_solve T v = (vars, sigma)"
  shows "sigma (Inr g) = restrict_global_st (sigma (Inr g))"
proof -
  define s0 :: "(pp, unit, 'a st) state" where eq0:
    "s0 = TD_side_bounded_narrowing_Interp.init_state
            \<lparr>c := insert v (c TD_side_bounded_narrowing_Interp.init_state)\<rparr>"
  obtain d state ug where iter:
    "TD_side_always_join_Interp.iterate T v s0 init_basic_ug_state = (d, state, ug)"
    by (cases "TD_side_always_join_Interp.iterate T v s0 init_basic_ug_state") auto
  have sig: "sigma = \<sigma> state"
    using sol[unfolded TD_side_always_join_Interp.solve_def]
    apply (simp add: iter eq0[symmetric] case_prod_unfold)
    by (metis TD_side.state.select_convs(1) TD_side_warrowing_per_origin_Interp.init_state_def eq0
        fst_conv iter snd_conv)
  have dm: "TD_side_always_join_Interp.iterate_dom T v s0 init_basic_ug_state"
    using dom[unfolded TD_side_always_join_Interp.solve_dom_def, folded eq0]
    by (simp add: TD_side_warrowing_per_origin_Interp.init_state_def eq0)
  have rg0: "rg_state s0"
    unfolding eq0 by (simp add: TD_side_always_join_Interp.init_state_def)
  have "rg_state state"
    by (rule TD_side_always_join_rg_ind(2)[OF sr dm iter[symmetric] rg0])
  then show ?thesis using sig by (simp add: rg_val_def)
qed

end
