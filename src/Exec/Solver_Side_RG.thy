theory Solver_Side_RG
  imports Exec_Refinement "TD.TD_side_upd_rule"
begin

section \<open>Globally-restricted side values\<close>

text \<open>
  \<^const>\<open>restrict_global_resolved_q\<close> is the idempotent projection onto global
  variables. A strategy tree is \<open>side_rg\<close> when every \<open>Side\<close> node it can reach
  (under any query answer) carries a value already fixed by that projection.
  The side-effecting solver then keeps every \<open>Inr\<close> slot
  \<open>restrict_global_resolved_q\<close>-shaped, since the running join of such values
  stays shaped -- that invariant is what the theorems below propagate through
  the solver's iteration.
\<close>

lemma restrict_global_resolved_q_idem [simp]:
  "restrict_global_resolved_q (restrict_global_resolved_q s) =
     restrict_global_resolved_q s"
proof (rule resolved_st_q_eq_iff[THEN iffD2])
  show "lookup_resolved_st_q (restrict_global_resolved_q
      (restrict_global_resolved_q s)) =
      lookup_resolved_st_q (restrict_global_resolved_q s)"
  proof (rule ext)
    fix loc
    show "lookup_resolved_st_q (restrict_global_resolved_q
        (restrict_global_resolved_q s)) loc =
        lookup_resolved_st_q (restrict_global_resolved_q s) loc"
      by (cases loc; simp)
  qed
qed

primrec side_rg ::
  "('x, 'g, ('a::bot) resolved_st_q lifted) strategy_tree \<Rightarrow> bool"
where
  "side_rg (Answer d) = True"
| "side_rg (QueryL y f) = (\<forall>v. side_rg (f v))"
| "side_rg (QueryG y f) = (\<forall>v. side_rg (f v))"
| "side_rg (Side y d t) = (map_lift restrict_global_resolved_q d = d \<and> side_rg t)"

lemma map_lift_restrict_global_resolved_q_idem [simp]:
  "map_lift restrict_global_resolved_q (map_lift restrict_global_resolved_q x) =
     map_lift restrict_global_resolved_q x"
  by (cases x) simp_all

section \<open>Generic: an executable termination check yields solver-domain membership\<close>

text \<open>Every domain instance restates the same three-line bridge --- unfold its own
  \<open>_terminates_def\<close>, then \<open>term_equivalence\<close> and \<open>solve_c_dom_def\<close> turn the executable
  \<open>solve_c x \<noteq> None\<close> check into \<open>solve_dom x\<close> --- once per update rule (join, warrowing, ...)
  and once per domain (Sign, Interval, Parity). Stating it generically \<^emph>\<open>inside\<close> the vendored
  \<^locale>\<open>TD_side_upd_rule\<close> makes it available on every concrete interpretation as
  \<open>TD_side_<rule>_Interp.solve_dom_of_solve_c\<close>, so a domain's \<open>_terminates_via_solve_c\<close> lemma
  reduces to unfolding its own definition and citing this fact.\<close>

lemma (in TD_side_upd_rule) solve_dom_of_solve_c:
  assumes "solve_c x \<noteq> None"
  shows "solve_dom x"
  unfolding term_equivalence solve_c_dom_def using assms by (cases "solve_c x") auto

section \<open>Side-effecting solver keeps \<open>Inr\<close> slots globally restricted\<close>

text \<open>If every reachable side contribution is fixed by
  @{const restrict_global_resolved_q}, the solver keeps every global slot in that image: slots
  start at bottom, joins preserve the image, and only such contributions reach them.
  This yields the \<open>Inr\<close>-slot invariant without a least-solution argument. The proof is
  domain-generic but intentionally phrased at the executable bridge's state projection.\<close>

definition rg_val :: "('a::bot) resolved_st_q \<Rightarrow> bool" where
  "rg_val d \<longleftrightarrow> (\<forall>x. lookup_resolved_st_q d (Local_Location x) = bot)"

lemma rg_val_bot [simp]:
  "rg_val (bot :: ('a::bounded_semilattice_sup_bot) resolved_st_q)"
  by (simp add: rg_val_def)

lemma rg_val_sup:
  assumes "rg_val a" and "rg_val b"
  shows "rg_val (a \<squnion> b)"
  using assms by (simp add: rg_val_def)

lemma rg_val_restrict_global [simp]:
  "rg_val (restrict_global_resolved_q d)"
  by (simp add: rg_val_def)


lemma rg_val_of_restrict_global:
  assumes "restrict_global_resolved_q d = d"
  shows "rg_val d"
proof -
  have eq: "d = restrict_global_resolved_q d"
    using assms by simp
  show ?thesis
    unfolding rg_val_def
    by (subst eq) simp
qed

lemma rg_val_eq_restrict_global:
  assumes "rg_val d"
  shows "d = restrict_global_resolved_q d"
  using assms
  unfolding rg_val_def resolved_st_q_eq_iff fun_eq_iff
  by (auto split: location.splits)

text \<open>
  \<open>rg_val_lift\<close> mirrors \<^const>\<open>side_rg\<close>'s \<open>Side\<close>-node check at the lifted level: a structural
  \<^const>\<open>Bot\<close> slot trivially satisfies it (there is no reconstructed state to check), only a
  \<^const>\<open>Lifted\<close> slot constrains its payload via the raw \<open>rg_val\<close> above.
\<close>

primrec rg_val_lift :: "('a::bot) resolved_st_q lifted \<Rightarrow> bool" where
  "rg_val_lift Bot = True"
| "rg_val_lift (Lifted d) = rg_val d"

lemma rg_val_lift_bot [simp]:
  "rg_val_lift (bot :: ('a::bounded_semilattice_sup_bot) resolved_st_q lifted)"
  by simp

lemma rg_val_lift_sup:
  assumes "rg_val_lift a" and "rg_val_lift b"
  shows "rg_val_lift (a \<squnion> b)"
  using assms by (cases a; cases b; simp add: rg_val_sup)

lemma rg_val_lift_restrict_global [simp]:
  "rg_val_lift (map_lift restrict_global_resolved_q d)"
  by (cases d) simp_all

lemma rg_val_lift_of_restrict_global:
  assumes "map_lift restrict_global_resolved_q d = d"
  shows "rg_val_lift d"
  using assms by (cases d) (auto intro: rg_val_of_restrict_global)

lemma rg_val_lift_eq_restrict_global:
  assumes "rg_val_lift d"
  shows "d = map_lift restrict_global_resolved_q d"
  using assms by (cases d) (auto intro: rg_val_eq_restrict_global)

abbreviation rg_state :: "(pp, unit, ('a::bot) resolved_st_q lifted) state \<Rightarrow> bool" where
  "rg_state s \<equiv> (\<forall>g. rg_val_lift (state.\<sigma> s (Inr g)))"

abbreviation rg_sides :: "(unit \<Rightarrow> ('a::bot) resolved_st_q lifted) \<Rightarrow> bool" where
  "rg_sides sa \<equiv> (\<forall>g. rg_val_lift (sa g))"

lemma TD_side_always_join_rg_ind:
  fixes T :: "(pp, unit, ('a::bounded_warrowing) resolved_st_q lifted) eqsT"  assumes sr: "\<And>z. side_rg (T z)"
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
  have sb: "rg_sides (\<lambda>_. (\<bottom> :: 'a resolved_st_q lifted))" by simp
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
    have sd: "map_lift restrict_global_resolved_q yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Subsumed(1))
    have rgy: "rg_val_lift yd" by (rule rg_val_lift_of_restrict_global[OF sd[THEN conjunct1]])
    have rgd: "rg_val_lift d'"
      using Side_Subsumed(2) rg_val_lift_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Subsumed(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    show ?thesis
      by (rule Eval.IH(5)[OF Side_Subsumed(1) Side_Subsumed(2) Side_Subsumed(3) refl
                              Side_Subsumed(4) refl Side_Subsumed(6) Eval.prems(2) rgsa' sg1])
  next
    case (Side_Effect y yd t1 d' sides_acc' d'' ug_state1 infl1 stabl1)
    have sd: "map_lift restrict_global_resolved_q yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Effect(1))
    have rgy: "rg_val_lift yd" by (rule rg_val_lift_of_restrict_global[OF sd[THEN conjunct1]])
    have rgd: "rg_val_lift d'"
      using Side_Effect(2) rg_val_lift_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Effect(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    have d''eq: "d'' = \<sigma> state (Inr y) \<squnion> d'"
      using Side_Effect(4)
      by (auto simp: update_global_always_join_def Let_def split: if_splits)
    have rgd'': "rg_val_lift d''"
      using d''eq rg_val_lift_sup[OF Eval.prems(2)[THEN spec] rgd] by simp
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
  fixes T :: "(pp, unit, ('a::bounded_warrowing) resolved_st_q lifted) eqsT"
  assumes dom: "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE('a resolved_st_q lifted) T v"
  assumes sr: "\<And>z. side_rg (T z)"
  assumes sol: "TD_side_always_join_Interp_solve T v = (vars, sigma)"
  shows "sigma (Inr g) = map_lift restrict_global_resolved_q (sigma (Inr g))"
proof -
  define s0 :: "(pp, unit, 'a resolved_st_q lifted) state" where eq0:
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
  have rgs: "rg_state state"
    by (rule TD_side_always_join_rg_ind(2)[OF sr dm iter[symmetric] rg0])
  have rg_sigma: "rg_val_lift (sigma (Inr g))"
    using rgs sig by simp
  show ?thesis
    by (rule rg_val_lift_eq_restrict_global[OF rg_sigma])
qed


section \<open>Bot-stable warrowing: preserving the Inr-restricted invariant under warrow\<close>

text \<open>
  The always-join update rule keeps the \<open>Inr\<close>-restricted invariant because @{term "(\<squnion>)"}
  preserves it directly (@{thm [source] rg_val_sup}). \<^const>\<open>update_global_warrowing_apinis\<close>
  instead combines the prior global value with a join over recorded per-origin contributions via
  @{term "(\<nabla>\<Delta>)"}. @{term "(\<nabla>\<Delta>)"} does not preserve @{const rg_val} for an arbitrary
  \<^class>\<open>warrowing\<close> instance: nothing in that class says \<open>bot \<nabla> bot = bot\<close> or
  \<open>bot \<Delta> bot = bot\<close>. That bot-stability is a genuine (if mild) property of a concrete domain's
  widen/narrow, so \<open>Wbb\<close>/\<open>Nbb\<close> below take it as an explicit hypothesis (discharged once per
  domain, e.g. \<open>ivl\<close>) rather than as a type class: the \<open>widening\<close>/\<open>narrowing\<close> classes here fix
  their sort via an explicit \<open>'a::order\<close> annotation inside \<open>fixes\<close> rather than via a superclass,
  which does not compose with an extra subclass adding further axioms about the class's own bare
  \<open>bot\<close>.
\<close>

text \<open>
  \<^typ>\<open>'a resolved_st_q\<close>'s own widen/narrow are pointwise
  (@{thm [source] lookup_widen_resolved_st_q}, @{thm [source] lookup_narrow_on_resolved_st_q}), so
  \<open>\<nabla>\<Delta>\<close> at the vector level picks one branch (widen or narrow, decided once by the whole-vector
  \<open>\<le>\<close>) and applies that same branch at every location uniformly --- including at every
  \<open>Local_Location\<close>, where both operands are already \<open>bot\<close> under \<^const>\<open>rg_val\<close>. Bot-stability
  of the base domain is exactly what closes that last step.
\<close>

lemma rg_val_warrow:
  fixes a b :: "('a::bounded_warrowing) resolved_st_q"
  assumes Wbb: "widen (bot::'a) bot = bot" and Nbb: "narrow (bot::'a) bot = bot"
    and "rg_val a" and "rg_val b"
  shows "rg_val (a \<nabla>\<Delta> b)"
proof (cases "b \<le> a")
  case True
  then have eq: "a \<nabla>\<Delta> b = a \<Delta> b" by (simp add: warrow_def)
  show ?thesis
    unfolding eq using assms unfolding rg_val_def
    by (simp add: narrow_resolved_st_q_def Nbb)
next
  case False
  then have eq: "a \<nabla>\<Delta> b = a \<nabla> b" by (simp add: warrow_def)
  show ?thesis
    unfolding eq using assms unfolding rg_val_def by (simp add: Wbb)
qed

text \<open>
  \<^const>\<open>update_global_warrowing_apinis\<close> reads back @{const sup_over_origins}, the join over
  every per-origin contribution recorded so far for a global slot: showing that join stays
  \<^const>\<open>rg_val\<close> needs a small closure fact for @{const sup_fset} that @{thm [source] rg_val_sup}
  alone does not give, since @{const sup_fset} folds over an arbitrary (possibly larger than
  two-element) finite set.
\<close>

lemma rg_val_sup_fset:
  fixes S :: "(('a::bounded_semilattice_sup_bot) resolved_st_q) fset"
  assumes "\<And>x. x |\<in>| S \<Longrightarrow> rg_val x" and "S \<noteq> {||}"
  shows "rg_val (sup_fset S)"
  using assms
proof (induction S)
  case empty
  then show ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases "S = {||}")
    case True
    then show ?thesis using insert.prems(1) by (simp add: sup_fset_def)
  next
    case False
    have ih: "rg_val (sup_fset S)"
      by (rule insert.IH) (use insert.prems(1) False in auto)
    have hx: "rg_val x" using insert.prems(1) by simp
    have fne: "fset S \<noteq> {}" using False by (metis bot_fset.rep_eq fset_cong)
    have goal_eq: "sup_fset (finsert x S) = x \<squnion> sup_fset S"
      by (simp add: sup_fset_def Sup_fin.insert fne)
    show ?thesis
      unfolding goal_eq using rg_val_sup[OF hx ih] .
  qed
qed

text \<open>
  Lifted counterparts of \<open>rg_val_warrow\<close>/\<open>rg_val_sup_fset\<close>: the warrowing solver's own
  \<open>state\<close>/\<open>ug_state\<close> now carry \<^typ>\<open>'a resolved_st_q lifted\<close> throughout (matching the
  executable trees the D/G generator feeds it), so both closure facts are needed at
  the lifted level too. \<^const>\<open>Bot\<close> is unconditionally warrow-stable on both sides
  (\<open>widen_lifted Bot Bot = Bot\<close>, \<open>narrow_lifted Bot Bot = Bot\<close>): no \<open>Wbb\<close>/\<open>Nbb\<close>-style
  hypothesis is needed for the structural \<open>Bot\<close> case, only for the \<^const>\<open>Lifted\<close>/
  \<^const>\<open>Lifted\<close> case, which reduces to the raw \<open>rg_val_warrow\<close>.
\<close>

lemma rg_val_lift_warrow:
  fixes a b :: "('a::bounded_warrowing) resolved_st_q lifted"
  assumes Wbb: "widen (bot::'a) bot = bot" and Nbb: "narrow (bot::'a) bot = bot"
    and ra: "rg_val_lift a" and rb: "rg_val_lift b"
  shows "rg_val_lift (a \<nabla>\<Delta> b)"
proof (cases a)
  case Bot
  then show ?thesis using rb by (cases b) (simp_all add: warrow_def)
next
  case (Lifted p)
  show ?thesis
  proof (cases b)
    case Bot
    then show ?thesis using Lifted ra by (simp add: warrow_def)
  next
    case (Lifted q)
    have rp: "rg_val p" and rq: "rg_val q"
      using ra rb \<open>a = lifted.Lifted p\<close> \<open>b = lifted.Lifted q\<close> by simp_all
    have "a \<nabla>\<Delta> b = lifted.Lifted (p \<nabla>\<Delta> q)"
      using \<open>a = lifted.Lifted p\<close> \<open>b = lifted.Lifted q\<close>
      unfolding warrow_def by simp
    then show ?thesis
      using rg_val_warrow[OF Wbb Nbb rp rq] by simp
  qed
qed

lemma rg_val_lift_sup_fset:
  fixes S :: "(('a::bounded_semilattice_sup_bot) resolved_st_q lifted) fset"
  assumes "\<And>x. x |\<in>| S \<Longrightarrow> rg_val_lift x" and "S \<noteq> {||}"
  shows "rg_val_lift (sup_fset S)"
  using assms
proof (induction S)
  case empty
  then show ?case by simp
next
  case (insert x S)
  show ?case
  proof (cases "S = {||}")
    case True
    then show ?thesis using insert.prems(1) by (simp add: sup_fset_def)
  next
    case False
    have ih: "rg_val_lift (sup_fset S)"
      by (rule insert.IH) (use insert.prems(1) False in auto)
    have hx: "rg_val_lift x" using insert.prems(1) by simp
    have fne: "fset S \<noteq> {}" using False by (metis bot_fset.rep_eq fset_cong)
    have goal_eq: "sup_fset (finsert x S) = x \<squnion> sup_fset S"
      by (simp add: sup_fset_def Sup_fin.insert fne)
    show ?thesis
      unfolding goal_eq using rg_val_lift_sup[OF hx ih] .
  qed
qed

section \<open>The warrowing update rule keeps the Inr-restricted invariant\<close>

text \<open>
  \<^const>\<open>update_global_warrowing_apinis\<close> additionally reads its own per-origin bookkeeping
  (\<open>\<rho>\<close>) to compute @{const sup_over_origins}, which @{const update_global_always_join} never
  does --- so, unlike \<open>TD_side_always_join_rg_ind\<close>, the induction here must also carry an
  invariant on the solver's \<open>ug_state\<close> component alongside \<open>rg_state\<close>.
\<close>

abbreviation rg_ug :: "('x, 'g, ('a::bot) resolved_st_q lifted) ug_state \<Rightarrow> bool" where
  "rg_ug ug \<equiv> (\<forall>g orig. rg_val_lift (rho_lookup (\<rho> ug) g orig))"

abbreviation rg_both where
  "rg_both state ug \<equiv> rg_state state \<and> rg_ug ug"

lemma TD_side_warrowing_apinis_rg_ind:
  fixes T :: "(pp, unit, ('a::bounded_warrowing) resolved_st_q lifted) eqsT"
  assumes sr: "\<And>z. side_rg (T z)"
    and Wbb: "widen (bot::'a) bot = bot" and Nbb: "narrow (bot::'a) bot = bot"
  shows
  "TD_side_warrowing_apinis_Interp.query_dom T x y state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_warrowing_apinis_Interp.query T x y state ug_state
    \<Longrightarrow> rg_both state ug_state \<Longrightarrow> rg_both state' ug_state'"
  and
  "TD_side_warrowing_apinis_Interp.iterate_dom T x state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_warrowing_apinis_Interp.iterate T x state ug_state
    \<Longrightarrow> rg_both state ug_state \<Longrightarrow> rg_both state' ug_state'"
  and
  "TD_side_warrowing_apinis_Interp.repeat_dom T x state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_warrowing_apinis_Interp.repeat T x state ug_state
    \<Longrightarrow> rg_both state ug_state \<Longrightarrow> rg_both state' ug_state'"
  and
  "TD_side_warrowing_apinis_Interp.eval_dom T x t sides_acc state ug_state
    \<Longrightarrow> (xd, state', ug_state') = TD_side_warrowing_apinis_Interp.eval T x t sides_acc state ug_state
    \<Longrightarrow> rg_both state ug_state \<Longrightarrow> rg_sides sides_acc \<Longrightarrow> side_rg t \<Longrightarrow> rg_both state' ug_state'"
proof (induction x y state ug_state and x state ug_state and x state ug_state
         and x t sides_acc state ug_state
       arbitrary: xd state' ug_state' and xd state' ug_state' and xd state' ug_state'
         and xd state' ug_state'
       rule: TD_side_warrowing_apinis_Interp.query_iterate_repeat_eval_pinduct)
  case (Query x y state ug_state)
  show ?case
    using Query.IH(1) Query.prems(1)
  proof (cases rule: TD_side_warrowing_apinis_Interp.query_iterate_lookup_cases_basic)
    case (Iterate state1 xd1 ug_state1)
    have rgc: "rg_both (state\<lparr>c := insert y (c state)\<rparr>) ug_state" using Query.prems(2) by simp
    have "rg_both state1 ug_state1"
      by (rule Query.IH(2)[OF Iterate(4) Iterate(2) rgc])
    then show ?thesis using Iterate(3) Iterate(5) by simp
  next
    case Lookup
    show ?thesis using Query.prems(2) Lookup(2) Lookup(4) by simp
  qed
next
  case (Iterate x state ug_state)
  show ?case
    using Iterate.IH(1) Iterate.prems(1)
  proof (cases rule: TD_side_warrowing_apinis_Interp.iterate_continue_fixpoint_cases)
    case Stable
    show ?thesis using Iterate.prems(2) Stable(1) Stable(4) by simp
  next
    case (Fixpoint state1 xd_new ug_state1)
    have rg1: "rg_both state1 ug_state1"
      by (rule Iterate.IH(2)[OF Fixpoint(5) refl Fixpoint(2) Iterate.prems(2)])
    show ?thesis using rg1 Fixpoint(6) Fixpoint(7) by simp
  next
    case (Continue state1 xd_new xd_new' infl2 stabl2 ug_state1)
    have rg1: "rg_both state1 ug_state1"
      by (rule Iterate.IH(2)[OF Continue(8) refl Continue(2) Iterate.prems(2)])
    have rg1': "rg_both (state1\<lparr>infl := infl2, stabl := stabl2,
                            \<sigma> := (\<sigma> state1)(Inl x := xd_new')\<rparr>) ug_state1"
      using rg1 by simp
    show ?thesis
      by (rule Iterate.IH(3)[OF Continue(8) refl Continue(2) refl refl Continue(3)
                                Continue(4) Continue(5) refl Continue(7) rg1'])
  qed
next
  case (Repeat x state ug_state)
  have sb: "rg_sides (\<lambda>_. (\<bottom> :: 'a resolved_st_q lifted))" by simp
  show ?case
    using Repeat.IH(1) Repeat.prems(1)
  proof (cases rule: TD_side_warrowing_apinis_Interp.repeat_unstable_stable_cases)
    case (Unstable state1 d1 ug_state1)
    have rgst: "rg_both (state\<lparr>stabl := insert x (stabl state)\<rparr>) ug_state"
      using Repeat.prems(2) by simp
    have rg1: "rg_both state1 ug_state1"
      by (rule Repeat.IH(2)[OF Unstable(2) rgst sb sr])
    show ?thesis
      by (rule Repeat.IH(3)[OF Unstable(2) refl refl Unstable(3) Unstable(5) rg1])
  next
    case Stable
    have rgst: "rg_both (state\<lparr>stabl := insert x (stabl state)\<rparr>) ug_state"
      using Repeat.prems(2) by simp
    show ?thesis
      by (rule Repeat.IH(2)[OF Stable(2) rgst sb sr])
  qed
next
  case (Eval x t sides_acc state ug_state)
  show ?case
    using Eval.IH(1) Eval.prems(1)
  proof (cases rule: TD_side_warrowing_apinis_Interp.eval_query_answer_cases_basic)
    case (QueryL y g yd state1 ug_state1)
    have rg1: "rg_both state1 ug_state1"
      by (rule Eval.IH(2)[OF QueryL(1) QueryL(3) Eval.prems(2)])
    have sgt: "side_rg (g yd)" using Eval.prems(4) by (simp add: QueryL(1))
    show ?thesis
      by (rule Eval.IH(3)[OF QueryL(1) QueryL(3) refl refl QueryL(5) rg1 Eval.prems(3) sgt])
  next
    case (QueryG y g yd)
    have rgI: "rg_both (state\<lparr>infl := fminsert (infl state) (Inr y) x\<rparr>) ug_state"
      using Eval.prems(2) by simp
    have sgt: "side_rg (g yd)" using Eval.prems(4) by (simp add: QueryG(1))
    show ?thesis
      by (rule Eval.IH(4)[OF QueryG(1) QueryG(2) QueryG(4) rgI Eval.prems(3) sgt])
  next
    case (Side_Subsumed y yd t1 sides_acc' d' ug_state1)
    have sd: "map_lift restrict_global_resolved_q yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Subsumed(1))
    have rgy: "rg_val_lift yd" by (rule rg_val_lift_of_restrict_global[OF sd[THEN conjunct1]])
    have rgd: "rg_val_lift d'"
      using Side_Subsumed(2) rg_val_lift_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Subsumed(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    have ug_eq: "ug_state1 = ug_state"
      using Side_Subsumed(4)
      by (auto simp: update_global_warrowing_apinis_def Let_def split: if_splits)
    have rgboth: "rg_both state ug_state1" using Eval.prems(2) ug_eq by simp
    show ?thesis
      by (rule Eval.IH(5)[OF Side_Subsumed(1) Side_Subsumed(2) Side_Subsumed(3) refl
                              Side_Subsumed(4) refl Side_Subsumed(6) rgboth rgsa' sg1])
  next
    case (Side_Effect y yd t1 d' sides_acc' d'' ug_state1 infl1 stabl1)
    have rgs: "rg_state state" using Eval.prems(2) by (rule conjunct1)
    have rgu: "rg_ug ug_state" using Eval.prems(2) by (rule conjunct2)
    have sd: "map_lift restrict_global_resolved_q yd = yd \<and> side_rg t1"
      using Eval.prems(4) by (simp add: Side_Effect(1))
    have rgy: "rg_val_lift yd" by (rule rg_val_lift_of_restrict_global[OF sd[THEN conjunct1]])
    have rgd: "rg_val_lift d'"
      using Side_Effect(2) rg_val_lift_sup[OF Eval.prems(3)[THEN spec] rgy] by simp
    have rgsa': "rg_sides sides_acc'"
      using Side_Effect(3) Eval.prems(3) rgd by (auto simp: fun_upd_apply)
    have sg1: "side_rg t1" using sd by simp
    have rho_eq: "\<rho> ug_state1 = (\<rho> ug_state)(y := fmupd x d' (\<rho> ug_state y))"
      and d''eq: "d'' = (\<sigma> state (Inr y)) \<nabla>\<Delta> (sup_over_origins ug_state1 y)"
      using Side_Effect(4)
      by (auto simp: update_global_warrowing_apinis_def Let_def split: if_splits)
    have rgug1: "rg_ug ug_state1"
    proof -
      have "rg_val_lift (rho_lookup (\<rho> ug_state1) g' orig')" for g' orig'
      proof (cases "g' = y")
        case True
        then show ?thesis
          using rho_eq rgd rgu
          by (simp add: fmlookup_default_def fmupd_lookup)
      next
        case False
        then show ?thesis using rho_eq rgu by (simp add: fmlookup_default_def)
      qed
      then show ?thesis by simp
    qed
    have rgsup: "rg_val_lift (sup_over_origins ug_state1 y)"
      unfolding sup_over_origins_def
    proof (rule rg_val_lift_sup_fset)
      show "\<And>z. z |\<in>| (rho_lookup (\<rho> ug_state1) y |`| fmdom (\<rho> ug_state1 y)) \<Longrightarrow> rg_val_lift z"
        using rgug1 by auto
      show "rho_lookup (\<rho> ug_state1) y |`| fmdom (\<rho> ug_state1 y) \<noteq> {||}"
        using rho_eq by (auto simp: fmdom_fmupd)
    qed
    have rgold: "rg_val_lift (\<sigma> state (Inr y))" using rgs by simp
    have rgd'': "rg_val_lift d''"
      using d''eq rg_val_lift_warrow[OF Wbb Nbb rgold rgsup] by simp
    have rgE: "rg_both (state\<lparr>infl := infl1, stabl := stabl1,
                          \<sigma> := (\<sigma> state)(Inr y := d'')\<rparr>) ug_state1"
      using rgs rgd'' rgug1 by (auto simp: fun_upd_apply)
    show ?thesis
      by (rule Eval.IH(6)[OF Side_Effect(1) Side_Effect(2) Side_Effect(3) refl
                              Side_Effect(4) refl refl Side_Effect(5) Side_Effect(7)
                              rgE rgsa' sg1])
  next
    case Answer
    show ?thesis using Eval.prems(2) Answer(2) Answer(3) by simp
  qed
qed


text \<open>
  Specialising to the top-level @{const TD_side_warrowing_apinis_Interp_solve}, exactly
  mirroring @{thm [source] TD_side_always_join_solve_Inr_rg}: the solver starts from
  @{const init_basic_ug_state} (empty \<open>\<rho>\<close>, so \<^const>\<open>rg_ug\<close> holds trivially) and
  @{term "TD_side_warrowing_apinis_Interp.init_state"} (every slot \<open>bot\<close>, so \<^const>\<open>rg_state\<close>
  holds), so the combined \<^const>\<open>rg_both\<close> invariant holds initially and is preserved to the
  result by \<open>TD_side_warrowing_apinis_rg_ind\<close>.
\<close>

lemma TD_side_warrowing_apinis_solve_Inr_rg:
  fixes T :: "(pp, unit, ('a::bounded_warrowing) resolved_st_q lifted) eqsT"
  assumes dom: "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE('a resolved_st_q lifted) T v"
  assumes sr: "\<And>z. side_rg (T z)"
    and Wbb: "widen (bot::'a) bot = bot" and Nbb: "narrow (bot::'a) bot = bot"
  assumes sol: "TD_side_warrowing_apinis_Interp_solve T v = (vars, sigma)"
  shows "sigma (Inr g) = map_lift restrict_global_resolved_q (sigma (Inr g))"
proof -
  define s0 :: "(pp, unit, 'a resolved_st_q lifted) state" where eq0:
    "s0 = TD_side_bounded_narrowing_Interp.init_state
            \<lparr>c := insert v (c TD_side_bounded_narrowing_Interp.init_state)\<rparr>"
  obtain d state ug where iter:
    "TD_side_warrowing_apinis_Interp.iterate T v s0 init_basic_ug_state = (d, state, ug)"
    by (cases "TD_side_warrowing_apinis_Interp.iterate T v s0 init_basic_ug_state") auto
  have sig: "sigma = \<sigma> state"
    using sol[unfolded TD_side_warrowing_apinis_Interp.solve_def]
    apply (simp add: iter eq0[symmetric] case_prod_unfold)
    by (metis TD_side.state.select_convs(1) TD_side_warrowing_per_origin_Interp.init_state_def eq0
        fst_conv iter snd_conv)
  have dm: "TD_side_warrowing_apinis_Interp.iterate_dom T v s0 init_basic_ug_state"
    using dom[unfolded TD_side_warrowing_apinis_Interp.solve_dom_def, folded eq0]
    by (simp add: TD_side_warrowing_per_origin_Interp.init_state_def eq0)
  have rg0: "rg_both s0 init_basic_ug_state"
  proof (intro conjI allI)
    fix g'
    show "rg_val_lift (\<sigma> s0 (Inr g'))"
      unfolding eq0 by (simp add: TD_side_warrowing_apinis_Interp.init_state_def)
  next
    fix g' orig'
    show "rg_val_lift (rho_lookup (\<rho> init_basic_ug_state) g' orig')"
    proof -
      have eq: "rho_lookup (\<rho> init_basic_ug_state) g' orig' = bot"
        by (simp add: init_basic_ug_state_def fmlookup_default_def)
      show ?thesis unfolding eq by simp
    qed
  qed
  have rgboth: "rg_both state ug"
    by (rule TD_side_warrowing_apinis_rg_ind(2)[OF sr Wbb Nbb dm iter[symmetric] rg0])
  have rg_sigma: "rg_val_lift (sigma (Inr g))"
    using rgboth sig by simp
  show ?thesis
    by (rule rg_val_lift_eq_restrict_global[OF rg_sigma])
qed


end


