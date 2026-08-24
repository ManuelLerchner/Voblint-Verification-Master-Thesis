section \<open>Example: backward guard refinement vs identity assume\<close>

theory Example_Guard_Refinement
  imports "Voblint_Analysis.Interval_Domain"
begin

hide_const (open) Update_rules.N

text \<open>
  The identity assumption transfer is sound but imprecise.  Backward guard
  refinement intersects the incoming interval with the states satisfying the
  guard, which preserves the bounded loop invariant through one body step.
  Sign cannot express the numeric bounds; interval filtering exposes the gain.
\<close>

subsection \<open>Setup: loop-head abstract state and identity baseline\<close>

definition sigma_x :: "ivl \<Rightarrow> ivl abs_state" where
  "sigma_x iv = (\<lambda>_. Ivl MinInf PlusInf)(STR ''x'' := iv)"

abbreviation "sigma_loop_head \<equiv> sigma_x (Ivl (Fin 0) (Fin 20))"

text \<open>The identity baseline leaves the abstract state unchanged.\<close>
definition assume_ivl_identity :: "exp \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "assume_ivl_identity _ sigma = sigma"

subsection \<open>One guard: @{text "x < 20"} narrows the upper bound\<close>

lemma refine_x_lt_20:
  "bfilter_ivl (Less (V (STR ''x'')) (N 20)) True sigma_loop_head (STR ''x'') = Ivl (Fin 0) (Fin 19)"
  unfolding sigma_x_def
  by eval

lemma identity_x_lt_20:
  "assume_ivl_identity (Less (V (STR ''x'')) (N 20)) sigma_loop_head (STR ''x'') =
   Ivl (Fin 0) (Fin 20)"
  by (simp add: assume_ivl_identity_def sigma_x_def)

text \<open>
  The refined interval is strictly tighter: @{text 20} is possible before the
  guard but excluded on the then-branch.
\<close>
lemma refine_excludes_20:
  "20 \<in> gamma_ivl (Ivl (Fin 0) (Fin 20))"
  "20 \<notin> gamma_ivl (Ivl (Fin 0) (Fin 19))"
  by simp_all

subsection \<open>One body step: @{text "x := x + 1"} after the guard\<close>

definition body_after_refined :: "ivl abs_state" where
  "body_after_refined =
     assign_ivl (STR ''x'') (Plus (V (STR ''x'')) (N 1))
       (bfilter_ivl (Less (V (STR ''x'')) (N 20)) True sigma_loop_head)"

definition body_after_identity :: "ivl abs_state" where
  "body_after_identity =
     assign_ivl (STR ''x'') (Plus (V (STR ''x'')) (N 1))
       (assume_ivl_identity (Less (V (STR ''x'')) (N 20)) sigma_loop_head)"

lemma body_step_refined:
  "body_after_refined (STR ''x'') = Ivl (Fin 1) (Fin 20)"
  unfolding body_after_refined_def sigma_x_def
  by eval

lemma body_step_identity:
  "body_after_identity (STR ''x'') = Ivl (Fin 1) (Fin 21)"
  unfolding body_after_identity_def sigma_x_def assume_ivl_identity_def
  by (simp add: assign_ivl_def normalize_ivl_def)

text \<open>
  Joining the initial @{text "[0,0]"} with the body exit is where the gap
  compounds: backward analysis yields the tight loop-head interval; identity
  assume drifts upward and never closes at @{text "[0,20]"} without widening.
\<close>
lemma loop_join_refined:
  "sigma_x (Ivl (Fin 0) (Fin 0)) (STR ''x'') \<squnion> body_after_refined (STR ''x'') = Ivl (Fin 0) (Fin 20)"
  unfolding body_after_refined_def sigma_x_def
  by eval

lemma loop_join_identity:
  "sigma_x (Ivl (Fin 0) (Fin 0)) (STR ''x'') \<squnion> body_after_identity (STR ''x'') = Ivl (Fin 0) (Fin 21)"
  unfolding body_after_identity_def sigma_x_def assume_ivl_identity_def
  by (simp add: sup_ivl_def assign_ivl_def normalize_ivl_def)

lemma backward_analysis_strictly_tighter:
  "Ivl (Fin 0) (Fin 20) \<le> Ivl (Fin 0) (Fin 21)"
  "Ivl (Fin 0) (Fin 21) \<le> Ivl (Fin 0) (Fin 20) \<longleftrightarrow> False"
  by (simp_all add: less_eq_ivl_def)

subsection \<open>An infeasible guard refines to canonical bottom\<close>

text \<open>
  A guard no state can satisfy empties the filtered interval.  The stored value
  is the canonical \<^const>\<open>bot\<close>, not one of the many reversed bound pairs that
  denote the empty set just as well: \<open>ivl_backward_domain\<close> is interpreted with
  \<^const>\<open>intersect_ivl\<close>, which normalises its result.

  The raw lattice \<^const>\<open>inf\<close> keeps the reversed pair, and has to --- dropping it
  to \<^const>\<open>bot\<close> would cost the greatest-lower-bound law, since the reversed pair
  is itself a common lower bound of the two operands.  The two operations
  therefore disagree syntactically while denoting the same empty set, which is
  the point of having both.
\<close>

lemma guard_infeasible_canonical_bot:
  "bfilter_ivl (Less (V (STR ''x'')) (N 0)) True (sigma_x (Ivl (Fin 5) (Fin 9))) (STR ''x'') = bot"
  unfolding sigma_x_def by eval

lemma intersect_ivl_disjoint_bot:
  "intersect_ivl (Ivl (Fin 0) (Fin 3)) (Ivl (Fin 5) (Fin 9)) = bot"
  by eval

lemma meet_ivl_disjoint_keeps_reversed_bounds:
  "meet_ivl (Ivl (Fin 0) (Fin 3)) (Ivl (Fin 5) (Fin 9)) = Ivl (Fin 5) (Fin 3)"
  by eval

lemma disjoint_intersection_and_meet_agree_semantically:
  "gamma_ivl (intersect_ivl (Ivl (Fin 0) (Fin 3)) (Ivl (Fin 5) (Fin 9))) = {}"
  "gamma_ivl (meet_ivl (Ivl (Fin 0) (Fin 3)) (Ivl (Fin 5) (Fin 9))) = {}"
  by (simp_all add: is_bottom_ivl_correct[symmetric] is_bottom_ivl_def bot_ivl_def)

subsection \<open>Forward feasibility decides guards backward narrowing keeps\<close>

definition guard_cmp_eq_one :: exp where
  "guard_cmp_eq_one = Eq (Less (V (STR ''x'')) (N 0)) (N 1)"

text \<open>
  \<^const>\<open>branch_ivl\<close> gates \<^const>\<open>bfilter_ivl\<close> behind a forward
  \<^const>\<open>interval_tobool\<close> test on the whole condition, and that gate is
  strictly stronger on a guard whose Boolean-valued subexpression sits in an
  operand position.  \<^const>\<open>guard_cmp_eq_one\<close> is such a guard: its
  \<^const>\<open>Eq\<close> inversion narrows the left operand's target to the empty
  interval, but \<^const>\<open>afilter_ivl\<close> has no narrowing rule for a comparison
  node, so that target is dropped and the incoming state survives unchanged.
  Forward evaluation of the same condition yields \<^term>\<open>Ivl (Fin 0) (Fin 0)\<close>,
  whose \<^const>\<open>interval_tobool\<close> contradicts the selected polarity, so the gate
  returns \<^const>\<open>bot\<close>.  @{thm [source] branch_ivl_le_bfilter_ivl} is the general
  inequality; this is a state where it is strict.
\<close>
lemma cmp_guard_forward_value:
  "aval_ivl guard_cmp_eq_one (sigma_x (Ivl (Fin 5) (Fin 5))) = Ivl (Fin 0) (Fin 0)"
  unfolding guard_cmp_eq_one_def sigma_x_def by eval

lemma bfilter_keeps_infeasible_operand_guard:
  "bfilter_ivl guard_cmp_eq_one True (sigma_x (Ivl (Fin 5) (Fin 5))) (STR ''x'')
     = Ivl (Fin 5) (Fin 5)"
  unfolding guard_cmp_eq_one_def sigma_x_def by eval

lemma branch_kills_infeasible_operand_guard:
  "branch_ivl guard_cmp_eq_one True (sigma_x (Ivl (Fin 5) (Fin 5))) (STR ''x'') = bot"
  unfolding guard_cmp_eq_one_def sigma_x_def by eval

subsection \<open>An infeasible disjunct is dropped from the join\<close>

definition sigma_xy :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl abs_state" where
  "sigma_xy ix iy = (\<lambda>_. Ivl MinInf PlusInf)(STR ''x'' := ix, STR ''y'' := iy)"

abbreviation "sigma_x5_y_unknown \<equiv> sigma_xy (Ivl (Fin 5) (Fin 5)) (Ivl MinInf PlusInf)"

definition guard_disj :: exp where
  "guard_disj = Or (Less (N 0) (V (STR ''y''))) guard_cmp_eq_one"

text \<open>
  \<^const>\<open>bfilter_ivl\<close>'s \<^const>\<open>Or\<close> case under a true polarity gates each
  disjunct before joining, so a disjunct no state satisfies contributes
  \<^const>\<open>bot\<close> --- the unit of the join --- rather than its own unrefined
  incoming state.  Here \<^const>\<open>guard_cmp_eq_one\<close> is impossible for
  \<open>x = [5,5]\<close>, so the join keeps exactly what the feasible disjunct
  established: \<open>y\<close> narrows to \<^term>\<open>Ivl (Fin 1) PlusInf\<close> rather than staying
  unconstrained.  This is the shape Goblint's \<open>inv_exp\<close> has for \<open>LOr\<close>, where
  the arm whose refinement raises \<open>Deadcode\<close> is dropped from the join.

  The branch transfer's own gate cannot reach this: it reads the whole
  condition, whose forward value spans \<^term>\<open>Ivl (Fin 0) (Fin 1)\<close> and so
  decides nothing.  Gating per disjunct is what recovers it, and the last
  lemma below is that identity --- the join of the two \<^const>\<open>branch_ivl\<close>
  results is what \<^const>\<open>bfilter_ivl\<close> computes.
\<close>

lemma disj_guard_forward_value:
  "aval_ivl guard_disj sigma_x5_y_unknown = Ivl (Fin 0) (Fin 1)"
  unfolding guard_disj_def guard_cmp_eq_one_def sigma_xy_def by eval

lemma feasible_disjunct_alone_refines_y:
  "bfilter_ivl (Less (N 0) (V (STR ''y''))) True sigma_x5_y_unknown (STR ''y'')
     = Ivl (Fin 1) PlusInf"
  unfolding sigma_xy_def by eval

lemma bfilter_or_drops_infeasible_disjunct:
  "bfilter_ivl guard_disj True sigma_x5_y_unknown (STR ''y'') = Ivl (Fin 1) PlusInf"
  unfolding guard_disj_def guard_cmp_eq_one_def sigma_xy_def by eval

lemma branch_or_drops_infeasible_disjunct:
  "branch_ivl guard_disj True sigma_x5_y_unknown (STR ''y'') = Ivl (Fin 1) PlusInf"
  unfolding guard_disj_def guard_cmp_eq_one_def sigma_xy_def by eval

lemma bfilter_or_is_the_gated_join:
  "(branch_ivl (Less (N 0) (V (STR ''y''))) True sigma_x5_y_unknown
     \<squnion> branch_ivl guard_cmp_eq_one True sigma_x5_y_unknown) (STR ''y'')
     = bfilter_ivl guard_disj True sigma_x5_y_unknown (STR ''y'')"
  unfolding guard_disj_def guard_cmp_eq_one_def sigma_xy_def by eval

end
