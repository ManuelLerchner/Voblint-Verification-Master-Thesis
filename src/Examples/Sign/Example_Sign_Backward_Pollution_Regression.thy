theory Example_Sign_Backward_Pollution_Regression
  imports
    "Voblint_Analysis_Sign.Sign_Backward"
    "Voblint_Analysis_Sign.Sign_Exec"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: disjunct-arm-pollution fix for backward filtering\<close>

text \<open>
  \<open>Or (And (x=0) (x=1)) (And (y=0) (y=1))\<close> known \<open>True\<close>: both disjuncts are
  individually self-contradictory (no integer is both \<open>0\<close> and \<open>1\<close>), but only
  after their own two-step backward narrowing. \<open>feasible\<close>'s single forward
  check on each disjunct evaluates both conjuncts independently against the
  same incoming state (\<open>aval_sign\<close>'s \<open>And\<close> case), so it cannot see the
  contradiction that only emerges once the first conjunct's narrowing feeds
  the second -- it answers \<open>SNonNeg\<close> (unknown) for both disjuncts, and
  \<open>feasible\<close> therefore passes both. Raw \<^const>\<open>bfilter_sign\<close>'s own
  recursion does find each disjunct's narrowed value \<open>SBot\<close>, but the other
  disjunct's untouched location survives the pointwise join and overrides
  it, so the whole state comes back exactly as unconstrained as it started
  for \<open>x\<close> and \<open>y\<close> -- \<open>bfilter\<close>'s documented join-arm-pollution limitation.
  \<open>sign_backward_domain.bfilter_lifted\<close> canonicalizes each disjunct to
  structural \<open>Bot\<close> before joining, so the genuine, whole-state infeasibility
  is discovered instead, and the executable \<open>bfilter_sign_st_lift\<close> mirror
  is proven exact to it.
\<close>

definition x_eq_0_and_1 :: exp where
  "x_eq_0_and_1 = And (Eq (V (STR ''x'')) (N 0)) (Eq (V (STR ''x'')) (N 1))"

definition y_eq_0_and_1 :: exp where
  "y_eq_0_and_1 = And (Eq (V (STR ''y'')) (N 0)) (Eq (V (STR ''y'')) (N 1))"

definition x_or_y_contradiction :: exp where
  "x_or_y_contradiction = Or x_eq_0_and_1 y_eq_0_and_1"

subsection \<open>The forward gate misses both arms' contradictions\<close>

text \<open>
  This is the actual failure mechanism, independent of what the join then
  does with it: \<^const>\<open>feasible_sign\<close> passes both disjuncts, so nothing
  gates either arm out before its own backward recursion runs.
\<close>

lemma feasible_sign_misses_arm_contradictions:
  "feasible_sign x_eq_0_and_1 True (\<lambda>_. STop)
   \<and> feasible_sign y_eq_0_and_1 True (\<lambda>_. STop)"
  unfolding x_eq_0_and_1_def y_eq_0_and_1_def by eval

subsection \<open>Raw \<^const>\<open>bfilter_sign\<close> loses all information about \<open>x\<close> and \<open>y\<close>\<close>

lemma bfilter_sign_pollution_raw_loses_precision:
  "bfilter_sign x_or_y_contradiction True (\<lambda>_. STop) (STR ''x'') = STop
   \<and> bfilter_sign x_or_y_contradiction True (\<lambda>_. STop) (STR ''y'') = STop"
  unfolding x_or_y_contradiction_def x_eq_0_and_1_def y_eq_0_and_1_def by eval

subsection \<open>Lifted \<open>bfilter_lifted\<close> discovers the genuine infeasibility\<close>

text \<open>
  Proved once for an arbitrary variable \<open>x\<close>, then instantiated at
  \<^term>\<open>STR ''x''\<close> and \<^term>\<open>STR ''y''\<close> below, rather than duplicated: any
  single \<open>And (Eq (V x) (N 0)) (Eq (V x) (N 1))\<close> arm narrows to \<open>SBot\<close> at
  \<open>x\<close> and is witness-bottom overall, regardless of which variable it is.
\<close>

lemma bfilter_sign_eq_0_and_1_lifted:
  "sign_backward_domain.bfilter_lifted
     (And (Eq (V x) (N 0)) (Eq (V x) (N 1))) True (\<lambda>_. STop) = Bot"
proof -
  have step1: "bfilter_sign (Eq (V x) (N 1)) True (\<lambda>_. STop) = (\<lambda>_. STop)(x := SPos)"
    by simp
  have step2: "bfilter_sign (Eq (V x) (N 0)) True ((\<lambda>_. STop)(x := SPos))
                 = ((\<lambda>_. STop)(x := SPos))(x := SBot)"
    by simp
  have not_empty_pos: "\<not> is_empty_state ((\<lambda>_. STop)(x := SPos))"
    by (simp add: is_empty_state_def is_bottom_sign_def)
  have empty_bot: "is_empty_state ((\<lambda>_. STop)(x := SBot))"
    by (auto simp: is_empty_state_def is_bottom_sign_def intro: exI[of _ x])
  have l1: "sign_backward_domain.bfilter_lifted (Eq (V x) (N 1)) True (\<lambda>_. STop)
              = Lifted ((\<lambda>_. STop)(x := SPos))"
    using step1 not_empty_pos by simp
  have l2: "sign_backward_domain.bfilter_lifted (Eq (V x) (N 0)) True
              ((\<lambda>_. STop)(x := SPos)) = Bot"
    using step2 empty_bot by simp
  show ?thesis using l1 l2 by simp
qed

lemma bfilter_sign_lifted_pollution_fixed:
  "sign_backward_domain.bfilter_lifted x_or_y_contradiction True (\<lambda>_. STop) = Bot"
proof -
  have hx: "sign_backward_domain.bfilter_lifted x_eq_0_and_1 True (\<lambda>_. STop) = Bot"
    unfolding x_eq_0_and_1_def using bfilter_sign_eq_0_and_1_lifted .
  have hy: "sign_backward_domain.bfilter_lifted y_eq_0_and_1 True (\<lambda>_. STop) = Bot"
    unfolding y_eq_0_and_1_def using bfilter_sign_eq_0_and_1_lifted .
  show ?thesis
    unfolding x_or_y_contradiction_def using hx hy by simp
qed

subsection \<open>The executable mirror is exact, not just the specification\<close>

text \<open>
  \<^const>\<open>bfilter_sign_st_lift\<close> is the code-generatable mirror of
  \<open>sign_backward_domain.bfilter_lifted\<close>; \<open>bfilter_st_lift_correct\<close>
  (\<^theory>\<open>Voblint_Analysis_Base.Exec_Backward\<close>) proves that readback commutes
  exactly with filtering. This lemma is not a restatement of that theorem:
  it separately checks that code
  generation for the whole dependency chain still succeeds (no
  non-executable \<open>is_empty_state\<close> leaked into it) and that the concrete,
  finite bottom test built into \<^const>\<open>update_resolved_st_q_lift\<close> actually
  fires and produces structural \<open>Bot\<close> -- exactly the failure mode the old
  whole-expression probe design would have missed.
\<close>

lemma bfilter_sign_exec_pollution_fixed:
  "bfilter_sign_st_lift (\<lambda>_. False) x_or_y_contradiction True (Lifted top_sign_st) = Bot"
  unfolding x_or_y_contradiction_def x_eq_0_and_1_def y_eq_0_and_1_def by eval

subsection \<open>The semantic branch operation inherits the fix\<close>

text \<open>
  \<open>x_or_y_contradiction\<close> is trivially feasible at the top level (\<open>STop\<close>
  answers every forward check as unknown), so \<^const>\<open>branch_lifted_sign\<close>
  reduces to \<open>sign_backward_domain.bfilter_lifted\<close> here and inherits its
  precision directly, exercising \<open>branch_lifted_sign\<close> itself rather than
  only its internal filter. \<open>branch_lifted_sign\<close> is not yet the domain's
  registered branch operation -- Sign still supplies plain
  \<^const>\<open>branch_sign\<close> -- so this regression covers the fixed operation
  itself, not yet a production analyzer run through it.
\<close>

lemma branch_sign_lifted_pollution_fixed:
  "branch_lifted_sign x_or_y_contradiction True (\<lambda>_. STop) = Bot"
  using bfilter_sign_lifted_pollution_fixed
  by (simp add: sign_backward_domain.branch_lifted_def sign_backward_domain.feasible_def)

end
