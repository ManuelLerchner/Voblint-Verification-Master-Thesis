theory Int_Refinement_Control
  imports Int_Refinement
begin

section \<open>How often to run the exchange, and what a run costs\<close>

text \<open>
  The laws in @{theory Voblint_Analysis_Int.Int_Refinement} say what one
  component may tell another; they say nothing about when to ask. This theory
  settles that. \<open>refine_round\<close> is one full pass over the exchange; a
  \<open>refine_mode\<close> picks how many passes an analysis run takes --- \<open>Refine_Never\<close>
  none, \<open>Refine_Once\<close> a single pass, \<open>Refine_Fixpoint\<close> passes until the value
  stops changing.

  The fixpoint mode is the awkward one. Iteration is a \<open>while_option\<close> loop, so
  it returns \<open>None\<close> when it does not stabilize; \<open>refine_fix\<close> keeps the input in
  that branch to stay a total function, while the generated code keeps running
  the structural-equality loop. Every mode is proved reductive and
  concretization-preserving, but only \<open>Refine_Never\<close> and \<open>Refine_Once\<close> are
  monotone --- \<open>refine_nonfixpoint_mono\<close> --- which is why callers that need
  monotonicity carry the \<open>mode \<noteq> Refine_Fixpoint\<close> side condition.
\<close>

datatype refine_mode =
    Refine_Never
  | Refine_Once
  | Refine_Fixpoint

definition canonical_refine_step :: "int_dom => int_dom" where
  "canonical_refine_step d =
     (let d' = refine_round d
      in if is_empty d' then bot else d')"

definition refine_fix_option :: "int_dom => int_dom option" where
  "refine_fix_option d =
     while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step
       d"

text \<open>
  The option result is \<open>None\<close> exactly when structural iteration does not
  stabilize. The total logical wrapper returns the input in that branch; generated
  execution remains in the structural-equality loop.
\<close>

definition refine_fix :: "int_dom => int_dom" where
  "refine_fix d =
     (case refine_fix_option d of
        Some r => r
      | None => d)"

definition refine :: "refine_mode => int_dom => int_dom" where
  "refine mode d =
     (case mode of
        Refine_Never => d
      | Refine_Once => refine_round d
      | Refine_Fixpoint => refine_fix d)"


lemma canonical_refine_step_exact:
  "gamma_int_dom (canonical_refine_step d) = gamma_int_dom d"
proof (cases "is_empty (refine_round d)")
  case True
  have round_empty:
    "gamma_int_dom (refine_round d) = {}"
    using True
    by (simp add: is_bottom_int_dom_correct)
  have input_empty: "gamma_int_dom d = {}"
    using round_empty
      int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
  have bottom_empty:
    "gamma_int_dom (bot :: int_dom) = {}"
  proof -
    have "\<gamma> (bot :: int_dom) = {}"
      by (rule gamma_bot)
    then show ?thesis by simp
  qed
  show ?thesis
    unfolding canonical_refine_step_def Let_def
    using True input_empty bottom_empty by simp
next
  case False
  show ?thesis
    unfolding canonical_refine_step_def Let_def
    using False
      int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
qed


lemma refine_fix_option_exact:
  assumes result: "refine_fix_option d = Some r"
  shows "gamma_int_dom r = gamma_int_dom d"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  have invariant:
    "\<And>x.
       gamma_int_dom x = gamma_int_dom d \<Longrightarrow>
       canonical_refine_step x \<noteq> x \<Longrightarrow>
       gamma_int_dom (canonical_refine_step x) =
       gamma_int_dom d"
    using canonical_refine_step_exact by simp
  show ?thesis
  proof (rule while_option_rule[
      where P="\<lambda>x.
        gamma_int_dom x = gamma_int_dom d"
        and b="\<lambda>x.
          canonical_refine_step x \<noteq> x"
        and c=canonical_refine_step
        and s=d
        and t=r])
    fix x
    assume "gamma_int_dom x = gamma_int_dom d"
      "canonical_refine_step x \<noteq> x"
    then show
      "gamma_int_dom (canonical_refine_step x) =
       gamma_int_dom d"
      using canonical_refine_step_exact by simp
  next
    show
      "while_option
        (\<lambda>x. canonical_refine_step x \<noteq> x)
        canonical_refine_step d = Some r"
      by (rule loop)
  next
    show "gamma_int_dom d = gamma_int_dom d"
      by simp
  qed
qed

lemma refine_fix_option_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "canonical_refine_step r = r"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  have "\<not> canonical_refine_step r \<noteq> r"
    by (rule while_option_stop[OF loop])
  then show ?thesis by simp
qed

lemma refine_round_bot [simp]:
  "refine_round (bot :: int_dom) = bot"
proof (rule antisym)
  show "refine_round (bot :: int_dom) <= bot"
    by (rule int_reduction_step_reductive[
          OF refine_round_reduction_step])
  show "bot <= refine_round (bot :: int_dom)"
    by simp
qed

lemma refine_fix_option_round_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "refine_round r = r"
proof -
  have stable: "canonical_refine_step r = r"
    by (rule refine_fix_option_stable[OF result])
  show ?thesis
  proof (cases "is_empty (refine_round r)")
    case True
    have "r = bot"
      using stable True
      unfolding canonical_refine_step_def Let_def
      by simp
    then show ?thesis by simp
  next
    case False
    with stable show ?thesis
      unfolding canonical_refine_step_def Let_def
      by simp
  qed
qed


lemma refine_fix_exact [simp]:
  "gamma_int_dom (refine_fix d) = gamma_int_dom d"
proof (cases "refine_fix_option d")
  case None
  then show ?thesis
    unfolding refine_fix_def by simp
next
  case (Some r)
  have "gamma_int_dom r = gamma_int_dom d"
    by (rule refine_fix_option_exact[OF Some])
  with Some show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_fix_round_stable:
  assumes result: "refine_fix_option d = Some r"
  shows "refine_round (refine_fix d) = refine_fix d"
proof -
  have "refine_round r = r"
    by (rule refine_fix_option_round_stable[OF result])
  with result show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_never [simp]:
  "refine Refine_Never d = d"
  by (simp add: refine_def)

lemma refine_once [simp]:
  "refine Refine_Once d = refine_round d"
  by (simp add: refine_def)

lemma refine_fixpoint [simp]:
  "refine Refine_Fixpoint d = refine_fix d"
  by (simp add: refine_def)

lemma refine_once_reduction_step:
  "int_reduction_step (refine Refine_Once)"
proof -
  have "refine Refine_Once = refine_round"
    by (rule ext) simp
  then show ?thesis
    by (simp add: refine_round_reduction_step)
qed

lemma refine_once_reductive:
  "refine Refine_Once d <= d"
  by (rule int_reduction_step_reductive[
        OF refine_once_reduction_step])

lemma refine_once_mono:
  "mono (refine Refine_Once)"
  by (rule int_reduction_step_mono[
        OF refine_once_reduction_step])

lemma refine_exact:
  "gamma_int_dom (refine mode d) = gamma_int_dom d"
proof (cases mode)
  case Refine_Never
  then show ?thesis by simp
next
  case Refine_Once
  then show ?thesis
    using int_reduction_step_exact[OF refine_round_reduction_step]
    by simp
next
  case Refine_Fixpoint
  then show ?thesis by simp
qed

lemma canonical_refine_step_reductive:
  "canonical_refine_step d <= d"
proof (cases "is_empty (refine_round d)")
  case True
  then show ?thesis
    unfolding canonical_refine_step_def Let_def
    by simp
next
  case False
  then show ?thesis
    unfolding canonical_refine_step_def Let_def
    using int_reduction_step_reductive[OF refine_round_reduction_step]
    by simp
qed

lemma refine_fix_option_reductive:
  assumes result: "refine_fix_option d = Some r"
  shows "r <= d"
proof -
  have loop:
    "while_option
       (\<lambda>x. canonical_refine_step x \<noteq> x)
       canonical_refine_step d = Some r"
    using result unfolding refine_fix_option_def .
  show ?thesis
  proof (rule while_option_rule[
      where P="\<lambda>x. x <= d"
        and b="\<lambda>x. canonical_refine_step x \<noteq> x"
        and c=canonical_refine_step
        and s=d
        and t=r])
    fix x
    assume "x <= d" "canonical_refine_step x \<noteq> x"
    then show "canonical_refine_step x <= d"
      using canonical_refine_step_reductive[of x] by simp
  next
    show
      "while_option
        (\<lambda>x. canonical_refine_step x \<noteq> x)
        canonical_refine_step d = Some r"
      by (rule loop)
  next
    show "d <= d" by simp
  qed
qed

lemma refine_fix_reductive [simp]:
  "refine_fix d <= d"
proof (cases "refine_fix_option d")
  case None
  then show ?thesis
    unfolding refine_fix_def by simp
next
  case (Some r)
  have "r <= d"
    by (rule refine_fix_option_reductive[OF Some])
  with Some show ?thesis
    unfolding refine_fix_def by simp
qed

lemma refine_reductive:
  "refine mode d <= d"
proof (cases mode)
  case Refine_Never
  then show ?thesis by simp
next
  case Refine_Once
  then show ?thesis
    using refine_once_reductive by simp
next
  case Refine_Fixpoint
  then show ?thesis by simp
qed

section \<open>Witnesses\<close>

text \<open>
  Concrete values for the claims above. \<open>progressive_refinement_input\<close> is the raw
  sum of an odd value in \<open>[-1,-1]\<close> and one in \<open>[0,1]\<close>: its components together
  denote only \<open>0\<close>, but one round still leaves Sign at \<open>SNonPos\<close>, so a further
  round makes progress and \<open>Refine_Once\<close> differs from \<open>Refine_Fixpoint\<close>.
\<close>

definition progressive_refinement_input :: int_dom where
  "progressive_refinement_input =
     int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven (top :: congruence)"

lemma refinement_round_is_progressive:
  "refine_round progressive_refinement_input =
     int_dom_sipc SNonPos (Ivl (Fin 0) (Fin 0)) PEven (mk_congruence 0 2)"
  by eval

lemma refinement_once_not_fixpoint:
  "refine Refine_Once progressive_refinement_input
     \<noteq> refine Refine_Fixpoint progressive_refinement_input"
  by eval

text \<open>
  Sign teaches Interval that a range's non-positive half is unreachable, and
  Congruence teaches Parity: \<open>x \<equiv> 0 (mod 4)\<close> forces \<open>x\<close> even. Neither component
  derives either fact alone.
\<close>

lemma sign_interval_positive_narrows:
  "int_ivl (refine_interval (int_dom_sip SPos (Ivl (Fin (-10)) (Fin 5)) PTop))
     = Ivl (Fin 1) (Fin 5)"
  by eval

lemma congruence_parity_mod4_narrows:
  "int_parity (refine_congruence (int_dom_sipc STop (top :: ivl) PTop (mk_congruence 0 4)))
     = PEven"
  by eval

text \<open>
  Why \<^theory>\<open>Voblint_Analysis_Int.Int_Warrowing\<close> runs no refinement after
  \<open>narrow\<close>. \<open>a\<close> is a widened state (top); \<open>b\<close> a newer, more precise result whose
  components together denote only \<open>0\<close> while Sign has not caught up.
  Componentwise narrowing satisfies \<open>b \<le> narrow a b \<le> a\<close>; refining that result
  lets Sign derive \<open>SNonPos\<close> from the exact Interval bound, strictly below \<open>b\<close>'s
  \<open>STop\<close>, which breaks the solver's \<open>narrow_ge\<close> bracket.
\<close>

lemma post_narrow_refinement_would_violate_narrow_ge:
  "let a = (top :: int_dom);
       b = int_dom_sipc STop (Ivl (Fin (-1)) (Fin 0)) PEven (top :: congruence)
   in b \<le> a \<and> \<not> (b \<le> refine Refine_Once (narrow a b))"
  by eval

end
