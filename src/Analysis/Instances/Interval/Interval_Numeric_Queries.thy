theory Interval_Numeric_Queries
  imports Interval_Lattice "Voblint_Domain.Backward_Numeric_Queries"
begin

section \<open>Interval interpretation of the generic numeric-query interface\<close>

text \<open>
  Second-domain validation for \<open>abstract_numeric_queries\<close>
  (\<^theory>\<open>Voblint_Domain.Abstract_Numeric_Queries\<close>): a real, minimal Interval instance,
  interpreted without touching that generic theory. Entailment/refutation of
  \<open><\<close>/\<open>=\<close> reduces to comparing bounds: two intervals' \<open><\<close> relation is
  provable exactly when one interval's upper bound is strictly below the
  other's lower bound; \<open>=\<close> exactly when both are the same singleton point;
  \<open>\<noteq>\<close> exactly when the intervals are disjoint. Empty intervals (\<open>l > u\<close>) make
  every judgment vacuously true, the same role \<open>SBot\<close> plays for Sign.
\<close>

lemma gamma_ivlD:
  assumes "x \<in> gamma_ivl (Ivl l u)"
  shows "l \<le> Fin x" and "Fin x \<le> u"
  using assms
  by auto

lemma ivl_upper_lower_less:
  assumes "Fin i \<le> u" and "u < l" and "l \<le> Fin j"
  shows "i < j"
  using assms
  unfolding less_eq_eint_def less_eint_def
  by (metis eint_le.simps(4) less_eq_eint_def nless_le order_trans)

lemma ivl_upper_lower_not_less:
  assumes "Fin j \<le> u" and "u < l" and "l \<le> Fin i"
  shows "\<not> i < j"
  using ivl_upper_lower_less[OF assms]
  by auto

lemma ivl_upper_lower_less_eq:
  assumes "Fin i \<le> u" and "u \<le> l" and "l \<le> Fin j"
  shows "i \<le> j"
  using assms
  unfolding less_eq_eint_def
  by (metis eint_le.simps(4) less_eq_eint_def order_trans)

lemma ivl_upper_lower_not_less_eq:
  assumes "Fin j \<le> u" and "u \<le> l" and "l \<le> Fin i"
  shows "\<not> i < j"
  using ivl_upper_lower_less_eq[OF assms]
  by auto


lemma ivl_separated_not_equal:
  assumes "Fin i \<le> u1"
      and "u1 < l2"
      and "l2 \<le> Fin j"
  shows "i \<noteq> j"
  using ivl_upper_lower_less[OF assms]
  by auto

fun interval_less_true :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" where
  "interval_less_true (Ivl l1 u1) (Ivl l2 u2) =
     (\<not> l1 \<le> u1 \<or> \<not> l2 \<le> u2 \<or> u1 < l2)"

lemma interval_less_true_sound:
  assumes query: "interval_less_true a b"
      and ai: "i \<in> gamma_ivl a"
      and bj: "j \<in> gamma_ivl b"
  shows "i < j"
proof -
  obtain l1 u1 where a_def: "a = Ivl l1 u1"
    by (cases a)
  obtain l2 u2 where b_def: "b = Ivl l2 u2"
    by (cases b)

  from ai have i_bounds:
    "l1 \<le> Fin i" "Fin i \<le> u1"
    unfolding a_def
    by (auto dest: gamma_ivlD)

  from bj have j_bounds:
    "l2 \<le> Fin j" "Fin j \<le> u2"
    unfolding b_def
    by (auto dest: gamma_ivlD)

  from i_bounds j_bounds have nonempty:
    "l1 \<le> u1" "l2 \<le> u2"
    by order+

  with query have separated: "u1 < l2"
    unfolding a_def b_def
    by simp

  show ?thesis
    using i_bounds(2) separated j_bounds(1)
    by (rule ivl_upper_lower_less)
qed


fun interval_less_false :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" where
  "interval_less_false (Ivl l1 u1) (Ivl l2 u2) =
     (\<not> l1 \<le> u1 \<or> \<not> l2 \<le> u2 \<or> u2 \<le> l1)"

lemma interval_less_false_sound:
  assumes query: "interval_less_false a b"
      and ai: "i \<in> gamma_ivl a"
      and bj: "j \<in> gamma_ivl b"
  shows "\<not> i < j"
proof -
  obtain l1 u1 where a_def: "a = Ivl l1 u1"
    by (cases a)
  obtain l2 u2 where b_def: "b = Ivl l2 u2"
    by (cases b)

  from ai have i_bounds:
    "l1 \<le> Fin i" "Fin i \<le> u1"
    unfolding a_def
    by (auto dest: gamma_ivlD)

  from bj have j_bounds:
    "l2 \<le> Fin j" "Fin j \<le> u2"
    unfolding b_def
    by (auto dest: gamma_ivlD)

  from i_bounds j_bounds have nonempty:
    "l1 \<le> u1" "l2 \<le> u2"
    by order+

  with query have separated: "u2 \<le> l1"
    unfolding a_def b_def
    by simp

  show ?thesis
    using j_bounds(2) separated i_bounds(1)
    by (rule ivl_upper_lower_not_less_eq)
qed

text \<open>
  Permanent regression witnesses for the touching-boundary case: before this
  file's \<open>u2 < l1\<close> was weakened to \<open>u2 \<le> l1\<close>, \<open>interval_less_false\<close> could not
  refute \<open>0 < x\<close> for \<open>x = [-inf,0]\<close> (a range entirely \<open>\<le> 0\<close>) because the
  witnessing bound touches rather than strictly separates.
\<close>

lemma interval_less_false_witness_touching_boundary:
  "interval_less_false (Ivl (Fin 0) (Fin 0)) (Ivl MinInf (Fin 0))"
  by simp

lemma interval_less_false_witness_touching_boundary_finite:
  "interval_less_false (Ivl (Fin 1) (Fin 1)) (Ivl MinInf (Fin 1))"
  by simp

fun interval_eq_true :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" where
  "interval_eq_true (Ivl l1 u1) (Ivl l2 u2) =
     (\<not> l1 \<le> u1 \<or> \<not> l2 \<le> u2 \<or> (l1 = u1 \<and> l2 = u2 \<and> l1 = l2))"

lemma interval_eq_true_sound:
  assumes query: "interval_eq_true a b"
      and ai: "i \<in> gamma_ivl a"
      and bj: "j \<in> gamma_ivl b"
  shows "i = j"
proof -
  obtain l1 u1 where a_def: "a = Ivl l1 u1"
    by (cases a)
  obtain l2 u2 where b_def: "b = Ivl l2 u2"
    by (cases b)

  from ai have i_bounds:
    "l1 \<le> Fin i" "Fin i \<le> u1"
    unfolding a_def
    by (auto dest: gamma_ivlD)

  from bj have j_bounds:
    "l2 \<le> Fin j" "Fin j \<le> u2"
    unfolding b_def
    by (auto dest: gamma_ivlD)

  from i_bounds j_bounds have nonempty:
    "l1 \<le> u1" "l2 \<le> u2"
    by (meson order_trans)+

  with query have singleton:
    "l1 = u1" "l2 = u2" "l1 = l2"
    unfolding a_def b_def
    by auto

  from ai singleton have "Fin i = l1"
    unfolding a_def
    using i_bounds(1,2) by order

  moreover from bj singleton have "Fin j = l1"
    unfolding b_def
    using j_bounds(1,2) by order

  ultimately show ?thesis
    by blast
qed

fun interval_eq_false :: "ivl \<Rightarrow> ivl \<Rightarrow> bool" where
  "interval_eq_false (Ivl l1 u1) (Ivl l2 u2) =
     (\<not> l1 \<le> u1 \<or> \<not> l2 \<le> u2 \<or> u1 < l2 \<or> u2 < l1)"

lemma interval_eq_false_sound:
  assumes query: "interval_eq_false a b"
      and ai: "i \<in> gamma_ivl a"
      and bj: "j \<in> gamma_ivl b"
  shows "i \<noteq> j"
proof -
  obtain l1 u1 where a_def: "a = Ivl l1 u1"
    by (cases a)
  obtain l2 u2 where b_def: "b = Ivl l2 u2"
    by (cases b)

  from ai have i_bounds:
    "l1 \<le> Fin i" "Fin i \<le> u1"
    unfolding a_def
    by (auto dest: gamma_ivlD)

  from bj have j_bounds:
    "l2 \<le> Fin j" "Fin j \<le> u2"
    unfolding b_def
    by (auto dest: gamma_ivlD)

  from i_bounds j_bounds have nonempty:
    "l1 \<le> u1" "l2 \<le> u2"
    by (meson order_trans)+

  with query have separated:
    "u1 < l2 \<or> u2 < l1"
    unfolding a_def b_def
    by force

  then show ?thesis
    using i_bounds(1,2) ivl_separated_not_equal j_bounds(1,2) by blast
qed

subsection \<open>Goblint-style optional-Boolean queries\<close>

definition interval_less :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_less a b = (if interval_less_true a b then Some True
                         else if interval_less_false a b then Some False else None)"

definition interval_eq :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "interval_eq a b = (if interval_eq_true a b then Some True
                       else if interval_eq_false a b then Some False else None)"

lemma interval_less_sound:
  assumes "interval_less a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i < j) = r"
  using assms interval_less_true_sound interval_less_false_sound
  unfolding interval_less_def by (auto split: if_splits)

lemma interval_eq_sound:
  assumes "interval_eq a b = Some r" and "i \<in> gamma a" and "j \<in> gamma b"
  shows "(i = j) = r"
  using assms interval_eq_true_sound interval_eq_false_sound
  unfolding interval_eq_def by (auto split: if_splits)

subsection \<open>Interpreting the generic numeric-query interface\<close>

global_interpretation interval_numeric_queries: abstract_numeric_queries interval_less interval_eq
  by unfold_locales (metis interval_less_sound interval_eq_sound)+

subsection \<open>Semantic intersection versus raw lattice meet\<close>

text \<open>
  Unlike Sign, whose \<open>SBot\<close> is the lattice's unique empty representative, the
  raw \<open>ivl\<close> type has infinitely many non-canonical empty representations
  (any \<open>Ivl l u\<close> with \<open>l > u\<close>, documented at \<open>normalize_ivl\<close>), and only
  \<open>Ivl PlusInf MinInf\<close> is literally \<open>bot\<close>. Testing the raw
  \<^const>\<open>inf\<close> against \<open>bot\<close> therefore under-approximates disjointness:
  two disjoint, non-empty finite intervals meet to an empty-but-non-canonical
  result. The witness below is disjoint by \<open>interval_eq_false\<close>'s sound table,
  yet its representation-level meet is not \<open>bot\<close>.

  The generic \<open>eq_false\<close> derived in \<^locale>\<open>backward_domain\<close>'s own context
  (\<^theory>\<open>Voblint_Domain.Backward_Numeric_Queries\<close>) instead tests semantic
  intersection via @{const is_empty}. \<^const>\<open>intersect_ivl\<close> returns a value
  @{const is_empty} classifies as empty on the same witness, so the generic
  derivation classifies it correctly regardless of whether that value is the
  canonical \<^const>\<open>bot\<close>.
  Interval also exposes its hand-tuned query table; both operations agree on
  this disjointness witness. \<open>interval_eq_true\<close> is independent of either
  operation because it derives equality from \<open>interval_less_false\<close> in both
  directions.
\<close>

lemma interval_eq_false_witness_disjoint:
  "interval_eq_false (Ivl (Fin 1) (Fin 2)) (Ivl (Fin 5) (Fin 6))"
  by (simp add: less_eint_def less_eq_eint_def)

lemma interval_meet_of_witness_not_bot:
  "meet_ivl (Ivl (Fin 1) (Fin 2)) (Ivl (Fin 5) (Fin 6)) \<noteq> bot"
  by (simp add: bot_ivl_def)

lemma interval_intersect_of_witness_bot:
  "intersect_ivl (Ivl (Fin 1) (Fin 2)) (Ivl (Fin 5) (Fin 6)) = bot"
  by eval

end
