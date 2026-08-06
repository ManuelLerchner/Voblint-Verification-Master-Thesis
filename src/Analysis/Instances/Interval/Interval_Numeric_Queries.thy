theory Interval_Numeric_Queries
  imports Interval_Lattice "Voblint_Core.Abstract_Checks"
begin

section \<open>Interval interpretation of the generic numeric-query interface\<close>

text \<open>
  Second-domain validation for \<open>abstract_numeric_queries\<close>
  (\<open>Voblint_Core.Abstract_Checks\<close>): a real, minimal Interval instance,
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
     (\<not> l1 \<le> u1 \<or> \<not> l2 \<le> u2 \<or> u2 < l1)"

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

  with query have separated: "u2 < l1"
    unfolding a_def b_def
    by simp

  show ?thesis
    using j_bounds(2) separated i_bounds(1)
    by (rule ivl_upper_lower_not_less)
qed

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

subsection \<open>Interpreting the generic numeric-query interface\<close>

global_interpretation interval_numeric_queries:
  abstract_numeric_queries gamma_ivl interval_less_true interval_less_false
    interval_eq_true interval_eq_false
  by unfold_locales
    (auto simp add:
       interval_less_true_sound
       interval_less_false_sound
       interval_eq_true_sound
       interval_eq_false_sound)

end
