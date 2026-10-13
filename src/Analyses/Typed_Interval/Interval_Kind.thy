theory Interval_Kind
  imports "Voblint_Analysis_Interval.Interval_Warrowing" "Voblint_Domain.Kind_Lifted"
begin

section \<open>Intervals at a kind\<close>

text \<open>
  The kind-indexed operations of Goblint's \<^verbatim>\<open>IntervalFunctor\<close> without widening
  thresholds. Widening keeps a bound that did not grow and moves a growing bound to the
  kind's limit. Narrowing replaces only a bound that sits at the kind's limit.

  Goblint widens operands of the kind, whose bounds already lie in its range. The class
  laws must hold for every operand, so a growing bound moves to the kind's limit or to
  the new bound, whichever is further out; on operands in range this is the kind's
  limit.
\<close>

text \<open>Bounds are compared in the linear order of \<^typ>\<open>eint\<close>, not by unfolding it.\<close>

declare less_eq_eint_def [simp del]

definition ik_lo :: "ikind \<Rightarrow> eint" where "ik_lo k = Fin (ik_min k)"
definition ik_hi :: "ikind \<Rightarrow> eint" where "ik_hi k = Fin (ik_max k)"

fun widen_ivl_ik :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "widen_ivl_ik k (Ivl l0 u0) (Ivl l1 u1) =
     Ivl (if l0 \<le> l1 then l0 else min (ik_lo k) l1)
         (if u1 \<le> u0 then u0 else max (ik_hi k) u1)"

fun narrow_ivl_ik :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "narrow_ivl_ik k (Ivl l0 u0) (Ivl l1 u1) =
     Ivl (if l0 = ik_lo k then l1 else l0) (if u0 = ik_hi k then u1 else u0)"

text \<open>The canonical bottom stays neutral, as for the kind-free widening.\<close>

instantiation ivl :: ik_domain
begin

definition widen_ik_ivl :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "widen_ik_ivl k a b = (if a = bot then b else if b = bot then a else widen_ivl_ik k a b)"

definition narrow_ik_ivl :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "narrow_ik_ivl = narrow_ivl_ik"

definition empty_ik_ivl :: "ikind \<Rightarrow> ivl \<Rightarrow> bool" where
  "empty_ik_ivl k a = is_bottom_ivl (a \<sqinter> Ivl (ik_lo k) (ik_hi k))"

instance proof
  fix k :: ikind and a b :: ivl
  obtain l0 u0 l1 u1 where a: "a = Ivl l0 u0" and b: "b = Ivl l1 u1"
    by (meson ivl_exhaustE)
  have lo: "(if l0 \<le> l1 then l0 else min (ik_lo k) l1) \<le> l0"
       "(if l0 \<le> l1 then l0 else min (ik_lo k) l1) \<le> l1"
    using linear[of l0 l1] by (auto intro: order.trans[OF min.cobounded2])
  have hi: "u0 \<le> (if u1 \<le> u0 then u0 else max (ik_hi k) u1)"
       "u1 \<le> (if u1 \<le> u0 then u0 else max (ik_hi k) u1)"
    using linear[of u0 u1] by (auto intro: order.trans[OF _ max.cobounded2])
  have core1: "a \<le> widen_ivl_ik k a b" and core2: "b \<le> widen_ivl_ik k a b"
    using lo hi by (simp_all only: a b widen_ivl_ik.simps less_eq_ivl_def prod.case ivl.case)
  have bot_le: "bot \<le> c" for c :: ivl
    by simp
  show "a \<le> widen_ik k a b"
    using core1 bot_le by (auto simp: widen_ik_ivl_def)
  show "b \<le> widen_ik k a b"
    using core2 bot_le by (auto simp: widen_ik_ivl_def)
  show "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b"
    by (cases a; cases b) (auto simp: narrow_ik_ivl_def less_eq_ivl_def)
  show "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    by (cases a; cases b) (auto simp: narrow_ik_ivl_def less_eq_ivl_def)
  have range: "gamma_ivl (Ivl (ik_lo k) (ik_hi k)) = ik_range k"
    by (auto simp: ik_lo_def ik_hi_def less_eq_eint_def)
  show "empty_ik k a \<longleftrightarrow> numeric_domain_class.gamma a \<inter> ik_range k = {}"
    by (simp add: empty_ik_ivl_def is_bottom_ivl_correct flip: range)
qed

end

text \<open>On operands within the kind's range, a growing bound moves exactly to the kind's
  limit, as in Goblint.\<close>

lemma widen_ivl_ik_in_range:
  assumes "l1 < l0" and "ik_lo k \<le> l1" and "u0 < u1" and "u1 \<le> ik_hi k"
  shows "widen_ivl_ik k (Ivl l0 u0) (Ivl l1 u1) = Ivl (ik_lo k) (ik_hi k)"
  using assms by (auto simp: min_def max_def)

end
