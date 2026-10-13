theory Interval_Kind
  imports
    "Voblint_Analysis_Interval.Interval_Arithmetic"
    "Voblint_Analysis_Interval.Interval_Numeric_Queries" "Voblint_Typed_Nonrel.Typed_Nonrel"
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


section \<open>Intervals as a kind-aware integer domain\<close>

text \<open>
  An operation at kind \<open>k\<close> computes the mathematical interval and keeps it when it lies
  in \<open>k\<close>'s range. Otherwise it normalizes the interval as Goblint does: an unsigned kind
  wraps it when the wrapped interval is exact, and every other overflow answers
  \<open>top_of k\<close>.
\<close>

definition ik_ivl :: "ikind \<Rightarrow> ivl" where "ik_ivl k = Ivl (ik_lo k) (ik_hi k)"

lemma gamma_ik_ivl [simp]: "gamma_ivl (ik_ivl k) = ik_range k"
  by (auto simp: ik_ivl_def ik_lo_def ik_hi_def less_eq_eint_def)

text \<open>
  Truncation keeps the order of a block of fewer than \<open>M\<close> consecutive integers
  whenever it keeps the order of the block's ends: the block then does not cross a
  multiple of \<open>M\<close>.
\<close>

lemma mod_interval_wrap:
  fixes x y n M :: int
  assumes M: "0 < M" and xn: "x \<le> n" and ny: "n \<le> y" and w: "y - x < M"
    and ord: "x mod M \<le> y mod M"
  shows "x mod M \<le> n mod M \<and> n mod M \<le> y mod M"
proof -
  define r where "r = x mod M"
  have r0: "0 \<le> r" "r < M" using M by (simp_all add: r_def)
  have shift: "(x + d) mod M = (r + d) mod M" for d
    by (simp add: r_def mod_add_left_eq)
  have fits: "r + (y - x) < M"
  proof (rule ccontr)
    assume "\<not> r + (y - x) < M"
    then have ge: "M \<le> r + (y - x)" by simp
    have "(r + (y - x)) mod M = ((r + (y - x) - M) + M) mod M" by simp
    also have "\<dots> = (r + (y - x) - M) mod M" by (rule mod_add_self2)
    also have "\<dots> = r + (y - x) - M"
      by (rule mod_pos_pos_trivial) (use ge r0 w in auto)
    finally have "(r + (y - x)) mod M = r + (y - x) - M" .
    moreover have "y mod M = (r + (y - x)) mod M" using shift[of "y - x"] by simp
    ultimately show False using ord w r_def by simp
  qed
  have yv: "y mod M = r + (y - x)"
    using shift[of "y - x"] fits r0 xn ny by simp
  have nv: "n mod M = r + (n - x)"
    using shift[of "n - x"] fits r0 xn ny by simp
  show ?thesis using yv nv xn ny r_def by simp
qed

text \<open>
  An unsigned kind wraps a finite interval that spans less than its modulus and whose
  wrapped ends stay ordered; any other overflow gives the kind's whole range. This is
  Goblint's \<^verbatim>\<open>norm\<close> in \<^verbatim>\<open>intervalDomain.ml\<close> under its default policy
  \<^verbatim>\<open>sem.int.signed_overflow = assume_top\<close>, where a signed kind does not wrap.
  Goblint treats a cast and an arithmetic result alike there; they differ only under
  \<^verbatim>\<open>assume_none\<close>, which assumes that no signed overflow occurs.
\<close>

definition wrap_ivl_ik :: "ikind \<Rightarrow> int \<Rightarrow> int \<Rightarrow> ivl" where
  "wrap_ivl_ik k x y =
     (if y - x < ik_mod k \<and> ik_norm k x \<le> ik_norm k y
      then Ivl (Fin (ik_norm k x)) (Fin (ik_norm k y)) else ik_ivl k)"

definition norm_ivl_ik :: "ikind \<Rightarrow> ivl \<Rightarrow> ivl" where
  "norm_ivl_ik k a =
     (if a \<le> ik_ivl k then a
      else case a of
        Ivl (Fin x) (Fin y) \<Rightarrow> if ik_signed k then ik_ivl k else wrap_ivl_ik k x y
      | _ \<Rightarrow> ik_ivl k)"

lemma ik_norm_unsigned: "\<not> ik_signed k \<Longrightarrow> ik_norm k n = n mod ik_mod k"
  by (simp add: ik_norm_def ik_mod_def take_bit_eq_mod)

lemma wrap_ivl_ik_sound:
  assumes "\<not> ik_signed k" and "x \<le> n" and "n \<le> y"
  shows "ik_norm k n \<in> gamma_ivl (wrap_ivl_ik k x y)"
proof (cases "y - x < ik_mod k \<and> ik_norm k x \<le> ik_norm k y")
  case True
  have "0 < ik_mod k" by (simp add: ik_mod_def)
  with True assms have "ik_norm k x \<le> ik_norm k n \<and> ik_norm k n \<le> ik_norm k y"
    by (simp add: ik_norm_unsigned mod_interval_wrap)
  with True show ?thesis by (simp add: wrap_ivl_ik_def less_eq_eint_def)
qed (auto simp: wrap_ivl_ik_def)

lemma norm_ivl_ik_sound:
  assumes "n \<in> gamma_ivl a"
  shows "ik_norm k n \<in> gamma_ivl (norm_ivl_ik k a)"
proof (cases "a \<le> ik_ivl k")
  case True
  then have "n \<in> ik_range k" using gamma_ivl_mono[OF True] assms by auto
  with True assms show ?thesis by (simp add: norm_ivl_ik_def)
next
  case False
  obtain l u where a: "a = Ivl l u" by (cases a)
  show ?thesis
  proof (cases "\<exists>x y. l = Fin x \<and> u = Fin y \<and> \<not> ik_signed k")
    case True
    then obtain x y where l: "l = Fin x" and u: "u = Fin y" and k: "\<not> ik_signed k" by blast
    have "x \<le> n" "n \<le> y" using assms by (simp_all add: a l u less_eq_eint_def)
    with False k show ?thesis by (simp add: norm_ivl_ik_def a l u wrap_ivl_ik_sound)
  next
    case nw: False
    then have "norm_ivl_ik k a = ik_ivl k"
      using False by (cases l; cases u) (auto simp: norm_ivl_ik_def a)
    then show ?thesis by simp
  qed
qed

fun ivl_aop :: "aop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "ivl_aop AAdd a b = a + b"
| "ivl_aop ASub a b = a - b"
| "ivl_aop AMul a b = a * b"
| "ivl_aop ADiv a b = ivl_div a b"
| "ivl_aop AMod a b = ivl_mod a b"

lemma ivl_aop_sound:
  "m \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> aop_eval op m n \<in> gamma_ivl (ivl_aop op a b)"
  by (cases op) (simp_all add: ivl_plus_sound ivl_minus_sound ivl_times_sound ivl_div_sound
      ivl_mod_sound)

definition ivl_lt :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "ivl_lt a b =
     (if interval_less_true a b then Some True
      else if interval_less_false a b then Some False else None)"

definition ivl_eq :: "ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "ivl_eq a b =
     (if interval_eq_true a b then Some True
      else if interval_eq_false a b then Some False else None)"

lemma ivl_lt_sound: "ivl_lt a b = Some r \<Longrightarrow> m \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> (m < n) = r"
  by (auto simp: ivl_lt_def split: if_splits
      dest: interval_less_true_sound interval_less_false_sound)

lemma ivl_eq_sound: "ivl_eq a b = Some r \<Longrightarrow> m \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> (m = n) = r"
  by (auto simp: ivl_eq_def split: if_splits
      dest: interval_eq_true_sound interval_eq_false_sound)

fun ivl_cop :: "cop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> bool option" where
  "ivl_cop CLt a b = ivl_lt a b"
| "ivl_cop CGt a b = ivl_lt b a"
| "ivl_cop CLe a b = map_option HOL.Not (ivl_lt b a)"
| "ivl_cop CGe a b = map_option HOL.Not (ivl_lt a b)"
| "ivl_cop CEq a b = ivl_eq a b"
| "ivl_cop CNe a b = map_option HOL.Not (ivl_eq a b)"

lemma ivl_cop_sound:
  "ivl_cop c a b = Some r \<Longrightarrow> m \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b \<Longrightarrow> cop_eval c m n = r"
  by (cases c) (auto dest: ivl_lt_sound ivl_eq_sound)

fun ivl_lo :: "ivl \<Rightarrow> eint" where "ivl_lo (Ivl l u) = l"
fun ivl_hi :: "ivl \<Rightarrow> eint" where "ivl_hi (Ivl l u) = u"

lemma gamma_ivl_bounds:
  assumes "n \<in> gamma_ivl a"
  shows "ivl_lo a \<le> Fin n" and "Fin n \<le> ivl_hi a"
  using assms by (cases a; simp)+

text \<open>The bounds a comparison known to hold puts on its operands: \<open>m < n\<close> bounds \<open>m\<close>
  by \<open>n\<close>'s upper bound less one and \<open>n\<close> by \<open>m\<close>'s lower bound plus one.\<close>

definition ivl_le_bounds :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl \<times> ivl" where
  "ivl_le_bounds a b = (a \<sqinter> Ivl MinInf (ivl_hi b), b \<sqinter> Ivl (ivl_lo a) PlusInf)"

definition ivl_lt_bounds :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl \<times> ivl" where
  "ivl_lt_bounds a b =
     (a \<sqinter> Ivl MinInf (ivl_hi b - Fin 1), b \<sqinter> Ivl (ivl_lo a + Fin 1) PlusInf)"

lemma eint_le_minus_one: "Fin m < Fin n \<Longrightarrow> Fin n \<le> u \<Longrightarrow> Fin m \<le> u - Fin 1"
  by (cases u) (auto simp: less_eq_eint_def less_eint_def)

lemma eint_plus_one_le: "Fin m < Fin n \<Longrightarrow> l \<le> Fin m \<Longrightarrow> l + Fin 1 \<le> Fin n"
  by (cases l) (auto simp: less_eq_eint_def less_eint_def)

lemma ivl_le_bounds_sound:
  assumes "m \<le> n" "m \<in> gamma_ivl a" "n \<in> gamma_ivl b"
  shows "m \<in> gamma_ivl (fst (ivl_le_bounds a b)) \<and> n \<in> gamma_ivl (snd (ivl_le_bounds a b))"
proof -
  have mn: "eint_le (Fin m) (Fin n)" using assms(1) by simp
  have "Fin m \<le> ivl_hi b" "ivl_lo a \<le> Fin n"
    using eint_le_trans[OF mn gamma_ivl_bounds(2)[OF assms(3), unfolded less_eq_eint_def]]
      eint_le_trans[OF gamma_ivl_bounds(1)[OF assms(2), unfolded less_eq_eint_def] mn]
    by (simp_all add: less_eq_eint_def)
  then show ?thesis using assms
    by (auto simp: ivl_le_bounds_def less_eq_eint_def intro!: meet_ivl_gamma)
qed

lemma ivl_lt_bounds_sound:
  assumes "m < n" "m \<in> gamma_ivl a" "n \<in> gamma_ivl b"
  shows "m \<in> gamma_ivl (fst (ivl_lt_bounds a b)) \<and> n \<in> gamma_ivl (snd (ivl_lt_bounds a b))"
proof -
  have lt: "Fin m < Fin n" using assms(1) by (simp add: less_eint_def)
  have "Fin m \<le> ivl_hi b - Fin 1" "ivl_lo a + Fin 1 \<le> Fin n"
    using eint_le_minus_one[OF lt gamma_ivl_bounds(2)[OF assms(3)]]
      eint_plus_one_le[OF lt gamma_ivl_bounds(1)[OF assms(2)]] by blast+
  then show ?thesis using assms
    by (auto simp: ivl_lt_bounds_def less_eq_eint_def intro!: meet_ivl_gamma)
qed

fun ivl_refine :: "cop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl \<times> ivl" where
  "ivl_refine CLt a b = ivl_lt_bounds a b"
| "ivl_refine CLe a b = ivl_le_bounds a b"
| "ivl_refine CGt a b = prod.swap (ivl_lt_bounds b a)"
| "ivl_refine CGe a b = prod.swap (ivl_le_bounds b a)"
| "ivl_refine CEq a b = (a \<sqinter> b, a \<sqinter> b)"
| "ivl_refine CNe a b = (a, b)"

lemma ivl_refine_sound:
  "cop_eval c m n \<Longrightarrow> m \<in> gamma_ivl a \<Longrightarrow> n \<in> gamma_ivl b
     \<Longrightarrow> m \<in> gamma_ivl (fst (ivl_refine c a b)) \<and> n \<in> gamma_ivl (snd (ivl_refine c a b))"
  by (cases c)
     (auto dest: ivl_le_bounds_sound ivl_lt_bounds_sound intro: meet_ivl_gamma)

instantiation ivl :: kind_int_domain
begin

definition top_ik_ivl :: "ikind \<Rightarrow> ivl" where "top_ik_ivl = ik_ivl"

definition of_int_ik_ivl :: "ikind \<Rightarrow> int \<Rightarrow> ivl" where
  "of_int_ik_ivl k n = Ivl (Fin (ik_norm k n)) (Fin (ik_norm k n))"

definition cast_ik_ivl :: "ikind option \<Rightarrow> ikind \<Rightarrow> ivl \<Rightarrow> ivl" where
  "cast_ik_ivl sk = norm_ivl_ik"

definition arith_ik_ivl :: "ikind \<Rightarrow> aop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where
  "arith_ik_ivl k op a b = norm_ivl_ik k (ivl_aop op a b)"

definition cmp_ik_ivl :: "cop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> bool option" where "cmp_ik_ivl = ivl_cop"

definition meet_ik_ivl :: "ivl \<Rightarrow> ivl \<Rightarrow> ivl" where "meet_ik_ivl a b = a \<sqinter> b"

definition refine_ik_ivl :: "cop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl \<times> ivl" where "refine_ik_ivl = ivl_refine"

definition raw_aop_ik_ivl :: "aop \<Rightarrow> ivl \<Rightarrow> ivl \<Rightarrow> ivl" where "raw_aop_ik_ivl = ivl_aop"

definition fits_ik_ivl :: "ikind \<Rightarrow> ivl \<Rightarrow> bool" where "fits_ik_ivl k a \<longleftrightarrow> a \<le> ik_ivl k"

definition answer_ik_ivl :: "ivl \<Rightarrow> answer" where "answer_ik_ivl = answer_of_ivl"

definition of_answer_ik_ivl :: "ikind option \<Rightarrow> answer \<Rightarrow> ivl" where
  "of_answer_ik_ivl sk q =
     (let r = (case sk of Some k \<Rightarrow> ik_ivl k | None \<Rightarrow> \<top>)
      in case q of QBot \<Rightarrow> \<bottom> | QTop \<Rightarrow> r | QLifted d \<Rightarrow> int_ivl d \<sqinter> r)"

instance proof
  fix n m :: int and k :: ikind and a b :: ivl and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: ivl)"
    by (simp add: top_ik_ivl_def)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: ivl)"
    by (simp add: of_int_ik_ivl_def less_eq_eint_def)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik sk k a)" for sk
    by (simp add: cast_ik_ivl_def norm_ivl_ik_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik k op a b)"
    by (simp add: arith_ik_ivl_def norm_ivl_ik_sound ivl_aop_sound)
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    by (simp add: cmp_ik_ivl_def ivl_cop_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    by (simp add: meet_ik_ivl_def meet_ivl_gamma)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    by (simp add: refine_ik_ivl_def ivl_refine_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    by (simp add: raw_aop_ik_ivl_def ivl_aop_sound)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    using gamma_ivl_mono[of a "ik_ivl k"] by (auto simp: fits_ik_ivl_def simp del: ik_range_iff)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    by (simp add: answer_ik_ivl_def)
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: ivl)" for sk q
    by (cases sk; cases q)
       (auto simp: of_answer_ik_ivl_def gamma_int_dom_def meet_ivl_gamma top_ivl_def gamma_ivl_top
         simp del: ik_range_iff)
qed

end

text \<open>\<^class>\<open>kind_int_domain\<close> extends \<^class>\<open>numeric_domain\<close>, so the code of a
  typed analysis carries the concretization in its class dictionary. It is never
  called, and its equation is not executable at \<^typ>\<open>int\<close>.\<close>

declare [[code abort: gamma_ivl]] 

end
