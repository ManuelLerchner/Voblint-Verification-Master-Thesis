theory Int_Tuple_Kind
  imports
    "Voblint_Analysis_Interval.Interval_Kind" "Voblint_Analysis_Congruence.Congruence_Kind"
    "Voblint_Analysis_Int.Int_Refinement_Control"
begin

section \<open>The reduced product of Interval and Congruence\<close>

text \<open>
  Goblint's \<^verbatim>\<open>IntDomTuple\<close> (\<^verbatim>\<open>int/intDomTuple.ml\<close>) restricted to its Interval and
  Congruence components. A value denotes the integers both components admit. Its type
  parameter selects how the components refine each other, as Goblint's
  \<^verbatim>\<open>ana.int.refinement\<close> does; the untyped Int analysis takes the same modes.
\<close>

class int_refinement =
  fixes int_mode :: "'a itself \<Rightarrow> refine_mode"

datatype int_never = Int_Never
datatype int_once = Int_Once
datatype int_fixpoint = Int_Fixpoint

instantiation int_never :: int_refinement
begin
definition "int_mode (_ :: int_never itself) = Refine_Never"
instance ..
end

instantiation int_once :: int_refinement
begin
definition "int_mode (_ :: int_once itself) = Refine_Once"
instance ..
end

instantiation int_fixpoint :: int_refinement
begin
definition "int_mode (_ :: int_fixpoint itself) = Refine_Fixpoint"
instance ..
end

datatype 'm int_tuple = IT (it_ivl: ivl) (it_cong: congruence)

definition gamma_it :: "'a int_tuple \<Rightarrow> int set" where
  "gamma_it a = gamma_ivl (it_ivl a) \<inter> gamma_congruence (it_cong a)"

lemma gamma_it_IT [simp]: "gamma_it (IT i c) = gamma_ivl i \<inter> gamma_congruence c"
  by (simp add: gamma_it_def)

subsection \<open>Lattice\<close>

text \<open>The order, join, bottom and top are taken componentwise.\<close>

instantiation int_tuple :: (type) "{order_top, bounded_semilattice_sup_bot}"
begin

definition less_eq_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> bool" where
  "a \<le> b \<longleftrightarrow> it_ivl a \<le> it_ivl b \<and> it_cong a \<le> it_cong b"

definition less_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> bool" where
  "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> (a :: 'a int_tuple)"

definition sup_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "a \<squnion> b = IT (it_ivl a \<squnion> it_ivl b) (it_cong a \<squnion> it_cong b)"

definition bot_int_tuple :: "'a int_tuple" where "bot = IT bot bot"

definition top_int_tuple :: "'a int_tuple" where "top = IT top top"

instance proof
  fix a b c :: "'a int_tuple"
  show "a < b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a" by (rule less_int_tuple_def)
  show "a \<le> a" by (simp add: less_eq_int_tuple_def)
  show "a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
    by (auto simp: less_eq_int_tuple_def intro: order.trans)
  show "a \<le> b \<Longrightarrow> b \<le> a \<Longrightarrow> a = b"
    by (cases a; cases b) (auto simp: less_eq_int_tuple_def)
  show "a \<le> a \<squnion> b" "b \<le> a \<squnion> b" by (simp_all add: less_eq_int_tuple_def sup_int_tuple_def)
  show "b \<le> a \<Longrightarrow> c \<le> a \<Longrightarrow> b \<squnion> c \<le> a"
    by (simp add: less_eq_int_tuple_def sup_int_tuple_def)
  show "bot \<le> a" by (simp add: less_eq_int_tuple_def bot_int_tuple_def)
  show "a \<le> top" by (simp add: less_eq_int_tuple_def top_int_tuple_def)
qed

end

lemma IT_le_IT [simp]: "IT i c \<le> IT j d \<longleftrightarrow> i \<le> j \<and> c \<le> d"
  by (simp add: less_eq_int_tuple_def)

subsection \<open>Exact emptiness\<close>

text \<open>A class meets an interval when its least value above the lower bound, or its
  greatest value below the upper bound, lies inside. The test is exact, so emptiness of
  the product is decided exactly.\<close>

lemma cong_greatest_below:
  fixes m c hi :: int
  assumes m: "0 < m"
  defines "r \<equiv> hi - (hi - c) mod m"
  shows "r \<le> hi" and "m dvd r - c"
    and "m dvd n - c \<Longrightarrow> n \<le> hi \<Longrightarrow> n \<le> r"
proof -
  show "r \<le> hi" using m by (simp add: r_def)
  have "r - c = (hi - c) - (hi - c) mod m" by (simp add: r_def)
  then show "m dvd r - c" by (simp only: dvd_minus_mod)
  assume d: "m dvd n - c" and hi: "n \<le> hi"
  have "(hi - n) mod m = (hi - c) mod m"
  proof -
    have "m dvd (hi - n) - (hi - c)" using d dvd_minus_iff[of m "n - c"] by simp
    then show ?thesis by (simp add: mod_eq_dvd_iff)
  qed
  moreover have "(hi - n) mod m \<le> hi - n"
    using hi m by (simp add: zmod_le_nonneg_dividend)
  ultimately show "n \<le> r" by (simp add: r_def)
qed

fun cong_meets :: "int \<times> int \<Rightarrow> eint \<Rightarrow> eint \<Rightarrow> bool" where
  "cong_meets (c, m) l u =
     (if m = 0 then l \<le> Fin c \<and> Fin c \<le> u
      else case (l, u) of
        (Fin x, Fin y) \<Rightarrow> x + (c - x) mod m \<le> y
      | (Fin x, PlusInf) \<Rightarrow> True
      | (MinInf, Fin y) \<Rightarrow> True
      | (MinInf, PlusInf) \<Rightarrow> True
      | _ \<Rightarrow> False)"

lemma cong_meets_correct:
  assumes "0 \<le> m"
  shows "cong_meets (c, m) l u \<longleftrightarrow> (\<exists>n. m dvd n - c \<and> l \<le> Fin n \<and> Fin n \<le> u)"
proof (cases "m = 0")
  case True
  then show ?thesis by auto
next
  case False
  with assms have m: "0 < m" by simp
  show ?thesis
  proof (cases l; cases u)
    fix x y assume l: "l = Fin x" and u: "u = Fin y"
    note least = cong_least_above[OF m, where lo = x and c = c]
    show ?thesis
      using least False by (auto simp: l u) force
  next
    fix x assume "l = Fin x" "u = PlusInf"
    then show ?thesis
      using cong_least_above[OF m, where lo = x and c = c] False
      by auto
  next
    fix y assume "l = MinInf" "u = Fin y"
    then show ?thesis
      using cong_greatest_below[OF m, where hi = y and c = c] False
      by auto
  next
    assume "l = MinInf" "u = PlusInf"
    then show ?thesis using False by (auto intro: exI[of _ c])
  qed (auto simp: False)
qed

definition it_empty :: "ivl \<Rightarrow> congruence \<Rightarrow> bool" where
  "it_empty i c =
     (case Rep_congruence c of
        None \<Rightarrow> True
      | Some cm \<Rightarrow> \<not> cong_meets cm (ivl_lower i) (ivl_upper i))"

lemma it_empty_correct: "it_empty i c \<longleftrightarrow> gamma_ivl i \<inter> gamma_congruence c = {}"
proof (cases c rule: congruence_rep_cases)
  case Bot
  then show ?thesis by (simp add: it_empty_def gamma_congruence_def)
next
  case (Class r m)
  have "0 \<le> m" using normalized_Rep_congruence[of c] Class by (cases "m = 0") auto
  then show ?thesis
    using cong_meets_correct[of m r "ivl_lower i" "ivl_upper i"] Class
    by (cases i) (auto simp: it_empty_def gamma_congruence_Some)
qed

subsection \<open>Mutual refinement\<close>

text \<open>
  Goblint's \<^verbatim>\<open>Congruence.refine_with_interval\<close>: a class meeting a finite interval
  in one value becomes that value, and one meeting it in none becomes bottom. The
  interval is then rounded to the class (\<^const>\<open>refine_ivl_with_congruence\<close>, Goblint's
  \<^verbatim>\<open>Interval.refine_with_congruence\<close>). This is one round of
  \<^verbatim>\<open>IntDomTuple.refine\<close> in that order.
\<close>

definition cong_refine_with_ivl :: "ivl \<Rightarrow> congruence \<Rightarrow> congruence" where
  "cong_refine_with_ivl i c =
     (case (i, Rep_congruence c) of
        (Ivl (Fin x) (Fin y), Some (r, m)) \<Rightarrow>
          if m = 0 then (if x \<le> r \<and> r \<le> y then c else bot)
          else (let lo = x + (r - x) mod m; hi = y - (y - r) mod m
                in if hi < lo then bot else if lo = hi then congruence_of_int lo else c)
      | _ \<Rightarrow> c)"

lemma cong_refine_with_ivl_sound:
  assumes n: "n \<in> gamma_ivl i" "n \<in> gamma_congruence c"
  shows "n \<in> gamma_congruence (cong_refine_with_ivl i c)"
proof (cases "\<exists>x y r m. i = Ivl (Fin x) (Fin y) \<and> Rep_congruence c = Some (r, m)")
  case True
  then obtain x y r m where i: "i = Ivl (Fin x) (Fin y)" and c: "Rep_congruence c = Some (r, m)"
    by blast
  have xy: "x \<le> n" "n \<le> y" using n(1) by (simp_all add: i)
  have d: "m dvd n - r" using n(2) c by (simp add: gamma_congruence_Some)
  show ?thesis
  proof (cases "m = 0")
    case True
    with d xy n(2) show ?thesis by (simp add: cong_refine_with_ivl_def i c)
  next
    case False
    then have m: "0 < m" using normalized_Rep_congruence[of c] c by auto
    have "x + (r - x) mod m \<le> n"
      using cong_least_above(3)[OF m d xy(1)] .
    moreover have "n \<le> y - (y - r) mod m"
      using cong_greatest_below(3)[OF m d xy(2)] .
    ultimately show ?thesis
      using False n(2) by (auto simp: cong_refine_with_ivl_def i c Let_def)
  qed
qed (use n in \<open>auto simp: cong_refine_with_ivl_def split: ivl.splits eint.splits option.splits\<close>)

definition it_refine :: "'m int_tuple \<Rightarrow> 'm int_tuple" where
  "it_refine a =
     (let c = cong_refine_with_ivl (it_ivl a) (it_cong a)
      in IT (refine_ivl_with_congruence c (it_ivl a)) c)"

lemma it_refine_sound: "n \<in> gamma_it a \<Longrightarrow> n \<in> gamma_it (it_refine a)"
  using cong_refine_with_ivl_sound refine_ivl_with_congruence_cover
  by (cases a) (fastforce simp: it_refine_def Let_def)

text \<open>\<open>Refine_Never\<close> leaves the components apart, \<open>Refine_Once\<close> exchanges once, and
  \<open>Refine_Fixpoint\<close> exchanges until nothing changes. Like the untyped
  \<^const>\<open>refine_fix\<close>, the fixpoint keeps its input when the loop does not stop.\<close>

definition it_refine_mode :: "refine_mode \<Rightarrow> 'm int_tuple \<Rightarrow> 'm int_tuple" where
  "it_refine_mode md a =
     (case md of
        Refine_Never \<Rightarrow> a
      | Refine_Once \<Rightarrow> it_refine a
      | Refine_Fixpoint \<Rightarrow>
          (case while_option (\<lambda>x. it_refine x \<noteq> x) it_refine a of Some r \<Rightarrow> r | None \<Rightarrow> a))"

lemma it_refine_mode_sound: "n \<in> gamma_it a \<Longrightarrow> n \<in> gamma_it (it_refine_mode md a)"
proof (cases md)
  case Refine_Fixpoint
  assume n: "n \<in> gamma_it a"
  have "n \<in> gamma_it r" if "while_option (\<lambda>x. it_refine x \<noteq> x) it_refine a = Some r" for r
    using while_option_rule[where P = "\<lambda>x. n \<in> gamma_it x", OF _ that] n it_refine_sound by blast
  with n Refine_Fixpoint show ?thesis by (auto simp: it_refine_mode_def split: option.splits)
qed (simp_all add: it_refine_mode_def it_refine_sound)

subsection \<open>Domain instances\<close>

text \<open>Widening and narrowing also act componentwise; a value is empty when its congruence
  class has no member between its interval's bounds.\<close>

instantiation int_tuple :: (type) numeric_domain
begin

definition widen_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "widen_int_tuple a b = IT (it_ivl a \<nabla> it_ivl b) (it_cong a \<nabla> it_cong b)"

definition narrow_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "narrow_int_tuple a b = IT (it_ivl a \<Delta> it_ivl b) (it_cong a \<Delta> it_cong b)"

definition is_empty_int_tuple :: "'a int_tuple \<Rightarrow> bool" where
  "is_empty_int_tuple a = it_empty (it_ivl a) (it_cong a)"

text \<open>A value prints as the untyped Int product does: bottom, a single integer when a
  component pins one, and otherwise each component.\<close>

definition to_string_int_tuple :: "'a int_tuple \<Rightarrow> String.literal" where
  "to_string_int_tuple a =
     (if it_empty (it_ivl a) (it_cong a) then sym_bottom
      else case ivl_constant (it_ivl a) of
        Some n \<Rightarrow> string_of_int n
      | None \<Rightarrow> (case congruence_constant (it_cong a) of
          Some n \<Rightarrow> string_of_int n
        | None \<Rightarrow> STR ''intervals:'' + to_string (it_ivl a) + STR ''; congruences:''
                    + to_string (it_cong a)))"

definition gamma_int_tuple :: "'a int_tuple \<Rightarrow> int set" where
  "gamma_int_tuple = gamma_it"

instance proof
  fix a b :: "'a int_tuple"
  show "a \<le> a \<nabla> b" "b \<le> a \<nabla> b"
    by (simp_all add: widen_int_tuple_def less_eq_int_tuple_def widen_ge1 widen_ge2)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b" "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a"
    by (simp_all add: narrow_int_tuple_def less_eq_int_tuple_def narrow_ge narrow_le)
  show "numeric_domain_class.gamma (bot :: 'a int_tuple) = {}"
    by (simp add: gamma_int_tuple_def bot_int_tuple_def bot_congruence_def)
  show "numeric_domain_class.gamma (top :: 'a int_tuple) = UNIV"
    using gamma_top[where 'a = ivl]
    by (simp add: gamma_int_tuple_def top_int_tuple_def)
  show "a \<le> b \<Longrightarrow> numeric_domain_class.gamma a \<subseteq> numeric_domain_class.gamma b"
    using gamma_ivl_mono[of "it_ivl a" "it_ivl b"]
      gamma_mono[of "it_cong a" "it_cong b"]
    by (auto simp: gamma_int_tuple_def gamma_it_def less_eq_int_tuple_def)
  show "is_empty a \<longleftrightarrow> numeric_domain_class.gamma a = {}"
    by (simp add: is_empty_int_tuple_def gamma_int_tuple_def gamma_it_def it_empty_correct)
qed

end

lemma gamma_int_tuple_IT [simp]:
  "numeric_domain_class.gamma (IT i c) = gamma_ivl i \<inter> gamma_congruence c"
  by (simp add: gamma_int_tuple_def)

lemma it_refine_IT_sound:
  "n \<in> gamma_ivl i \<Longrightarrow> n \<in> gamma_congruence c
     \<Longrightarrow> n \<in> numeric_domain_class.gamma (it_refine_mode md (IT i c))"
  using it_refine_mode_sound[of n "IT i c"] by (simp add: gamma_int_tuple_def)

instantiation int_tuple :: (type) ik_domain
begin

definition widen_ik_int_tuple :: "ikind \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "widen_ik_int_tuple k a b =
     IT (widen_ik k (it_ivl a) (it_ivl b)) (widen_ik k (it_cong a) (it_cong b))"

definition narrow_ik_int_tuple :: "ikind \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "narrow_ik_int_tuple k a b =
     IT (narrow_ik k (it_ivl a) (it_ivl b)) (narrow_ik k (it_cong a) (it_cong b))"

definition empty_ik_int_tuple :: "ikind \<Rightarrow> 'a int_tuple \<Rightarrow> bool" where
  "empty_ik_int_tuple k a = it_empty (it_ivl a \<sqinter> ik_ivl k) (it_cong a)"

instance proof
  fix k :: ikind and a b :: "'a int_tuple"
  show "a \<le> widen_ik k a b" "b \<le> widen_ik k a b"
    by (simp_all add: widen_ik_int_tuple_def less_eq_int_tuple_def widen_ik_ge1 widen_ik_ge2)
  show "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b" "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    by (simp_all add: narrow_ik_int_tuple_def less_eq_int_tuple_def narrow_ik_ge narrow_ik_le)
  show "empty_ik k a \<longleftrightarrow> numeric_domain_class.gamma a \<inter> ik_range k = {}"
    by (cases a) (auto simp: empty_ik_int_tuple_def it_empty_correct)
qed

end

text \<open>
  Arithmetic follows \<^verbatim>\<open>IntDomTuple.map2ovc\<close>: the interval computes first, and when
  its mathematical result fits the kind, no value overflows (\<^verbatim>\<open>no_ov\<close>), so the
  congruence keeps its exact class. A conversion keeps the class on the same condition.
  Comparisons take the first component that decides, as \<^verbatim>\<open>map2bool\<close> takes the
  components' common answer. Every result is refined as the mode says.
\<close>

instantiation int_tuple :: (int_refinement) kind_int_domain
begin

definition top_ik_int_tuple :: "ikind \<Rightarrow> 'a int_tuple" where
  "top_ik_int_tuple k = IT (top_ik k) (top_ik k)"

definition of_int_ik_int_tuple :: "ikind \<Rightarrow> int \<Rightarrow> 'a int_tuple" where
  "of_int_ik_int_tuple k n = IT (of_int_ik k n) (of_int_ik k n)"

definition cast_ik_int_tuple ::
    "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "cast_ik_int_tuple ovp sk k a =
     it_refine_mode (int_mode TYPE('a)) (IT (cast_ik ovp sk k (it_ivl a))
                   (if fits_ik k (it_ivl a) then it_cong a else cast_ik ovp sk k (it_cong a)))"

text \<open>The interval decides Goblint's \<^verbatim>\<open>no_ov\<close>: when the mathematical result fits, the
  congruence keeps its unnormalized class.\<close>

definition arith_ik_int_tuple ::
    "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "arith_ik_int_tuple ovp k op fits a b =
     (let r = raw_aop_ik op (it_ivl a) (it_ivl b)
      in it_refine_mode (int_mode TYPE('a)) (IT (cast_ik ovp None k r)
                       (if fits_ik k r then raw_aop_ik op (it_cong a) (it_cong b)
                        else arith_ik ovp k op fits (it_cong a) (it_cong b))))"

definition cmp_ik_int_tuple :: "cop \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> bool option" where
  "cmp_ik_int_tuple c a b =
     (case cmp_ik c (it_ivl a) (it_ivl b) of
        Some r \<Rightarrow> Some r
      | None \<Rightarrow> cmp_ik c (it_cong a) (it_cong b))"

definition meet_ik_int_tuple :: "'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "meet_ik_int_tuple a b =
     it_refine_mode (int_mode TYPE('a)) (IT (meet_ik (it_ivl a) (it_ivl b)) (meet_ik (it_cong a) (it_cong b)))"

definition refine_ik_int_tuple :: "cop \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<times> 'a int_tuple"
  where
  "refine_ik_int_tuple c a b =
     (let (i1, i2) = refine_ik c (it_ivl a) (it_ivl b);
          (c1, c2) = refine_ik c (it_cong a) (it_cong b)
      in (it_refine_mode (int_mode TYPE('a)) (IT i1 c1), it_refine_mode (int_mode TYPE('a)) (IT i2 c2)))"

definition raw_aop_ik_int_tuple :: "aop \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple \<Rightarrow> 'a int_tuple" where
  "raw_aop_ik_int_tuple op a b =
     IT (raw_aop_ik op (it_ivl a) (it_ivl b)) (raw_aop_ik op (it_cong a) (it_cong b))"

definition fits_ik_int_tuple :: "ikind \<Rightarrow> 'a int_tuple \<Rightarrow> bool" where
  "fits_ik_int_tuple k a \<longleftrightarrow> fits_ik k (it_ivl a) \<or> fits_ik k (it_cong a)"

definition answer_ik_int_tuple :: "'a int_tuple \<Rightarrow> answer" where
  "answer_ik_int_tuple a = answer_ik (it_ivl a) \<sqinter> answer_ik (it_cong a)"

definition of_answer_ik_int_tuple :: "ikind option \<Rightarrow> answer \<Rightarrow> 'a int_tuple" where
  "of_answer_ik_int_tuple sk q = IT (of_answer_ik sk q) (of_answer_ik sk q)"

instance proof
  fix n m :: int and k :: ikind and a b :: "'a int_tuple" and op :: aop and c :: cop and r :: bool
  show "n \<in> ik_range k \<Longrightarrow> n \<in> numeric_domain_class.gamma (top_ik k :: 'a int_tuple)"
    using top_ik_sound[of n k, where 'a = ivl] top_ik_sound[of n k, where 'a = congruence]
    by (simp add: top_ik_int_tuple_def)
  show "ik_norm k n \<in> numeric_domain_class.gamma (of_int_ik k n :: 'a int_tuple)"
    using of_int_ik_sound[of k n, where 'a = ivl] of_int_ik_sound[of k n, where 'a = congruence]
    by (simp add: of_int_ik_int_tuple_def)
  show "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> numeric_domain_class.gamma a
      \<Longrightarrow> ik_norm k n \<in> numeric_domain_class.gamma (cast_ik ovp sk k a)" for ovp sk
  proof -
    assume src: "\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k'" and n: "n \<in> numeric_domain_class.gamma a"
    obtain i cg where a: "a = IT i cg" by (cases a)
    have ni: "n \<in> gamma_ivl i" and nc: "n \<in> gamma_congruence cg" using n by (simp_all add: a)
    have "ik_norm k n \<in> gamma_ivl (cast_ik ovp sk k i)"
      using cast_ik_sound[where a = i and k = k and ovp = ovp, OF src] ni by simp
    moreover have "ik_norm k n \<in> gamma_congruence
        (if fits_ik k i then cg else cast_ik ovp sk k cg)"
      using fits_ik_sound[of k i n] cast_ik_sound[where a = cg and k = k and ovp = ovp, OF src] ni
        nc
      by (auto simp del: ik_range_iff)
    ultimately show ?thesis
      unfolding cast_ik_int_tuple_def a int_tuple.sel by (rule it_refine_IT_sound)
  qed
  show "(fits \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> numeric_domain_class.gamma (arith_ik ovp k op fits a b)" for ovp fits
  proof -
    assume fit: "fits \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k"
      and ma: "m \<in> numeric_domain_class.gamma a" and nb: "n \<in> numeric_domain_class.gamma b"
    obtain i1 c1 i2 c2 where a: "a = IT i1 c1" and b: "b = IT i2 c2" by (cases a; cases b)
    let ?r = "raw_aop_ik op i1 i2"
    have rv: "aop_eval op m n \<in> gamma_ivl ?r"
      using raw_aop_ik_sound[of m i1 n i2] ma nb by (simp add: a b)
    have "ik_norm k (aop_eval op m n) \<in> gamma_ivl (cast_ik ovp None k ?r)"
      using cast_ik_None_sound[where a = ?r and k = k and ovp = ovp] rv by simp
    moreover have "ik_norm k (aop_eval op m n) \<in> gamma_congruence
        (if fits_ik k ?r then raw_aop_ik op c1 c2 else arith_ik ovp k op fits c1 c2)"
      using fits_ik_sound[of k ?r] rv raw_aop_ik_sound[of m c1 n c2]
        arith_ik_sound[where k = k and op = op and operands_fit = fits and ovp = ovp and a = c1 and
          b = c2,
          OF fit] ma nb
      by (auto simp: a b simp del: ik_range_iff)
    ultimately show ?thesis
      unfolding arith_ik_int_tuple_def a b int_tuple.sel Let_def by (rule it_refine_IT_sound)
  qed
  show "cmp_ik c a b = Some r \<Longrightarrow> m \<in> numeric_domain_class.gamma a
      \<Longrightarrow> n \<in> numeric_domain_class.gamma b \<Longrightarrow> cop_eval c m n = r"
    by (cases a; cases b)
       (auto simp: cmp_ik_int_tuple_def split: option.splits dest: cmp_ik_sound)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> m \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (meet_ik a b)"
    using meet_ik_sound[of m "it_ivl a" "it_ivl b"] meet_ik_sound[of m "it_cong a" "it_cong b"]
    by (cases a; cases b) (simp add: meet_ik_int_tuple_def it_refine_IT_sound)
  show "cop_eval c m n \<Longrightarrow> m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> m \<in> numeric_domain_class.gamma (fst (refine_ik c a b))
        \<and> n \<in> numeric_domain_class.gamma (snd (refine_ik c a b))"
    using refine_ik_sound[of c m n "it_ivl a" "it_ivl b"]
      refine_ik_sound[of c m n "it_cong a" "it_cong b"]
    by (cases a; cases b)
       (auto simp: refine_ik_int_tuple_def it_refine_IT_sound split: prod.splits)
  show "m \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> numeric_domain_class.gamma b
      \<Longrightarrow> aop_eval op m n \<in> numeric_domain_class.gamma (raw_aop_ik op a b)"
    using raw_aop_ik_sound[of m "it_ivl a" n "it_ivl b" op]
      raw_aop_ik_sound[of m "it_cong a" n "it_cong b" op]
    by (cases a; cases b) (simp add: raw_aop_ik_int_tuple_def)
  show "fits_ik k a \<Longrightarrow> n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> ik_range k"
    using fits_ik_sound[of k "it_ivl a" n] fits_ik_sound[of k "it_cong a" n]
    by (cases a) (auto simp: fits_ik_int_tuple_def simp del: ik_range_iff)
  show "n \<in> numeric_domain_class.gamma a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    using answer_ik_sound[of n "it_ivl a"] answer_ik_sound[of n "it_cong a"]
    by (cases a) (simp add: answer_ik_int_tuple_def gamma_query_lift_inf[OF gamma_inf_int_dom])
  show "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
      \<Longrightarrow> n \<in> numeric_domain_class.gamma (of_answer_ik sk q :: 'a int_tuple)" for sk q
    using of_answer_ik_sound[of sk n q, where 'a = ivl]
      of_answer_ik_sound[of sk n q, where 'a = congruence]
    by (simp add: of_answer_ik_int_tuple_def)
qed

end

end
