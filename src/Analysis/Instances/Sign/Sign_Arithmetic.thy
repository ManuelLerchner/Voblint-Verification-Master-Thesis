theory Sign_Arithmetic
  imports Sign_Lattice "Voblint_VIMP.VIMP_Expr" "Voblint_VIMP.VIMP_Elaborated"
    Voblint_Core.Abstract_Arithmetic
begin

section \<open>Sign arithmetic\<close>

instantiation sign :: plus begin
fun plus_sign :: "sign => sign => sign" where
    "plus_sign SBot    _       = SBot"
  | "plus_sign _       SBot    = SBot"
  | "plus_sign SNeg    SNeg    = SNeg"
  | "plus_sign SNeg    SNonPos = SNeg"
  | "plus_sign SNonPos SNeg    = SNeg"
  | "plus_sign SNonPos SNonPos = SNonPos"
  | "plus_sign SPos    SPos    = SPos"
  | "plus_sign SPos    SNonNeg = SPos"
  | "plus_sign SNonNeg SPos    = SPos"
  | "plus_sign SNonNeg SNonNeg = SNonNeg"
  | "plus_sign SZero   b       = b"
  | "plus_sign a       SZero   = a"
  | "plus_sign _       _       = STop"
instance ..
end

instantiation sign :: minus begin
fun minus_sign :: "sign => sign => sign" where
    "minus_sign SBot    _       = SBot"
  | "minus_sign _       SBot    = SBot"
  | "minus_sign SNeg    SPos    = SNeg"
  | "minus_sign SNeg    SNonNeg = SNeg"
  | "minus_sign SPos    SNeg    = SPos"
  | "minus_sign SPos    SNonPos = SPos"
  | "minus_sign SNeg    SZero   = SNeg"
  | "minus_sign SPos    SZero   = SPos"
  | "minus_sign SZero   SZero   = SZero"
  | "minus_sign SZero   SNeg    = SPos"
  | "minus_sign SZero   SPos    = SNeg"
  | "minus_sign SZero   SNonNeg = SNonPos"
  | "minus_sign SZero   SNonPos = SNonNeg"
  | "minus_sign SNonNeg SZero   = SNonNeg"
  | "minus_sign SNonNeg SNeg    = SPos"
  | "minus_sign SNonNeg SNonPos = SNonNeg"
  | "minus_sign SNonPos SZero   = SNonPos"
  | "minus_sign SNonPos SPos    = SNeg"
  | "minus_sign SNonPos SNonNeg = SNonPos"
  | "minus_sign _       _       = STop"
instance ..
end

instantiation sign :: times begin
fun times_sign :: "sign => sign => sign" where
    "times_sign SBot    _       = SBot"
  | "times_sign _       SBot    = SBot"
  | "times_sign SZero   _       = SZero"
  | "times_sign _       SZero   = SZero"
  | "times_sign SNeg    SNeg    = SPos"
  | "times_sign SPos    SPos    = SPos"
  | "times_sign SNeg    SPos    = SNeg"
  | "times_sign SPos    SNeg    = SNeg"
  | "times_sign SNeg    SNonPos = SNonNeg"
  | "times_sign SNonPos SNeg    = SNonNeg"
  | "times_sign SNeg    SNonNeg = SNonPos"
  | "times_sign SNonNeg SNeg    = SNonPos"
  | "times_sign SPos    SNonNeg = SNonNeg"
  | "times_sign SNonNeg SPos    = SNonNeg"
  | "times_sign SPos    SNonPos = SNonPos"
  | "times_sign SNonPos SPos    = SNonPos"
  | "times_sign SNonNeg SNonNeg = SNonNeg"
  | "times_sign SNonNeg SNonPos = SNonPos"
  | "times_sign SNonPos SNonNeg = SNonPos"
  | "times_sign SNonPos SNonPos = SNonNeg"
  | "times_sign _       _       = STop"
instance ..
end

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

lemma sign_of_int_gamma: "n : gamma_sign (sign_of_int n)"
  by (auto split: if_splits)

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  \<open>sign_lt\<close>/\<open>sign_eqb\<close>/\<open>sign_tobool\<close> are Sign's three-valued \<open>bool option\<close>
  queries for \<open>Voblint_Core.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale: \<open>Some True\<close>/\<open>Some False\<close> when the two operands' sign bounds alone
  decide it, \<open>None\<close> otherwise. Every guard here is a \<open>sign_le\<close> test against a
  fixed threshold, so downward-closedness under \<open>\<le>\<close> (needed for
  \<open>aval_dom_mono\<close>) follows from \<open>sign_le\<close>'s own transitivity, not from any
  extra reasoning about \<open>SBot\<close>.
\<close>

fun sign_lt :: "sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "sign_lt a b =
     (if sign_le a SNeg \<and> sign_le b SNonNeg then Some True
      else if sign_le a SNonPos \<and> sign_le b SPos then Some True
      else if sign_le b SNonPos \<and> sign_le a SNonNeg then Some False
      else if sign_le b SNeg \<and> sign_le a SPos then Some False
      else None)"

fun sign_eqb :: "sign \<Rightarrow> sign \<Rightarrow> bool option" where
  "sign_eqb a b =
     (if a = SZero \<and> b = SZero then Some True
      else if (sign_le a SNeg \<and> sign_le b SNonNeg) \<or> (sign_le b SNeg \<and> sign_le a SNonNeg)
           \<or> (sign_le a SPos \<and> sign_le b SNonPos) \<or> (sign_le b SPos \<and> sign_le a SNonPos)
      then Some False
      else None)"

fun sign_tobool :: "sign \<Rightarrow> bool option" where
  "sign_tobool a =
     (if sign_le a SNeg \<or> sign_le a SPos then Some True
      else if sign_le a SZero then Some False
      else None)"

lemma sign_lt_sound:
  assumes "sign_lt a b = Some c" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "(i < j) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; cases b; auto split: if_splits)

lemma sign_eqb_sound:
  assumes "sign_eqb a b = Some c" and "i \<in> gamma_sign a" and "j \<in> gamma_sign b"
  shows "(i = j) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; cases b; auto split: if_splits)

lemma sign_tobool_sound:
  assumes "sign_tobool a = Some c" and "i \<in> gamma_sign a"
  shows "(i \<noteq> 0) = c"
  using assms unfolding less_eq_sign_def[symmetric]
  by (cases a; auto split: if_splits)

lemma sign_le_trans_below:
  fixes a1 a2 :: sign
  assumes "sign_le a2 t" and "a1 \<le> a2"
  shows "sign_le a1 t"
  using assms sign_le_trans unfolding less_eq_sign_def
  by blast

lemma sign_lt_mono:
  assumes hp: "\<not> is_bot (a1::sign)" and hq: "\<not> is_bot b1"
      and hab: "a1 \<le> a2" and hbb: "b1 \<le> b2"
      and hwide: "sign_lt a2 b2 = Some c"
  shows "sign_lt a1 b1 = Some c"
proof (cases c)
  case True
  then have "sign_le a2 SNeg \<and> sign_le b2 SNonNeg \<or> sign_le a2 SNonPos \<and> sign_le b2 SPos"
    using hwide by (auto split: if_splits)
  then have "sign_le a1 SNeg \<and> sign_le b1 SNonNeg \<or> sign_le a1 SNonPos \<and> sign_le b1 SPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  then show ?thesis using True by auto
next
  case False
  then have "sign_le b2 SNonPos \<and> sign_le a2 SNonNeg \<or> sign_le b2 SNeg \<and> sign_le a2 SPos"
    using hwide by (auto split: if_splits)
  then have hyp: "sign_le b1 SNonPos \<and> sign_le a1 SNonNeg \<or> sign_le b1 SNeg \<and> sign_le a1 SPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  show ?thesis using hyp False hp hq unfolding is_bot_sign is_bottom_sign_def
    by (cases a1; cases b1; auto)
qed

lemma sign_eqb_mono:
  assumes hp: "\<not> is_bot (a1::sign)" and hq: "\<not> is_bot b1"
      and hab: "a1 \<le> a2" and hbb: "b1 \<le> b2"
      and hwide: "sign_eqb a2 b2 = Some c"
  shows "sign_eqb a1 b1 = Some c"
proof (cases c)
  case True
  then have "a2 = SZero \<and> b2 = SZero" using hwide by (auto split: if_splits)
  then have "sign_le a2 SZero" and "sign_le b2 SZero"
    unfolding less_eq_sign_def[symmetric] by simp_all
  then have hle1: "sign_le a1 SZero" and hle2: "sign_le b1 SZero"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast+
  have ha1: "a1 = SBot \<or> a1 = SZero" using hle1 by (cases a1) auto
  have hb1: "b1 = SBot \<or> b1 = SZero" using hle2 by (cases b1) auto
  show ?thesis using True hp hq ha1 hb1 unfolding is_bot_sign is_bottom_sign_def by auto
next
next
  case False
  then have "sign_le a2 SNeg \<and> sign_le b2 SNonNeg \<or> sign_le b2 SNeg \<and> sign_le a2 SNonNeg
             \<or> sign_le a2 SPos \<and> sign_le b2 SNonPos \<or> sign_le b2 SPos \<and> sign_le a2 SNonPos"
    using hwide by (auto split: if_splits)
  then have "sign_le a1 SNeg \<and> sign_le b1 SNonNeg \<or> sign_le b1 SNeg \<and> sign_le a1 SNonNeg
             \<or> sign_le a1 SPos \<and> sign_le b1 SNonPos \<or> sign_le b1 SPos \<and> sign_le a1 SNonPos"
    using sign_le_trans_below[OF _ hab] sign_le_trans_below[OF _ hbb] by blast
  then show ?thesis using False by auto
qed

lemma sign_tobool_mono:
  assumes "\<not> is_bot (a1::sign)" and "a1 \<le> a2" and "sign_tobool a2 = Some c"
  shows "sign_tobool a1 = Some c"
  using assms unfolding is_bot_sign is_bottom_sign_def
  by (cases a1; cases a2; auto simp: less_eq_sign_def split: if_splits)

subsection \<open>Abstract expression evaluation\<close>

text \<open>
  \<open>sign_cast\<close> is not a generic boundary-literal fallback cast: sign carries
  no magnitude, so a boundary-literal test via \<^const>\<open>sign_lt\<close> can never
  certify an unbounded value (\<open>SNeg\<close>/\<open>SNonPos\<close>/
  \<open>SNonNeg\<close>/\<open>SPos\<close>) already fits an \<open>ikind\<close>'s range, so it always widens
  those to \<open>STop\<close> regardless of the target kind. An unsigned target admits
  a uniform, strictly sharper fact instead: \<^const>\<open>ik_norm\<close> for an unsigned
  \<open>ikind\<close> always lands in \<open>[0, ik_max ik]\<close> (\<open>ik_norm_in_range\<close>, since
  \<open>ik_min ik = 0\<close>), so casting to an unsigned kind is always sound at
  \<open>SNonNeg\<close> -- never \<open>STop\<close> -- no matter the source value. \<open>SZero\<close> is
  exact at every kind: zero is representable at any width. A signed target
  genuinely admits nothing sharper than \<open>STop\<close> for any other value, since
  the sign-only abstraction carries no bound on how far a value in, say,
  \<open>SPos\<close> could exceed the kind's range.
\<close>

definition sign_cast :: "ikind => sign => sign" where
  "sign_cast ik a =
     (if is_bot a then bot
      else if a = SZero then SZero
      else if \<not> ik_signed ik then SNonNeg
      else top)"

lemma sign_cast_sound:
  assumes v: "v \<in> gamma a"
  shows "ik_norm ik v \<in> gamma (sign_cast ik a)"
proof (cases "is_bot a")
  case True
  then show ?thesis using v by (simp add: is_bot_sign is_bottom_sign_correct gamma_abs_sign)
next
  case False
  show ?thesis
  proof (cases "a = SZero")
    case True
    with v have "v = 0" by (simp add: gamma_abs_sign)
    then show ?thesis
      using True by (simp add: sign_cast_def ik_norm_def is_bot_sign is_bottom_sign_correct)
  next
    case a_ne: False
    show ?thesis
    proof (cases "ik_signed ik")
      case True
      with False a_ne show ?thesis by (simp add: sign_cast_def gamma_abs_sign gamma_sign_top)
    next
      case False
      have "0 \<le> ik_norm ik v" using ik_norm_in_range[of ik v]
        by (simp add: ik_range_def ik_min_def False)
      with False a_ne \<open>\<not> is_bot a\<close> show ?thesis
        by (simp add: sign_cast_def gamma_abs_sign)
    qed
  qed
qed

lemma sign_cast_mono:
  assumes le: "a1 \<le> (a2 :: sign)"
  shows "sign_cast ik a1 \<le> sign_cast ik a2"
proof (cases "is_bot a1")
  case True
  then show ?thesis by (simp add: sign_cast_def bot_least)
next
  case nb1: False
  have sub: "gamma_sign a1 \<subseteq> gamma_sign a2"
    using le by (simp add: less_eq_sign_def gamma_sign_mono)
  have nb2: "\<not> is_bot a2"
  proof -
    from nb1 obtain x where "x \<in> gamma_sign a1"
      by (auto simp: is_bot_sign is_bottom_sign_correct)
    with sub show ?thesis by (auto simp: is_bot_sign is_bottom_sign_correct)
  qed
  show ?thesis
  proof (cases "a1 = SZero")
    case True
    then show ?thesis
      using nb1 nb2
      by (cases "a2 = SZero") (simp_all add: sign_cast_def less_eq_sign_def top_sign_def)
  next
    case a1_ne: False
    have a2_ne: "a2 \<noteq> SZero"
    proof
      assume "a2 = SZero"
      with sub have subz: "gamma_sign a1 \<subseteq> {0}" by simp
      have "\<exists>x. x \<in> gamma_sign a1 \<and> x \<noteq> 0"
        using nb1 a1_ne
        by (cases a1)
           (auto simp: is_bot_sign is_bottom_sign_correct
              intro: exI[of _ "- 1"] exI[of _ "1"])
      with subz show False by auto
    qed
    show ?thesis
      using nb1 nb2 a1_ne a2_ne by (simp add: sign_cast_def)
  qed
qed

lemma sign_cast_sound_sign:
  "v \<in> gamma_sign a \<Longrightarrow> ik_norm ik v \<in> gamma_sign (sign_cast ik a)"
  using sign_cast_sound[of v a ik] by (simp add: gamma_abs_sign)

text \<open>
  \<open>aval_sign_t\<close> is the sole evaluator for sign: it operates directly on
  an already-elaborated \<^typ>\<open>texp\<close>, so it needs no \<open>\<Gamma>\<close>/\<open>ik\<close> parameter of
  its own -- every node already carries the kind it should be cast/normed
  at. Every arithmetic node is normed once through \<^const>\<open>sign_cast\<close> at
  its own kind, and \<open>TLess\<close>/\<open>TEq\<close>/\<open>TNot\<close>/\<open>TAnd\<close>/\<open>TOr\<close> never norm their own
  0/1-shaped result, matching \<^const>\<open>teval\<close>. \<open>aval_sign\<close>
  (\<^theory>\<open>Voblint_Core.Abstract_Arithmetic\<close>'s \<open>expression_domain_sound\<close>
  locale this interprets below) is a thin wrapper elaborating its argument
  once and handing it to \<open>aval_sign_t\<close>, not a second, independent
  recursion to keep in sync: both \<open>Sign_Transfer\<close>'s forward obligations
  and \<open>Sign_Backward\<close>'s \<open>backward_domain\<close> interpretation target it.
\<close>

fun aval_sign_t :: "texp => (vname => sign) => sign" where
    "aval_sign_t (TN ik n)        \<sigma> = sign_cast ik (sign_of_int n)"
  | "aval_sign_t (TV ik x)        \<sigma> = sign_cast ik (\<sigma> x)"
  | "aval_sign_t (TPlus  ik a b)  \<sigma> = sign_cast ik (aval_sign_t a \<sigma> + aval_sign_t b \<sigma>)"
  | "aval_sign_t (TMinus ik a b)  \<sigma> = sign_cast ik (aval_sign_t a \<sigma> - aval_sign_t b \<sigma>)"
  | "aval_sign_t (TTimes ik a b)  \<sigma> = sign_cast ik (aval_sign_t a \<sigma> * aval_sign_t b \<sigma>)"
  | "aval_sign_t (TLess a b) \<sigma> =
       (if is_bot (aval_sign_t a \<sigma>) \<or> is_bot (aval_sign_t b \<sigma>) then bot
        else if sign_lt (aval_sign_t a \<sigma>) (aval_sign_t b \<sigma>) = Some True then SPos
        else if sign_lt (aval_sign_t a \<sigma>) (aval_sign_t b \<sigma>) = Some False then SZero
        else SNonNeg)"
  | "aval_sign_t (TEq a b) \<sigma> =
       (if is_bot (aval_sign_t a \<sigma>) \<or> is_bot (aval_sign_t b \<sigma>) then bot
        else if sign_eqb (aval_sign_t a \<sigma>) (aval_sign_t b \<sigma>) = Some True then SPos
        else if sign_eqb (aval_sign_t a \<sigma>) (aval_sign_t b \<sigma>) = Some False then SZero
        else SNonNeg)"
  | "aval_sign_t (TNot a) \<sigma> =
       (if is_bot (aval_sign_t a \<sigma>) then bot
        else if sign_tobool (aval_sign_t a \<sigma>) = Some True then SZero
        else if sign_tobool (aval_sign_t a \<sigma>) = Some False then SPos
        else SNonNeg)"
  | "aval_sign_t (TAnd a b) \<sigma> =
       (if is_bot (aval_sign_t a \<sigma>) \<or> is_bot (aval_sign_t b \<sigma>) then bot
        else if sign_tobool (aval_sign_t a \<sigma>) = Some False
                \<or> sign_tobool (aval_sign_t b \<sigma>) = Some False
        then SZero
        else if sign_tobool (aval_sign_t a \<sigma>) = Some True
                \<and> sign_tobool (aval_sign_t b \<sigma>) = Some True
        then SPos
        else SNonNeg)"
  | "aval_sign_t (TOr a b) \<sigma> =
       (if is_bot (aval_sign_t a \<sigma>) \<or> is_bot (aval_sign_t b \<sigma>) then bot
        else if sign_tobool (aval_sign_t a \<sigma>) = Some True
                \<or> sign_tobool (aval_sign_t b \<sigma>) = Some True
        then SPos
        else if sign_tobool (aval_sign_t a \<sigma>) = Some False
                \<and> sign_tobool (aval_sign_t b \<sigma>) = Some False
        then SZero
        else SNonNeg)"

definition aval_sign :: "tyenv => ikind => exp => (vname => sign) => sign" where
  "aval_sign \<Gamma> ik a \<sigma> = aval_sign_t (elaborate \<Gamma> ik a) \<sigma>"

lemma sign_plus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i + j \<in> gamma_sign (a + b)"
  using assms by (cases a; cases b; auto)

lemma sign_minus_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i - j \<in> gamma_sign (a - b)"
  using assms by (cases a; cases b; auto)

lemma sign_times_sound:
  assumes "i \<in> gamma_sign a" "j \<in> gamma_sign b"
  shows "i * j \<in> gamma_sign (a * b)"
  using assms by (cases a; cases b; auto simp: mult_neg_neg mult_neg_pos mult_pos_neg
                                                zero_le_mult_iff mult_le_0_iff)

lemma sign_plus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 + b \<le> a2 + (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_plus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a + b1 \<le> a + (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_minus_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 - b \<le> a2 - (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_minus_mono2:
  "b1 \<le> b2 \<Longrightarrow> a - b1 \<le> a - (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_times_mono1:
  "a1 \<le> a2 \<Longrightarrow> a1 * b \<le> a2 * (b::sign)"
  unfolding less_eq_sign_def
  by (cases a1; cases a2; cases b; simp)

lemma sign_times_mono2:
  "b1 \<le> b2 \<Longrightarrow> a * b1 \<le> a * (b2::sign)"
  unfolding less_eq_sign_def
  by (cases a; cases b1; cases b2; simp)

lemma sign_plus_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 + b1 \<le> a2 + (b2::sign)"
  by (meson order.trans sign_plus_mono1 sign_plus_mono2)

lemma sign_minus_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 - b1 \<le> a2 - (b2::sign)"
  by (meson order.trans sign_minus_mono1 sign_minus_mono2)

lemma sign_times_combine_mono:
  "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 * b1 \<le> a2 * (b2::sign)"
  by (meson order.trans sign_times_mono1 sign_times_mono2)

interpretation sign_arith: expression_domain_sound
    aval_sign sign_cast sign_of_int sign_lt sign_eqb sign_tobool
  apply unfold_locales
  apply (simp_all add: aval_sign_def sign_of_int_gamma sign_plus_sound sign_minus_sound
                        sign_times_sound sign_plus_combine_mono sign_minus_combine_mono
                        sign_times_combine_mono sign_lt_sound sign_eqb_sound
                        sign_tobool_sound[unfolded truthy_def] sup_sign_def join_sign.simps
                        truthy_def gamma_sign_top Let_def sign_cast_sound_sign sign_cast_mono
                    del: sign_lt.simps sign_eqb.simps sign_tobool.simps)
  apply (blast intro: sign_lt_mono[unfolded is_bot_sign])
  apply (blast intro: sign_eqb_mono[unfolded is_bot_sign])
  apply (blast intro: sign_tobool_mono[unfolded is_bot_sign])
  done

lemmas aval_sign_sound = sign_arith.aval_dom_sound[unfolded gamma_abs_sign]
lemmas aval_sign_mono = sign_arith.aval_dom_mono

text \<open>
  \<open>aval_sign_t (elaborate \<Gamma> ik a) = aval_sign \<Gamma> ik a\<close> is immediate from
  \<open>aval_sign\<close>'s own definition -- no induction needed, since \<open>aval_sign_t\<close>
  is the primitive recursion and \<open>aval_sign\<close> is defined in terms of it.
\<close>

lemma aval_sign_t_elaborate [simp]:
  "aval_sign_t (elaborate \<Gamma> ik a) \<sigma> = aval_sign \<Gamma> ik a \<sigma>"
  by (simp add: aval_sign_def)

lemma aval_sign_t_elaborate_syn [simp]:
  "aval_sign_t (elaborate_syn \<Gamma> a) \<sigma> = aval_sign \<Gamma> (opk (esyn \<Gamma> a)) a \<sigma>"
  by (simp add: elaborate_syn_def)

lemma aval_sign_t_sound:
  assumes "\<forall>x. s x \<in> gamma_sign (sigma x)"
  shows "taval \<Gamma> ik a s \<in> gamma_sign (aval_sign_t (elaborate \<Gamma> ik a) sigma)"
  using aval_sign_sound[OF assms] by simp

lemma aval_sign_t_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_sign_t (elaborate \<Gamma> ik a) sigma1 \<le> aval_sign_t (elaborate \<Gamma> ik a) sigma2"
  using aval_sign_mono by simp

lemma aval_sign_t_sound_syn:
  assumes "\<forall>x. s x \<in> gamma_sign (sigma x)"
  shows "taval_syn \<Gamma> a s \<in> gamma_sign (aval_sign_t (elaborate_syn \<Gamma> a) sigma)"
  unfolding taval_syn_def elaborate_syn_def using aval_sign_t_sound[OF assms] .

lemma aval_sign_t_mono_syn:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_sign_t (elaborate_syn \<Gamma> a) sigma1 \<le> aval_sign_t (elaborate_syn \<Gamma> a) sigma2"
  unfolding elaborate_syn_def using aval_sign_t_mono .

end
