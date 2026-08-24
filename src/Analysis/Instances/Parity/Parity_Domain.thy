theory Parity_Domain
  imports Voblint_Core.Abstract_Domain "Voblint_VIMP.VIMP_Expr" "Voblint_VIMP.VIMP_Elaborated"
    "TD.Update_rules" Voblint_Core.Abstract_Arithmetic
begin

section \<open>Parity domain: finite even/odd abstraction\<close>

text \<open>
  parity abstracts integers by their parity:
    Bot   -- empty (unreachable)
    Even  -- {n | even n}
    Odd   -- {n | odd n}
    Top   -- all integers

  Four-element lattice (Bot \<sqsubseteq> Even,Odd \<sqsubseteq> Top).  Finite; widen = sup.
  Guards do not refine parity, so the assume transfer is the identity.
\<close>

subsection \<open>Datatype and concretization\<close>

datatype parity = PBot | PEven | POdd | PTop

fun gamma_parity :: "parity => int set" where
    "gamma_parity PBot  = {}"
  | "gamma_parity PEven = {n. even n}"
  | "gamma_parity POdd  = {n. odd n}"
  | "gamma_parity PTop  = UNIV"

subsection \<open>Partial order\<close>

fun parity_le :: "parity => parity => bool" where
    "parity_le PBot  _     = True"
  | "parity_le _     PTop  = True"
  | "parity_le PEven PEven = True"
  | "parity_le POdd  POdd  = True"
  | "parity_le _     _     = False"

lemma parity_le_refl: "parity_le s s" by (cases s) simp_all

lemma parity_le_antisym: "parity_le s t \<Longrightarrow> parity_le t s \<Longrightarrow> s = t"
  by (cases s; cases t; simp)

lemma parity_le_trans: "parity_le s t \<Longrightarrow> parity_le t u \<Longrightarrow> parity_le s u"
  by (cases s; cases t; cases u; simp)

lemma gamma_parity_mono: "parity_le s t \<Longrightarrow> gamma_parity s \<subseteq> gamma_parity t"
  by (cases s; cases t; auto)

instantiation parity :: ord begin
definition less_eq_parity :: "parity => parity => bool" where "(a::parity) \<le> b = parity_le a b"
definition less_parity    :: "parity => parity => bool" where "(a::parity) <  b = (parity_le a b \<and> \<not> parity_le b a)"
instance ..
end

instance parity :: preorder
proof
  fix x y z :: parity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_parity_def less_eq_parity_def by simp
  show "x \<le> x" by (simp add: less_eq_parity_def parity_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_parity_def by (rule parity_le_trans)
qed

instantiation parity :: bot begin
definition "bot_parity = PBot"
instance ..
end

text \<open>
  \<open>PBot\<close> is the only empty value a finite enumerated domain can have, the
  same reasoning as Sign's \<open>is_bottom_sign\<close>, so a direct equality test is
  exact here too.
\<close>

definition is_bottom_parity :: "parity \<Rightarrow> bool" where
  "is_bottom_parity p = (p = PBot)"

lemma is_bottom_parity_correct: "is_bottom_parity p \<longleftrightarrow> gamma_parity p = {}"
  unfolding is_bottom_parity_def
  by (cases p) (auto simp: gamma_parity.simps intro: exI[of _ "0"] exI[of _ "1"])

subsection \<open>Join\<close>

fun join_parity :: "parity => parity => parity" where
    "join_parity PBot  b     = b"
  | "join_parity a     PBot  = a"
  | "join_parity PTop  _     = PTop"
  | "join_parity _     PTop  = PTop"
  | "join_parity PEven PEven = PEven"
  | "join_parity POdd  POdd  = POdd"
  | "join_parity _     _     = PTop"

lemma join_parity_ub1: "parity_le a (join_parity a b)" by (cases a; cases b; simp)
lemma join_parity_ub2: "parity_le b (join_parity a b)" by (cases a; cases b; simp)
lemma join_parity_least: "parity_le a c \<Longrightarrow> parity_le b c \<Longrightarrow> parity_le (join_parity a b) c"
  by (cases a; cases b; cases c; simp)

subsection \<open>Order / lattice instances\<close>

instantiation parity :: order begin
instance proof
  fix x y :: parity
  assume "x \<le> y" "y \<le> x"
  then show "x = y" unfolding less_eq_parity_def by (blast intro: parity_le_antisym)
qed
end

instantiation parity :: order_bot begin
instance proof
  fix x :: parity
  show "bot \<le> x" unfolding less_eq_parity_def bot_parity_def by simp
qed
end

instantiation parity :: top begin
definition "top_parity = PTop"
instance ..
end

instantiation parity :: order_top begin
instance proof intro_classes
  fix x :: parity
  show "x \<le> top"
    unfolding less_eq_parity_def top_parity_def by (cases x) simp_all
qed
end

text \<open>\<open>PTop\<close> is the unique top of a finite enumeration, the same reasoning as Sign's \<open>is_top_sign\<close>.\<close>

definition is_top_parity :: "parity \<Rightarrow> bool" where
  "is_top_parity p = (p = PTop)"

lemma is_top_parity_correct: "is_top_parity p \<longleftrightarrow> p = top"
  unfolding is_top_parity_def top_parity_def ..

lemma gamma_parity_top: "gamma_parity top = UNIV"
  unfolding top_parity_def by simp

instantiation parity :: sup begin
definition sup_parity :: "parity => parity => parity" where "sup_parity = join_parity"
instance ..
end

instance parity :: semilattice_sup
proof
  fix x y z :: parity
  show "x \<le> x \<squnion> y" unfolding sup_parity_def less_eq_parity_def by (rule join_parity_ub1)
  show "y \<le> x \<squnion> y" unfolding sup_parity_def less_eq_parity_def by (rule join_parity_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" unfolding sup_parity_def less_eq_parity_def by (rule join_parity_least)
qed

instance parity :: bounded_semilattice_sup_bot ..

subsection \<open>Warrowing for the TD solver (widen = join, narrow = fst)\<close>

instantiation parity :: warrowing begin
  definition "widen (a :: parity) b = join_parity a b"
  definition "narrow (a :: parity) b = a"
instance proof
  fix a b :: parity
  show "a \<le> widen a b" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub1)
  show "b \<le> widen a b" unfolding less_eq_parity_def widen_parity_def by (rule join_parity_ub2)
  show "b \<le> a \<Longrightarrow> b \<le> narrow a b" unfolding narrow_parity_def by simp
  show "b \<le> a \<Longrightarrow> narrow a b \<le> a" unfolding narrow_parity_def by (simp add: less_eq_parity_def parity_le_refl)
qed
end

subsection \<open>Abstract arithmetic\<close>

instantiation parity :: plus begin
fun plus_parity :: "parity => parity => parity" where
    "plus_parity PBot  _     = PBot"
  | "plus_parity _     PBot  = PBot"
  | "plus_parity PEven PEven = PEven"
  | "plus_parity POdd  POdd  = PEven"
  | "plus_parity PEven POdd  = POdd"
  | "plus_parity POdd  PEven = POdd"
  | "plus_parity _     _     = PTop"
instance ..
end

instantiation parity :: minus begin
fun minus_parity :: "parity => parity => parity" where
    "minus_parity PBot  _     = PBot"
  | "minus_parity _     PBot  = PBot"
  | "minus_parity PEven PEven = PEven"
  | "minus_parity POdd  POdd  = PEven"
  | "minus_parity PEven POdd  = POdd"
  | "minus_parity POdd  PEven = POdd"
  | "minus_parity _     _     = PTop"
instance ..
end

instantiation parity :: times begin
fun times_parity :: "parity => parity => parity" where
    "times_parity PBot  _     = PBot"
  | "times_parity _     PBot  = PBot"
  | "times_parity PEven _     = PEven"
  | "times_parity _     PEven = PEven"
  | "times_parity POdd  POdd  = POdd"
  | "times_parity _     _     = PTop"
instance ..
end

fun parity_of_int :: "int => parity" where
  "parity_of_int n = (if even n then PEven else POdd)"

lemma parity_of_int_gamma: "n \<in> gamma_parity (parity_of_int n)" by auto

lemma parity_plus_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i + j \<in> gamma_parity (a + b)"
  by (cases a; cases b; auto simp: even_add)

lemma parity_minus_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i - j \<in> gamma_parity (a - b)"
  by (cases a; cases b; auto simp: even_diff)

lemma parity_times_sound:
  "i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> i * j \<in> gamma_parity (a * b)"
  by (cases a; cases b; auto simp: even_mult_iff)

subsection \<open>Monotonicity of arithmetic\<close>

lemma parity_plus_mono1: "a1 \<le> a2 \<Longrightarrow> a1 + b \<le> a2 + (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_plus_mono2: "b1 \<le> b2 \<Longrightarrow> a + b1 \<le> a + (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)
lemma parity_minus_mono1: "a1 \<le> a2 \<Longrightarrow> a1 - b \<le> a2 - (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_minus_mono2: "b1 \<le> b2 \<Longrightarrow> a - b1 \<le> a - (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)
lemma parity_times_mono1: "a1 \<le> a2 \<Longrightarrow> a1 * b \<le> a2 * (b::parity)"
  unfolding less_eq_parity_def by (cases a1; cases a2; cases b; simp)
lemma parity_times_mono2: "b1 \<le> b2 \<Longrightarrow> a * b1 \<le> a * (b2::parity)"
  unfolding less_eq_parity_def by (cases a; cases b1; cases b2; simp)

lemma parity_plus_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 + b1 \<le> a2 + (b2::parity)"
  by (meson order.trans parity_plus_mono1 parity_plus_mono2)

lemma parity_minus_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 - b1 \<le> a2 - (b2::parity)"
  by (meson order.trans parity_minus_mono1 parity_minus_mono2)

lemma parity_times_combine_mono: "\<lbrakk>a1 \<le> a2; b1 \<le> b2\<rbrakk> \<Longrightarrow> a1 * b1 \<le> a2 * (b2::parity)"
  by (meson order.trans parity_times_mono1 parity_times_mono2)




subsection \<open>sound_domain instance\<close>

instantiation parity :: sound_domain begin
definition gamma_abs_parity [simp]: "gamma (a :: parity) = gamma_parity a"
definition is_bot_parity [simp]: "is_bot (a :: parity) = is_bottom_parity a"
definition is_top_parity' [simp]: "is_top (a :: parity) = is_top_parity a"
instance proof
  show "gamma (bot :: parity) = {}" unfolding bot_parity_def by simp
next
  fix a b :: parity
  assume H: "a \<le> b"
  have "gamma_parity a \<subseteq> gamma_parity b" using H unfolding less_eq_parity_def by (rule gamma_parity_mono)
  then show "gamma a \<subseteq> gamma b" by simp
next
  fix a :: parity
  show "is_bot a \<longleftrightarrow> gamma a = {}"
    by (simp add: is_bottom_parity_correct)
next
  fix a :: parity
  show "is_top a \<longleftrightarrow> a = top"
    by (simp add: is_top_parity_correct)
qed
end

instance parity :: abstract_domain ..

subsection \<open>Comparison and truthiness queries\<close>

text \<open>
  Parity carries no ordering information, so \<open>parity_lt\<close> is always \<open>None\<close>.
  Equality is decidable exactly when the two operands have opposite parity --
  an even value can never equal an odd one -- and truthiness is decidable
  exactly for \<open>POdd\<close>, since every odd integer is nonzero.
\<close>

fun parity_lt :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
  "parity_lt _ _ = None"

fun parity_eqb :: "parity \<Rightarrow> parity \<Rightarrow> bool option" where
    "parity_eqb PEven POdd = Some False"
  | "parity_eqb POdd PEven = Some False"
  | "parity_eqb _ _ = None"

fun parity_tobool :: "parity \<Rightarrow> bool option" where
    "parity_tobool POdd = Some True"
  | "parity_tobool _ = None"

lemma parity_lt_sound:
  "parity_lt a b = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> (i < j) = c"
  by simp

lemma parity_eqb_sound:
  "parity_eqb a b = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> j \<in> gamma_parity b \<Longrightarrow> (i = j) = c"
  by (cases a; cases b; auto)

lemma parity_tobool_sound:
  "parity_tobool a = Some c \<Longrightarrow> i \<in> gamma_parity a \<Longrightarrow> (i \<noteq> 0) = c"
  by (cases a; auto)

lemma parity_lt_mono:
  "\<not> is_bot (a1::parity) \<Longrightarrow> \<not> is_bot b1 \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
   parity_lt a2 b2 = Some c \<Longrightarrow> parity_lt a1 b1 = Some c"
  by simp

lemma parity_eqb_mono:
  "\<not> is_bot (a1::parity) \<Longrightarrow> \<not> is_bot b1 \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow>
   parity_eqb a2 b2 = Some c \<Longrightarrow> parity_eqb a1 b1 = Some c"
  unfolding is_bot_parity is_bottom_parity_def less_eq_parity_def
  by (cases a1; cases a2; cases b1; cases b2; simp)

lemma parity_tobool_mono:
  "\<not> is_bot (a1::parity) \<Longrightarrow> a1 \<le> a2 \<Longrightarrow> parity_tobool a2 = Some c \<Longrightarrow> parity_tobool a1 = Some c"
  unfolding is_bot_parity is_bottom_parity_def less_eq_parity_def
  by (cases a1; cases a2; simp)

subsection \<open>Abstract expression evaluation\<close>

text \<open>
  \<open>parity_cast\<close> is the identity, not a generic boundary-literal fallback
  cast: every \<open>ikind\<close> this project defines has \<open>ik_bits ik \<ge> 1\<close>, so
  \<^const>\<open>ik_norm\<close> only ever adjusts its argument by a multiple of
  \<open>2 ^ (ik_bits ik - 1)\<close> or \<open>2 ^ ik_bits ik\<close> -- both even -- and evenness is
  therefore invariant under \<^const>\<open>ik_norm\<close> for every kind, unlike a domain
  whose modulus does not divide every wraparound modulus (Congruence). A
  boundary-literal fallback would be unconditionally maximally imprecise
  here anyway, since \<^const>\<open>parity_lt\<close> is always \<open>None\<close> and can never
  certify a value already in range.
\<close>

definition parity_cast :: "ikind => parity => parity" where
  "parity_cast ik a = a"

lemma even_mod_iff:
  fixes a c :: int
  assumes "even c"
  shows "even (a mod c) \<longleftrightarrow> even a"
  using assms by (simp add: even_iff_mod_2_eq_zero mod_mod_cancel)

lemma even_ik_norm [simp]: "even (ik_norm ik v) \<longleftrightarrow> even v"
  unfolding ik_norm_def
  by (cases ik) (simp_all add: take_bit_eq_mod signed_take_bit_eq_take_bit_shift even_mod_iff)

lemma parity_cast_sound:
  assumes v: "v \<in> gamma a"
  shows "ik_norm ik v \<in> gamma (parity_cast ik a)"
  unfolding parity_cast_def gamma_abs_parity
  using v unfolding gamma_abs_parity by (cases a) auto

lemma parity_cast_sound_parity:
  "v \<in> gamma_parity a \<Longrightarrow> ik_norm ik v \<in> gamma_parity (parity_cast ik a)"
  using parity_cast_sound[of v a ik] by (simp add: gamma_abs_parity)

lemma parity_cast_mono:
  assumes le: "a1 \<le> (a2 :: parity)"
  shows "parity_cast ik a1 \<le> parity_cast ik a2"
  using le by (simp add: parity_cast_def)

text \<open>
  \<open>aval_parity_t\<close> is the sole evaluator for parity: it operates directly on
  an already-elaborated \<^typ>\<open>texp\<close>, so it needs no \<open>\<Gamma>\<close>/\<open>ik\<close> parameter of
  its own -- every node already carries the kind it should be cast at. Every
  arithmetic node is normed once through \<^const>\<open>parity_cast\<close> at its own
  kind, and \<open>TLess\<close>/\<open>TEq\<close>/\<open>TNot\<close>/\<open>TAnd\<close>/\<open>TOr\<close> never norm their own 0/1-shaped
  result, matching \<^const>\<open>teval\<close>. \<open>aval_parity\<close> (\<^theory>\<open>Voblint_Core.Abstract_Arithmetic\<close>'s
  \<open>expression_domain_sound\<close> locale this interprets below) is a thin wrapper
  elaborating its argument once and handing it to \<open>aval_parity_t\<close>, not a
  second, independent recursion to keep in sync: both \<open>Parity_Transfer\<close>'s
  forward obligations and the domain's special-call dispatch target it.
\<close>

fun aval_parity_t :: "texp => (vname => parity) => parity" where
    "aval_parity_t (TN ik n)        \<sigma> = parity_cast ik (parity_of_int n)"
  | "aval_parity_t (TV ik x)        \<sigma> = parity_cast ik (\<sigma> x)"
  | "aval_parity_t (TPlus  ik a b)  \<sigma> = parity_cast ik (aval_parity_t a \<sigma> + aval_parity_t b \<sigma>)"
  | "aval_parity_t (TMinus ik a b)  \<sigma> = parity_cast ik (aval_parity_t a \<sigma> - aval_parity_t b \<sigma>)"
  | "aval_parity_t (TTimes ik a b)  \<sigma> = parity_cast ik (aval_parity_t a \<sigma> * aval_parity_t b \<sigma>)"
  | "aval_parity_t (TLess a b) \<sigma> =
       (if is_bot (aval_parity_t a \<sigma>) \<or> is_bot (aval_parity_t b \<sigma>) then bot
        else if parity_lt (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>) = Some True then POdd
        else if parity_lt (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>) = Some False then PEven
        else PTop)"
  | "aval_parity_t (TEq a b) \<sigma> =
       (if is_bot (aval_parity_t a \<sigma>) \<or> is_bot (aval_parity_t b \<sigma>) then bot
        else if parity_eqb (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>) = Some True then POdd
        else if parity_eqb (aval_parity_t a \<sigma>) (aval_parity_t b \<sigma>) = Some False then PEven
        else PTop)"
  | "aval_parity_t (TNot a) \<sigma> =
       (if is_bot (aval_parity_t a \<sigma>) then bot
        else if parity_tobool (aval_parity_t a \<sigma>) = Some True then PEven
        else if parity_tobool (aval_parity_t a \<sigma>) = Some False then POdd
        else PTop)"
  | "aval_parity_t (TAnd a b) \<sigma> =
       (if is_bot (aval_parity_t a \<sigma>) \<or> is_bot (aval_parity_t b \<sigma>) then bot
        else if parity_tobool (aval_parity_t a \<sigma>) = Some False
                \<or> parity_tobool (aval_parity_t b \<sigma>) = Some False
        then PEven
        else if parity_tobool (aval_parity_t a \<sigma>) = Some True
                \<and> parity_tobool (aval_parity_t b \<sigma>) = Some True
        then POdd
        else PTop)"
  | "aval_parity_t (TOr a b) \<sigma> =
       (if is_bot (aval_parity_t a \<sigma>) \<or> is_bot (aval_parity_t b \<sigma>) then bot
        else if parity_tobool (aval_parity_t a \<sigma>) = Some True
                \<or> parity_tobool (aval_parity_t b \<sigma>) = Some True
        then POdd
        else if parity_tobool (aval_parity_t a \<sigma>) = Some False
                \<and> parity_tobool (aval_parity_t b \<sigma>) = Some False
        then PEven
        else PTop)"

definition aval_parity :: "tyenv => ikind => exp => (vname => parity) => parity" where
  "aval_parity \<Gamma> ik a \<sigma> = aval_parity_t (elaborate \<Gamma> ik a) \<sigma>"

interpretation parity_arith: expression_domain_sound
    aval_parity parity_cast parity_of_int parity_lt parity_eqb parity_tobool
  apply unfold_locales
  apply (simp_all add: aval_parity_def parity_of_int_gamma parity_plus_sound parity_minus_sound
                        parity_times_sound parity_plus_combine_mono parity_minus_combine_mono
                        parity_times_combine_mono parity_lt_sound parity_eqb_sound
                        parity_tobool_sound[unfolded truthy_def] sup_parity_def join_parity.simps
                        truthy_def gamma_parity_top Let_def parity_cast_sound_parity parity_cast_mono
                    del: parity_lt.simps parity_eqb.simps parity_tobool.simps)
  apply (blast intro: parity_lt_mono[unfolded is_bot_parity])
  apply (blast intro: parity_eqb_mono[unfolded is_bot_parity])
  apply (blast intro: parity_tobool_mono[unfolded is_bot_parity])
  done

lemmas aval_parity_sound = parity_arith.aval_dom_sound[unfolded gamma_abs_parity]
lemmas aval_parity_mono = parity_arith.aval_dom_mono

text \<open>
  \<open>aval_parity_t (elaborate \<Gamma> ik a) = aval_parity \<Gamma> ik a\<close> is immediate from
  \<open>aval_parity\<close>'s own definition -- no induction needed, since \<open>aval_parity_t\<close>
  is the primitive recursion and \<open>aval_parity\<close> is defined in terms of it.
\<close>

lemma aval_parity_t_elaborate [simp]:
  "aval_parity_t (elaborate \<Gamma> ik a) \<sigma> = aval_parity \<Gamma> ik a \<sigma>"
  by (simp add: aval_parity_def)

lemma aval_parity_t_elaborate_syn [simp]:
  "aval_parity_t (elaborate_syn \<Gamma> a) \<sigma> = aval_parity \<Gamma> (opk (esyn \<Gamma> a)) a \<sigma>"
  by (simp add: elaborate_syn_def)

lemma aval_parity_t_sound:
  assumes "\<forall>x. s x \<in> gamma_parity (sigma x)"
  shows "taval \<Gamma> ik a s \<in> gamma_parity (aval_parity_t (elaborate \<Gamma> ik a) sigma)"
  using aval_parity_sound[OF assms] by simp

lemma aval_parity_t_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_parity_t (elaborate \<Gamma> ik a) sigma1 \<le> aval_parity_t (elaborate \<Gamma> ik a) sigma2"
  using aval_parity_mono by simp

lemma aval_parity_t_sound_syn:
  assumes "\<forall>x. s x \<in> gamma_parity (sigma x)"
  shows "taval_syn \<Gamma> a s \<in> gamma_parity (aval_parity_t (elaborate_syn \<Gamma> a) sigma)"
  unfolding taval_syn_def elaborate_syn_def using aval_parity_t_sound[OF assms] .

lemma aval_parity_t_mono_syn:
  "sigma1 \<le> sigma2 \<Longrightarrow>
   aval_parity_t (elaborate_syn \<Gamma> a) sigma1 \<le> aval_parity_t (elaborate_syn \<Gamma> a) sigma2"
  unfolding elaborate_syn_def using aval_parity_t_mono .

end
