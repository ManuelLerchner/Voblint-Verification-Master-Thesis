theory Sign_Lattice
  imports "Voblint_Domain.Abstract_Domain"
begin

section \<open>Sign lattice\<close>

text \<open>
  sign abstracts integers by their sign:
    Bot    -- empty (unreachable / undefined)
    Neg    -- strictly negative   {n | n < 0}
    NonPos -- non-positive        \<open>{n | n \<le> 0}\<close>
    Zero   -- exactly zero        {0}
    NonNeg -- non-negative        \<open>{n | n \<ge> 0}\<close>
    Pos    -- strictly positive   {n | n > 0}
    Top    -- all integers        UNIV

  Seven-element lattice (\<open>Bot \<le> Neg,Zero,Pos \<le> NonPos,NonNeg \<le> Top\<close>).
  Finite; no widening needed.
\<close>

subsection \<open>Carrier and concretization\<close>

datatype sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop

fun gamma_sign :: "sign => int set" where
    "gamma_sign SBot    = {}"
  | "gamma_sign SNeg    = {n. n < 0}"
  | "gamma_sign SNonPos = {n. n \<le> 0}"
  | "gamma_sign SZero   = {0}"
  | "gamma_sign SNonNeg = {n. n \<ge> 0}"
  | "gamma_sign SPos    = {n. n > 0}"
  | "gamma_sign STop    = UNIV"

fun sign_of_int :: "int => sign" where
  "sign_of_int n = (if n < 0 then SNeg else if n = 0 then SZero else SPos)"

lemma sign_of_int_gamma: "n : gamma_sign (sign_of_int n)"
  by (auto split: if_splits)

subsection \<open>Order\<close>

text \<open>
  \<open>sign_le\<close> puts \<open>SNeg\<close> and \<open>SZero\<close> below \<open>SNonPos\<close>, and
  \<open>SZero\<close> and \<open>SPos\<close> below \<open>SNonNeg\<close>; concretization is monotone in it.
\<close>

fun sign_le :: "sign => sign => bool" where
    "sign_le SBot    _       = True"
  | "sign_le _       STop    = True"
  | "sign_le SNeg    SNeg    = True"
  | "sign_le SNeg    SNonPos = True"
  | "sign_le SNonPos SNonPos = True"
  | "sign_le SZero   SZero   = True"
  | "sign_le SZero   SNonPos = True"
  | "sign_le SZero   SNonNeg = True"
  | "sign_le SNonNeg SNonNeg = True"
  | "sign_le SPos    SPos    = True"
  | "sign_le SPos    SNonNeg = True"
  | "sign_le _       _       = False"

lemma sign_le_refl:    "sign_le s s"                              by (cases s) simp_all

lemma sign_le_antisym:
  assumes st: "sign_le s t" and ts: "sign_le t s"
  shows "s = t"
  using st ts by (cases s; cases t; simp)

lemma sign_le_trans:
  assumes st: "sign_le s t" and tu: "sign_le t u"
  shows "sign_le s u"
  using st tu by (cases s; cases t; cases u; simp)

lemma gamma_sign_mono:
  assumes st: "sign_le s t"
  shows "gamma_sign s <= gamma_sign t"
  using st by (cases s; cases t; auto)

instantiation sign :: ord begin
definition less_eq_sign :: "sign => sign => bool" where "(a::sign) <= b = sign_le a b"
definition less_sign    :: "sign => sign => bool" where
  "(a::sign) <  b = (sign_le a b \<and> \<not> sign_le b a)"
instance ..
end

instance sign :: preorder
proof intro_classes
  fix x y z :: sign
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    unfolding less_sign_def less_eq_sign_def by simp
  show "x \<le> x"
    by (simp add: less_eq_sign_def sign_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    unfolding less_eq_sign_def by (rule sign_le_trans)
qed

instantiation sign :: order begin
instance proof intro_classes
  fix x y :: sign
  assume "x \<le> y" "y \<le> x"
  then show "x = y"
    unfolding less_eq_sign_def by (blast intro: sign_le_antisym)
qed
end

text \<open>
  The bottom instance lifts pointwise to abstract states and enables monotone
  least-upper-bound iteration.
\<close>

instantiation sign :: bot begin
definition "bot_sign = SBot"
instance ..
end

instantiation sign :: order_bot begin
instance proof intro_classes
  fix x :: sign
  show "bot \<le> x"
    unfolding less_eq_sign_def bot_sign_def by simp
qed
end

instantiation sign :: top begin
definition "top_sign = STop"
instance ..
end

instantiation sign :: order_top begin
instance proof intro_classes
  fix x :: sign
  show "x \<le> top"
    unfolding less_eq_sign_def top_sign_def by (cases x) simp_all
qed
end

lemma gamma_sign_top: "gamma_sign top = UNIV"
  unfolding top_sign_def by simp

subsection \<open>Join\<close>

text \<open>
  \<open>join_sign\<close> returns the least sign covering both arguments, for example
  \<open>SNeg\<close> and \<open>SZero\<close> join to \<open>SNonPos\<close>.
\<close>

fun join_sign :: "sign => sign => sign" where
    "join_sign SBot    b       = b"
  | "join_sign a       SBot    = a"
  | "join_sign STop    _       = STop"
  | "join_sign _       STop    = STop"
  | "join_sign SNeg    SNeg    = SNeg"
  | "join_sign SNeg    SZero   = SNonPos"
  | "join_sign SNeg    SNonPos = SNonPos"
  | "join_sign SZero   SNeg    = SNonPos"
  | "join_sign SZero   SZero   = SZero"
  | "join_sign SZero   SPos    = SNonNeg"
  | "join_sign SZero   SNonPos = SNonPos"
  | "join_sign SZero   SNonNeg = SNonNeg"
  | "join_sign SNonPos SNeg    = SNonPos"
  | "join_sign SNonPos SZero   = SNonPos"
  | "join_sign SNonPos SNonPos = SNonPos"
  | "join_sign SNonNeg SZero   = SNonNeg"
  | "join_sign SNonNeg SPos    = SNonNeg"
  | "join_sign SNonNeg SNonNeg = SNonNeg"
  | "join_sign SPos    SZero   = SNonNeg"
  | "join_sign SPos    SNonNeg = SNonNeg"
  | "join_sign SPos    SPos    = SPos"
  | "join_sign _       _       = STop"

lemma join_sign_ub1: "sign_le a (join_sign a b)"
  by (cases a; cases b; simp)

lemma join_sign_ub2: "sign_le b (join_sign a b)"
  by (cases a; cases b; simp)

lemma join_sign_least: "sign_le a csg \<Longrightarrow> sign_le b csg \<Longrightarrow> sign_le (join_sign a b) csg"
  by (cases a; cases b; cases csg; simp)

instantiation sign :: sup begin
definition sup_sign :: "sign => sign => sign" where
  "sup_sign = join_sign"
instance ..
end

instance sign :: semilattice_sup
proof intro_classes
  fix x y z :: sign
  show "x \<le> x \<squnion> y"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_ub1)
  show "y \<le> x \<squnion> y"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    unfolding sup_sign_def less_eq_sign_def by (rule join_sign_least)
qed

text \<open>
  \<open>sign\<close> is already an \<open>order_bot\<close> and a \<open>semilattice_sup\<close>, so the bounded
  semilattice comes for free.
\<close>

instance sign :: bounded_semilattice_sup_bot ..

subsection \<open>Meet\<close>

text \<open>
  The sign meet is exact: it concretizes to the intersection of its operands.
  As a @{class semilattice_inf} instance it gives @{text \<open>inf_mono\<close>} for free,
  which the monotonicity proof of @{text bfilter} needs.
\<close>

instantiation sign :: inf begin

fun inf_sign :: "sign => sign => sign" where
    "inf_sign SBot    _       = SBot"
  | "inf_sign _       SBot    = SBot"
  | "inf_sign STop    b       = b"
  | "inf_sign a       STop    = a"
  | "inf_sign SNeg    SNeg    = SNeg"
  | "inf_sign SNeg    SNonPos = SNeg"
  | "inf_sign SNonPos SNeg    = SNeg"
  | "inf_sign SNonPos SNonPos = SNonPos"
  | "inf_sign SNonPos SZero   = SZero"
  | "inf_sign SZero   SNonPos = SZero"
  | "inf_sign SNonPos SNonNeg = SZero"
  | "inf_sign SNonNeg SNonPos = SZero"
  | "inf_sign SZero   SZero   = SZero"
  | "inf_sign SZero   SNonNeg = SZero"
  | "inf_sign SNonNeg SZero   = SZero"
  | "inf_sign SNonNeg SNonNeg = SNonNeg"
  | "inf_sign SNonNeg SPos    = SPos"
  | "inf_sign SPos    SNonNeg = SPos"
  | "inf_sign SPos    SPos    = SPos"
  | "inf_sign _       _       = SBot"

instance ..

end

lemma gamma_inf_sign [simp]:
  "gamma_sign (a \<sqinter> b) = gamma_sign a \<inter> gamma_sign b"
  by (cases a; cases b) auto

lemma inf_sign_sound:
  "n \<in> gamma_sign a \<Longrightarrow> n \<in> gamma_sign b \<Longrightarrow> n \<in> gamma_sign (a \<sqinter> b)"
  by simp

instance sign :: semilattice_inf
proof intro_classes
  fix x y z :: sign
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y; auto simp: less_eq_sign_def)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z; auto simp: less_eq_sign_def)
qed

instance sign :: lattice ..
instance sign :: bounded_lattice_bot ..

subsection \<open>Executable interface\<close>

text \<open>
  \<open>SBot\<close> is the only empty value a finite enumerated domain can have (every
  other constructor denotes a nonempty set of integers), so a direct
  equality test is already exact --- unlike Interval's analogous fact,
  which cannot use equality against one representative because Interval's
  bound-pair representation has many empty values besides its canonical
  \<open>bot\<close>. Exposed here, at the domain's own theory, rather than inlined
  where a caller happens to need it, so every consumer (not just one) gets
  the same domain-owned fact.
\<close>

definition is_bottom_sign :: "sign \<Rightarrow> bool" where
  "is_bottom_sign s = (s = SBot)"

lemma is_bottom_sign_correct: "is_bottom_sign s \<longleftrightarrow> gamma_sign s = {}"
  unfolding is_bottom_sign_def
  by (cases s) (auto intro: exI[of _ "-1"] exI[of _ "0"] exI[of _ "1"])

text \<open>\<open>STop\<close> is likewise the unique top of a finite enumeration.\<close>

definition is_top_sign :: "sign \<Rightarrow> bool" where
  "is_top_sign s = (s = STop)"

lemma is_top_sign_correct_gamma: "is_top_sign s \<longleftrightarrow> gamma_sign s = UNIV"
  by(cases s) (auto simp: is_top_sign_def set_eq_iff; presburger)+

text \<open>
  Goblint has no sign value domain; its tutorial sign analysis prints \<open>-\<close>, \<open>0\<close>
  and \<open>+\<close>, which the two non-strict elements extend as \<open>\<le>0\<close> and \<open>\<ge>0\<close>.
\<close>

fun string_of_sign :: "sign \<Rightarrow> String.literal" where
    "string_of_sign SBot    = sym_bottom"
  | "string_of_sign SNeg    = STR ''-''"
  | "string_of_sign SNonPos = sym_le + STR ''0''"
  | "string_of_sign SZero   = STR ''0''"
  | "string_of_sign SNonNeg = sym_ge + STR ''0''"
  | "string_of_sign SPos    = STR ''+''"
  | "string_of_sign STop    = sym_top"

end
