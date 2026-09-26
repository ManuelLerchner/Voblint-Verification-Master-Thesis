theory Parity_Lattice
  imports "Voblint_Domain.Abstract_Domain"
begin

section \<open>Parity lattice\<close>

text \<open>
  parity abstracts integers by their parity:
    Bot   -- empty (unreachable)
    Even  -- {n | even n}
    Odd   -- {n | odd n}
    Top   -- all integers

  Four-element lattice (\<open>Bot \<sqsubseteq> Even,Odd \<sqsubseteq> Top\<close>). Finite; widen = sup.
  This analysis does not implement backward guard refinement. Its branch transfer
  therefore preserves parity information from the incoming state.
\<close>

subsection \<open>Carrier and concretization\<close>

datatype parity = PBot | PEven | POdd | PTop

fun gamma_parity :: "parity => int set" where
    "gamma_parity PBot  = {}"
  | "gamma_parity PEven = {n. even n}"
  | "gamma_parity POdd  = {n. odd n}"
  | "gamma_parity PTop  = UNIV"

fun parity_of_int :: "int => parity" where
  "parity_of_int n = (if even n then PEven else POdd)"

lemma parity_of_int_gamma: "n \<in> gamma_parity (parity_of_int n)" by auto

subsection \<open>Order\<close>

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
definition less_parity    :: "parity => parity => bool" where
  "(a::parity) <  b = (parity_le a b \<and> \<not> parity_le b a)"
instance ..
end

instance parity :: preorder
proof
  fix x y z :: parity
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" unfolding less_parity_def less_eq_parity_def by simp
  show "x \<le> x" by (simp add: less_eq_parity_def parity_le_refl)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_parity_def by (rule parity_le_trans)
qed

instantiation parity :: order begin
instance proof
  fix x y :: parity
  assume "x \<le> y" "y \<le> x"
  then show "x = y" unfolding less_eq_parity_def by (blast intro: parity_le_antisym)
qed
end

instantiation parity :: bot begin
definition "bot_parity = PBot"
instance ..
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

lemma gamma_parity_top: "gamma_parity top = UNIV"
  unfolding top_parity_def by simp

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

instantiation parity :: sup begin
definition sup_parity :: "parity => parity => parity" where "sup_parity = join_parity"
instance ..
end

instance parity :: semilattice_sup
proof
  fix x y z :: parity
  show "x \<le> x \<squnion> y" unfolding sup_parity_def less_eq_parity_def by (rule join_parity_ub1)
  show "y \<le> x \<squnion> y" unfolding sup_parity_def less_eq_parity_def by (rule join_parity_ub2)
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    unfolding sup_parity_def less_eq_parity_def by (rule join_parity_least)
qed

instance parity :: bounded_semilattice_sup_bot ..

subsection \<open>Meet\<close>

text \<open>
  Parity is closed under intersection: the meet of two classes is their common
  class, or bottom when one is even and the other odd.
\<close>

instantiation parity :: inf begin

fun inf_parity :: "parity => parity => parity" where
    "inf_parity PTop b    = b"
  | "inf_parity a    PTop = a"
  | "inf_parity a    b    = (if a = b then a else PBot)"

instance ..

end

lemma gamma_inf_parity [simp]:
  "gamma_parity (a \<sqinter> b) = gamma_parity a \<inter> gamma_parity b"
  by (cases a; cases b; auto)

instance parity :: semilattice_inf
proof intro_classes
  fix x y z :: parity
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y; simp add: less_eq_parity_def)
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y; simp add: less_eq_parity_def)
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z; simp add: less_eq_parity_def)
qed

instance parity :: lattice ..
instance parity :: bounded_lattice_bot ..

subsection \<open>Executable interface\<close>

text \<open>
  \<open>PBot\<close> is the only value with empty concretization, so a direct equality test
  decides emptiness exactly. Finiteness of the carrier is not what settles this ---
  a finite domain may perfectly well have two empty values. What settles it is the
  four concretizations themselves: the other three are each inhabited.
\<close>

definition is_bottom_parity :: "parity \<Rightarrow> bool" where
  "is_bottom_parity p = (p = PBot)"

lemma is_bottom_parity_correct: "is_bottom_parity p \<longleftrightarrow> gamma_parity p = {}"
  unfolding is_bottom_parity_def
  by (cases p) (auto intro: exI[of _ "0"] exI[of _ "1"])

text \<open>\<open>PTop\<close> is the unique top of a finite enumeration, the same reasoning as Sign's \<open>is_top_sign\<close>.\<close>

definition is_top_parity :: "parity \<Rightarrow> bool" where
  "is_top_parity p = (p = PTop)"

lemma is_top_parity_correct_gamma: "is_top_parity p \<longleftrightarrow> gamma_parity p = UNIV"
  by(cases p) (auto simp: is_top_parity_def set_eq_iff; presburger)+

text \<open>
  Goblint has no parity domain. A parity is the congruence class modulo 2, so it
  prints in Goblint's congruence notation: \<open>2\<int>\<close>, \<open>1+2\<int>\<close>, and \<open>\<int>\<close> for a
  product component's top. A standalone parity prints its top as \<open>\<top>\<close>.
\<close>

fun string_of_parity :: "parity \<Rightarrow> String.literal" where
    "string_of_parity PBot  = sym_bottom"
  | "string_of_parity PEven = STR ''2'' + sym_int"
  | "string_of_parity POdd  = STR ''1+2'' + sym_int"
  | "string_of_parity PTop  = sym_int"

lemma string_of_parity_regression:
  "string_of_parity PBot = STR ''<bottom>''"
  "string_of_parity PEven = STR ''2<int>''"
  "string_of_parity POdd = STR ''1+2<int>''"
  "string_of_parity PTop = STR ''<int>''"
  by eval+

end
