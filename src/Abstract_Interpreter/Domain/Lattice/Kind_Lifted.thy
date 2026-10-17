theory Kind_Lifted
  imports Abstract_Domain "Voblint_VIMP.Machine_Kind"
begin

section \<open>Kind-tagged values\<close>

text \<open>
  Goblint's \<^verbatim>\<open>IntDomLifter\<close> stores an integer domain element together with its
  \<^verbatim>\<open>ikind\<close>, so that operations without a kind argument, the lattice join and the
  solver's widening among them, can still act at the right kind. The value domain
  around it adds a bottom and a top, and turns a join of elements of different kinds
  into top. \<open>'a kd\<close> is that construction: \<open>KD k a\<close> is the element \<open>a\<close> at kind
  \<open>k\<close>, and it denotes only integers in the range of \<open>k\<close>.

  The component domain supplies the kind-indexed operations of Goblint's
  \<^verbatim>\<open>IntDomain.S\<close> that the lifter needs: widening and narrowing at a kind, and an
  emptiness test against a kind's range.
\<close>

class ik_domain = numeric_domain +
  fixes widen_ik :: "ikind \<Rightarrow> 'a::{bounded_semilattice_sup_bot, order_top} \<Rightarrow> 'a \<Rightarrow> 'a"
    and narrow_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and empty_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> bool"
  assumes widen_ik_ge1: "a \<le> widen_ik k a b"
    and widen_ik_ge2: "b \<le> widen_ik k a b"
    and narrow_ik_ge: "b \<le> a \<Longrightarrow> b \<le> narrow_ik k a b"
    and narrow_ik_le: "b \<le> a \<Longrightarrow> narrow_ik k a b \<le> a"
    and empty_ik_correct: "empty_ik k a \<longleftrightarrow> \<gamma> a \<inter> ik_range k = {}"

datatype 'a kd = KBot | KD ikind 'a | KTop

subsection \<open>Order and join\<close>

text \<open>Elements are comparable only at the same kind. A join across kinds is top, as
  in Goblint's value domain, which catches the lifter's \<^verbatim>\<open>IncompatibleIKinds\<close>.\<close>

instantiation kd :: (ik_domain) order_bot
begin

fun less_eq_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> bool" where
  "less_eq_kd KBot _ \<longleftrightarrow> True"
| "less_eq_kd _ KTop \<longleftrightarrow> True"
| "less_eq_kd (KD k a) (KD l b) \<longleftrightarrow> k = l \<and> a \<le> b"
| "less_eq_kd _ _ \<longleftrightarrow> False"

definition less_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> bool" where
  "less_kd a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

definition bot_kd :: "'a kd" where "bot_kd = KBot"

instance proof
  fix x y z :: "'a kd"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_kd_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) (auto intro: antisym)
  show "bot \<le> x" by (simp add: bot_kd_def)
qed

end

instantiation kd :: (ik_domain) order_top
begin

definition top_kd :: "'a kd" where "top_kd = KTop"

instance proof
  fix x :: "'a kd"
  show "x \<le> top" by (cases x) (simp_all add: top_kd_def)
qed

end

instantiation kd :: (ik_domain) semilattice_sup
begin

fun sup_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
  "sup_kd KBot b = b"
| "sup_kd a KBot = a"
| "sup_kd (KD k a) (KD l b) = (if k = l then KD k (a \<squnion> b) else KTop)"
| "sup_kd _ _ = KTop"

instance proof
  fix x y z :: "'a kd"
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) auto
qed

end

instance kd :: (ik_domain) bounded_semilattice_sup_bot ..

subsection \<open>Widening and narrowing at the operands' kind\<close>

text \<open>Two operands of one kind are widened or narrowed by the component domain at that
  kind. Widening operands of different kinds gives \<^const>\<open>KTop\<close>.\<close>

instantiation kd :: (ik_domain) warrowing
begin

fun widen_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
  "widen_kd KBot b = b"
| "widen_kd a KBot = a"
| "widen_kd (KD k a) (KD l b) = (if k = l then KD k (widen_ik k a b) else KTop)"
| "widen_kd _ _ = KTop"

fun narrow_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
  "narrow_kd KTop b = b"
| "narrow_kd (KD k a) (KD l b) = (if k = l then KD k (narrow_ik k a b) else KD k a)"
| "narrow_kd a _ = KBot"

instance proof
  fix a b :: "'a kd"
  show "a \<le> a \<nabla> b" by (cases a; cases b) (simp_all add: widen_ik_ge1)
  show "b \<le> a \<nabla> b" by (cases a; cases b) (simp_all add: widen_ik_ge2)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b"
    by (cases a; cases b) (auto simp: narrow_ik_ge)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a"
    by (cases a; cases b) (auto simp: narrow_ik_le)
qed

end

subsection \<open>Concretization\<close>

text \<open>A kind-tagged element denotes the integers of its component that its kind can
  represent.\<close>

fun gamma_kd :: "'a::ik_domain kd \<Rightarrow> int set" where
  "gamma_kd KBot = {}"
| "gamma_kd (KD k a) = \<gamma> a \<inter> ik_range k"
| "gamma_kd KTop = UNIV"

instantiation kd :: (ik_domain) numeric_domain
begin

fun is_empty_kd :: "'a kd \<Rightarrow> bool" where
  "is_empty_kd KBot \<longleftrightarrow> True"
| "is_empty_kd (KD k a) \<longleftrightarrow> empty_ik k a"
| "is_empty_kd KTop \<longleftrightarrow> False"

fun to_string_kd :: "'a kd \<Rightarrow> String.literal" where
  "to_string_kd KBot = to_string (bot :: 'a)"
| "to_string_kd (KD k a) = to_string a"
| "to_string_kd KTop = sym_top"

definition gamma_kd_def [simp]: "numeric_domain_class.gamma (a :: 'a kd) = gamma_kd a"

instance proof
  fix a b :: "'a kd"
  show "\<gamma> (bot :: 'a kd) = {}" by (simp add: bot_kd_def)
  show "\<gamma> (top :: 'a kd) = UNIV" by (simp add: top_kd_def)
  show "a \<le> b \<Longrightarrow> \<gamma> a \<subseteq> \<gamma> b"
    by (cases a; cases b) (auto dest: gamma_mono)
  show "is_empty a \<longleftrightarrow> \<gamma> a = {}"
    by (cases a) (simp_all add: empty_ik_correct)
qed

end

end
