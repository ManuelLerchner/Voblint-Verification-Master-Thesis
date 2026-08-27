theory Kind_Tagged
  imports Abstract_Domain "TD.Update_rules"
begin

section \<open>Kind-tagged abstract values\<close>

text \<open>
  Goblint threads an \<open>ikind\<close> through \<open>top_of\<close>, the arithmetic, the joins and
  both convergence operators, so no interval it holds ever leaves the kind's
  range. Here the kind reaches the arithmetic and the conversions but not the
  convergence operators: \<^class>\<open>warrowing\<close> fixes \<open>widen\<close> and \<open>narrow\<close> at
  \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>, and the vendored solver demands exactly that
  signature of its value type. A widened bound therefore leaves the range,
  and the conversion at the next node has an operand it cannot represent.

  Tagging the value with its kind supplies the missing argument without
  touching the class. \<open>widen\<close> still has the class signature; it reads the
  kind off its own operands.
\<close>

datatype 'a kd = KBot | KD ikind 'a | KTop

text \<open>
  The tag is a horizontal sum rather than a pair because the class laws
  quantify over every value of the type, mismatched tags included, and a
  lawful answer needs one element below and one above all tagged cells.
  \<^const>\<open>KBot\<close> and \<^const>\<open>KTop\<close> exist for that reason alone: \<open>wf_kd\<close>
  below pins every cell a well-typed state builds to \<^const>\<open>KD\<close> at that
  variable's declared kind, and \<^const>\<open>KTop\<close> is unreachable from it.
\<close>

subsection \<open>Order\<close>

instantiation kd :: (order) order
begin

fun less_eq_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> bool" where
    "less_eq_kd KBot _ = True"
  | "less_eq_kd _ KTop = True"
  | "less_eq_kd KTop _ = False"
  | "less_eq_kd (KD _ _) KBot = False"
  | "less_eq_kd (KD k a) (KD l b) = (k = l \<and> a \<le> b)"

definition less_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> bool" where
  "less_kd x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof intro_classes
  fix x y z :: "'a kd"
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" by (rule less_kd_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) auto
qed

end

subsection \<open>Bottom and top\<close>

instantiation kd :: (order) "{bot,top}"
begin
definition "bot_kd = KBot"
definition "top_kd = KTop"
instance ..
end

instance kd :: (order) order_bot
  by intro_classes (simp add: bot_kd_def)

instance kd :: (order) order_top
proof intro_classes
  fix a :: "'a kd"
  show "a \<le> top" unfolding top_kd_def by (cases a) simp_all
qed

subsection \<open>Join\<close>

text \<open>
  Two cells at the same kind join componentwise. Two cells at different kinds
  have no common tagged upper bound -- neither is below the other and no
  \<^const>\<open>KD\<close> is above both -- so \<^const>\<open>KTop\<close> is the least one available.
\<close>

instantiation kd :: (semilattice_sup) semilattice_sup
begin

fun sup_kd :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
    "sup_kd KBot y = y"
  | "sup_kd x KBot = x"
  | "sup_kd KTop _ = KTop"
  | "sup_kd _ KTop = KTop"
  | "sup_kd (KD k a) (KD l b) = (if k = l then KD k (a \<squnion> b) else KTop)"

instance
proof intro_classes
  fix x y z :: "'a kd"
  show "x \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) auto
qed

end

instance kd :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

subsection \<open>Concretization\<close>

text \<open>
  A tagged cell denotes its component's denotation cut down to the tag's
  range. This is the kind-relative concretization the precise transfers need,
  obtained definitionally rather than as a separate relation: a cell for a
  variable of kind \<open>k\<close> denotes only values representable in \<open>k\<close>.

  \<^const>\<open>KTop\<close> and the kind's own top cell \<open>KD k top\<close> are distinct and denote
  different sets -- \<open>UNIV\<close> against \<^term>\<open>ik_range k\<close> -- which is exactly why
  \<open>kd_top_of\<close> below is the tagged cell and not \<^const>\<open>KTop\<close>. \<^const>\<open>KBot\<close>
  and \<open>KD k bot\<close> are likewise distinct with the same empty denotation, so
  emptiness is tested through a predicate rather than by comparison with
  \<^const>\<open>bot\<close>.
\<close>

definition gamma_kd :: "'a::sound_domain kd \<Rightarrow> int set" where
  "gamma_kd x =
     (case x of KBot \<Rightarrow> {} | KTop \<Rightarrow> UNIV | KD k a \<Rightarrow> gamma a \<inter> ik_range k)"

lemma gamma_kd_simps [simp]:
  "gamma_kd KBot = {}"
  "gamma_kd KTop = UNIV"
  "gamma_kd (KD k a) = gamma a \<inter> ik_range k"
  by (simp_all add: gamma_kd_def)

lemma gamma_kd_mono:
  fixes x y :: "'a::sound_domain kd"
  assumes "x \<le> y"
  shows "gamma_kd x \<subseteq> gamma_kd y"
  using assms by (cases x; cases y) (auto dest: gamma_mono[THEN subsetD])

definition kd_top_of :: "ikind \<Rightarrow> 'a::top kd" where
  "kd_top_of k = KD k top"

lemma gamma_kd_top_of [simp]:
  "gamma_kd (kd_top_of k :: 'a::sound_domain kd) = gamma (top :: 'a) \<inter> ik_range k"
  by (simp add: kd_top_of_def)

definition is_bot_kd :: "'a::sound_domain kd \<Rightarrow> bool" where
  "is_bot_kd x = (case x of KBot \<Rightarrow> True | KTop \<Rightarrow> False | KD k a \<Rightarrow> is_bot a)"

lemma is_bot_kd_sound: "is_bot_kd x \<Longrightarrow> gamma_kd x = {}"
  by (auto simp: is_bot_kd_def is_bot_correct split: kd.splits)

subsection \<open>Well-typed cells\<close>

text \<open>
  A cell is well-typed at \<open>k\<close> when it is tagged \<open>k\<close>, or is the untagged
  empty cell an unreached variable carries. Nothing else occurs in a state a
  well-typed program builds: every write goes through a conversion at the
  destination's declared kind, and every read of an undeclared name is
  rejected before the analysis runs. \<^const>\<open>KTop\<close> is therefore unreachable,
  which is what \<open>wf_kd_not_KTop\<close> says.
\<close>

definition wf_kd :: "ikind \<Rightarrow> 'a kd \<Rightarrow> bool" where
  "wf_kd k x = (x = KBot \<or> (\<exists>a. x = KD k a))"

lemma wf_kd_not_KTop: "wf_kd k x \<Longrightarrow> x \<noteq> KTop"
  by (auto simp: wf_kd_def)

lemma wf_kd_bot [simp, intro]: "wf_kd k bot"
  by (simp add: wf_kd_def bot_kd_def)

lemma wf_kd_KD [simp, intro]: "wf_kd k (KD k a)"
  by (simp add: wf_kd_def)

lemma wf_kd_top_of [simp, intro]: "wf_kd k (kd_top_of k)"
  by (simp add: wf_kd_def kd_top_of_def)

text \<open>
  Well-typedness at one kind is closed under the join, so a state built only
  from well-typed cells stays well-typed however many predecessors it merges.
  This is the step that makes the join's mismatched-tag branch unreachable
  rather than merely lawful.
\<close>

lemma wf_kd_sup [intro]:
  fixes x y :: "'a::semilattice_sup kd"
  assumes "wf_kd k x" "wf_kd k y"
  shows "wf_kd k (x \<squnion> y)"
  using assms by (auto simp: wf_kd_def)

subsection \<open>Components that can be cut down to a kind's range\<close>

text \<open>
  Widening a bound outward is what takes a value out of its kind's range, and
  the conversion at the next node then has an operand it cannot represent.
  Goblint never reaches that state because its widening saturates at the
  kind's own extremes. Doing the same here needs one operation the component
  must supply: a greatest element for the kind, and a cut-down against it.

  This is deliberately not a lattice meet. \<^class>\<open>bounded_semilattice_sup_bot\<close>
  has no \<open>inf\<close>, and the backward filters take their intersection as a locale
  parameter precisely because the general meet is not the one they want. What
  is needed here is weaker: a greatest lower bound against \<open>a_top_of k\<close> alone.
\<close>

class kind_clamp = bounded_semilattice_sup_bot +
  fixes a_top_of :: "ikind \<Rightarrow> 'a"
  fixes a_clamp :: "ikind \<Rightarrow> 'a \<Rightarrow> 'a"
  assumes a_clamp_le: "a_clamp k c \<le> c"
  assumes a_clamp_top: "a_clamp k c \<le> a_top_of k"
  assumes a_clamp_greatest: "a \<le> c \<Longrightarrow> a \<le> a_top_of k \<Longrightarrow> a \<le> a_clamp k c"

text \<open>
  A cell is in range when its component sits below its tag's greatest element.
  Every cell the analysis builds is: a conversion at the destination kind is
  the last step of every write, and \<open>a_clamp_top\<close> makes the widened cell one
  too.
\<close>

definition in_range_kd :: "ikind \<Rightarrow> 'a::kind_clamp kd \<Rightarrow> bool" where
  "in_range_kd k x = (case x of KBot \<Rightarrow> True | KTop \<Rightarrow> False | KD l a \<Rightarrow> l = k \<and> a \<le> a_top_of k)"

lemma in_range_kd_wf: "in_range_kd k x \<Longrightarrow> wf_kd k x"
  by (auto simp: in_range_kd_def wf_kd_def split: kd.splits)

lemma in_range_kd_bot [simp, intro]: "in_range_kd k (bot :: 'a::kind_clamp kd)"
  by (simp add: in_range_kd_def bot_kd_def)

text \<open>
  \<open>kd_range_top\<close> is the greatest cell at \<open>k\<close> that is still in range. It is not
  \<open>kd_top_of k\<close>: that tags the component's lattice top, which for an interval
  is the unbounded one. The two denote the same set of integers, since the tag
  cuts either down to \<^term>\<open>ik_range k\<close>, but only this one is a value the
  conversions can represent.
\<close>

definition kd_range_top :: "ikind \<Rightarrow> 'a::kind_clamp kd" where
  "kd_range_top k = KD k (a_top_of k)"

lemma in_range_kd_range_top [simp, intro]:
  "in_range_kd k (kd_range_top k :: 'a::kind_clamp kd)"
  by (simp add: in_range_kd_def kd_range_top_def)

lemma in_range_kd_sup [intro]:
  fixes x y :: "'a::kind_clamp kd"
  assumes "in_range_kd k x" "in_range_kd k y"
  shows "in_range_kd k (x \<squnion> y)"
  using assms by (cases x; cases y) (auto simp: in_range_kd_def)

subsection \<open>Widening and narrowing\<close>

text \<open>
  \<^class>\<open>warrowing\<close> fixes \<open>widen\<close> at \<^typ>\<open>'a \<Rightarrow> 'a \<Rightarrow> 'a\<close>, which is why the
  kind could not reach it before. Here it arrives on the operands: a matched
  pair widens its components and cuts the result down to the tag's range, so a
  widened cell stays representable and the conversion at the next node has an
  operand it can keep.

  The cut is guarded. Clamping shrinks, so an operand already outside the
  range would break \<open>a \<le> a \<nabla> b\<close> -- the very law the solver's termination
  argument rests on. Widening two such operands therefore falls back to the
  component's own answer, which satisfies the law unconditionally. That branch
  is total but unreachable: \<open>in_range_kd\<close> holds of every cell the analysis
  builds, and \<open>widen_kd_in_range\<close> below shows widening preserves it.

  Every unmatched shape answers \<^const>\<open>KTop\<close> for widening and keeps the left
  operand for narrowing, both of which discharge their laws with no side
  condition.
\<close>

instantiation kd :: (kind_clamp) kind_clamp
begin
definition "a_top_of_kd k = kd_range_top k"
definition "a_clamp_kd k x =
   (case x of KBot \<Rightarrow> KBot | KTop \<Rightarrow> kd_range_top k
    | KD l a \<Rightarrow> if l = k then KD k (a_clamp k a) else KBot)"
instance
proof intro_classes
  fix k :: ikind and a c :: "'a kd"
  show "a_clamp k c \<le> c"
    by (cases c) (auto simp: a_clamp_kd_def kd_range_top_def a_clamp_le)
  show "a_clamp k c \<le> a_top_of k"
    by (cases c) (auto simp: a_clamp_kd_def a_top_of_kd_def kd_range_top_def a_clamp_top)
  show "a \<le> c \<Longrightarrow> a \<le> a_top_of k \<Longrightarrow> a \<le> a_clamp k c"
    by (cases a; cases c)
       (auto simp: a_clamp_kd_def a_top_of_kd_def kd_range_top_def a_clamp_greatest)
qed
end

instantiation kd :: ("{kind_clamp,warrowing}") warrowing
begin

fun widen_kd_core :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
    "widen_kd_core KBot y = y"
  | "widen_kd_core x KBot = x"
  | "widen_kd_core (KD k a) (KD l b) =
       (if k \<noteq> l then KTop
        else if a \<le> a_top_of k \<and> b \<le> a_top_of k
             then KD k (a_clamp k (a \<nabla> b))
             else KD k (a \<nabla> b))"
  | "widen_kd_core _ _ = KTop"

fun narrow_kd_core :: "'a kd \<Rightarrow> 'a kd \<Rightarrow> 'a kd" where
    "narrow_kd_core (KD k a) (KD l b) = (if k = l then KD k (a \<Delta> b) else KD k a)"
  | "narrow_kd_core x _ = x"

definition "widen (x :: 'a kd) y = widen_kd_core x y"
definition "narrow (x :: 'a kd) y = narrow_kd_core x y"

instance
proof intro_classes
  fix a b :: "'a kd"
  show "a \<le> a \<nabla> b"
    unfolding widen_kd_def
    by (cases a; cases b)
       (auto simp: widen_ge1 a_clamp_greatest intro: order_trans)
  show "b \<le> a \<nabla> b"
    unfolding widen_kd_def
    by (cases a; cases b)
       (auto simp: widen_ge2 a_clamp_greatest intro: order_trans)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b"
    unfolding narrow_kd_def
    by (cases a; cases b) (auto simp: narrow_ge)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a"
    unfolding narrow_kd_def
    by (cases a; cases b) (auto simp: narrow_le)
qed

end

text \<open>
  The invariant the whole construction exists for: widening a pair of in-range
  cells answers an in-range cell. Composed with \<open>in_range_kd_sup\<close>, every state
  the solver reaches through joins and widenings stays inside its variables'
  declared kinds, so no conversion downstream is ever handed an operand it
  cannot represent.
\<close>

lemma widen_kd_in_range [intro]:
  fixes x y :: "'a::{kind_clamp,warrowing} kd"
  assumes "in_range_kd k x" "in_range_kd k y"
  shows "in_range_kd k (x \<nabla> y)"
  using assms
  unfolding widen_kd_def
  by (cases x; cases y) (auto simp: in_range_kd_def a_clamp_top)

lemma narrow_kd_in_range [intro]:
  fixes x y :: "'a::{kind_clamp,warrowing} kd"
  assumes "in_range_kd k x" "in_range_kd k y" "y \<le> x"
  shows "in_range_kd k (x \<Delta> y)"
  using assms
  unfolding narrow_kd_def
  by (cases x; cases y)
     (auto simp: in_range_kd_def intro: order_trans[OF narrow_le])

end
