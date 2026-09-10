theory DG_State
  imports "Voblint_Domain.Abstract_Domain"
begin

section \<open>The value a D/G unknown carries\<close>

text \<open>An analysis chooses a flow-sensitive answer domain \<open>D\<close> and a
  flow-insensitive side-effect domain \<open>G\<close>. The framework keeps them opaque and
  stores them in separate components of \<open>dg_state\<close>; it never copies a global
  component into a local answer.

  This theory is that carrier and its order, and nothing else: no address, no
  solver tree, no transfer. Everything above it only projects and repacks the
  two components, which is what makes those constructions independent of the
  concrete domains.\<close>



subsection \<open>A lattice copy type for D-times-G unknown values\<close>
text \<open>
  The solver's single value type must order local and global halves
  componentwise. Raw pairs cannot: this repository loads
  \<open>HOL-Library.Product_Lexorder\<close>, so every \<open>'l * 'g\<close> in scope already
  carries the lexicographic order, and a componentwise instance for the same
  type would clash with it. \<open>dg_state\<close> is a distinct carrier so that both
  orders can coexist.
\<close>

datatype ('l, 'g) dg_state = DG (locals: 'l) (globs: 'g)

instantiation dg_state :: (ord, ord) ord
begin

definition less_eq_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> bool" where
  "less_eq_dg_state d1 d2 = (locals d1 \<le> locals d2 \<and> globs d1 \<le> globs d2)"

definition less_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> bool" where
  "less_dg_state d1 d2 = (d1 \<le> d2 \<and> \<not> d2 \<le> d1)"

instance ..

end

instance dg_state :: (order, order) order
proof intro_classes
  fix x y z :: "('a, 'b) dg_state"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_dg_state_def)
  show "x \<le> x" by (simp add: less_eq_dg_state_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_dg_state_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_dg_state_def intro: dg_state.expand antisym)
qed

instantiation dg_state :: (semilattice_sup, semilattice_sup) semilattice_sup
begin

definition sup_dg_state :: "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state" where
  "sup_dg_state d1 d2 = DG (locals d1 \<squnion> locals d2) (globs d1 \<squnion> globs d2)"

instance
  by standard (auto simp: less_eq_dg_state_def sup_dg_state_def)

end

instantiation dg_state :: (order_bot, order_bot) order_bot
begin

definition bot_dg_state :: "('a, 'b) dg_state" where
  "bot_dg_state = DG bot bot"

instance
  by standard (simp add: less_eq_dg_state_def bot_dg_state_def)

end

instance dg_state ::
  (bounded_semilattice_sup_bot, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

subsection \<open>Reading the two components back\<close>

text \<open>Every construction above this theory projects and repacks, so the four
  projection equations and the constructor comparison are what its proofs
  should meet instead of the instance definitions. The order itself stays
  unfolded: \<open>less_eq_dg_state_def\<close> is not a simp rule, because a bound
  between two values that are not both constructor terms reads better as one
  \<open>\<le>\<close> than as a conjunction of two.\<close>

lemma locals_sup [simp]:
  fixes x y :: "('a::semilattice_sup, 'b::semilattice_sup) dg_state"
  shows "locals (x \<squnion> y) = locals x \<squnion> locals y"
  by (simp add: sup_dg_state_def)

lemma globs_sup [simp]:
  fixes x y :: "('a::semilattice_sup, 'b::semilattice_sup) dg_state"
  shows "globs (x \<squnion> y) = globs x \<squnion> globs y"
  by (simp add: sup_dg_state_def)

lemma locals_bot [simp]:
  "locals (bot :: ('a::order_bot, 'b::order_bot) dg_state) = bot"
  by (simp add: bot_dg_state_def)

lemma globs_bot [simp]:
  "globs (bot :: ('a::order_bot, 'b::order_bot) dg_state) = bot"
  by (simp add: bot_dg_state_def)

lemma DG_le_DG [simp]:
  fixes d d' :: "'a::ord" and g g' :: "'b::ord"
  shows "DG d g \<le> DG d' g' \<longleftrightarrow> d \<le> d' \<and> g \<le> g'"
  by (simp add: less_eq_dg_state_def)

instantiation dg_state :: (bounded_warrowing, bounded_warrowing) bounded_warrowing
begin

definition widen_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "widen_dg_state a b = DG (widen (locals a) (locals b)) (widen (globs a) (globs b))"

definition narrow_dg_state ::
  "('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state \<Rightarrow> ('a, 'b) dg_state"
where
  "narrow_dg_state a b = DG (narrow (locals a) (locals b)) (narrow (globs a) (globs b))"

instance
  by standard
    (simp_all add: less_eq_dg_state_def widen_dg_state_def narrow_dg_state_def
      narrowing_class.narrow_ge narrowing_class.narrow_le
      widening_class.widen_ge1 widening_class.widen_ge2)

end

end
