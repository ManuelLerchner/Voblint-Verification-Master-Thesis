theory DG_State
  imports Transfer_Interface State_Restriction "Voblint_Domain.Nonrelational_Reachability"
    "Voblint_Solver.Strategy_Tree_Post_Solution" "Voblint_Solver.Strategy_Tree_Side_Buffering"
    "Voblint_Solver.Strategy_Tree_Fold"
    "Voblint_CFG.CFG_Transfer"
begin

section \<open>The D/G framework core\<close>

text \<open>An analysis chooses a flow-sensitive answer domain \<open>D\<close> and a
  flow-insensitive side-effect domain \<open>G\<close>. The framework keeps them opaque and stores
  them in separate components of \<open>dg_state\<close>; it never copies a global component
  into a local answer.

  \<open>dg_edge_tree\<close> and \<open>dg_combine_tree\<close> only project and repack those
  components, so their construction is independent of the concrete domains.\<close>



subsection \<open>A lattice copy type for D-times-G unknown values\<close>
text \<open>
  The solver's single value type must order local and global halves
  componentwise. Raw pairs cannot: \<open>CFG_Def\<close> imports
  \<open>HOL-Library.Product_Lexorder\<close>, so \<open>'l * 'g\<close> already carries the
  lexicographic order throughout this repository. \<open>dg_state\<close> supplies a
  distinct componentwise-ordered carrier.
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
