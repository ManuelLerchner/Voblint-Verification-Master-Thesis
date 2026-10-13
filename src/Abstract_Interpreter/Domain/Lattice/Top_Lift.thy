theory Top_Lift
  imports Abstract_Domain
begin

section \<open>A separate top element\<close>

text \<open>
  \<open>TL a\<close> is an element of the underlying lattice and \<open>TTop\<close> lies above all of them.
  A typed state uses \<open>TTop\<close> for the state that describes every store, typed or not,
  which no typed state can express: its own top still constrains each variable to the
  range of its kind.
\<close>

datatype 'a toplift = TTop | TL 'a

instantiation toplift :: (order) order
begin

fun less_eq_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> bool" where
  "less_eq_toplift _ TTop \<longleftrightarrow> True"
| "less_eq_toplift TTop (TL b) \<longleftrightarrow> False"
| "less_eq_toplift (TL a) (TL b) \<longleftrightarrow> a \<le> b"

definition less_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> bool" where
  "less_toplift a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

instance proof
  fix x y z :: "'a toplift"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_toplift_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) (auto intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) auto
qed

end

instantiation toplift :: (order_bot) order_bot
begin
definition bot_toplift :: "'a toplift" where "bot_toplift = TL bot"
instance by standard (case_tac a, simp_all add: bot_toplift_def)
end

instantiation toplift :: (order) order_top
begin
definition top_toplift :: "'a toplift" where "top_toplift = TTop"
instance by standard (case_tac a, simp_all add: top_toplift_def)
end

instantiation toplift :: (semilattice_sup) semilattice_sup
begin

fun sup_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "sup_toplift (TL a) (TL b) = TL (a \<squnion> b)"
| "sup_toplift _ _ = TTop"

instance proof
  fix x y z :: "'a toplift"
  show "x \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y" by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) auto
qed

end

instance toplift :: (bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

instantiation toplift :: ("{order, warrowing}") warrowing
begin

fun widen_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "widen_toplift (TL a) (TL b) = TL (a \<nabla> b)"
| "widen_toplift _ _ = TTop"

fun narrow_toplift :: "'a toplift \<Rightarrow> 'a toplift \<Rightarrow> 'a toplift" where
  "narrow_toplift TTop b = b"
| "narrow_toplift (TL a) (TL b) = TL (a \<Delta> b)"
| "narrow_toplift (TL a) TTop = TL a"

instance proof
  fix a b :: "'a toplift"
  show "a \<le> a \<nabla> b" by (cases a; cases b) (simp_all add: widen_ge1)
  show "b \<le> a \<nabla> b" by (cases a; cases b) (simp_all add: widen_ge2)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b" by (cases a; cases b) (simp_all add: narrow_ge)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a" by (cases a; cases b) (simp_all add: narrow_le)
qed

end

end
