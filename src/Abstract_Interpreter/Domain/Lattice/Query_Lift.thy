theory Query_Lift
  imports Main
begin

unbundle lattice_syntax

section \<open>Lifting a domain with a fresh bottom and top\<close>

text \<open>
  Goblint answers \<open>EvalInt\<close> in \<open>Lattice.Lift(IntDomTuple)\<close>
  (\<open>valueDomainQueries.ml\<close> at \<open>0dc12d355\<close>): the integer domain with a fresh
  \<open>\<bottom>\<close> and \<open>\<top>\<close> around it. The fresh top lets an analysis that does not
  understand a query decline it without knowing the value domain's own top,
  and the fresh bottom marks a query asked of an unreachable state. This is
  kept apart from the reachability lift of the solver's carrier: the two
  bottoms mean different things, and only this one has a fresh top.
\<close>

datatype 'a query_lift = QBot | QLifted 'a | QTop

instantiation query_lift :: (ord) ord
begin

fun less_eq_query_lift :: "'a query_lift \<Rightarrow> 'a query_lift \<Rightarrow> bool" where
  "less_eq_query_lift QBot _ = True"
| "less_eq_query_lift _ QTop = True"
| "less_eq_query_lift (QLifted a) (QLifted b) = (a \<le> b)"
| "less_eq_query_lift _ _ = False"

definition less_query_lift :: "'a query_lift \<Rightarrow> 'a query_lift \<Rightarrow> bool" where
  "less_query_lift a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

instance ..

end

instance query_lift :: (order) order
proof
  fix x y z :: "'a query_lift"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
    by (simp add: less_query_lift_def)
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) auto
qed

instantiation query_lift :: (order) order_bot
begin
definition bot_query_lift :: "'a query_lift" where "bot_query_lift = QBot"
instance by standard (simp add: bot_query_lift_def)
end

instantiation query_lift :: (order) order_top
begin
definition top_query_lift :: "'a query_lift" where "top_query_lift = QTop"
instance
proof
  fix x :: "'a query_lift"
  show "x \<le> \<top>"
    by (cases x) (simp_all add: top_query_lift_def)
qed
end

text \<open>
  \<open>QTop\<close> is the identity of the meet and \<open>QBot\<close> absorbs it; two lifted
  values meet in the underlying domain.
\<close>

instantiation query_lift :: (inf) inf
begin

fun inf_query_lift :: "'a query_lift \<Rightarrow> 'a query_lift \<Rightarrow> 'a query_lift" where
  "inf_query_lift QBot _ = QBot"
| "inf_query_lift _ QBot = QBot"
| "inf_query_lift QTop b = b"
| "inf_query_lift a QTop = a"
| "inf_query_lift (QLifted a) (QLifted b) = QLifted (a \<sqinter> b)"

instance ..

end

instance query_lift :: (semilattice_inf) semilattice_inf
proof
  fix x y z :: "'a query_lift"
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
qed

subsection \<open>Concretization\<close>

text \<open>
  A lifted value denotes what the underlying domain says; the fresh bottom
  denotes nothing and the fresh top everything. An exact underlying meet
  stays exact after lifting.
\<close>

fun gamma_query_lift :: "('a \<Rightarrow> 'b set) \<Rightarrow> 'a query_lift \<Rightarrow> 'b set" where
  "gamma_query_lift \<gamma> QBot = {}"
| "gamma_query_lift \<gamma> (QLifted a) = \<gamma> a"
| "gamma_query_lift \<gamma> QTop = UNIV"

lemma gamma_query_lift_top [simp]: "gamma_query_lift \<gamma> \<top> = UNIV"
  by (simp add: top_query_lift_def)

lemma gamma_query_lift_bot [simp]: "gamma_query_lift \<gamma> \<bottom> = {}"
  by (simp add: bot_query_lift_def)

lemma gamma_query_lift_inf:
  assumes "\<And>a b. \<gamma> (a \<sqinter> b) = \<gamma> a \<inter> \<gamma> b"
  shows "gamma_query_lift \<gamma> (x \<sqinter> y) = gamma_query_lift \<gamma> x \<inter> gamma_query_lift \<gamma> y"
  using assms by (cases x; cases y) simp_all

end
