theory Order_Lattice
  imports "Voblint_Domain.Abstract_Domain" "Voblint_Domain.State_Concretization"
    "HOL-Library.Product_Lexorder"
begin

section \<open>Order lattice\<close>

text \<open>
  \<open>relc\<close> tracks a finite set of known pairwise-ordered variables, \<open>(x, y)\<close>
  meaning \<open>x \<le> y\<close> at every store the value describes. No closure: two known
  facts \<open>x \<le> y\<close> and \<open>y \<le> z\<close> do not automatically yield \<open>x \<le> z\<close> in this
  carrier. This is deliberately the least amount of relational structure that
  is still relational (a pair of variables, not one) and not \<open>abs_state\<close>
  (no \<open>vname \<Rightarrow> 'a\<close> function type anywhere in the carrier). Its concretization is a
  set of stores, not of integers, so it is an \<^class>\<open>executable_domain\<close> but not a
  \<^class>\<open>numeric_domain\<close>.
\<close>

subsection \<open>Carrier and order\<close>

datatype relc = RelBot | RelC (relc_pairs: "(vname \<times> vname) set")

text \<open>Order is reverse inclusion on the constraint set: more known pairs is
  more information, hence lower (more precise) in the abstract-interpretation
  order. \<open>sup\<close> keeps only the pairs both sides agree on.

  \<open>RelBot\<close> is a separate explicit constructor rather than \<open>RelC UNIV\<close> (the
  most-constrained set, "every pair known ordered"): representing \<open>UNIV\<close>
  forces the code generator to use the \<open>Coset\<close> branch of HOL's executable-set
  representation, and the stock library does not give every set operation
  (subset test among them) a code equation for every \<open>Set\<close>/\<open>Coset\<close>
  combination over an infinite element type such as \<open>vname\<close> -- confirmed
  directly: \<open>RelC UNIV\<close> batch-checked and even unit-tested via \<open>value\<close>
  cleanly, but running it through the solver raised \<open>exception Match\<close> in
  the generated code the first time a genuine \<open>Coset\<close>/\<open>Coset\<close> combination
  arose. Keeping \<open>RelC\<close>'s field always finite avoids the gap entirely: no
  value this theory ever constructs is a \<open>Coset\<close>.\<close>

instantiation relc :: bounded_semilattice_sup_bot
begin

fun less_eq_relc :: "relc \<Rightarrow> relc \<Rightarrow> bool" where
  "less_eq_relc RelBot _ = True"
| "less_eq_relc (RelC _) RelBot = False"
| "less_eq_relc (RelC a) (RelC b) = (b \<subseteq> a)"

definition less_relc :: "relc \<Rightarrow> relc \<Rightarrow> bool" where
  "less_relc a b \<longleftrightarrow> a \<le> b \<and> \<not> b \<le> a"

fun sup_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "sup_relc RelBot b = b"
| "sup_relc a RelBot = a"
| "sup_relc (RelC a) (RelC b) = RelC (a \<inter> b)"

definition bot_relc :: relc where
  "bot_relc = RelBot"

instance
proof intro_classes
  fix x y z :: relc
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_relc_def)
  show "x \<le> x" by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by (cases x; cases y; cases z) auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" by (cases x; cases y) auto
  show "x \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<squnion> y" by (cases x; cases y) auto
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x" by (cases x; cases y; cases z) auto
  show "bot \<le> x" by (cases x) (simp_all add: bot_relc_def)
qed

end

lemma bot_relc_eq [simp]: "(\<bottom> :: relc) = RelBot"
  by (simp add: bot_relc_def)

text \<open>\<open>\<top>\<close> is the empty constraint set: vacuously true of every pair, so its
  concretization is \<open>UNIV\<close> (\<open>gamma_relc_top\<close>).\<close>

instantiation relc :: order_top
begin

definition top_relc :: relc where
  "top_relc = RelC {}"

instance by intro_classes (case_tac a; simp add: top_relc_def)

end

text \<open>The vendored TD solver's \<open>TD_side_upd_rule\<close> locale fixes its equation
  value type at sort \<open>{bounded_semilattice_sup_bot, warrowing}\<close> uniformly --
  every update rule in the solver menu needs it, not only the \<open>warrow\<close>
  entry, even on a loop-free equation system where widening is never
  actually invoked. \<open>widen = sup\<close> reuses the join laws already proved
  above; \<open>narrow a b = b\<close> is the simplest sound choice ("accept the
  incoming value, refine nothing") -- consistent with this carrier's own
  no-closure, no-normalization scope.\<close>

instantiation relc :: warrowing
begin

definition widen_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "widen_relc a b = a \<squnion> b"

definition narrow_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where
  "narrow_relc a b = b"

instance
proof intro_classes
  fix a b :: relc
  show "a \<le> a \<nabla> b" by (simp add: widen_relc_def)
  show "b \<le> a \<nabla> b" by (simp add: widen_relc_def)
  show "b \<le> a \<Longrightarrow> b \<le> a \<Delta> b" by (simp add: narrow_relc_def)
  show "b \<le> a \<Longrightarrow> a \<Delta> b \<le> a" by (simp add: narrow_relc_def)
qed

end

subsection \<open>Concretization\<close>

text \<open>
  A set of pairs denotes the stores satisfying \<open>s x <= s y\<close> for each pair;
  \<open>RelBot\<close> denotes no store. Concretization is monotone in the order.
\<close>

fun gamma_relc :: "relc \<Rightarrow> store set" where
  "gamma_relc RelBot = {}"
| "gamma_relc (RelC ps) = {s. \<forall>(x, y) \<in> ps. s x \<le> s y}"

adhoc_overloading gamma_S == gamma_relc

lemma gamma_relc_top [simp]: "\<lbrakk>\<top> :: relc\<rbrakk> = UNIV"
  unfolding top_relc_def by simp

lemma gamma_relc_mono:
  fixes d d' :: relc
  assumes "d \<le> d'"
  shows "\<lbrakk>d\<rbrakk> \<subseteq> \<lbrakk>d'\<rbrakk>"
  using assms by (cases d; cases d') auto

text \<open>
  Executable membership reader. \<open>RelBot\<close> answers \<open>True\<close> for every pair: its
  concretization is empty, so every fact holds of it vacuously, and it never needs
  to materialize \<open>UNIV\<close>.
\<close>

fun relc_has :: "vname \<Rightarrow> vname \<Rightarrow> relc \<Rightarrow> bool" where
  "relc_has x y RelBot = True"
| "relc_has x y (RelC ps) = ((x, y) \<in> ps)"

subsection \<open>Forgetting a variable\<close>

text \<open>The one operation every imprecise fallback reuses.\<close>

fun forget_relc :: "vname \<Rightarrow> relc \<Rightarrow> relc" where
  "forget_relc x RelBot = RelBot"
| "forget_relc x (RelC ps) = RelC {(a, b) \<in> ps. a \<noteq> x \<and> b \<noteq> x}"

lemma forget_relc_sound[intro]:
  assumes "s \<in> \<lbrakk>d\<rbrakk>"
  shows "s(x := v) \<in> \<lbrakk>forget_relc x d\<rbrakk>"
  using assms by (cases d) auto

subsection \<open>Executable operations\<close>

text \<open>
  The notation follows Goblint's two-variable equality domain, which prints a
  conjunction \<open>{x=y \<and> z=y}\<close> and its extremes as \<open>\<bottom>\<close> and \<open>\<top>\<close>; here each conjunct is
  an ordering \<open>x\<le>y\<close>. \<open>vname \<times> vname\<close> is \<open>linorder\<close> (\<open>Product_Lexorder\<close>), so
  \<^const>\<open>sorted_list_of_set\<close> gives a deterministic enumeration.
\<close>

fun string_of_pairs :: "(vname \<times> vname) list \<Rightarrow> String.literal" where
  "string_of_pairs [] = STR ''''"
| "string_of_pairs [(x, y)] = x + sym_le + y"
| "string_of_pairs ((x, y) # p # ps) =
      x + sym_le + y + STR '' '' + sym_and + STR '' '' + string_of_pairs (p # ps)"

instantiation relc :: executable_domain
begin

definition is_empty_relc :: "relc \<Rightarrow> bool" where
  "is_empty_relc d \<longleftrightarrow> d = RelBot"

definition to_string_relc :: "relc \<Rightarrow> String.literal" where
  "to_string_relc d =
     (case d of
        RelBot \<Rightarrow> sym_bottom
      | RelC ps \<Rightarrow>
          (if ps = {} then sym_top
           else STR ''{'' + string_of_pairs (sorted_list_of_set ps) + STR ''}''))"

instance ..

end

lemma is_empty_relc_gamma: "is_empty d \<longleftrightarrow> \<lbrakk>d\<rbrakk> = {}" for d :: relc
proof (cases d)
  case (RelC ps)
  then have "(\<lambda>_. 0) \<in> \<lbrakk>d\<rbrakk>" by auto
  with RelC show ?thesis by (auto simp: is_empty_relc_def)
qed (simp add: is_empty_relc_def)

lemma exact_emptiness_relc: "exact_emptiness (is_empty :: relc \<Rightarrow> bool) gamma_relc"
  by (rule exact_emptinessI) (rule is_empty_relc_gamma)

lemma to_string_relc_regression:
  "to_string RelBot = sym_bottom"
  "to_string (RelC {}) = sym_top"
  "to_string (RelC {(STR ''y'', STR ''z''), (STR ''x'', STR ''y'')}) =
     STR ''{x<le>y <and> y<le>z}''"
  by eval+

end
