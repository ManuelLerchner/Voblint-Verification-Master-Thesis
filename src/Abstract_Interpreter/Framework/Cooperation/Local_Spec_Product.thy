theory Local_Spec_Product
  imports "Voblint_Framework.DG_Spec_Sound"
begin

section \<open>The product carrier\<close>

text \<open>
  Two components run side by side on a pair of states. The pair is a datatype
  and not \<^typ>\<open>'a \<times> 'b\<close>, for the reason \<^typ>\<open>('l, 'g) dg_state\<close> is: this
  repository loads \<open>HOL-Library.Product_Lexorder\<close>, so raw pairs already carry
  the lexicographic order, and the product needs the componentwise one. Every
  instance below, including the solver's widening and narrowing, is
  componentwise.
\<close>

datatype ('a, 'b) analysis_product = Product (pleft: 'a) (pright: 'b)

instantiation analysis_product :: (ord, ord) ord
begin

definition less_eq_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> bool" where
  "less_eq_analysis_product p q \<longleftrightarrow> pleft p \<le> pleft q \<and> pright p \<le> pright q"

definition less_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> bool" where
  "less_analysis_product p q \<longleftrightarrow> p \<le> q \<and> \<not> q \<le> p"

instance ..

end

instance analysis_product :: (order, order) order
proof intro_classes
  fix x y z :: "('a, 'b) analysis_product"
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (simp add: less_analysis_product_def)
  show "x \<le> x" by (simp add: less_eq_analysis_product_def)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (auto simp: less_eq_analysis_product_def intro: order_trans)
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (auto simp: less_eq_analysis_product_def intro: analysis_product.expand antisym)
qed

instantiation analysis_product :: (semilattice_sup, semilattice_sup) semilattice_sup
begin

definition sup_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "sup_analysis_product p q = Product (pleft p \<squnion> pleft q) (pright p \<squnion> pright q)"

instance
  by standard (auto simp: less_eq_analysis_product_def sup_analysis_product_def)

end

instantiation analysis_product :: (order_bot, order_bot) order_bot
begin

definition bot_analysis_product :: "('a, 'b) analysis_product" where
  "bot_analysis_product = Product \<bottom> \<bottom>"

instance
  by standard (simp add: less_eq_analysis_product_def bot_analysis_product_def)

end

instance analysis_product ::
  (bounded_semilattice_sup_bot, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot ..

lemma Product_le_Product [simp]:
  "Product a b \<le> Product a' b' \<longleftrightarrow> a \<le> a' \<and> b \<le> b'"
  by (simp add: less_eq_analysis_product_def)

instantiation analysis_product ::
  ("{bounded_semilattice_sup_bot, warrowing}", "{bounded_semilattice_sup_bot, warrowing}") warrowing
begin

definition widen_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
where
  "widen_analysis_product p q = Product ((pleft p) \<nabla> (pleft q)) ((pright p) \<nabla> (pright q))"

definition narrow_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
where
  "narrow_analysis_product p q =
     Product ((pleft p) \<Delta> (pleft q)) ((pright p) \<Delta> (pright q))"

instance
  by standard
    (simp_all add: less_eq_analysis_product_def widen_analysis_product_def
      narrow_analysis_product_def narrowing_class.narrow_ge narrowing_class.narrow_le
      widening_class.widen_ge1 widening_class.widen_ge2)

end


end
