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
  "widen_analysis_product p q = Product (widen (pleft p) (pleft q)) (widen (pright p) (pright q))"

definition narrow_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
where
  "narrow_analysis_product p q =
     Product (narrow (pleft p) (pleft q)) (narrow (pright p) (pright q))"

instance
  by standard
    (simp_all add: less_eq_analysis_product_def widen_analysis_product_def
      narrow_analysis_product_def narrowing_class.narrow_ge narrowing_class.narrow_le
      widening_class.widen_ge1 widening_class.widen_ge2)

end

section \<open>Composing two components\<close>

text \<open>
  Every operation of the product applies the two components' operations side by
  side. Both components receive the same answers: the product asks the questions
  of both and hands the collected answers to each, so each component sees what
  the other knows. The concretization is the intersection, and the handler meets
  the two answers, as Goblint's \<open>MCP.query\<close> meets the answers of all analyses.
\<close>

definition pmap :: "('a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b) \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
where
  "pmap f g p = Product (f (pleft p)) (g (pright p))"

definition pmap2 ::
  "('a \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> ('b \<Rightarrow> 'b \<Rightarrow> 'b)
   \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product"
where
  "pmap2 f g p q = Product (f (pleft p) (pleft q)) (g (pright p) (pright q))"

text \<open>
  A call enters with every pair of the components' alternatives, as Goblint's
  \<open>MCP.enter\<close> takes the Cartesian product of the alternative lists (\<open>mCP.ml\<close>
  line 539 at \<open>5320a6b7\<close>). Each component's list covers the concrete entry on
  its own, so some pair covers it for both.
\<close>

definition prod_enter ::
  "('a \<Rightarrow> 'a enter_result list) \<Rightarrow> ('b \<Rightarrow> 'b enter_result list)
   \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product enter_result list"
where
  "prod_enter f g p =
     [(Product c1 c2, Product e1 e2). (c1, e1) \<leftarrow> f (pleft p), (c2, e2) \<leftarrow> g (pright p)]"

definition gamma_prod :: "('a \<Rightarrow> 's set) \<Rightarrow> ('b \<Rightarrow> 's set) \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> 's set"
where
  "gamma_prod g1 g2 p = g1 (pleft p) \<inter> g2 (pright p)"

definition qry_prod ::
  "('a \<Rightarrow> answers) \<Rightarrow> ('b \<Rightarrow> answers) \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> answers"
where
  "qry_prod q1 q2 p q = q1 (pleft p) q \<sqinter> q2 (pright p) q"

definition qs_prod ::
  "(edge_action \<Rightarrow> 'a \<Rightarrow> query list) \<Rightarrow> (edge_action \<Rightarrow> 'b \<Rightarrow> query list)
   \<Rightarrow> edge_action \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> query list"
where
  "qs_prod qs1 qs2 a p = qs1 a (pleft p) @ qs2 a (pright p)"

lemma local_spec_step_pmap:
  "local_spec_step (pmap sk1 sk2) (\<lambda>x e. pmap (asn1 x e) (asn2 x e))
     (\<lambda>c x. pmap (sp1 c x) (sp2 c x)) (\<lambda>b pol. pmap (br1 b pol) (br2 b pol))
     (\<lambda>p. pmap (bd1 p) (bd2 p)) (\<lambda>e p. pmap (rt1 e p) (rt2 e p))
     (\<lambda>v. pmap (ev1 v) (ev2 v)) a
   = pmap (local_spec_step sk1 asn1 sp1 br1 bd1 rt1 ev1 a)
       (local_spec_step sk2 asn2 sp2 br2 bd2 rt2 ev2 a)"
  by (cases a) simp_all

theorem product_local_spec:
  assumes "sound_local_dg_spec q1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1 g1 \<G>"
    and "sound_local_dg_spec q2 sk2 asn2 sp2 br2 bd2 rt2 en2 ev2 ce2 ca2 g2 \<G>"
  shows "sound_local_dg_spec (qry_prod q1 q2)
           (\<lambda>A. pmap (sk1 A) (sk2 A))
           (\<lambda>A x e. pmap (asn1 A x e) (asn2 A x e))
           (\<lambda>A c x. pmap (sp1 A c x) (sp2 A c x))
           (\<lambda>A b pol. pmap (br1 A b pol) (br2 A b pol))
           (\<lambda>A p. pmap (bd1 A p) (bd2 A p))
           (\<lambda>A e p. pmap (rt1 A e p) (rt2 A e p))
           (\<lambda>ci. prod_enter (en1 ci) (en2 ci))
           (\<lambda>A v. pmap (ev1 A v) (ev2 A v))
           (\<lambda>ci. pmap2 (ce1 ci) (ce2 ci)) (\<lambda>ci. pmap2 (ca1 ci) (ca2 ci))
           (gamma_prod g1 g2) \<G>"
proof -
  interpret A: sound_local_dg_spec q1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1 g1 \<G>
    by (fact assms(1))
  interpret B: sound_local_dg_spec q2 sk2 asn2 sp2 br2 bd2 rt2 en2 ev2 ce2 ca2 g2 \<G>
    by (fact assms(2))
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d')
    then show ?case
      by (auto simp: gamma_prod_def less_eq_analysis_product_def
          dest: A.gammaD_mono B.gammaD_mono)
  next
    case (2 a d Ans)
    let ?O = "Collect (eval_query.oracle_holds Ans)"
    have "edge_collect a (gamma_prod g1 g2 d \<inter> ?O)
            \<subseteq> edge_collect a (g1 (pleft d) \<inter> ?O) \<inter> edge_collect a (g2 (pright d) \<inter> ?O)"
      by (intro Int_greatest edge_collect_mono) (auto simp: gamma_prod_def)
    also have "\<dots> \<subseteq> gamma_prod g1 g2
                  (pmap (local_spec_step (sk1 Ans) (asn1 Ans) (sp1 Ans) (br1 Ans) (bd1 Ans)
                           (rt1 Ans) (ev1 Ans) a)
                        (local_spec_step (sk2 Ans) (asn2 Ans) (sp2 Ans) (br2 Ans) (bd2 Ans)
                           (rt2 Ans) (ev2 Ans) a) d)"
      using A.step_sound_local[of a "pleft d" Ans] B.step_sound_local[of a "pright d" Ans]
      by (auto simp: gamma_prod_def pmap_def)
    finally show ?case by (simp only: local_spec_step_pmap)
  next
    case (3 s d ci)
    then obtain c1 e1 c2 e2 where
      "(c1, e1) \<in> set (en1 ci (pleft d))" "s \<in> g1 c1"
      "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g1 e1"
      "(c2, e2) \<in> set (en2 ci (pright d))" "s \<in> g2 c2"
      "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g2 e2"
      using A.enter_sound_local[of s "pleft d" ci] B.enter_sound_local[of s "pright d" ci]
      by (auto simp: gamma_prod_def entry_pairs_cover_def)
    moreover from this have "(Product c1 c2, Product e1 e2) \<in> set (prod_enter (en1 ci) (en2 ci) d)"
      by (force simp: prod_enter_def)
    ultimately show ?case
      unfolding entry_pairs_cover_def gamma_prod_def by fastforce
  next
    case (4 s dc t de ci)
    then show ?case
      by (auto simp: gamma_prod_def pmap2_def intro: A.combine_sound_local B.combine_sound_local)
  next
    case (5 s d q)
    then have "eval_holds q (q1 (pleft d) q) s" "eval_holds q (q2 (pright d) q) s"
      using A.qry_sound B.qry_sound by (auto simp: gamma_prod_def)
    then show ?case
      unfolding qry_prod_def by (rule eval_query.inf_sound)
  qed
qed

section \<open>Two cooperating analyses are sound\<close>

text \<open>
  The headline result: two components, each proved against arbitrary sound
  answers and each with a sound handler, form a product whose specification
  satisfies \<open>analysis_contract\<close>. In the generated system every transfer of the
  product receives, for each question either component names, the meet of both
  handlers' answers on the state the edge starts from. Nothing about either
  partner enters the other's proof.
\<close>

theorem product_contract:
  assumes "sound_local_dg_spec q1 sk1 asn1 sp1 br1 bd1 rt1 en1 ev1 ce1 ca1 g1 \<G>"
    and "sound_local_dg_spec q2 sk2 asn2 sp2 br2 bd2 rt2 en2 ev2 ce2 ca2 g2 \<G>"
  shows "analysis_contract
           (local_dg_spec (qs_prod qs1 qs2) (qry_prod q1 q2)
              (\<lambda>A. pmap (sk1 A) (sk2 A))
              (\<lambda>A x e. pmap (asn1 A x e) (asn2 A x e))
              (\<lambda>A c x. pmap (sp1 A c x) (sp2 A c x))
              (\<lambda>A b pol. pmap (br1 A b pol) (br2 A b pol))
              (\<lambda>A p. pmap (bd1 A p) (bd2 A p))
              (\<lambda>A e p. pmap (rt1 A e p) (rt2 A e p))
              (\<lambda>ci. prod_enter (en1 ci) (en2 ci))
              (\<lambda>A v. pmap (ev1 A v) (ev2 A v))
              (\<lambda>ci. pmap2 (ce1 ci) (ce2 ci)) (\<lambda>ci. pmap2 (ca1 ci) (ca2 ci)))
           (\<lambda>d g. gamma_prod g1 g2 d) \<G>"
  by (rule sound_local_dg_spec.local_spec_contract[OF product_local_spec[OF assms]])

end
