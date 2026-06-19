theory Constraint_System
  imports "Voblint_CFG.CFG_Def" Abstract_Domain "Voblint_IMP2.IMP2_Globals" "Voblint_IMP2.IMP2_Expr" "TD.Basics_side"
begin

section \<open>Equation system over a CFG\<close>

text \<open>
  Given:
    - A CFG  g
    - An abstract domain  D  (instance of abstract_domain)
    - Per-domain transfer functions for each edge action

  We construct an equation system (constraint system) where each
  program point v has an equation:
    \<sigma>(v) = join_over { tf(a)(\<sigma>(u)) | (u,a,v) in g }

  plus the special base case at the entry:
    \<sigma>(entry) includes the initial abstract state.

  The equation system is represented as an RHS function:
    rhs :: pp => (pp => D abs_state) => D abs_state

  This is the format expected by the top-down solver locale.

  All transfer functions are parameterised over the domain via a locale
  so the same equation-system construction works for Sign, Interval, etc.
\<close>

subsection \<open>Abstract transfer function record\<close>

text \<open>
  A domain_transfer bundles the per-action abstract transformers.
  Parameterised by the abstract value type 'a.
\<close>

record 'a domain_transfer =
  tf_assign    :: "vname => aexp => ('a abs_state) => ('a abs_state)"
  tf_assume    :: "bexp  => ('a abs_state) => ('a abs_state)"
  tf_assume_not :: "bexp => ('a abs_state) => ('a abs_state)"
  tf_enter     :: "('a abs_state) => ('a abs_state)"

subsection \<open>Apply transfer function to one edge\<close>

fun apply_tf :: "'a domain_transfer
                 => edge_action
                 => ('a abs_state)
                 => ('a abs_state)" where
    "apply_tf tf EA_Nop              \<sigma> = \<sigma>"
  | "apply_tf tf (EA_Assign x a)     \<sigma> = tf_assign tf x a \<sigma>"
  | "apply_tf tf (EA_Assume b)       \<sigma> = tf_assume tf b \<sigma>"
  | "apply_tf tf (EA_AssumeNot b)    \<sigma> = tf_assume_not tf b \<sigma>"
  | "apply_tf tf EA_Enter            \<sigma> = tf_enter tf \<sigma>"

subsection \<open>Abstract join over a set\<close>

text \<open>
  Fold join_abs over a finite set of abstract states.
  Requires comp_fun_commute join_abs for the result to be order-independent.
  Finiteness of the predecessor set follows from finite (edges g).
\<close>

definition abs_join_set ::
    "('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state set
     => 'a abs_state"
where
  "abs_join_set join_abs bot_abs S = Finite_Set.fold join_abs bot_abs S"

definition rhs ::
    "cfg
     => 'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => (pp => 'a abs_state)
     => pp
     => 'a abs_state"
where
  "rhs g tf join_abs bot_abs s0 env v =
     (let preds = {(u, a) | u a. (u, a, v) : edges g};
          vals  = image (\<lambda>(u, a). apply_tf tf a (env u)) preds;
          base  = if v = cfg_entry g then insert s0 vals else vals
      in  abs_join_set join_abs bot_abs base)"

lemma abs_join_set_empty [simp]:
  "abs_join_set join_abs bot_abs {} = bot_abs"
  unfolding abs_join_set_def by simp

lemma rhs_no_predecessors_not_entry:
  assumes "v \<noteq> cfg_entry g"
  assumes "\<And>u a. (u, a, v) \<notin> edges g"
  shows "rhs g tf join_abs bot_abs s0 env v = bot_abs"
  unfolding rhs_def using assms by (simp add: Let_def)

lemma rhs_entry_no_predecessors:
  assumes "v = cfg_entry g"
  assumes "\<And>u a. (u, a, v) \<notin> edges g"
  shows "rhs g tf join_abs bot_abs s0 env v = abs_join_set join_abs bot_abs {s0}"
  unfolding rhs_def using assms by (simp add: Let_def)

definition is_post_fixpoint ::
    "cfg
     => ('a::ord domain_transfer)
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => (pp => 'a abs_state)
     => bool"
where
  "is_post_fixpoint g tf join_abs bot_abs s0 env =
     (\<forall>v. rhs g tf join_abs bot_abs s0 env v <= env v)"

subsection \<open>Monotonicity of rhs\<close>

text \<open>
  The RHS is monotone in the environment: if env1 <= env2 pointwise (in the
  abstract order), then rhs env1 <= rhs env2.  This is required by the top-down
  solver.  The proof uses the join algebra of @{const sound_domain} /
  @{const abstract_domain} instances (upper bounds, mixed monotonicity,
  least-upper-bound for binary join) and monotonicity of @{const apply_tf} in
  the abstract state.
\<close>

lemma mem_image_le_fold_insert_step:
  fixes f :: "'p \<Rightarrow> 'a::preorder" and j :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and z :: 'a and p F
  assumes finF: "finite F" and pnF: "p \<notin> F"
    and cfu: "comp_fun_commute j"
    and ub1: "\<And>a b. a \<le> j a b" and ub2: "\<And>a b. b \<le> j a b"
    and IH: "\<And>x'. x' \<in> f ` F \<Longrightarrow> x' \<le> Finite_Set.fold j z (f ` F)"
  shows "\<And>x. x \<in> f ` insert p F \<Longrightarrow> x \<le> Finite_Set.fold j z (f ` insert p F)"
proof -
  fix x
  assume ximg: "x \<in> f ` insert p F"
  from ximg obtain y where yins: "y \<in> insert p F" and xeq: "x = f y"
    by blast
  interpret jc: comp_fun_commute j
    by (rule cfu)
  consider (yp) "y = p" | (ynp) "y \<noteq> p"
    by auto
  then show "x \<le> Finite_Set.fold j z (f ` insert p F)"
  proof cases
    case yp
    then have xfp: "x = f p"
      using xeq by simp
    consider (infF) "f p \<in> f ` F" | (ninfF) "f p \<notin> f ` F"
      by auto
    then show ?thesis
    proof cases
      case infF
      then have img: "f ` insert p F = f ` F"
        by auto
      have "f p \<in> f ` F"
        by fact
      then have "f p \<le> Finite_Set.fold j z (f ` F)"
        by (simp add: IH[rule_format])
      then show ?thesis
        unfolding xfp img by simp
    next
      case ninfF
      then have ninfF: "f p \<notin> f ` F"
        by simp
      have img: "f ` insert p F = insert (f p) (f ` F)"
        using ninfF by auto
      have fold_eq: "Finite_Set.fold j z (f ` insert p F) = j (f p) (Finite_Set.fold j z (f ` F))"
        using finF pnF ninfF unfolding img by (simp add: jc.fold_insert)
      show ?thesis
        unfolding xfp fold_eq by (simp add: ub1)
    qed
  next
    case ynp
    with yins have yF: "y \<in> F"
      by simp
    have xF: "x \<in> f ` F"
      using xeq yF by auto
    have xleF: "x \<le> Finite_Set.fold j z (f ` F)"
      by (simp add: IH[rule_format, OF xF])
    consider (infF') "f p \<in> f ` F" | (ninfF') "f p \<notin> f ` F"
      by auto
    then show ?thesis
    proof cases
      case infF'
      then have img: "f ` insert p F = f ` F"
        by auto
      then show ?thesis
        unfolding img using xleF by simp
    next
      case ninfF'
      then have ninfF': "f p \<notin> f ` F"
        by simp
      have img: "f ` insert p F = insert (f p) (f ` F)"
        using ninfF' by auto
      have fold_i: "Finite_Set.fold j z (f ` insert p F) = j (f p) (Finite_Set.fold j z (f ` F))"
        using finF pnF ninfF' unfolding img by (simp add: jc.fold_insert)
      have "x \<le> Finite_Set.fold j z (f ` F)"
        by (fact xleF)
      also have "\<dots> \<le> j (f p) (Finite_Set.fold j z (f ` F))"
        by (rule ub2)
      also have "\<dots> = Finite_Set.fold j z (f ` insert p F)"
        unfolding fold_i by simp
      finally show ?thesis .
    qed
  qed
qed

lemma mem_image_le_fold:
  fixes f :: "'p \<Rightarrow> 'a::preorder" and j :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and z :: 'a
  assumes fin: "finite A"
    and cfu: "comp_fun_commute j"
    and ub1: "\<And>a b. a \<le> j a b"
    and ub2: "\<And>a b. b \<le> j a b"
  shows "\<And>x. x \<in> f ` A \<Longrightarrow> x \<le> Finite_Set.fold j z (f ` A)"
  using fin
proof (induct A rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert p F)
  show "\<And>x. x \<in> f ` insert p F \<Longrightarrow> x \<le> Finite_Set.fold j z (f ` insert p F)"
    by (rule mem_image_le_fold_insert_step[OF insert.hyps(1) insert.hyps(2) cfu ub1 ub2 insert.hyps(3)])
qed

lemma fold_join_image_mono:
  fixes P :: "'p set" and f1 f2 :: "'p \<Rightarrow> 'a::preorder" and j :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" and z :: 'a
  assumes fin: "finite P"
    and cfu: "comp_fun_commute j"
    and ub1: "\<And>a b. a \<le> j a b"
    and ub2: "\<And>a b. b \<le> j a b"
    and least: "\<And>x y z. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> j x y \<le> z"
    and mono: "\<And>x1 y1 x2 y2. x1 \<le> y1 \<Longrightarrow> x2 \<le> y2 \<Longrightarrow> j x1 x2 \<le> j y1 y2"
    and le: "\<And>p. f1 p \<le> f2 p"
  shows "Finite_Set.fold j z (f1 ` P) \<le> Finite_Set.fold j z (f2 ` P)"
  using fin
proof (induct P rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert p F)
  interpret jc: comp_fun_commute j
    by (rule cfu)
  have finF: "finite F" and pF: "p \<notin> F"
    using insert.hyps by simp_all
  have IH: "Finite_Set.fold j z (f1 ` F) \<le> Finite_Set.fold j z (f2 ` F)"
    using insert.hyps(3) by simp
  have lep: "f1 p \<le> f2 p"
    by (simp add: le)
  have leF: "\<And>q. q \<in> F \<Longrightarrow> f1 q \<le> f2 q"
    by (simp add: le)
  show ?case
  proof (cases "f1 p \<in> f1 ` F")
    assume H1: "f1 p \<in> f1 ` F"
    show ?thesis
    proof (cases "f2 p \<in> f2 ` F")
      assume H2: "f2 p \<in> f2 ` F"
      have L: "f1 ` insert p F = f1 ` F" and R: "f2 ` insert p F = f2 ` F"
        using H1 H2 by auto
      show ?thesis
        unfolding L R by (rule IH)
    next
      assume H2': "f2 p \<notin> f2 ` F"
      have L: "f1 ` insert p F = f1 ` F"
        using H1 by auto
      have Rimg: "f2 ` insert p F = insert (f2 p) (f2 ` F)"
        using H2' by auto
      have Rfold: "Finite_Set.fold j z (f2 ` insert p F) = j (f2 p) (Finite_Set.fold j z (f2 ` F))"
        using insert.hyps H2' unfolding Rimg
        by (simp add: jc.fold_insert)
      have foldf1: "Finite_Set.fold j z (f1 ` F) \<le> j (f2 p) (Finite_Set.fold j z (f2 ` F))"
        by (rule order_trans[OF IH ub2])
      show ?thesis
        unfolding L Rimg
      proof (rule order_trans[OF foldf1])
        show "j (f2 p) (Finite_Set.fold j z (f2 ` F)) \<le> Finite_Set.fold j z (insert (f2 p) (f2 ` F))"
          by (simp only: Rimg[symmetric] Rfold[symmetric] order_refl)
      qed
    qed
  next
    assume H1': "f1 p \<notin> f1 ` F"
    have Limg: "f1 ` insert p F = insert (f1 p) (f1 ` F)"
      using H1' by auto
    have Lfold: "Finite_Set.fold j z (f1 ` insert p F) = j (f1 p) (Finite_Set.fold j z (f1 ` F))"
      using insert.hyps H1' unfolding Limg
      by (simp add: jc.fold_insert)
    show ?thesis
    proof (cases "f2 p \<in> f2 ` F")
      assume H2: "f2 p \<in> f2 ` F"
      have R: "f2 ` insert p F = f2 ` F"
        using H2 by auto
      have f2p_le: "f2 p \<le> Finite_Set.fold j z (f2 ` F)"
        by (rule mem_image_le_fold[OF finF cfu ub1 ub2, rule_format, OF H2])
      have f1p_le: "f1 p \<le> Finite_Set.fold j z (f2 ` F)"
        by (rule order_trans[OF lep f2p_le])
      have "j (f1 p) (Finite_Set.fold j z (f1 ` F)) \<le> Finite_Set.fold j z (f2 ` F)"
        by (rule least[OF f1p_le IH])
      then show ?thesis
        unfolding Lfold R by simp
    next
      assume H2': "f2 p \<notin> f2 ` F"
      have Rimg: "f2 ` insert p F = insert (f2 p) (f2 ` F)"
        using H2' by auto
      have Rfold: "Finite_Set.fold j z (f2 ` insert p F) = j (f2 p) (Finite_Set.fold j z (f2 ` F))"
        using insert.hyps H2' unfolding Rimg
        by (simp add: jc.fold_insert)
      have lej: "j (f1 p) (Finite_Set.fold j z (f1 ` F)) \<le> j (f2 p) (Finite_Set.fold j z (f2 ` F))"
        by (rule mono[OF lep IH])
      show ?thesis
        unfolding Lfold Rfold
        by (rule lej)
    qed
  qed
qed

lemma rhs_mono:
  fixes env1 env2 :: "pp \<Rightarrow> 'a::preorder abs_state"
  assumes fin: "finite (edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes join_ub1: "\<And>x y. x \<le> join_abs x y"
  assumes join_ub2: "\<And>x y. y \<le> join_abs x y"
  assumes join_mono:
      "\<And>x1 y1 x2 y2::'a abs_state. x1 \<le> y1 \<Longrightarrow> x2 \<le> y2 \<Longrightarrow> join_abs x1 x2 \<le> join_abs y1 y2"
  assumes join_least:
      "\<And>x y z::'a abs_state. x \<le> z \<Longrightarrow> y \<le> z \<Longrightarrow> join_abs x y \<le> z"
  assumes tf_mono:
      "\<And>a \<sigma>1 \<sigma>2::'a abs_state. \<sigma>1 \<le> \<sigma>2 \<Longrightarrow> apply_tf tf a \<sigma>1 \<le> apply_tf tf a \<sigma>2"
  assumes env_le: "\<forall>v. env1 v \<le> env2 v"
  shows "rhs g tf join_abs bot_abs s0 env1 v \<le> rhs g tf join_abs bot_abs s0 env2 v"
proof -
  define P :: "(pp \<times> edge_action) set"
    where "P = {(u, a). (u, a, v) \<in> edges g}"
  have "P = predecessors g v"
    by (simp add: P_def predecessors_def)
  then have finP: "finite P"
    by (simp add: finite_predecessors[OF fin])
  define f1 f2 where
    "f1 \<equiv> \<lambda>(u, a). apply_tf tf a (env1 u)"
    and "f2 \<equiv> \<lambda>(u, a). apply_tf tf a (env2 u)"
  have le_pa: "\<And>p. f1 p \<le> f2 p"
  proof -
    fix p :: "pp \<times> edge_action"
    obtain u a where p: "p = (u, a)"
      by (cases p) auto
    have "env1 u \<le> env2 u"
      using env_le by simp
    then have "apply_tf tf a (env1 u) \<le> apply_tf tf a (env2 u)"
      by (rule tf_mono)
    then show "f1 p \<le> f2 p"
      unfolding f1_def f2_def p by simp
  qed
  show ?thesis
  proof (cases "v = cfg_entry g")
    case True
    define P' :: "(pp \<times> edge_action) option set" where "P' = insert None (Some ` P)"
    define f1' f2' where
      "f1' \<equiv> \<lambda>q. case q of None \<Rightarrow> s0 | Some p \<Rightarrow> f1 p"
      and "f2' \<equiv> \<lambda>q. case q of None \<Rightarrow> s0 | Some p \<Rightarrow> f2 p"
    have finP': "finite P'"
      unfolding P'_def using finP by simp
    have le_q': "\<And>q. f1' q \<le> f2' q"
    proof -
      fix q
      show "f1' q \<le> f2' q"
        unfolding f1'_def f2'_def by (cases q; simp add: le_pa)
    qed
    have img1: "f1' ` P' = insert s0 (f1 ` P)"
    proof -
      have "f1' ` insert None (Some ` P) = insert (f1' None) (f1' ` Some ` P)"
        by simp
      also have "\<dots> = insert s0 (f1 ` P)"
        unfolding f1'_def by (simp add: image_image)
      finally show ?thesis
        unfolding P'_def by simp
    qed
    have img2: "f2' ` P' = insert s0 (f2 ` P)"
    proof -
      have "f2' ` insert None (Some ` P) = insert (f2' None) (f2' ` Some ` P)"
        by simp
      also have "\<dots> = insert s0 (f2 ` P)"
        unfolding f2'_def by (simp add: image_image)
      finally show ?thesis
        unfolding P'_def by simp
    qed
    have "Finite_Set.fold join_abs bot_abs (f1' ` P') \<le> Finite_Set.fold join_abs bot_abs (f2' ` P')"
      by (rule fold_join_image_mono[OF finP' cfu join_ub1 join_ub2 join_least join_mono le_q'])
    then have "Finite_Set.fold join_abs bot_abs (insert s0 (f1 ` P))
             \<le> Finite_Set.fold join_abs bot_abs (insert s0 (f2 ` P))"
      unfolding img1 img2 by simp
    then show ?thesis
      unfolding rhs_def Let_def abs_join_set_def P_def f1_def f2_def
      using \<open>v = cfg_entry g\<close> by simp
  next
    case False
    have "Finite_Set.fold join_abs bot_abs (f1 ` P) \<le> Finite_Set.fold join_abs bot_abs (f2 ` P)"
      by (rule fold_join_image_mono[OF finP cfu join_ub1 join_ub2 join_least join_mono le_pa])
    then show ?thesis
      unfolding rhs_def Let_def abs_join_set_def P_def f1_def f2_def
      using \<open>v \<noteq> cfg_entry g\<close> by simp
  qed
qed
subsection \<open>Interprocedural RHS\<close>

definition combine_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "combine_abs sc se = (\<lambda>x. if is_global x then se x else sc x)"

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for combine_abs sc se.
  A pure sound_domain fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
\<close>
context sound_domain
begin

lemma combine_states_sound:
  assumes sc: "s \<in> gamma_state \<sigma>c" and se: "t \<in> gamma_state \<sigma>e"
  shows "combine_states s t \<in> gamma_state (combine_abs \<sigma>c \<sigma>e)"
proof -
  from sc have Vc: "\<forall>z. s z \<in> \<gamma> (\<sigma>c z)"
    unfolding gamma_state_def by auto
  from se have Ve: "\<forall>z. t z \<in> \<gamma> (\<sigma>e z)"
    unfolding gamma_state_def by auto
  show ?thesis unfolding gamma_state_def combine_abs_def combine_states_def
    using Vc Ve by auto
qed

end

definition rhs_ip ::
    "cfg
     \<Rightarrow> 'a domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp
     \<Rightarrow> 'a abs_state"
where
  "rhs_ip g tf join_abs bot_abs s0 env v =
     (let edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u))
                          {(u, a) | u a. (u, a, v) \<in> edges g};
          comb_vals = image (\<lambda>(c, e). combine_abs (env c) (env e))
                          {(c, e) | c e. (c, e, v) \<in> combines g};
          base = if v = cfg_entry g
                 then insert s0 (edge_vals \<union> comb_vals)
                 else edge_vals \<union> comb_vals
      in  abs_join_set join_abs bot_abs base)"

definition is_post_fixpoint_ip ::
    "cfg
     \<Rightarrow> ('a::ord domain_transfer)
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> bool"
where
  "is_post_fixpoint_ip g tf join_abs bot_abs s0 env =
     (\<forall>v. rhs_ip g tf join_abs bot_abs s0 env v \<le> env v)"

lemma rhs_ip_eq_rhs_if_no_combines:
  assumes "combines g = {}"
  shows "rhs_ip g tf join_abs bot_abs s0 env v = rhs g tf join_abs bot_abs s0 env v"
  unfolding rhs_ip_def rhs_def using assms by (simp add: Let_def)

lemma sup_fold_ge_state:
  assumes "finite (A :: 'a::bounded_semilattice_sup_bot abs_state set)"
    and "x \<in> A"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot A"
  using assms
  by (metis Sup_fin.coboundedI Sup_fin.eq_fold finite_insert insertCI)

lemma fold_bot_le_superset:
  fixes X Y :: "'a::bounded_semilattice_sup_bot abs_state set"
  assumes finY: "finite Y"
  assumes sub: "X \<subseteq> Y"
  shows "Finite_Set.fold (\<squnion>) bot X \<le> Finite_Set.fold (\<squnion>) bot Y"
  by (metis (no_types, lifting) ext Sup_fin.eq_fold Sup_fin.insert Sup_fin.subset finY finite_subset
      fold_empty sub sup.absorb_iff2 sup.commute sup_bot_left)

lemma abs_join_set_le_superset:
  fixes X Y :: "'a::bounded_semilattice_sup_bot abs_state set"
  assumes finY: "finite Y"
  assumes sub: "X \<subseteq> Y"
  shows "abs_join_set (\<squnion>) bot X \<le> abs_join_set (\<squnion>) bot Y"
  unfolding abs_join_set_def
  by (simp add: finY fold_bot_le_superset sub)

lemma abs_join_set_le:
  fixes X :: "'a::bounded_semilattice_sup_bot abs_state"
  assumes fin: "finite S" and le: "\<And>s. s \<in> S \<Longrightarrow> s \<le> X"
  shows "abs_join_set (\<squnion>) bot S \<le> X"
proof -
  have "abs_join_set (\<squnion>) bot S = Sup_fin (insert bot S)"
    unfolding abs_join_set_def using fin by (simp add: Sup_fin.eq_fold)
  also have "\<dots> \<le> X" using fin le by (intro Sup_fin.boundedI) auto
  finally show ?thesis .
qed

lemma rhs_le_rhs_ip:
  fixes g :: cfg and tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and env :: "pp \<Rightarrow> 'a abs_state" and s0 :: "'a abs_state" and v :: pp
  assumes finE: "finite (edges g)"
  assumes finC: "finite (combines g)"
  shows "rhs g tf (\<squnion>) bot s0 env v
        \<le> rhs_ip g tf (\<squnion>) bot s0 env v"
proof (cases "combines g = {}")
  case True
  then show ?thesis
    unfolding rhs_ip_eq_rhs_if_no_combines[OF True] by (simp)
next
  case False
  define P where "P = predecessors g v"
  define C where "C = combine_predecessors g v"
  define fv where "fv = image (\<lambda>(u, a). apply_tf tf a (env u)) P"
  define cv where "cv = image (\<lambda>(c, e). combine_abs (env c) (env e)) C"
  have finP: "finite P"
    using finE by (simp add: P_def finite_predecessors)
  have finCv: "finite C"
    using finC by (simp add: C_def finite_combine_predecessors)
  have fin_fv: "finite fv" and fin_cv: "finite cv"
    using finP finCv unfolding fv_def cv_def by auto
  have rhs_eq: "rhs g tf (\<squnion>) bot s0 env v =
    abs_join_set (\<squnion>) bot (if v = cfg_entry g then insert s0 fv else fv)"
    unfolding rhs_def Let_def abs_join_set_def P_def fv_def predecessors_def by simp
  have ip_eq: "rhs_ip g tf (\<squnion>) bot s0 env v =
    abs_join_set (\<squnion>) bot (if v = cfg_entry g then insert s0 (fv \<union> cv) else fv \<union> cv)"
    unfolding rhs_ip_def Let_def abs_join_set_def P_def C_def fv_def cv_def
      combine_predecessors_def
    using predecessors_def by presburger  
  show ?thesis unfolding rhs_eq ip_eq
    apply(auto simp add: abs_join_set_le_superset fin_cv fin_fv)
    by (meson Un_upper1 abs_join_set_le_superset fin_cv fin_fv finite.insertI finite_UnI
        insert_mono)

qed

text \<open>
  Key soundness statement for the constraint system:
  If env is a post-fixpoint (env v <= rhs ... env v for all v),
  then env overapproximates the CFG collecting semantics.
  Proved in Constraint_System_Sound.thy.
  Interprocedural variant: Constraint_System_IP_Sound.thy.
\<close>

subsection \<open>C-faithful initial store set\<close>

text \<open>
  In C, global variables are zero-initialised before \<open>main\<close> starts
  (ISO C 6.7.9p10); local variables are uninitialized and may hold any
  integer value.  \<open>cinit_stores\<close> is the corresponding set of concrete stores:
  those where every global is 0 and locals are unconstrained.

  Any analysis that uses a domain-specific abstract seed \<open>s0\<close> satisfying
  \<open>cinit_stores \<subseteq> gamma_state s0\<close> may state its soundness theorem against
  \<open>cinit_stores\<close> rather than \<open>UNIV\<close>, matching C program semantics.
\<close>

definition cinit_stores :: "store set" where
  "cinit_stores = {s. \<forall>x. is_global x \<longrightarrow> s x = 0}"

text \<open>
  Sound transfer function: a domain_transfer tf that soundly over-approximates
  the concrete edge actions w.r.t. a sound_domain's concretization.  Bundles the
  four per-action soundness obligations (assign / assume / assume-not / enter)
  as locale assumptions.  Concrete domains discharge these once via
  `interpretation`.
\<close>
locale sound_transfer = sound_domain +
  fixes tf :: "'a domain_transfer"
  assumes tf_sound_assign:
    "\<forall>x (a::aexp) \<sigma>. \<forall>s \<in> gamma_state \<sigma>.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a \<sigma>)"
  assumes tf_sound_assume:
    "\<forall>(b::bexp) \<sigma>. \<forall>s \<in> gamma_state \<sigma>. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b \<sigma>)"
  assumes tf_sound_assume_not:
    "\<forall>(b::bexp) \<sigma>. \<forall>s \<in> gamma_state \<sigma>. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b \<sigma>)"
  assumes tf_sound_enter:
    "\<forall>\<sigma>. \<forall>s \<in> gamma_state \<sigma>.
       enter_state s \<in> gamma_state (tf_enter tf \<sigma>)"


subsection \<open>Effectful transfer function record\<close>

text \<open>
  An effectful_domain_transfer bundles per-action strategy tree producers.
  Each field takes the edge-action parameters plus the source program point u and
  returns a strategy tree that may QueryL/QueryG arbitrary unknowns, emit Side
  contributions to named globals, and ends with Answer carrying the local result.

  apply_etf dispatches on edge_action to the matching field.

  The pure-domain shim (pure_edge_tree / etf_from_tf) lives in TD_Side_CFG where
  restrict_local / restrict_global are defined.
\<close>

type_synonym ('g, 'd) edge_tf_tree =
  "pp \<Rightarrow> (pp, 'g, 'd abs_state) strategy_tree"

text \<open>
  A combine (procedure return) tree producer takes the caller program point and
  the callee-exit program point and builds a tree that queries both their local
  unknowns (and any globals), emits Side contributions, and ends with the
  combined local result.  Unlike an edge, it has two local inputs.
\<close>
type_synonym ('g, 'd) combine_tf_tree =
  "pp \<Rightarrow> pp \<Rightarrow> (pp, 'g, 'd abs_state) strategy_tree"

record ('g, 'd) effectful_domain_transfer =
  etf_nop        :: "('g, 'd) edge_tf_tree"
  etf_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_assume     :: "bexp  \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_assume_not :: "bexp  \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_enter      :: "('g, 'd) edge_tf_tree"
  etf_combine    :: "('g, 'd) combine_tf_tree"

fun apply_etf ::
  "('g, 'd) effectful_domain_transfer \<Rightarrow> edge_action \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'd abs_state) strategy_tree"
where
  "apply_etf etf EA_Nop           u = etf_nop etf u"
| "apply_etf etf (EA_Assign x a)  u = etf_assign etf x a u"
| "apply_etf etf (EA_Assume b)    u = etf_assume etf b u"
| "apply_etf etf (EA_AssumeNot b) u = etf_assume_not etf b u"
| "apply_etf etf EA_Enter         u = etf_enter etf u"

subsection \<open>Reassembled full result and effectful soundness\<close>

text \<open>
  An effectful edge tree splits its outcome between a local Answer (the value of
  the source unknown after the edge) and Side contributions to the named globals.
  etf_full reassembles the complete abstract post-state: the local result joined
  with the contribution to the single global unknown.  For the pure-domain shim
  this is exactly apply_tf tf a (combined), so the soundness obligation below is
  the existing sound_transfer obligation stated against the combined input.

  Stating soundness against etf_full -- rather than against the local Answer
  alone -- is essential: the local restriction sends globals to bot, and
  gamma_state of a bot global is empty (gamma_bot), so the local Answer in
  isolation never over-approximates a concrete post-state that touches globals.
  The contributions must be put back together first.
\<close>

text \<open>
  all_sides totals every Side contribution of a tree, regardless of the named
  global it targets.  Unlike sides_of_rhs (which keeps a per-name map), this is a
  single finite join over the tree's Side nodes -- the data needed to reassemble
  the full post-state across arbitrarily many named globals without an infinite
  Sup.  At 'g = unit every Side targets (), so all_sides coincides with
  sides_of_rhs _ (Inr ()) (all_sides_eq_sides_Inr_unit below).
\<close>

primrec all_sides ::
  "(pp, 'g, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state) \<Rightarrow> 'a abs_state"
where
  "all_sides (Answer d) \<sigma> = \<bottom>"
| "all_sides (QueryL y f) \<sigma> = all_sides (f (\<sigma> (Inl y))) \<sigma>"
| "all_sides (QueryG y f) \<sigma> = all_sides (f (\<sigma> (Inr y))) \<sigma>"
| "all_sides (Side y d t) \<sigma> = d \<squnion> all_sides t \<sigma>"

lemma all_sides_eq_sides_Inr_unit:
  fixes t :: "(pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  shows "all_sides t \<sigma> = sides_of_rhs t \<sigma> (Inr ())"
  by (induction t) (auto simp: Let_def sup_commute)

definition etf_full ::
  "(pp, unit, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> (pp + unit \<Rightarrow> 'a abs_state) \<Rightarrow> 'a abs_state"
where
  "etf_full t \<sigma> = traverse_rhs t \<sigma> \<squnion> sides_of_rhs t \<sigma> (Inr ())"

text \<open>
  Soundness contract for an effectful transfer record: each per-action tree's
  reassembled full result over-approximates the concrete edge step applied to the
  combined source state.  The combined source state is \<open>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<close>
  (locals at u joined with the single global unknown -- see side_env).  This is
  the Goblint-aligned interface: the obligation is stated on traverse_rhs /
  sides_of_rhs, exactly the data the TD solver consumes.
\<close>

locale sound_effectful_transfer = sound_domain +
  fixes etf :: "(unit, 'a) effectful_domain_transfer"
  assumes etf_sound_nop:
    "\<forall>u \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
       s \<in> gamma_state (etf_full (etf_nop etf u) \<sigma>)"
  assumes etf_sound_assign:
    "\<forall>x e u \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
       s(x := aval e s) \<in> gamma_state (etf_full (etf_assign etf x e u) \<sigma>)"
  assumes etf_sound_assume:
    "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())). bval b s
       \<longrightarrow> s \<in> gamma_state (etf_full (etf_assume etf b u) \<sigma>)"
  assumes etf_sound_assume_not:
    "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())). \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (etf_full (etf_assume_not etf b u) \<sigma>)"  assumes etf_sound_enter:
    "\<forall>u \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())).
       enter_state s \<in> gamma_state (etf_full (etf_enter etf u) \<sigma>)"
  assumes etf_sound_combine:
    "\<forall>cc ex \<sigma>. \<forall>s \<in> gamma_state (\<sigma> (Inl cc) \<squnion> \<sigma> (Inr ())).
       \<forall>t \<in> gamma_state (\<sigma> (Inl ex) \<squnion> \<sigma> (Inr ())).
         combine_states s t \<in> gamma_state (etf_full (etf_combine etf cc ex) \<sigma>)"
end
