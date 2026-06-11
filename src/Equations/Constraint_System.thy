theory Constraint_System
  imports CFG_Def Abstract_Domain IMP2_Globals IMP2_SmallStep
begin

(*
  Equation System over a CFG.

  Given:
    - A CFG  g
    - An abstract domain  D  (instance of abstract_domain)
    - Per-domain transfer functions for each edge action

  We construct an equation system (constraint system) where each
  program point v has an equation:
    sigma(v) = join_over { tf(a)(sigma(u)) | (u,a,v) in g }

  plus the special base case at the entry:
    sigma(entry) includes the initial abstract state.

  The equation system is represented as an RHS function:
    rhs :: pp => (pp => D abs_state) => D abs_state

  This is the format expected by the top-down solver locale.

  All transfer functions are parameterised over the domain via a locale
  so the same equation-system construction works for Sign, Interval, etc.
*)

(* ── Abstract Transfer Function Record ───────────────────────── *)
(*
  A domain_transfer bundles the per-action abstract transformers.
  Parameterised by the abstract value type 'a.
*)

record 'a domain_transfer =
  tf_assign    :: "vname => aexp => ('a abs_state) => ('a abs_state)"
  tf_assume    :: "bexp  => ('a abs_state) => ('a abs_state)"
  tf_assume_not :: "bexp => ('a abs_state) => ('a abs_state)"
  tf_enter     :: "('a abs_state) => ('a abs_state)"

(* ── Apply Transfer Function to One Edge ─────────────────────── *)

fun apply_tf :: "'a domain_transfer
                 => edge_action
                 => ('a abs_state)
                 => ('a abs_state)" where
    "apply_tf tf EA_Nop              sigma = sigma"
  | "apply_tf tf (EA_Assign x a)     sigma = tf_assign tf x a sigma"
  | "apply_tf tf (EA_Assume b)       sigma = tf_assume tf b sigma"
  | "apply_tf tf (EA_AssumeNot b)    sigma = tf_assume_not tf b sigma"
  | "apply_tf tf EA_Enter            sigma = tf_enter tf sigma"

(* ── Abstract Join over a Set ─────────────────────────────────── *)
(*
  Fold join_abs over a finite set of abstract states.
  Requires comp_fun_commute join_abs for the result to be order-independent.
  Finiteness of the predecessor set follows from finite (edges g).
*)

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

(* ── Monotonicity of rhs ──────────────────────────────────────── *)
(*
  The RHS is monotone in the environment: if env1 <= env2 pointwise
  (in the abstract order), then rhs env1 <= rhs env2.
  This is required by the top-down solver for it to be applicable.
*)

(*
  Monotonicity of @{const rhs} in the environment.

  Requires join algebra typical of @{const sound_domain} / @{const abstract_domain}
  instances (upper bounds + mixed monotonicity + least-upper-bound property for
  binary join), and monotonicity of @{const apply_tf} in the abstract state.
*)

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
(* -- Interprocedural RHS (M1 slice 3) -------------------------------- *)

definition combine_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "combine_abs sc se = (\<lambda>x. if is_global x then se x else sc x)"

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

(*
  Key soundness statement for the constraint system:
  If env is a post-fixpoint (env v <= rhs ... env v for all v),
  then env overapproximates the CFG collecting semantics.
  Proved in Constraint_System_Sound.thy.
  Interprocedural variant: Constraint_System_IP_Sound.thy.
*)

(*
  Sound transfer function: a domain_transfer tf that soundly over-approximates
  the concrete edge actions w.r.t. a sound_domain's concretization.  Bundles the
  four per-action soundness obligations (assign / assume / assume-not / enter)
  that previously threaded through every soundness theorem as explicit
  assumptions.  Concrete domains discharge these once via `interpretation`.
*)
locale sound_transfer = sound_domain +
  fixes tf :: "'a domain_transfer"
  assumes tf_sound_assign:
    "\<forall>x (a::aexp) sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>(b::bexp) sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>(b::bexp) sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes tf_sound_enter:
    "\<forall>sigma. \<forall>s \<in> gamma_state sigma.
       enter_state s \<in> gamma_state (tf_enter tf sigma)"

end
