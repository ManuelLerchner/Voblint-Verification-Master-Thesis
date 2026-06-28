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


lemma abs_join_set_empty [simp]:
  "abs_join_set join_abs bot_abs {} = bot_abs"
  unfolding abs_join_set_def by simp



subsection \<open>Fold-join monotonicity helpers\<close>

text \<open>
  Generic lemmas about @{const Finite_Set.fold} of a commutative join over the
  image of a finite set: a member is below the fold, and the fold is monotone in
  the pointwise order of the indexed family.  Reused by the equation-system
  soundness and by the named-global environment join.
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
        using finF pnF ninfF unfolding img by simp
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
        using finF pnF ninfF' unfolding img by simp
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
        using insert.hyps H2' unfolding Rimg by simp
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
      using insert.hyps H1' unfolding Limg by simp
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
        using insert.hyps H2' unfolding Rimg by simp
      have lej: "j (f1 p) (Finite_Set.fold j z (f1 ` F)) \<le> j (f2 p) (Finite_Set.fold j z (f2 ` F))"
        by (rule mono[OF lep IH])
      show ?thesis
        unfolding Lfold Rfold
        by (rule lej)
    qed
  qed
qed

subsection \<open>Right-hand side of the equation system\<close>

definition combine_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" ("\<langle>_|_\<rangle>") where
  "combine_abs sc se = (\<lambda>x. if is_global x then se x else sc x)"

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for combine_abs sc se.
  A pure sound_domain fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
\<close>
lemma combine_states_sound:
  fixes \<sigma>c \<sigma>e :: "'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>\<langle>\<sigma>c|\<sigma>e\<rangle>\<rbrakk>"
proof -
  from sc have Vc: "\<forall>z. s z \<in> gamma (\<sigma>c z)"
    unfolding gamma_state_def by auto
  from se have Ve: "\<forall>z. t z \<in> gamma (\<sigma>e z)"
    unfolding gamma_state_def by auto
  show ?thesis unfolding gamma_state_def combine_abs_def combine_states_def
    using Vc Ve by auto
qed

definition rhs ::
    "cfg
     \<Rightarrow> 'a domain_transfer
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp
     \<Rightarrow> 'a abs_state"
where
  "rhs g tf join_abs bot_abs s0 env v =
     (let edge_vals = image (\<lambda>(u, a). apply_tf tf a (env u))
                          {(u, a) | u a. (u, a, v) \<in> edges g};
          comb_vals = image (\<lambda>(c, e). \<langle>env c|env e\<rangle>)
                          {(c, e) | c e. (c, e, v) \<in> combines g};
          base = if v = cfg_entry g
                 then insert s0 (edge_vals \<union> comb_vals)
                 else edge_vals \<union> comb_vals
      in  abs_join_set join_abs bot_abs base)"

definition is_post_fixpoint ::
    "cfg
     \<Rightarrow> ('a::ord domain_transfer)
     \<Rightarrow> ('a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
     \<Rightarrow> 'a abs_state
     \<Rightarrow> 'a abs_state
     \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> bool"
where
  "is_post_fixpoint g tf join_abs bot_abs s0 env =
     (\<forall>v. rhs g tf join_abs bot_abs s0 env v \<le> env v)"


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
  by (metis (no_types, lifting) Sup_fin.eq_fold Sup_fin.insert Sup_fin.subset finY finite_subset
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


text \<open>
  Key soundness statement for the constraint system:
  If env is a post-fixpoint (env v <= rhs ... env v for all v),
  then env overapproximates the CFG collecting semantics.
  Proved in Constraint_System_Sound.thy.
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
locale sound_transfer =
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes tf_sound_assign:
    "\<forall>x (a::aexp) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       s(x := aval a s) \<in> \<lbrakk>tf_assign tf x a \<sigma>\<rbrakk>"
  assumes tf_sound_assume:
    "\<forall>(b::bexp) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s
       \<longrightarrow> s \<in> \<lbrakk>tf_assume tf b \<sigma>\<rbrakk>"
  assumes tf_sound_assume_not:
    "\<forall>(b::bexp) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<not> bval b s
       \<longrightarrow> s \<in> \<lbrakk>tf_assume_not tf b \<sigma>\<rbrakk>"
  assumes tf_sound_enter:
    "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       enter_state s \<in> \<lbrakk>tf_enter tf \<sigma>\<rbrakk>"


subsection \<open>Effectful transfer function record\<close>

text \<open>
  An effectful_domain_transfer bundles per-action strategy tree producers.
  Each field takes the edge-action parameters plus the source program point u and
  returns a strategy tree that may QueryL/QueryG arbitrary unknowns, emit Side
  contributions to named globals, and ends with Answer carrying the local result.

  apply_etf dispatches on edge_action to the matching field.

  Unit-global pure-transfer tree constructors live in TD_Side_CFG where
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
  with the contribution to the global unknowns. For unit-global pure transfers
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
  "(pp, 'g, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state) \<Rightarrow> 'a abs_state"
where
  "etf_full t \<sigma> = traverse_rhs t \<sigma> \<squnion> all_sides t \<sigma>"

text \<open>
  Soundness contract for an effectful transfer record: each per-action tree's
  reassembled full result over-approximates the concrete edge step applied to the
  combined source state.  The combined source state is \<open>\<sigma> (Inl u) \<squnion> \<sigma> (Inr ())\<close>
  (locals at u joined with the single global unknown -- see side_env).  This is
  the Goblint-aligned interface: the obligation is stated on traverse_rhs /
  sides_of_rhs, exactly the data the TD solver consumes.
\<close>

subsection \<open>The named-global environment\<close>

text \<open>
  glob_env joins all named-global unknowns of sigma into a single abstract
  state: the full flow-insensitive global value seen at any point.  With a
  finite global-name type the join is a finite fold (abs_join_set over the image
  of UNIV), so it is well defined in a non-complete bounded_semilattice_sup_bot.
  At 'g = unit it is the single pot sigma (Inr ()) (glob_env_unit), so it
  generalises the unit pipeline's read of the global unknown.
\<close>

definition glob_env ::
  "(pp + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> 'a abs_state"
where
  "glob_env \<sigma> = abs_join_set (\<squnion>) \<bottom> ((\<lambda>g. \<sigma> (Inr g)) ` UNIV)"

lemma glob_env_upper: "\<sigma> (Inr g) \<le> glob_env \<sigma>"
  unfolding glob_env_def abs_join_set_def
  by (rule mem_image_le_fold[OF finite_UNIV comp_fun_commute_sup sup_ge1 sup_ge2]) blast

lemma glob_env_unit:
  fixes \<sigma> :: "pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "glob_env \<sigma> = \<sigma> (Inr ())"
proof (rule order_antisym)
  show "glob_env \<sigma> \<le> \<sigma> (Inr ())"
    unfolding glob_env_def by (rule abs_join_set_le) auto
  show "\<sigma> (Inr ()) \<le> glob_env \<sigma>" by (rule glob_env_upper)
qed

lemma glob_env_mono:
  assumes "\<sigma>1 \<le> \<sigma>2" shows "glob_env \<sigma>1 \<le> glob_env \<sigma>2"
proof -
  have le: "\<And>p. \<sigma>1 (Inr p) \<le> \<sigma>2 (Inr p)" by (rule le_funD[OF assms])
  show ?thesis
    unfolding glob_env_def abs_join_set_def
    by (rule fold_join_image_mono[OF finite_UNIV comp_fun_commute_sup sup_ge1 sup_ge2
          sup_least sup_mono le])
qed

text \<open>
  Per-name monotonicity of glob_env: it reads only the named-global slots, so a
  pointwise bound on the Inr components alone suffices.  Used to route a per-name
  side bound (sides_of_rhs t \<sigma> (Inr g) \<le> \<sigma> (Inr g)) into a global-env bound.
\<close>
lemma glob_env_mono_Inr:
  assumes "\<And>p. \<sigma>1 (Inr p) \<le> \<sigma>2 (Inr p)"
  shows "glob_env \<sigma>1 \<le> glob_env \<sigma>2"
  unfolding glob_env_def abs_join_set_def
  by (rule fold_join_image_mono[OF finite_UNIV comp_fun_commute_sup sup_ge1 sup_ge2
        sup_least sup_mono assms])
text \<open>
  Executable form: when the global-name type additionally enumerates (Enum),
  fold over the enumeration's image rather than over UNIV.  Used by the unit
  pipeline's value-evaluation (unit is enum); the abstract development keeps the
  UNIV definition.
\<close>

lemma glob_env_code [code]:
  "glob_env (\<sigma> :: pp + 'g::enum \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   = List.fold (\<squnion>) (map (\<lambda>g. \<sigma> (Inr g)) Enum.enum) \<bottom>"
proof -
  interpret ci: comp_fun_idem "(\<squnion>) :: 'a abs_state \<Rightarrow> _ \<Rightarrow> _"
    by unfold_locales (auto simp: sup_left_commute)
  have "glob_env \<sigma> = Finite_Set.fold (\<squnion>) \<bottom> (set (map (\<lambda>g. \<sigma> (Inr g)) Enum.enum))"
    unfolding glob_env_def abs_join_set_def by (simp add: UNIV_enum)
  also have "\<dots> = List.fold (\<squnion>) (map (\<lambda>g. \<sigma> (Inr g)) Enum.enum) \<bottom>"
    by (rule ci.fold_set_fold)
  finally show ?thesis .
qed

text \<open>
  Drop the UNIV-based definitional code equation: it folds over an abstract UNIV
  and is not executable.  glob_env_code (enum) is the executable replacement.
\<close>
declare glob_env_def [code del]

text \<open>
  Bridge between the two side aggregations: the total of a tree's Side
  contributions is below the join of the per-name side map.  This routes the
  full-state reassembly (all_sides, in etf_full) through the per-name post-fixpoint
  bounds (sides_of_rhs (Inr g) <= sigma (Inr g)) used by the solver: composed with
  glob_env_mono it gives all_sides t sigma <= glob_env sigma for any post-solution.
\<close>

lemma all_sides_le_glob_env_sides:
  fixes t :: "(pp, 'g::finite, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  shows "all_sides t \<sigma> \<le> glob_env (sides_of_rhs t \<sigma>)"
proof (induction t)
  case (Answer d) show ?case by (simp add: le_fun_def)
next
  case (QueryL y f)
  have "all_sides (f (\<sigma> (Inl y))) \<sigma> \<le> glob_env (sides_of_rhs (f (\<sigma> (Inl y))) \<sigma>)"
    using QueryL.IH by blast
  then show ?case by simp
next
  case (QueryG y f)
  have "all_sides (f (\<sigma> (Inr y))) \<sigma> \<le> glob_env (sides_of_rhs (f (\<sigma> (Inr y))) \<sigma>)"
    using QueryG.IH by blast
  then show ?case by simp
next
  case (Side y d t)
  have mono: "sides_of_rhs t \<sigma> \<le> sides_of_rhs (Side y d t) \<sigma>"
    by (auto simp: le_fun_def Let_def)
  have d_le: "d \<le> glob_env (sides_of_rhs (Side y d t) \<sigma>)"
  proof -
    have "d \<le> sides_of_rhs (Side y d t) \<sigma> (Inr y)" by (simp add: Let_def)
    also have "\<dots> \<le> glob_env (sides_of_rhs (Side y d t) \<sigma>)" by (rule glob_env_upper)
    finally show ?thesis .
  qed
  have rest_le: "all_sides t \<sigma> \<le> glob_env (sides_of_rhs (Side y d t) \<sigma>)"
    using Side.IH glob_env_mono[OF mono] by (rule order_trans)
  from d_le rest_le show ?case
    unfolding all_sides.simps(4) by (rule sup_least)
qed

locale sound_effectful_transfer =
  fixes etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
  assumes etf_sound_nop:
    "\<forall>u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
       s \<in> \<lbrakk>etf_full (etf_nop etf u) \<sigma>\<rbrakk>"
  assumes etf_sound_assign:
    "\<forall>x e u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
       s(x := aval e s) \<in> \<lbrakk>etf_full (etf_assign etf x e u) \<sigma>\<rbrakk>"
  assumes etf_sound_assume:
    "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. bval b s
       \<longrightarrow> s \<in> \<lbrakk>etf_full (etf_assume etf b u) \<sigma>\<rbrakk>"
  assumes etf_sound_assume_not:
    "\<forall>(b::bexp) u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. \<not> bval b s
       \<longrightarrow> s \<in> \<lbrakk>etf_full (etf_assume_not etf b u) \<sigma>\<rbrakk>"
  assumes etf_sound_enter:
    "\<forall>u \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>.
       enter_state s \<in> \<lbrakk>etf_full (etf_enter etf u) \<sigma>\<rbrakk>"
  assumes etf_sound_combine:
    "\<forall>cc ex \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma> (Inl cc) \<squnion> glob_env \<sigma>\<rbrakk>.
       \<forall>t \<in> \<lbrakk>\<sigma> (Inl ex) \<squnion> glob_env \<sigma>\<rbrakk>.
         <s|t> \<in> \<lbrakk>etf_full (etf_combine etf cc ex) \<sigma>\<rbrakk>"

end
