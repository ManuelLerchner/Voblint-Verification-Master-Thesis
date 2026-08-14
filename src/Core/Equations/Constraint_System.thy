theory Constraint_System
  imports CFG_Enumeration "Voblint_CFG.CFG_Transfer" Abstract_Domain
    "Voblint_VIMP.VIMP_Globals" "Voblint_VIMP.VIMP_Expr" "Voblint_VIMP.VIMP_Proc"
    "TD.Basics_side"
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

text \<open>
  \<open>tf_branch\<close> is the single, polarity-parametrized branch transfer, matching Goblint's
  \<open>Spec.branch : man -> exp -> bool -> D.t\<close> (one operation taking a boolean outcome, not two
  independently-named callbacks). \<open>tf_branch tf b True\<close> takes the branch where \<open>b\<close> evaluates
  true; \<open>tf_branch tf b False\<close> takes the branch where \<open>b\<close> evaluates false.
\<close>

subsection \<open>Analysis events\<close>

text \<open>
  An \<open>analysis_event\<close> is an analyzer-visible occurrence distinct from an ordinary
  control-flow transfer: a domain may observe it, but it must not by itself refine
  execution (see the note on \<open>tf_event\<close>'s dispatch below). This matches Goblint's
  own separation of its ordinary
  \<open>Spec\<close> transfer methods (\<open>assign\<close>/\<open>branch\<close>/\<open>skip\<close>/...) from \<open>Spec.event\<close>, which
  handles \<open>Events.Assert\<close> and similar occurrences outside the ordinary transfer
  vocabulary. Voblint's sole current event is a check's condition; the vocabulary is
  deliberately left open rather than pre-populated, so that a future VIMP source
  construct with no current counterpart (e.g. an eventual assume/assert pair) adds a
  constructor here instead of a new domain-transfer field.
\<close>
datatype analysis_event =
  Check_Event bexp

record 'a domain_transfer =
  tf_assign    :: "vname => aexp => ('a abs_state) => ('a abs_state)" ("assign\<^sup>#")
  tf_random    :: "vname => ('a abs_state) => ('a abs_state)"
  tf_branch    :: "bexp => bool => ('a abs_state) => ('a abs_state)" ("branch\<^sup>#")
  tf_skip      :: "('a abs_state) => ('a abs_state)" ("skip\<^sup>#")
  tf_body      :: "pname => ('a abs_state) => ('a abs_state)" ("body\<^sup>#")
  tf_return    :: "aexp option => pname => ('a abs_state) => ('a abs_state)" ("return\<^sup>#")
  tf_enter     :: "vname list \<Rightarrow> aexp list \<Rightarrow> ('a abs_state) \<Rightarrow> ('a abs_state)" ("enter\<^sup>#")
  tf_event     :: "analysis_event => ('a abs_state) => ('a abs_state)" ("event\<^sup>#")
  tf_combine   :: "('a abs_state) => ('a abs_state) => ('a abs_state)"

subsection \<open>Apply transfer function to one edge\<close>

text \<open>
  \<open>EA_Nop\<close>, \<open>EA_Ret\<close>, and (via \<^const>\<open>tf_body\<close>, at procedure entry rather than
  through this dispatcher) function-body entry are each a real lifecycle event with
  its own transfer field, matching Goblint's \<open>skip\<close>/\<open>return\<close>/entry-then-body split,
  even though every current domain implements \<open>skip\<^sup>#\<close> and \<open>body\<^sup>#\<close> as the identity
  and \<open>return\<^sup>#\<close> as the assignment it publishes. \<open>EA_Check\<close> routes through
  \<^const>\<open>tf_event\<close> rather than \<^const>\<open>tf_skip\<close>: a check is an analysis event
  (matching Goblint's \<open>Spec.event\<close>, not \<open>Spec.skip\<close>), and conflating it with skip
  would make a future domain's non-identity \<open>skip\<^sup>#\<close> silently change what a check
  edge does. Every current domain implements \<open>event\<^sup>#\<close> as the identity too --
  \<open>abstract_check_domain\<close> does the actual proving/refuting/reporting, over the
  unmodified environment at the check's own node -- but that is a fact about today's
  domains, not one this dispatcher hardcodes.
\<close>
fun apply_tf :: "'a domain_transfer
                 => edge_action
                 => ('a abs_state)
                 => ('a abs_state)" where
    "apply_tf tf EA_Nop              \<sigma> = skip\<^sup># tf \<sigma>"
  | "apply_tf tf (EA_Assign x a)     \<sigma> = assign\<^sup># tf x a \<sigma>"
  | "apply_tf tf (EA_Random x)       \<sigma> = tf_random tf x \<sigma>"
  | "apply_tf tf (EA_Assume b)       \<sigma> = branch\<^sup># tf b True \<sigma>"
  | "apply_tf tf (EA_AssumeNot b)    \<sigma> = branch\<^sup># tf b False \<sigma>"
  | "apply_tf tf (EA_Ret e p)        \<sigma> = return\<^sup># tf e p \<sigma>"
  | "apply_tf tf (EA_Check c)        \<sigma> = event\<^sup># tf (Check_Event c) \<sigma>"

text \<open>
  Point-free counterparts of \<^const>\<open>apply_tf\<close>'s primitive equations. The defining
  equations only rewrite once an abstract state is applied; call sites that carry
  \<^const>\<open>apply_tf\<close> tf a as an unapplied function value need these instead to reach
  the underlying domain_transfer field.
\<close>
lemma apply_tf_EA_Nop [simp]:
  "apply_tf tf EA_Nop = skip\<^sup># tf"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_Assign [simp]:
  "apply_tf tf (EA_Assign x a) = assign\<^sup># tf x a"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_Random [simp]:
  "apply_tf tf (EA_Random x) = tf_random tf x"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_Assume [simp]:
  "apply_tf tf (EA_Assume b) = branch\<^sup># tf b True"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_AssumeNot [simp]:
  "apply_tf tf (EA_AssumeNot b) = branch\<^sup># tf b False"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_Ret [simp]:
  "apply_tf tf (EA_Ret e p) = return\<^sup># tf e p"
  by (simp add: fun_eq_iff)

lemma apply_tf_EA_Check [simp]:
  "apply_tf tf (EA_Check c) = event\<^sup># tf (Check_Event c)"
  by (simp add: fun_eq_iff)

text \<open>Some families this codebase builds over \<^typ>\<open>edge_action\<close> happen to reduce a
  void return and a check to the same value as \<^const>\<open>EA_Nop\<close>, and a value return
  to the same value as the \<^const>\<open>EA_Assign\<close> it publishes -- true of every current
  executable mirror (\<open>sign_tf_st_for\<close> and siblings), since their \<open>EA_Ret\<close>/\<open>EA_Check\<close>
  cases still literally implement today's \<open>skip\<^sup>#\<close>/\<open>return\<^sup>#\<close> semantics by hand. This
  is a fact about a concrete family \<open>F\<close>, not a structural property \<^const>\<open>apply_tf\<close>
  itself provides any more (\<open>return\<^sup>#\<close>/\<open>skip\<^sup>#\<close> are free fields a future domain may
  implement differently), so \<open>action_reduces\<close> is not used to discharge
  \<^const>\<open>apply_tf\<close>'s own \<^typ>\<open>edge_action\<close> case split (see \<open>apply_tf_wrap_eqI\<close>
  below); it only packages a mirror's own self-consistency for callers such as
  \<open>unit_dg_exec_analysis\<close> that state it as an explicit obligation.\<close>
locale action_reduces =
  fixes F :: "edge_action \<Rightarrow> 'y"
  assumes ret_none[simp,intro]: "\<And>p. F (EA_Ret None p) = F EA_Nop"
    and ret_some[simp,intro]: "\<And>a p. F (EA_Ret (Some a) p) = F (EA_Assign ret_var a)"
    and check[simp,intro]: "\<And>c. F (EA_Check c) = F EA_Nop"

text \<open>Composing an \<open>action_reduces\<close> family with any outer function preserves the
  reduction: this is what lets every \<open>_commute\<close>-style theorem below derive
  \<open>action_reduces\<close> for its own wrapped family (e.g.
  \<open>\<lambda>a. fun_of_resolved_st_q_for gs (sign_tf_st a s)\<close>) from the domain's single
  registered \<open>action_reduces\<close> fact in one step, instead of re-proving the three
  reduction equations at every call site.\<close>
lemma action_reduces_comp:
  assumes "action_reduces F"
  shows "action_reduces (\<lambda>a. g (F a))"
proof -
  interpret action_reduces F by (rule assms)
  show ?thesis by unfold_locales (simp_all add: ret_none ret_some check)
qed

text \<open>Closure principle for any family built by applying a single transfer function
  and post-processing the result the same way at every action. Deliberately left
  untagged: F and H are schematic, so tagging this \<open>[simp]\<close>/\<open>[dest]\<close>/\<open>[intro]\<close>
  would let it fire against any equality of this shape.\<close>
lemma apply_tf_wrap_eqI:
  fixes tf :: "'a domain_transfer"
    and F :: "edge_action \<Rightarrow> 'y"
    and H :: "('a abs_state \<Rightarrow> 'a abs_state) \<Rightarrow> 'y"
  assumes nop: "F EA_Nop = H (apply_tf tf EA_Nop)"
    and assign: "\<And>x e. F (EA_Assign x e) = H (apply_tf tf (EA_Assign x e))"
    and random: "\<And>x. F (EA_Random x) = H (apply_tf tf (EA_Random x))"
    and assm: "\<And>b. F (EA_Assume b) = H (apply_tf tf (EA_Assume b))"
    and assm_not: "\<And>b. F (EA_AssumeNot b) = H (apply_tf tf (EA_AssumeNot b))"
    and ret: "\<And>e p. F (EA_Ret e p) = H (apply_tf tf (EA_Ret e p))"
    and check: "\<And>c. F (EA_Check c) = H (apply_tf tf (EA_Check c))"
  shows "F a = H (apply_tf tf a)"
  by (cases a) (simp_all add: nop assign random assm assm_not ret check)

subsection \<open>Abstract join over a set\<close>

text \<open>
  Fold join_abs over a finite set of abstract states.
  Requires comp_fun_commute join_abs for the result to be order-independent.
  Finiteness of the predecessor set follows from finite (intra g) and finite (calls g).
\<close>

text \<open>
  Generic in the folded payload type -- \<open>'a abs_state\<close> is one instance, and
  \<open>'a abs_state lifted\<close> (AD-52's role-aware reconstruction) another, since
  \<^const>\<open>Finite_Set.fold\<close> and \<^const>\<open>Sup_fin\<close> never depend on the payload being a
  function type. Same-role accumulation (folding several global-slot or several
  local-alternative contributions together) always uses ordinary \<open>\<squnion>\<close> regardless
  of payload; only cross-role reconstruction (a local input against the
  accumulated global) needs the asymmetric \<^const>\<open>assemble_local_global\<close>, and
  that never goes through this fold.
\<close>

definition abs_join_set ::
    "('d => 'd => 'd)
     => 'd
     => 'd set
     => 'd"
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

definition combine_env_abs ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  ("combine'_env\<^sup>#")
where
  "combine_env_abs gs sc se = (\<lambda>x. if gs x then se x else sc x)"

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for \<open>combine_env\<^sup># gs sc se\<close>.
  A pure sound_domain fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
\<close>
lemma combine_env_sound:
  fixes \<sigma>c \<sigma>e :: "'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># gs \<sigma>c \<sigma>e\<rbrakk>"
proof -
  from sc have Vc: "\<forall>z. s z \<in> gamma (\<sigma>c z)"
    unfolding gamma_state_def by auto
  from se have Ve: "\<forall>z. t z \<in> gamma (\<sigma>e z)"
    unfolding gamma_state_def by auto
  show ?thesis unfolding gamma_state_def combine_env_abs_def combine_env_def
    using Vc Ve by auto
qed

text \<open>
  Formal binding evaluates actual arguments in the caller state and assigns each
  abstract value to the matching callee formal.
\<close>
definition bind_formals_abs ::
    "vname list \<Rightarrow> 'a list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "bind_formals_abs xs avs \<sigma> = fold (\<lambda>(x, a) \<tau>. \<tau>(x := a)) (zip xs avs) \<sigma>"

lemma gamma_state_upd:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes s: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and v: "v \<in> gamma a"
  shows "s(x := v) \<in> \<lbrakk>\<sigma>(x := a)\<rbrakk>"
  using s v unfolding gamma_state_def by auto

text \<open>
  Binding formals preserves soundness: pointwise-sound actual values bound to the
  same formals yield a sound entry state.
\<close>
lemma bind_formals_abs_sound:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes s: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
    and vals: "list_all2 (\<lambda>v a. v \<in> gamma a) vs avs"
  shows "bind_formals xs vs s \<in> \<lbrakk>bind_formals_abs xs avs \<sigma>\<rbrakk>"
  using vals s
proof (induction xs arbitrary: vs avs s \<sigma>)
  case Nil
  then show ?case
    by (simp add: bind_formals_def bind_formals_abs_def)
next
  case (Cons x xs)
  show ?case
  proof (cases vs)
    case Nil
    then show ?thesis
      using Cons.prems
      by (simp add: bind_formals_def bind_formals_abs_def)
  next
    case (Cons v vs')
    then obtain a avs' where avs: "avs = a # avs'"
      using Cons.prems(1) by (cases avs) auto
    have v_a: "v \<in> gamma a"
      using Cons.prems(1) unfolding Cons avs by simp
    have rest: "list_all2 (\<lambda>v a. v \<in> gamma a) vs' avs'"
      using Cons.prems(1) unfolding Cons avs by simp
    have upd: "s(x := v) \<in> \<lbrakk>\<sigma>(x := a)\<rbrakk>"
      by (rule gamma_state_upd[OF Cons.prems(2) v_a])
    have "bind_formals xs vs' (s(x := v))
            \<in> \<lbrakk>bind_formals_abs xs avs' (\<sigma>(x := a))\<rbrakk>"
      by (rule Cons.IH[OF rest upd])
    then show ?thesis
      unfolding Cons avs bind_formals_def bind_formals_abs_def by simp
  qed
qed

lemma bind_formals_abs_mono:
  fixes \<sigma>1 \<sigma>2 :: "'a::order abs_state"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) avs1 avs2"
  shows "bind_formals_abs xs avs1 \<sigma>1 \<le> bind_formals_abs xs avs2 \<sigma>2"
  using vals base
proof (induction xs arbitrary: avs1 avs2 \<sigma>1 \<sigma>2)
  case Nil
  then show ?case by (simp add: bind_formals_abs_def)
next
  case (Cons x xs)
  show ?case
  proof (cases avs1)
    case Nil
    then show ?thesis
      using Cons.prems by (simp add: bind_formals_abs_def)
  next
    case (Cons a avs1')
    then obtain b avs2' where avs2: "avs2 = b # avs2'"
      using Cons.prems(1) by (cases avs2) auto
    have ab: "a \<le> b" using Cons.prems(1) unfolding Cons avs2 by simp
    have rest: "list_all2 (\<le>) avs1' avs2'"
      using Cons.prems(1) unfolding Cons avs2 by simp
    have upd: "\<sigma>1(x := a) \<le> \<sigma>2(x := b)"
      using Cons.prems(2) ab by (simp add: le_fun_def)
    show ?thesis
      unfolding Cons avs2
      using Cons.IH[OF rest upd]
      by (simp add: bind_formals_abs_def fun_upd_def)
  qed
qed

text \<open>
  Generic procedure-entry frame: reset locals to a fixed, fully-imprecise
  \<open>top_val\<close>, keep globals, then bind the formals via @{const bind_formals_abs}.
  Every domain's own enter-frame construction (Sign's @{text enter_frame_sign},
  Interval's @{text enter_frame_ivl}) is this same shape, differing only in
  which value stands for "unknown" -- so this is parameterised over that one
  value rather than duplicated per domain.
\<close>
definition enter_frame_D :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_frame_D gs top_val \<sigma> = (\<lambda>x. if gs x then \<sigma> x else top_val)"

lemma enter_frame_D_sound:
  fixes top_val :: "'a::sound_domain"
  assumes sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and top_full: "gamma top_val = UNIV"
  shows "enter_state gs s \<in> \<lbrakk>enter_frame_D gs top_val \<sigma>\<rbrakk>"
  unfolding gamma_state_def enter_frame_D_def enter_state_def
  using gamma_stateD[OF sv] top_full by auto

lemma enter_frame_D_mono:
  fixes top_val :: "'a::order"
  assumes "\<sigma>1 \<le> \<sigma>2"
  shows "enter_frame_D gs top_val \<sigma>1 \<le> enter_frame_D gs top_val \<sigma>2"
proof (rule le_funI)
  fix x
  show "enter_frame_D gs top_val \<sigma>1 x \<le> enter_frame_D gs top_val \<sigma>2 x"
  proof (cases "gs x")
    case True
    with assms show ?thesis unfolding enter_frame_D_def by (simp add: le_funD)
  next
    case False
    then show ?thesis unfolding enter_frame_D_def by simp
  qed
qed

definition enter_D ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (aexp \<Rightarrow> 'a abs_state \<Rightarrow> 'a) \<Rightarrow> vname list \<Rightarrow> aexp list
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_D gs top_val aval_abs xs es \<sigma> =
     bind_formals_abs xs (map (\<lambda>e. aval_abs e \<sigma>) es) (enter_frame_D gs top_val \<sigma>)"

lemma enter_D_sound:
  fixes top_val :: "'a::sound_domain"
  assumes sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and top_full: "gamma top_val = UNIV"
    and vals: "list_all2 (\<lambda>v a. v \<in> gamma a)
                 (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_abs e \<sigma>) es)"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
           \<in> \<lbrakk>enter_D gs top_val aval_abs xs es \<sigma>\<rbrakk>"
proof -
  have base: "enter_state gs s \<in> \<lbrakk>enter_frame_D gs top_val \<sigma>\<rbrakk>"
    by (rule enter_frame_D_sound[OF sv top_full])
  from bind_formals_abs_sound[OF base vals]
  show ?thesis unfolding enter_D_def .
qed

lemma enter_D_mono:
  fixes top_val :: "'a::order"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) (map (\<lambda>e. aval_abs e \<sigma>1) es) (map (\<lambda>e. aval_abs e \<sigma>2) es)"
  shows "enter_D gs top_val aval_abs xs es \<sigma>1 \<le> enter_D gs top_val aval_abs xs es \<sigma>2"
  unfolding enter_D_def
  by (rule bind_formals_abs_mono[OF enter_frame_D_mono[OF base] vals])

text \<open>
  Abstract counterpart of @{const combine_assign}: write the callee's return slot
  into the caller's destination, or leave the caller untouched when the call
  discards its result.
\<close>
fun combine_assign_abs ::
    "vname option \<Rightarrow> 'a \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    ("combine'_assign\<^sup>#") where
    "combine_assign_abs None _ \<sigma> = \<sigma>"
  | "combine_assign_abs (Some x) v \<sigma> = \<sigma>(x := v)"

text \<open>
  Return combination joins caller locals with callee globals and then assigns the
  callee's @{const ret_var} to the optional destination.  The ordinary abstract
  state update publishes the result without domain-specific return machinery.
\<close>
definition combine_collect_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    ("combine\<^sup>#") where
  "combine_collect_abs gs dst \<sigma>c \<sigma>e = combine_assign\<^sup># dst (\<sigma>e ret_var) (combine_env\<^sup># gs \<sigma>c \<sigma>e)"

lemma combine_collect_abs_mono:
  fixes \<sigma>c1 \<sigma>c2 \<sigma>e1 \<sigma>e2 :: "'a::order abs_state"
  assumes c: "\<sigma>c1 \<le> \<sigma>c2" and e: "\<sigma>e1 \<le> \<sigma>e2"
  shows "combine\<^sup># gs dst \<sigma>c1 \<sigma>e1 \<le> combine\<^sup># gs dst \<sigma>c2 \<sigma>e2"
proof (cases dst)
  case None
  then show ?thesis
    using c e by (simp add: combine_collect_abs_def combine_env_abs_def le_fun_def)
next
  case (Some x)
  then show ?thesis
    using c e by (simp add: combine_collect_abs_def combine_env_abs_def le_fun_def)
qed

text \<open>
  The binary env-combine is the destination-free instance of the
  return-threaded combine: with no destination the return slot is not written.
\<close>
lemma combine_collect_abs_None:
  "combine\<^sup># gs None a b = combine_env\<^sup># gs a b"
  by (simp add: combine_collect_abs_def)

text \<open>
  Per-analysis return combine.  \<^const>\<open>combine_collect_abs\<close> fixes the environment
  merge to \<^const>\<open>combine_env_abs\<close>; \<open>tf_combine_collect_abs\<close> instead reads the merge
  from the \<^typ>\<open>'a domain_transfer\<close> in scope, so each analysis may supply its own
  sound over-approximation of \<^const>\<open>combine_env\<close> instead of the structural
  local/global split.  The return-value write stays \<^const>\<open>combine_assign_abs\<close>: it is
  already domain-agnostic under the function-based \<^typ>\<open>'a abs_state\<close> representation,
  so only the merge step is a per-analysis choice.
\<close>
definition tf_combine_collect_abs ::
    "'a domain_transfer \<Rightarrow> vname option \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "tf_combine_collect_abs tf dst \<sigma>c \<sigma>e = combine_assign\<^sup># dst (\<sigma>e ret_var) (tf_combine tf \<sigma>c \<sigma>e)"

text \<open>The fixed structural merge is the special case where \<open>tf_combine\<close> is
  \<^const>\<open>combine_env_abs\<close>: the general definition specializes to the old one by
  instantiation, rather than duplicating it.\<close>
lemma tf_combine_collect_abs_combine_env_abs:
  assumes "tf_combine tf = combine_env\<^sup># gs"
  shows "tf_combine_collect_abs tf dst \<sigma>c \<sigma>e = combine\<^sup># gs dst \<sigma>c \<sigma>e"
  using assms unfolding tf_combine_collect_abs_def combine_collect_abs_def by simp

text \<open>
  Soundness of the abstract combine including result publication.  A pure
  @{class sound_domain} fact: the destination slot is sound because the callee's
  @{const ret_var} slot is, and every other slot is handled by
  @{thm combine_env_sound}.
\<close>
lemma combine_collect_sound:
  fixes \<sigma>c \<sigma>e :: "'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_collect gs dst s t \<in> \<lbrakk>combine\<^sup># gs dst \<sigma>c \<sigma>e\<rbrakk>"
proof (cases dst)
  case None
  then show ?thesis
    using combine_env_sound[OF sc se]
    by (simp add: combine_collect_def combine_collect_abs_def)
next
  case (Some x)
  have base: "combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># gs \<sigma>c \<sigma>e\<rbrakk>"
    by (rule combine_env_sound[OF sc se])
  have ret: "t ret_var \<in> gamma (\<sigma>e ret_var)"
    using se unfolding gamma_state_def by auto
  show ?thesis
    using base ret Some
    unfolding gamma_state_def combine_collect_def combine_collect_abs_def
    by auto
qed

text \<open>
  Discharge the concrete return combine from an abstract bound: given
  \<open>combine\<^sup># dst sc se \<le> sr\<close>, any concrete return assembled from a
  caller store sound for \<open>sc\<close> and a callee-exit store sound for \<open>se\<close> lies in
  \<open>\<lbrakk>sr\<rbrakk>\<close>.  @{thm combine_collect_sound} carried to the bound by
  @{thm gamma_state_mono}.  The order-theoretic \<open>combine_bound\<close> shape is
  checkable against a post-solution, so no raw \<open><s|t>\<close> obligation reaches callers.
\<close>
lemma combine_env_abs_bound_sound:
  fixes sc se sr :: "'a::sound_domain abs_state"
  assumes bound: "combine\<^sup># gs dst sc se \<le> sr"
    and sc: "s \<in> \<lbrakk>sc\<rbrakk>" and se: "t \<in> \<lbrakk>se\<rbrakk>"
  shows "combine_collect gs dst s t \<in> \<lbrakk>sr\<rbrakk>"
proof -
  have "combine_collect gs dst s t \<in> \<lbrakk>combine\<^sup># gs dst sc se\<rbrakk>"
    using sc se by (rule combine_collect_sound)
  thus ?thesis using gamma_state_mono[OF bound] by blast
qed

text \<open>
  Each predecessor kind contributes a set of abstract states.  Keeping the
  families separate gives downstream proofs precise introduction rules; their
  union is the single source of truth used by the executable right-hand side.
\<close>

definition rhs_edge_sources ::
    "cfg \<Rightarrow> 'a domain_transfer \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp \<Rightarrow> 'a abs_state set" where
  "rhs_edge_sources g tf env v =
     (\<lambda>(u, a). apply_tf tf a (env u)) ` intra_predecessors g v"

text \<open>
  \<^const>\<open>tf_body\<close> applies immediately after \<^const>\<open>tf_enter\<close>, at the actual
  procedure-entry transition -- not somewhere merely near it: \<open>v\<close> here is always
  the \<^const>\<open>FunctionEntry\<close> \<^const>\<open>entry_calls\<close> selects it for, so
  \<^const>\<open>entry_proc\<close> \<open>v\<close> is the callee \<^const>\<open>tf_body\<close> fires for (the
  \<open>CallEdge\<close>'s own \<open>dst\<close> is the call's assignment target, not the callee). This
  is the one call site \<^const>\<open>tf_body\<close> is ever applied at.
\<close>
definition rhs_entry_sources ::
    "cfg \<Rightarrow> 'a domain_transfer \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp \<Rightarrow> 'a abs_state set" where
  "rhs_entry_sources g tf env v =
     (\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> body\<^sup># tf (entry_proc v) (tf_enter tf fs as (env c)))
       ` entry_calls g v"

definition rhs_combine_sources ::
    "cfg \<Rightarrow> 'a domain_transfer \<Rightarrow> (pp \<Rightarrow> 'a abs_state) \<Rightarrow> pp \<Rightarrow> 'a abs_state set" where
  "rhs_combine_sources g tf env v =
     (\<lambda>(c, dst, ex). tf_combine_collect_abs tf dst (env c) (env ex)) ` return_calls g v"

definition rhs_sources ::
    "cfg \<Rightarrow> 'a domain_transfer \<Rightarrow> (pp \<Rightarrow> 'a abs_state)
     \<Rightarrow> pp \<Rightarrow> 'a abs_state set" where
  "rhs_sources g tf env v =
     rhs_edge_sources g tf env v \<union>
     rhs_entry_sources g tf env v \<union>
     rhs_combine_sources g tf env v"

lemma rhs_sources_characterization [simp]:
  "rhs_sources g tf env v =
     (\<lambda>(u, a). apply_tf tf a (env u)) ` intra_predecessors g v \<union>
     (\<lambda>(c, ca). case ca of CallEdge dst fs as \<Rightarrow> body\<^sup># tf (entry_proc v) (tf_enter tf fs as (env c)))
       ` entry_calls g v \<union>
     (\<lambda>(c, dst, ex). tf_combine_collect_abs tf dst (env c) (env ex))
       ` return_calls g v"
  unfolding rhs_sources_def rhs_edge_sources_def rhs_entry_sources_def
    rhs_combine_sources_def by simp

lemma rhs_edge_sources_iff:
  "x \<in> rhs_edge_sources g tf env v \<longleftrightarrow>
   (\<exists>u a. (u, a, v) \<in> intra g \<and> x = apply_tf tf a (env u))"
  unfolding rhs_edge_sources_def intra_predecessors_def by auto

lemma rhs_entry_sourcesI:
  assumes "(c, CallEdge dst fs as, v, k) \<in> calls g"
  shows "body\<^sup># tf (entry_proc v) (tf_enter tf fs as (env c)) \<in> rhs_entry_sources g tf env v"
  unfolding rhs_entry_sources_def entry_calls_def
  using assms by (force simp: image_iff)

lemma rhs_combine_sourcesI:
  assumes "(c, CallEdge dst fs as, FunctionEntry p, v) \<in> calls g"
  shows "tf_combine_collect_abs tf dst (env c) (env (FunctionResult p))
         \<in> rhs_combine_sources g tf env v"
  unfolding rhs_combine_sources_def return_calls_def
  using assms by (force simp: image_iff)

text \<open>
  \<open>rhs\<close> is the equation system's right-hand side at \<open>v\<close>: the join over
  \<^const>\<open>rhs_sources\<close>'s abstract predecessor contributions, plus the seed
  \<open>s0\<close> exactly when \<open>v\<close> is the graph's entry --- the one node with no
  predecessor edge to supply a starting value otherwise.
\<close>
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
     abs_join_set join_abs bot_abs
       (if v = cfg_entry g then insert s0 (rhs_sources g tf env v)
        else rhs_sources g tf env v)"

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

(* The pointwise instance is_post_fixpoint_def unfolds to; downstream
   proofs cite this instead of re-unfolding the quantified definition. *)
lemma is_post_fixpointD [dest]:
  "is_post_fixpoint g tf join_abs bot_abs s0 env
   \<Longrightarrow> rhs g tf join_abs bot_abs s0 env v \<le> env v"
  unfolding is_post_fixpoint_def by simp


lemma sup_fold_ge_state:
  assumes "finite (A :: 'd::bounded_semilattice_sup_bot set)"
    and "x \<in> A"
  shows "x \<le> Finite_Set.fold (\<squnion>) bot A"
  using assms
  by (metis Sup_fin.coboundedI Sup_fin.eq_fold finite_insert insertCI)

lemma fold_bot_le_superset:
  fixes X Y :: "'d::bounded_semilattice_sup_bot set"
  assumes finY: "finite Y"
  assumes sub: "X \<subseteq> Y"
  shows "Finite_Set.fold (\<squnion>) bot X \<le> Finite_Set.fold (\<squnion>) bot Y"
  by (metis (no_types, lifting) Sup_fin.eq_fold Sup_fin.insert Sup_fin.subset finY finite_subset
      fold_empty sub sup.absorb_iff2 sup.commute sup_bot_left)

lemma abs_join_set_le_superset:
  fixes X Y :: "'d::bounded_semilattice_sup_bot set"
  assumes finY: "finite Y"
  assumes sub: "X \<subseteq> Y"
  shows "abs_join_set (\<squnion>) bot X \<le> abs_join_set (\<squnion>) bot Y"
  unfolding abs_join_set_def
  by (simp add: finY fold_bot_le_superset sub)

lemma abs_join_set_le:
  fixes X :: "'d::bounded_semilattice_sup_bot"
  assumes fin: "finite S" and le: "\<And>s. s \<in> S \<Longrightarrow> s \<le> X"
  shows "abs_join_set (\<squnion>) bot S \<le> X"
proof -
  have "abs_join_set (\<squnion>) bot S = Sup_fin (insert bot S)"
    unfolding abs_join_set_def using fin by (simp add: Sup_fin.eq_fold)
  also have "\<dots> \<le> X" using fin le by (intro Sup_fin.boundedI) auto
  finally show ?thesis .
qed


text \<open>
  A valuation that bounds every equation right-hand side is a post-fixpoint.
  Such valuations overapproximate the corresponding CFG collecting semantics.
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

definition cinit_stores :: "(vname \<Rightarrow> bool) \<Rightarrow> store set" where
  "cinit_stores gs = {s. \<forall>x. gs x \<longrightarrow> s x = 0}"

text \<open>
  Sound transfer function: a domain_transfer tf that soundly over-approximates
  the concrete edge actions w.r.t. a sound_domain's concretization, relative to
  an explicit classifier gs.  Bundles the five per-action soundness obligations
  (assign / assume / assume-not / enter / combine) as locale assumptions.
  Concrete domains discharge these once via `interpretation`.
\<close>
locale sound_transfer_for =
  fixes gs :: "vname => bool"
    and tf :: "'a::sound_domain domain_transfer"
  assumes tf_sound_assign_for[intro]:
    "\<forall>x (a::aexp) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
  assumes tf_sound_random_for[intro]:
    "\<forall>x \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<forall>v. s(x := v) \<in> \<lbrakk>tf_random tf x \<sigma>\<rbrakk>"
  assumes tf_sound_branch_for[intro]:
    "\<forall>(b::bexp) (pol::bool) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s = pol
       \<longrightarrow> s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
  assumes tf_sound_skip_for[intro]:
    "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
  assumes tf_sound_body_for[intro]:
    "\<forall>p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
  assumes tf_sound_return_for[intro]:
    "\<forall>(e::aexp option) p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
         \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
  assumes tf_sound_enter_for[intro]:
    "\<forall>xs (es::aexp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
         \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
  assumes tf_sound_event_for[intro]:
    "\<forall>ev \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
  assumes tf_sound_combine_for[intro]:
    "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>.
       combine_env gs s t \<in> \<lbrakk>tf_combine tf \<sigma>c \<sigma>e\<rbrakk>"

context sound_transfer_for
begin

lemma tf_sound_assign_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
  using tf_sound_assign_for by blast

lemma tf_sound_random_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := v) \<in> \<lbrakk>tf_random tf x \<sigma>\<rbrakk>"
  using tf_sound_random_for by blast

lemma tf_sound_branch_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s = pol \<Longrightarrow> s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
  using tf_sound_branch_for by blast

lemma tf_sound_skip_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
  using tf_sound_skip_for by blast

lemma tf_sound_body_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
  using tf_sound_body_for by blast

lemma tf_sound_return_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
     s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
       \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
  using tf_sound_return_for by blast

lemma tf_sound_enter_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
     bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
       \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
  using tf_sound_enter_for by blast

lemma tf_sound_event_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
  using tf_sound_event_for by blast

lemma tf_sound_combine_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
     combine_env gs s t \<in> \<lbrakk>tf_combine tf \<sigma>c \<sigma>e\<rbrakk>"
  using tf_sound_combine_for by blast

end

lemma sound_transferI_for:
  fixes gs :: "vname => bool"
    and tf :: "'a::sound_domain domain_transfer"
  assumes assign[intro]:
    "\<And>x a \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
    and random[intro]:
    "\<And>x \<sigma> s v. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(x := v) \<in> \<lbrakk>tf_random tf x \<sigma>\<rbrakk>"
    and branch[intro]:
    "\<And>b pol \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> bval b s = pol \<Longrightarrow>
       s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
    and skip[intro]:
    "\<And>\<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
    and body[intro]:
    "\<And>p \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
    and return[intro]:
    "\<And>e p \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
         \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
    and enter[intro]:
    "\<And>xs es \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
         \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
    and event[intro]:
    "\<And>ev \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
    and combine[intro]:
    "tf_combine tf = combine_env\<^sup># gs"
  shows "sound_transfer_for gs tf"
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
      s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
    using assign by blast
  show "\<forall>x \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<forall>v.
      s(x := v) \<in> \<lbrakk>tf_random tf x \<sigma>\<rbrakk>"
    using random by blast
  show "\<forall>b pol \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. bval b s = pol \<longrightarrow>
      s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
    using branch by blast
  show "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
    using skip by blast
  show "\<forall>p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
    using body by blast
  show "\<forall>e p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
      s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
        \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
    using return by blast
  show "\<forall>xs (es::aexp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
      bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
        \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
    using enter by blast
  show "\<forall>ev \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
    using event by blast
  show "\<forall>\<sigma>c \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>c\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>.
      combine_env gs s t \<in> \<lbrakk>tf_combine tf \<sigma>c \<sigma>e\<rbrakk>"
    unfolding combine using combine_env_sound by blast
qed


subsection \<open>Effectful transfer function record\<close>

text \<open>
  An effectful_domain_transfer bundles per-action strategy tree producers.
  Each field takes the edge-action parameters plus the source program point u and
  returns a strategy tree that may QueryL/QueryG arbitrary unknowns, emit Side
  contributions to named globals, and ends with Answer carrying the local result.

  apply_etf dispatches on edge_action to the matching field.

  Unit-global effectful tree constructors live in TD_Side_CFG where
  restrict_local / restrict_global are defined.
\<close>

type_synonym ('g, 'd) edge_tf_tree =
  "pp \<Rightarrow> (pp, 'g, 'd abs_state lifted) strategy_tree"

text \<open>
  A combine (procedure return) tree producer takes the caller program point and
  the callee-exit program point and builds a tree that queries both their local
  unknowns (and any globals), emits Side contributions, and ends with the
  combined local result.  Unlike an edge, it has two local inputs.
\<close>
type_synonym ('g, 'd) combine_tf_tree =
  "pp \<Rightarrow> pp \<Rightarrow> (pp, 'g, 'd abs_state lifted) strategy_tree"

record ('g, 'd) effectful_domain_transfer =
  etf_skip       :: "('g, 'd) edge_tf_tree"
  etf_assign     :: "vname \<Rightarrow> aexp \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_random     :: "vname \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_branch     :: "bexp \<Rightarrow> bool \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_body       :: "pname \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_return     :: "aexp option \<Rightarrow> pname \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_enter      :: "vname list \<Rightarrow> aexp list \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_event      :: "analysis_event \<Rightarrow> ('g, 'd) edge_tf_tree"
  etf_combine    :: "vname option \<Rightarrow> ('g, 'd) combine_tf_tree"

text \<open>
  \<open>EA_Check\<close> routes through \<^const>\<open>etf_event\<close> here, matching \<^const>\<open>apply_tf\<close>'s
  own \<open>event\<^sup>#\<close> dispatch: a family built over this record supplies the concrete
  tree (with whatever \<^typ>\<open>vname \<Rightarrow> bool\<close> classifier it closed over when it was
  built), the same way it already supplies \<^const>\<open>etf_skip\<close>/\<^const>\<open>etf_body\<close>.
\<close>
fun apply_etf ::
  "('g, 'd) effectful_domain_transfer \<Rightarrow> edge_action \<Rightarrow> pp
   \<Rightarrow> (pp, 'g, 'd abs_state lifted) strategy_tree"
where
  "apply_etf etf EA_Nop           u = etf_skip etf u"
| "apply_etf etf (EA_Assign x a)  u = etf_assign etf x a u"
| "apply_etf etf (EA_Random x)    u = etf_random etf x u"
| "apply_etf etf (EA_Assume b)    u = etf_branch etf b True u"
| "apply_etf etf (EA_AssumeNot b) u = etf_branch etf b False u"
| "apply_etf etf (EA_Ret e p)     u = etf_return etf e p u"
| "apply_etf etf (EA_Check c)     u = etf_event etf (Check_Event c) u"

fun local_edge_action :: "(vname => bool) => edge_action \<Rightarrow> bool" where
  "local_edge_action gs EA_Nop = True"
| "local_edge_action gs (EA_Assign x e) =
    ((~ gs x) & (~ aexp_mentions_where gs e))"
| "local_edge_action gs (EA_Random x) = (~ gs x)"
| "local_edge_action gs (EA_Assume b) = (~ bexp_mentions_where gs b)"
| "local_edge_action gs (EA_AssumeNot b) = (~ bexp_mentions_where gs b)"
| "local_edge_action gs (EA_Ret e p) =
    (case e of None \<Rightarrow> True
     | Some a \<Rightarrow> ((~ gs ret_var) & (~ aexp_mentions_where gs a)))"
| "local_edge_action gs (EA_Check c) = True"

text \<open>
  @{const local_edge_action}: the edge neither reads nor writes globals (enter and
  combine are separate).  A global assignment such as
  @{term \<open>EA_Assign (STR ''Gx'') e\<close>} is not local even when @{term e} mentions only
  locals.
\<close>

subsection \<open>Reassembled full result and effectful soundness\<close>

text \<open>
  An effectful edge tree splits its outcome between a local Answer (the value of
  the source unknown after the edge) and Side contributions to the named globals.
  etf_full reassembles the complete abstract post-state: the local result joined
  with the contribution to the global unknowns. For unit-global records built
  from apply_tf, this recovers the domain transfer's full abstract post-state on
  the combined input.

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
  "(pp, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'd) \<Rightarrow> 'd"
where
  "all_sides (Answer d) \<sigma> = \<bottom>"
| "all_sides (QueryL y f) \<sigma> = all_sides (f (\<sigma> (Inl y))) \<sigma>"
| "all_sides (QueryG y f) \<sigma> = all_sides (f (\<sigma> (Inr y))) \<sigma>"
| "all_sides (Side y d t) \<sigma> = d \<squnion> all_sides t \<sigma>"

lemma all_sides_eq_sides_Inr_unit:
  fixes t :: "(pp, unit, 'd::bounded_semilattice_sup_bot) strategy_tree"
  shows "all_sides t \<sigma> = sides_of_rhs t \<sigma> (Inr ())"
  by (induction t) (auto simp: Let_def sup_commute)

definition etf_full ::
  "(pp, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'd) \<Rightarrow> 'd"
where
  "etf_full t \<sigma> = traverse_rhs t \<sigma> \<squnion> all_sides t \<sigma>"

subsection \<open>The named-global environment\<close>

text \<open>
  glob_env joins all named-global unknowns of sigma into a single abstract
  state: the full flow-insensitive global value seen at any point.  With a
  finite global-name type the join is a finite fold (abs_join_set over the image
  of UNIV), so it is well defined in a non-complete bounded_semilattice_sup_bot.
  At 'g = unit it is the single pot sigma (Inr ()) (glob_env_unit), so it
  generalises the unit pipeline's read of the global unknown.

  Generic in the folded payload (\<open>'d::bounded_semilattice_sup_bot\<close>): several
  global-slot contributions are always same-role accumulation, joined with
  ordinary \<open>\<squnion>\<close> whether the payload is a raw \<open>abs_state\<close> or an
  \<open>abs_state lifted\<close> reconstruction (AD-52) -- \<open>Bot\<close> here means only "no
  contribution published yet" and is \<open>\<squnion>\<close>'s identity, never a control-flow claim.
\<close>

definition glob_env ::
  "(pp + 'g::finite \<Rightarrow> 'd::bounded_semilattice_sup_bot) \<Rightarrow> 'd"
where
  "glob_env \<sigma> = abs_join_set (\<squnion>) \<bottom> ((\<lambda>g. \<sigma> (Inr g)) ` UNIV)"

lemma glob_env_upper: "\<sigma> (Inr g) \<le> glob_env \<sigma>"
  unfolding glob_env_def abs_join_set_def
  by (rule mem_image_le_fold[OF finite_UNIV comp_fun_commute_sup sup_ge1 sup_ge2]) blast

lemma glob_env_unit:
  fixes \<sigma> :: "pp + unit \<Rightarrow> 'd::bounded_semilattice_sup_bot"
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
  @{const glob_env} reads only named-global slots.  A pointwise bound on those
  components therefore lifts every per-name side bound to the joined global
  environment.
\<close>
lemma glob_env_mono_Inr:
  assumes "\<And>p. \<sigma>1 (Inr p) \<le> \<sigma>2 (Inr p)"
  shows "glob_env \<sigma>1 \<le> glob_env \<sigma>2"
  unfolding glob_env_def abs_join_set_def
  by (rule fold_join_image_mono[OF finite_UNIV comp_fun_commute_sup sup_ge1 sup_ge2
        sup_least sup_mono assms])

text \<open>
  Collecting soundness for local-only trees: @{const etf_full} carries locals;
  globals are restored by combining in @{const glob_env}. Unlike @{const glob_env}
  itself, this combination is cross-role (a local result against the accumulated
  globals), so it is parametric in the combinator rather than hardwired to
  \<open>\<squnion>\<close>: the raw \<open>abs_state\<close> pipeline instantiates it at ordinary \<open>\<squnion>\<close>
  (\<open>etf_collecting_full\<close> below, unchanged), while the lifted
  \<open>abs_state lifted\<close> pipeline instantiates it at
  \<^const>\<open>assemble_local_global\<close> (\<open>etf_collecting_full_lift\<close>), so that a
  \<open>Bot\<close> local result is never resurrected by a live \<open>glob_env\<close> contribution --
  exactly the resurrection AD-52 identifies in the raw split representation.
\<close>

definition etf_collecting_full_with ::
  "('d::bounded_semilattice_sup_bot \<Rightarrow> 'd \<Rightarrow> 'd)
   \<Rightarrow> (pp, 'g::finite, 'd) strategy_tree \<Rightarrow> (pp + 'g \<Rightarrow> 'd) \<Rightarrow> 'd"
where
  "etf_collecting_full_with assemble t \<sigma> = assemble (etf_full t \<sigma>) (glob_env \<sigma>)"

definition etf_collecting_full ::
  "(pp, 'g::finite, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state) \<Rightarrow> 'a abs_state"
where
  "etf_collecting_full = etf_collecting_full_with (\<squnion>)"

definition etf_collecting_full_lift ::
  "(pp, 'g::finite, 'a::sound_domain abs_state lifted) strategy_tree
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state lifted) \<Rightarrow> 'a abs_state lifted"
where
  "etf_collecting_full_lift = etf_collecting_full_with assemble_local_global"

lemma etf_full_le_etf_collecting_full_with:
  fixes assemble :: "'d::bounded_semilattice_sup_bot \<Rightarrow> 'd \<Rightarrow> 'd"
  assumes "\<And>l g. l \<le> assemble l g"
  shows "etf_full t \<sigma> \<le> etf_collecting_full_with assemble t \<sigma>"
  unfolding etf_collecting_full_with_def using assms .

lemma etf_full_le_etf_collecting_full:
  "etf_full t \<sigma> \<le> etf_collecting_full t \<sigma>"
  unfolding etf_collecting_full_def
  by (rule etf_full_le_etf_collecting_full_with) (rule sup_ge1)

lemma etf_full_le_etf_collecting_full_lift:
  fixes t :: "(pp, 'g::finite, 'a::sound_domain abs_state lifted) strategy_tree"
  shows "etf_full t \<sigma> \<le> etf_collecting_full_lift t \<sigma>"
  unfolding etf_collecting_full_lift_def
  by (rule etf_full_le_etf_collecting_full_with) (rule assemble_local_global_ge_local)

lemma in_gamma_etf_collecting_full:
  "s \<in> \<lbrakk>etf_full t \<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>etf_collecting_full t \<sigma>\<rbrakk>"
  using gamma_state_mono[OF etf_full_le_etf_collecting_full] by blast

lemma in_gamma_etf_collecting_full_lift:
  fixes t :: "(pp, 'g::finite, 'a::sound_domain abs_state lifted) strategy_tree"
  shows "s \<in> gamma_state_lift (etf_full t \<sigma>) \<Longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift t \<sigma>)"
  using gamma_lift_mono[OF gamma_state_mono etf_full_le_etf_collecting_full_lift] by fastforce

text \<open>
  A tree's own local Answer and its own Side contribution can, for an
  arbitrary \<^typ>\<open>(pp, 'g, 'd) strategy_tree\<close>, disagree on reachability: a
  \<open>bot\<close> local Answer says ``this edge is dead'', but nothing in the
  strategy_tree type itself forces the Side write emitted by the same tree to
  also be \<open>bot\<close>. \<open>reachability_coherent_tree\<close> names exactly the missing
  constraint -- the two must agree -- so that \<^const>\<open>etf_full\<close>'s plain-sup
  combination cannot resurrect a dead local Answer through a live Side value.
  \<open>unit_edge_tree\<close>, \<open>local_edge_tree\<close>, and \<open>unit_combine_tree\<close> each discharge
  it because both halves are computed from one witness-checked reconstruction.
\<close>
definition reachability_coherent_tree ::
  "(pp, 'g, 'd::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> (pp + 'g \<Rightarrow> 'd) \<Rightarrow> bool"
where
  "reachability_coherent_tree t \<sigma> \<longleftrightarrow> (traverse_rhs t \<sigma> = bot \<longrightarrow> all_sides t \<sigma> = bot)"

text \<open>
  The algebraic kernel every \<open>_combined_le_eff\<close>-style bound reduces to:
  separate bounds on a tree's local Answer and its Side contribution recombine
  through \<^const>\<open>assemble_local_global\<close> exactly when the tree is
  reachability-coherent. Without coherence a \<open>bot\<close> local bound \<open>l\<close> forces
  \<^term>\<open>traverse_rhs t \<sigma> = bot\<close> but not \<^term>\<open>all_sides t \<sigma> = bot\<close>, and
  \<^term>\<open>assemble_local_global bot g = bot\<close> cannot dominate a live \<open>all_sides\<close>
  contribution the way plain \<open>\<squnion>\<close> would -- exactly AD-52's resurrection, one
  layer up.
\<close>
lemma etf_full_le_assemble_local_global:
  fixes t :: "(pp, 'g, 'a::sound_domain abs_state lifted) strategy_tree"
    and \<sigma> :: "pp + 'g \<Rightarrow> 'a abs_state lifted"
  assumes loc: "traverse_rhs t \<sigma> \<le> l"
    and glob: "all_sides t \<sigma> \<le> g"
    and coh: "reachability_coherent_tree t \<sigma>"
  shows "etf_full t \<sigma> \<le> assemble_local_global l g"
proof (cases "traverse_rhs t \<sigma>")
  case Bot
  then have "all_sides t \<sigma> = Bot"
    using coh unfolding reachability_coherent_tree_def by simp
  with Bot show ?thesis unfolding etf_full_def by simp
next
  case (Lifted la')
  note tr_eq = this
  then obtain la where l_eq: "l = Lifted la" and la': "la' \<le> la"
    using loc by (cases l) auto
  show ?thesis
  proof (cases "all_sides t \<sigma>")
    case Bot
    have "Lifted la' \<le> Lifted la" using la' by simp
    also have "\<dots> \<le> assemble_local_global (Lifted la) g" by simp
    finally show ?thesis unfolding etf_full_def tr_eq Bot l_eq by simp
  next
    case (Lifted lg')
    then obtain lg where g_eq: "g = Lifted lg" and lg': "lg' \<le> lg"
      using glob by (cases g) auto
    show ?thesis
      unfolding etf_full_def tr_eq Lifted l_eq g_eq
      using sup_mono[OF la' lg'] by simp
  qed
qed

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
  @{thm glob_env_code} supplies the executable equation by folding over the finite
  enumeration.  The set-based definition remains the mathematical interface.
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
  fixes t :: "(pp, 'g::finite, 'd::bounded_semilattice_sup_bot) strategy_tree"
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

subsection \<open>Side-effecting constraint for a strategy tree\<close>

text \<open>
  A valuation covers a strategy tree when it bounds both the tree's local answer
  and every side contribution produced during the same traversal.  The local
  unknown bounds @{const traverse_rhs}; the complete valuation bounds
  @{const sides_of_rhs} pointwise.
\<close>

definition se_constraint_holds ::
  "('x,'g,'d::bounded_semilattice_sup_bot) strategy_tree \<Rightarrow> ('x + 'g \<Rightarrow> 'd) \<Rightarrow> 'x \<Rightarrow> bool"
where
  "se_constraint_holds t \<sigma> u \<equiv>
     traverse_rhs t \<sigma> \<le> \<sigma> (Inl u) \<and> sides_of_rhs t \<sigma> \<le> \<sigma>"

(* The two halves of se_constraint_holds, split out so call sites can cite
   the half they need instead of re-unfolding the conjunction. *)
lemma se_constraint_holds_local [dest]:
  "se_constraint_holds t \<sigma> u \<Longrightarrow> traverse_rhs t \<sigma> \<le> \<sigma> (Inl u)"
  unfolding se_constraint_holds_def by simp

lemma se_constraint_holds_sides [dest]:
  "se_constraint_holds t \<sigma> u \<Longrightarrow> sides_of_rhs t \<sigma> \<le> \<sigma>"
  unfolding se_constraint_holds_def by simp

text \<open>
  A post-solution covers the local answer and subsumes every emitted side
  contribution.
\<close>
lemma part_post_solution_imp_se_constraint_holds:
  assumes "part_post_solution T x \<sigma> vars" and "u \<in> vars"
  shows "se_constraint_holds (T u) \<sigma> u"
  using assms unfolding se_constraint_holds_def by auto

text \<open>
  @{const part_post_solution} decomposes into well-founded local dependencies and
  the side-effecting constraint at every unknown.  @{const se_constraint_holds}
  isolates the per-unknown post-fixpoint obligation.
\<close>
lemma part_post_solution_iff_se_constraint_holds:
  "part_post_solution T x \<sigma> vars \<longleftrightarrow>
     x \<in> vars \<and> (\<forall>u \<in> vars. dep\<^sub>L T \<sigma> u \<subseteq> vars \<and> se_constraint_holds (T u) \<sigma> u)"
  unfolding se_constraint_holds_def by auto

text \<open>
  Once the side map is subsumed, the reassembled post-state @{const etf_full} is
  bounded by the local unknown joined with @{const glob_env}.  The latter collects
  the flow-insensitive global contributions visible to the traversal.
\<close>
lemma se_constraint_holds_imp_etf_full_le_env:
  fixes t :: "(pp, 'g::finite, 'a::bounded_semilattice_sup_bot abs_state) strategy_tree"
  assumes "se_constraint_holds t \<sigma> u"
  shows "etf_full t \<sigma> \<le> \<sigma> (Inl u) \<squnion> glob_env \<sigma>"
proof -
  have loc: "traverse_rhs t \<sigma> \<le> \<sigma> (Inl u)" using assms by (rule se_constraint_holds_local)
  have sid: "sides_of_rhs t \<sigma> \<le> \<sigma>" using assms by (rule se_constraint_holds_sides)
  have "all_sides t \<sigma> \<le> glob_env (sides_of_rhs t \<sigma>)"
    by (rule all_sides_le_glob_env_sides)
  also have "\<dots> \<le> glob_env \<sigma>" by (rule glob_env_mono[OF sid])
  finally have g: "all_sides t \<sigma> \<le> glob_env \<sigma>" .
  show ?thesis
    unfolding etf_full_def by (rule sup_mono[OF loc g])
qed

text \<open>
  Lifted: a \<open>Bot\<close> global slot trivially satisfies "carries bot in its local
  components" (there is no reconstructed state to check), so only \<open>Lifted \<tau>\<close>
  constrains \<open>\<tau>\<close> pointwise as before.
\<close>

definition inr_slot_locals_bot ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state lifted) \<Rightarrow> bool"
where
  "inr_slot_locals_bot gs \<sigma> =
     (\<forall>g. \<forall>x. \<not> gs x \<longrightarrow> (case \<sigma> (Inr g) of Bot \<Rightarrow> True | Lifted \<tau> \<Rightarrow> \<tau> x = bot))"

text \<open>
  Dual of @{const inr_slot_locals_bot}: every local program-point unknown carries
  bot in its global components.  Holds for the effectful generator's solutions
  because each edge tree ends in a local-restricted Answer, so the local
  unknowns never accumulate globals.  The keyed enter bound uses it to discard the
  caller's (bot) global part of a callee-entry frame.
\<close>

definition inl_slot_globals_bot ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state lifted) \<Rightarrow> bool"
where
  "inl_slot_globals_bot gs \<sigma> =
     (\<forall>v. \<forall>x. gs x \<longrightarrow> (case \<sigma> (Inl v) of Bot \<Rightarrow> True | Lifted \<tau> \<Rightarrow> \<tau> x = bot))"

text \<open>
  The snapshot relaxation of @{const inl_slot_globals_bot}: a local unknown may
  carry globals, but each is bounded by the global environment.  An analysis
  whose local Answers keep written globals @{emph \<open>and\<close>} publish the same values
  to the global slot satisfies it at any solution: every local-slot global sits
  below @{const glob_env}.  This is exactly what the keyed enter bound needs:
  the caller's global part of a callee-entry frame is already covered by the
  globals.
\<close>
definition inl_glob_le_glob_env ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state lifted) \<Rightarrow> bool"
where
  "inl_glob_le_glob_env gs \<sigma> =
     (\<forall>v. \<forall>x. gs x \<longrightarrow> (case \<sigma> (Inl v) of Bot \<Rightarrow> True
                        | Lifted \<tau> \<Rightarrow> \<tau> x \<le> (case glob_env \<sigma> of Bot \<Rightarrow> bot | Lifted g \<Rightarrow> g x)))"

lemma inl_slot_globals_bot_le_glob_env:
  "inl_slot_globals_bot gs \<sigma> \<Longrightarrow> inl_glob_le_glob_env gs \<sigma>"
  by (fastforce simp: inl_slot_globals_bot_def inl_glob_le_glob_env_def split: lifted.splits)

text \<open>
  \<open>inr_slot_locals_bot gs \<sigma> \<longrightarrow> (\<forall>s \<in> \<lbrakk>\<sigma> (Inl u) \<squnion> glob_env \<sigma>\<rbrakk>. ...)\<close> used to state
  the reconstructed edge input by ordinary \<open>\<squnion>\<close>. With the solver payload lifted
  (AD-52), that reconstruction is cross-role -- a queried local unknown against
  the accumulated global -- so it goes through \<^const>\<open>assemble_local_global\<close>
  instead: a \<open>Bot\<close> local unknown must dominate a live global rather than being
  resurrected by it. \<^const>\<open>gamma_state_lift\<close> then makes the \<open>Bot\<close> case discharge
  itself, since \<open>gamma_state_lift Bot = {}\<close> makes the membership premise
  vacuously false; no explicit \<open>Bot\<close>/\<open>Lifted\<close> case split is needed at any
  assumption below.
\<close>

locale sound_effectful_transfer =
  fixes gs :: "vname => bool"
    and etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
  assumes etf_sound_skip[intro]:
    "\<forall>u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         s \<in> gamma_state_lift (etf_collecting_full_lift (etf_skip etf u) \<sigma>))"
  assumes etf_sound_assign[intro]:
    "\<forall>x e u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         s(x := aval e s) \<in> gamma_state_lift (etf_collecting_full_lift (etf_assign etf x e u) \<sigma>))"
  assumes etf_sound_random[intro]:
    "\<forall>x u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)). \<forall>v.
         s(x := v) \<in> gamma_state_lift (etf_collecting_full_lift (etf_random etf x u) \<sigma>))"
  assumes etf_sound_branch[intro]:
    "\<forall>(b::bexp) (pol::bool) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)). bval b s = pol
       \<longrightarrow> s \<in> gamma_state_lift (etf_collecting_full_lift (etf_branch etf b pol u) \<sigma>))"
  assumes etf_sound_body[intro]:
    "\<forall>p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         s \<in> gamma_state_lift (etf_collecting_full_lift (etf_body etf p u) \<sigma>))"
  assumes etf_sound_return[intro]:
    "\<forall>(e::aexp option) p u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
           \<in> gamma_state_lift (etf_collecting_full_lift (etf_return etf e p u) \<sigma>))"
  assumes etf_sound_enter[intro]:
    "\<forall>xs (es::aexp list) u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
           \<in> gamma_state_lift (etf_collecting_full_lift (etf_enter etf xs es u) \<sigma>))"
  assumes etf_sound_event[intro]:
    "\<forall>ev u \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl u)) (glob_env \<sigma>)).
         s \<in> gamma_state_lift (etf_collecting_full_lift (etf_event etf ev u) \<sigma>))"
  assumes etf_sound_combine[intro]:
    "\<forall>dst cc ex \<sigma>. inr_slot_locals_bot gs \<sigma> \<longrightarrow>
       (\<forall>s \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl cc)) (glob_env \<sigma>)).
       \<forall>t \<in> gamma_state_lift (assemble_local_global (\<sigma> (Inl ex)) (glob_env \<sigma>)).
         combine_collect gs dst s t \<in> gamma_state_lift (etf_full (etf_combine etf dst cc ex) \<sigma>))"

text \<open>
  The keyed generator filters call-enter edges out of the intra predecessor fold
  and instead seeds each callee-entry frame with a fixed fresh local frame.  For
  that to stay sound the enter transfer must be bounded above by that fresh frame
  joined with the global environment: entering a procedure resets locals into the
  fresh frame and preserves only globals.  This is the upper-bound companion of
  @{const sound_effectful_transfer}'s lower-bound @{text etf_sound_enter}.
\<close>

text \<open>
  Formal parameters name locals.  \<^const>\<open>bind_formals_abs\<close> writes each formal
  into the callee's fresh frame, so a formal naming a global would write a
  caller-local value into a global slot and break the frame bound.  VIMP scoping
  supplies this; the CFG well-formedness discharges it at each enter edge.
\<close>

definition local_formals :: "(vname => bool) => vname list \<Rightarrow> bool" where
  "local_formals gs xs \<longleftrightarrow> (\<forall>x \<in> set xs. \<not> gs x)"

lemma local_formals_Nil [simp]: "local_formals gs []"
  unfolding local_formals_def by simp

text \<open>Concrete companion of \<open>bind_formals_abs_global\<close>: binding local
  formals leaves the global slots of the store untouched.\<close>
lemma bind_formals_global:
  assumes lf: "local_formals gs xs" and g: "gs x"
  shows "bind_formals xs vs s x = s x"
proof -
  have "x \<notin> set xs" using lf g by (auto simp: local_formals_def)
  thus ?thesis by (rule bind_formals_nonformal)
qed
lemma bind_formals_abs_global:
  assumes "local_formals gs xs" and "gs x"
  shows "bind_formals_abs xs avs \<sigma> x = \<sigma> x"
  using assms unfolding local_formals_def bind_formals_abs_def
proof (induction xs arbitrary: avs \<sigma>)
  case Nil thus ?case by simp
next
  case (Cons y ys)
  show ?case
  proof (cases avs)
    case Nil thus ?thesis by simp
  next
    case (Cons a rest)
    have "x \<noteq> y" using Cons.prems(1) Cons.prems(2) by auto
    then show ?thesis
      using Cons.IH[of rest "\<sigma>(y := a)"] Cons.prems local.Cons
      by simp
  qed
qed

locale sound_effectful_transfer_framed = sound_effectful_transfer +
  fixes fresh_frame :: "'a::sound_domain abs_state"
  assumes etf_enter_framed_le[intro]:
    "\<forall>xs (es::aexp list) u \<sigma>.
       local_formals gs xs \<longrightarrow>
       inr_slot_locals_bot gs \<sigma> \<longrightarrow> inl_slot_globals_bot gs \<sigma> \<longrightarrow>
       etf_full (etf_enter etf xs es u) \<sigma> \<le> assemble_local_global (Lifted fresh_frame) (glob_env \<sigma>)"

text \<open>
  The snapshot-compatible companion of @{locale sound_effectful_transfer_framed}:
  the enter bound holds under the weaker premise @{const inl_glob_le_glob_env}, so
  an analysis whose local slots carry globals can still discharge it.  Since
  @{const inl_slot_globals_bot} implies @{const inl_glob_le_glob_env}, this contract
  is stronger; the sublocale below recovers the publish contract, making every
  @{locale sound_effectful_transfer_framed} fact available here for free.
\<close>
locale sound_effectful_transfer_framed_le = sound_effectful_transfer +
  fixes fresh_frame :: "'a::sound_domain abs_state"
  assumes etf_enter_framed_glob_le[intro]:
    "\<forall>xs (es::aexp list) u \<sigma>.
       local_formals gs xs \<longrightarrow>
       inr_slot_locals_bot gs \<sigma> \<longrightarrow> inl_glob_le_glob_env gs \<sigma> \<longrightarrow>
       etf_full (etf_enter etf xs es u) \<sigma> \<le> assemble_local_global (Lifted fresh_frame) (glob_env \<sigma>)"

sublocale sound_effectful_transfer_framed_le \<subseteq> sound_effectful_transfer_framed gs etf fresh_frame
  by (simp add: sound_effectful_transfer_framed_def sound_effectful_transfer_axioms
        sound_effectful_transfer_framed_axioms_def
        etf_enter_framed_glob_le inl_slot_globals_bot_le_glob_env)

end

