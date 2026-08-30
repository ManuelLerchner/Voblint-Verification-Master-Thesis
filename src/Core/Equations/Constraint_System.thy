theory Constraint_System
  imports CFG_Enumeration "Voblint_CFG.CFG_Transfer" "Voblint_Domain.Abstract_Domain"
    "Voblint_VIMP.VIMP_Globals" "Voblint_VIMP.VIMP_Expr" "Voblint_VIMP.VIMP_Proc"
    "TD.Basics_side"
begin

section \<open>Equation system over a CFG\<close>

text \<open>
  Given:
    - A CFG  g
    - An abstract domain  D  (instance of abstract_domain)
    - Per-domain transfer functions for each edge action

  this theory fixes the per-edge/per-domain transfer interface
  (\<open>domain_transfer\<close>, \<open>apply_tf\<close>) and its soundness contract
  (\<open>sound_transfer\<close>) that every concrete
  equation-system generator is built from. The generators themselves --
  the side-effecting D/G equation system (\<open>DG_Framework\<close>'s \<open>dg_gen\<close>)
  solved by the verified top-down solver -- live downstream, in
  \<open>Solver/Context/DG\<close>.

  All transfer functions are parameterised over the domain via a locale
  so the same interface works for Sign, Interval, etc.
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
  Check_Event exp

record 'a domain_transfer =
  tf_assign    :: "vname => exp => ('a abs_state) => ('a abs_state)" ("assign\<^sup>#")
  tf_special   :: "special_call => vname => ('a abs_state) => ('a abs_state)" ("special\<^sup>#")
  tf_branch    :: "exp => bool => ('a abs_state) => ('a abs_state)" ("branch\<^sup>#")
  tf_skip      :: "('a abs_state) => ('a abs_state)" ("skip\<^sup>#")
  tf_body      :: "pname => ('a abs_state) => ('a abs_state)" ("body\<^sup>#")
  tf_return    :: "exp option => pname => ('a abs_state) => ('a abs_state)" ("return\<^sup>#")
  tf_enter     :: "vname list \<Rightarrow> exp list \<Rightarrow> ('a abs_state) \<Rightarrow> ('a abs_state)" ("enter\<^sup>#")
  tf_event     :: "analysis_event => ('a abs_state) => ('a abs_state)" ("event\<^sup>#")
  tf_caller_cont :: "call_info => ('a abs_state) => ('a abs_state)" ("caller'_cont\<^sup>#")
  tf_combine_env :: "call_info => ('a abs_state) => ('a abs_state) => ('a abs_state)" ("combine'_env\<^sup>#")

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
  | "apply_tf tf (EA_Special sc x)   \<sigma> = special\<^sup># tf sc x \<sigma>"
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

lemma apply_tf_EA_Special [simp]:
  "apply_tf tf (EA_Special sc x) = special\<^sup># tf sc x"
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
    and special: "\<And>sc x. F (EA_Special sc x) = H (apply_tf tf (EA_Special sc x))"
    and assm: "\<And>b. F (EA_Assume b) = H (apply_tf tf (EA_Assume b))"
    and assm_not: "\<And>b. F (EA_AssumeNot b) = H (apply_tf tf (EA_AssumeNot b))"
    and ret: "\<And>e p. F (EA_Ret e p) = H (apply_tf tf (EA_Ret e p))"
    and check: "\<And>c. F (EA_Check c) = H (apply_tf tf (EA_Check c))"
  shows "F a = H (apply_tf tf a)"
  by (cases a) (simp_all add: nop assign special assm assm_not ret check)

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
where
  "combine_env_abs gs sc se = (\<lambda>x. if gs x then se x else sc x)"

lemma combine_env_abs_mono:
  fixes sc1 sc2 se1 se2 :: "'a::order abs_state"
  assumes "sc1 \<le> sc2" and "se1 \<le> se2"
  shows "combine_env_abs gs sc1 se1 \<le> combine_env_abs gs sc2 se2"
  using assms by (auto simp: combine_env_abs_def le_fun_def)

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for \<open>combine_env_abs gs sc se\<close>.
  A pure sound_domain fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
  \<open>combine_env_abs\<close> is the fixed structural default; the \<open>combine_env\<^sup>#\<close> notation
  belongs to the domain-supplied \<open>tf_combine_env\<close>, not to this helper.
\<close>
lemma combine_env_sound:
  fixes \<sigma>c \<sigma>e :: "'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env_abs gs \<sigma>c \<sigma>e\<rbrakk>"
proof -
  from sc have Vc: "\<forall>z. s z \<in> gamma (\<sigma>c z)"
    unfolding gamma_state_def by auto
  from se have Ve: "\<forall>z. t z \<in> gamma (\<sigma>e z)"
    unfolding gamma_state_def by auto
  show ?thesis unfolding gamma_state_def combine_env_abs_def combine_env_def
    using Vc Ve by auto
qed

lemma gamma_state_upd:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes s: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and v: "v \<in> gamma a"
  shows "s(x := v) \<in> \<lbrakk>\<sigma>(x := a)\<rbrakk>"
  using s v unfolding gamma_state_def by auto

text \<open>
  Binding formals preserves soundness: pointwise-sound actual values bound to the
  same formals yield a sound entry state.
\<close>
lemma bind_formals_sound:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes s: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
    and vals: "list_all2 (\<lambda>v a. v \<in> gamma a) vs avs"
  shows "bind_formals xs vs s \<in> \<lbrakk>bind_formals xs avs \<sigma>\<rbrakk>"
  using vals s
proof (induction xs arbitrary: vs avs s \<sigma>)
  case Nil
  then show ?case
    by simp
next
  case (Cons x xs)
  show ?case
  proof (cases vs)
    case Nil
    then show ?thesis
      using Cons.prems
      by simp
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
            \<in> \<lbrakk>bind_formals xs avs' (\<sigma>(x := a))\<rbrakk>"
      by (rule Cons.IH[OF rest upd])
    then show ?thesis
      unfolding Cons avs zip_Cons_Cons fold.simps comp_apply prod.case .
  qed
qed

lemma bind_formals_mono:
  fixes \<sigma>1 \<sigma>2 :: "'a::order abs_state"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) avs1 avs2"
  shows "bind_formals xs avs1 \<sigma>1 \<le> bind_formals xs avs2 \<sigma>2"
  using vals base
proof (induction xs arbitrary: avs1 avs2 \<sigma>1 \<sigma>2)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases avs1)
    case Nil
    then show ?thesis
      using Cons.prems by simp
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
      by (simp add: fun_upd_def)
  qed
qed

text \<open>
  Generic procedure-entry frame: reset locals to a fixed, fully-imprecise
  \<open>top_val\<close>, keep globals, then bind the formals via @{const bind_formals}.
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
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a) \<Rightarrow> vname list \<Rightarrow> exp list
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_D gs top_val aval_abs xs es \<sigma> =
     bind_formals xs (map (\<lambda>e. aval_abs e \<sigma>) es) (enter_frame_D gs top_val \<sigma>)"

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
  from bind_formals_sound[OF base vals]
  show ?thesis unfolding enter_D_def .
qed

lemma enter_D_mono:
  fixes top_val :: "'a::order"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) (map (\<lambda>e. aval_abs e \<sigma>1) es) (map (\<lambda>e. aval_abs e \<sigma>2) es)"
  shows "enter_D gs top_val aval_abs xs es \<sigma>1 \<le> enter_D gs top_val aval_abs xs es \<sigma>2"
  unfolding enter_D_def
  by (rule bind_formals_mono[OF enter_frame_D_mono[OF base] vals])

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

text \<open>The return-value write is a single-slot update, hence monotone in both the
  written value and the state it writes into.  Any combine built over it inherits
  monotonicity from this one fact.\<close>

lemma combine_assign_abs_mono:
  fixes s1 s2 :: "'a::order abs_state"
  assumes v: "v1 \<le> v2" and s: "s1 \<le> s2"
  shows "combine_assign\<^sup># dst v1 s1 \<le> combine_assign\<^sup># dst v2 s2"
  using assms by (cases dst) (auto simp: le_fun_def)

text \<open>
  Return combination joins caller locals with callee globals and then assigns the
  callee's @{const ret_var} to the optional destination.  The ordinary abstract
  state update publishes the result without domain-specific return machinery.
\<close>
definition combine_collect_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    ("combine\<^sup>#") where
  "combine_collect_abs gs dst \<sigma>c \<sigma>e = combine_assign\<^sup># dst (\<sigma>e ret_var) (combine_env_abs gs \<sigma>c \<sigma>e)"

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
  "combine\<^sup># gs None a b = combine_env_abs gs a b"
  by (simp add: combine_collect_abs_def)

text \<open>
  Per-analysis return combine.  \<^const>\<open>combine_collect_abs\<close> fixes the environment
  merge to \<^const>\<open>combine_env_abs\<close>; \<open>tf_combine_collect_abs\<close> instead reads the merge
  from the \<^typ>\<open>'a domain_transfer\<close> in scope, so each analysis may supply its own
  sound over-approximation of \<^const>\<open>combine_env\<close> instead of the structural
  local/global split.  The return-value write stays \<^const>\<open>combine_assign_abs\<close>: it is
  already domain-agnostic under the function-based \<^typ>\<open>'a abs_state\<close> representation,
  so only the merge step is a per-analysis choice.  This mirrors Goblint's own
  \<open>Spec.combine_env\<close>/\<open>Spec.combine_assign\<close> split: there is no primitive whole
  \<open>combine\<close>, only the domain-supplied \<open>combine_env\<^sup>#\<close> followed by the generic
  \<open>combine_assign\<^sup>#\<close>.
\<close>
text \<open>
  \<open>caller_cont\<^sup>#\<close> is logically an \<^emph>\<open>output of enter\<close>, not a step of the combine:
  Goblint's \<open>Spec.enter\<close> returns \<open>(D.t * D.t) list\<close> and \<open>constraints.ml\<close> hands the first
  component -- the caller continuation -- to \<open>combine_env\<close> as \<open>cd\<close>, while the second seeds
  the callee entry.  \<open>tf_enter_pair\<close> below is that protocol, stated as one function
  from the call-site state to the pair.  The combine operations accordingly take the
  \<^emph>\<open>continuation\<close> as their caller operand, never the raw call-site state: nothing in
  \<open>combine_env\<^sup>#\<close> or \<open>tf_combine_collect_abs\<close> reapplies \<open>caller_cont\<^sup>#\<close>.

  Its contract is continuation-specific rather than a preservation law: \<open>caller_cont\<^sup># ci\<close>
  over-approximates the pre-call concrete caller store, retaining only the information meant
  to stay usable once the call returns, and may forget abstract facts a callee could
  invalidate -- exactly Goblint's \<open>varEq\<close>, whose \<open>combine_env\<close> meets the callee exit with a
  taint-filtered caller state.  Forgetting is sound because it moves up the abstract order,
  where \<open>gamma\<close> only grows.  The obligation is stated against the same concrete store because
  VIMP has no concrete caller-side transition at a call; a language that gained one would
  generalize the obligation's concrete side, not this field's role.
\<close>
definition tf_enter_pair ::
    "'a domain_transfer \<Rightarrow> call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state" where
  "tf_enter_pair tf ci \<sigma> =
     (caller_cont\<^sup># tf ci \<sigma>, enter\<^sup># tf (ci_formals ci) (ci_args ci) \<sigma>)"

lemma fst_tf_enter_pair [simp]: "fst (tf_enter_pair tf ci \<sigma>) = caller_cont\<^sup># tf ci \<sigma>"
  by (simp add: tf_enter_pair_def)

lemma snd_tf_enter_pair [simp]:
  "snd (tf_enter_pair tf ci \<sigma>) = enter\<^sup># tf (ci_formals ci) (ci_args ci) \<sigma>"
  by (simp add: tf_enter_pair_def)

text \<open>The whole return operation: \<open>combine_env\<^sup>#\<close> on the continuation and the callee exit,
  then the generic \<^const>\<open>combine_assign_abs\<close> writing the callee's @{const ret_var} into the
  destination.  \<open>\<sigma>cont\<close> is \<^emph>\<open>already\<close> \<^const>\<open>tf_enter_pair\<close>'s first component.\<close>
definition tf_combine_collect_abs ::
    "'a domain_transfer \<Rightarrow> call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "tf_combine_collect_abs tf ci \<sigma>cont \<sigma>e =
     combine_assign\<^sup># (ci_dst ci) (\<sigma>e ret_var) (combine_env\<^sup># tf ci \<sigma>cont \<sigma>e)"

text \<open>The fixed structural merge is the special case where \<open>tf_combine_env\<close> is
  \<^const>\<open>combine_env_abs\<close>: the general definition specializes to the old one by
  instantiation, rather than duplicating it.\<close>
lemma tf_combine_collect_abs_combine_env_abs:
  assumes "tf_combine_env tf = (\<lambda>_. combine_env_abs gs)"
  shows "tf_combine_collect_abs tf ci = combine\<^sup># gs (ci_dst ci)"
  unfolding tf_combine_collect_abs_def combine_collect_abs_def assms ..

text \<open>Monotonicity of the analysis-supplied combine reduces to monotonicity of its
  merge: the return-value write is \<^const>\<open>combine_assign_abs\<close>, monotone in both the
  written value and the state it updates.  The caller operand here is already the
  continuation, so no \<open>caller_cont\<^sup>#\<close> monotonicity enters: that obligation belongs to
  whatever supplies the continuation.\<close>
lemma tf_combine_collect_abs_mono:
  fixes \<sigma>c1 \<sigma>c2 \<sigma>e1 \<sigma>e2 :: "'a::order abs_state"
  assumes merge: "\<And>a1 a2 b1 b2 :: 'a abs_state.
      a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> combine_env\<^sup># tf ci a1 b1 \<le> combine_env\<^sup># tf ci a2 b2"
    and c: "\<sigma>c1 \<le> \<sigma>c2" and e: "\<sigma>e1 \<le> \<sigma>e2"
  shows "tf_combine_collect_abs tf ci \<sigma>c1 \<sigma>e1 \<le> tf_combine_collect_abs tf ci \<sigma>c2 \<sigma>e2"
proof (cases "ci_dst ci")
  case None
  then show ?thesis
    using merge[OF c e] by (simp add: tf_combine_collect_abs_def)
next
  case (Some x)
  then show ?thesis
    using merge[OF c e] e
    by (simp add: tf_combine_collect_abs_def le_fun_def)
qed

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
  have base: "combine_env gs s t \<in> \<lbrakk>combine_env_abs gs \<sigma>c \<sigma>e\<rbrakk>"
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
    "\<forall>x (a::exp) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
  assumes tf_sound_special_for[intro]:
    "\<forall>sc x \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<forall>v. special_result sc s v \<longrightarrow> s(x := v) \<in> \<lbrakk>special\<^sup># tf sc x \<sigma>\<rbrakk>"
  assumes tf_sound_branch_for[intro]:
    "\<forall>(b::exp) (pol::bool) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. truthy (aval b s) = pol
       \<longrightarrow> s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
  assumes tf_sound_skip_for[intro]:
    "\<forall>\<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
  assumes tf_sound_body_for[intro]:
    "\<forall>p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
  assumes tf_sound_return_for[intro]:
    "\<forall>(e::exp option) p \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
         \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
  assumes tf_sound_enter_for[intro]:
    "\<forall>xs (es::exp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
       bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
         \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
  assumes tf_sound_event_for[intro]:
    "\<forall>ev \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
  assumes tf_sound_caller_cont_for[intro]:
    "\<forall>ci \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>caller_cont\<^sup># tf ci \<sigma>\<rbrakk>"
  assumes tf_sound_combine_env_for[intro]:
    "\<forall>ci \<sigma>cont \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>cont\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>.
       combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"

context sound_transfer_for
begin

lemma tf_sound_assign_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
  using tf_sound_assign_for by blast

lemma tf_sound_special_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> special_result sc s v \<Longrightarrow> s(x := v) \<in> \<lbrakk>special\<^sup># tf sc x \<sigma>\<rbrakk>"
  using tf_sound_special_for by blast

lemma tf_sound_branch_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow> s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
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

lemma tf_sound_caller_cont_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>caller_cont\<^sup># tf ci \<sigma>\<rbrakk>"
  using tf_sound_caller_cont_for by blast

lemma tf_sound_combine_env_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>cont\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
     combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
  using tf_sound_combine_env_for by blast

text \<open>The two halves composed at a call site: the caller's own state goes through
  \<open>caller_cont\<^sup>#\<close> first, exactly as \<^const>\<open>tf_enter_pair\<close> produces it, and the merge is then
  sound at that continuation.  This is the form a combine tree needs, since the tree
  reconstructs the raw call-site state rather than a stored continuation.\<close>
lemma tf_sound_combine_env_at_call_forD[intro]:
  "s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
     combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci (caller_cont\<^sup># tf ci \<sigma>c) \<sigma>e\<rbrakk>"
  by (rule tf_sound_combine_env_forD[OF tf_sound_caller_cont_forD])

text \<open>Soundness of the analysis-supplied whole combine.  The merge obligation is the
  locale's own \<open>tf_sound_combine_env_for\<close>; the destination slot is sound because the
  callee's @{const ret_var} slot is.  No extra assumption on the analysis is needed:
  a sound \<open>combine_env\<^sup>#\<close> already makes \<^const>\<open>tf_combine_collect_abs\<close> sound.\<close>
lemma tf_sound_combine_collect_forD[intro]:
  assumes sc: "s \<in> \<lbrakk>\<sigma>cont\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_collect gs (ci_dst ci) s t
           \<in> \<lbrakk>tf_combine_collect_abs tf ci \<sigma>cont \<sigma>e\<rbrakk>"
proof -
  have base: "combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
    by (rule tf_sound_combine_env_forD[OF sc se])
  have ret: "t ret_var \<in> gamma (\<sigma>e ret_var)"
    using se unfolding gamma_state_def by auto
  show ?thesis
  proof (cases "ci_dst ci")
    case None
    then show ?thesis
      using base by (simp add: combine_collect_def tf_combine_collect_abs_def)
  next
    case (Some x)
    then show ?thesis
      using base ret
      unfolding gamma_state_def combine_collect_def tf_combine_collect_abs_def
      by auto
  qed
qed

text \<open>The same statement at a call site, where the caller operand is the raw call-site
  state and the continuation is produced on the spot by \<open>caller_cont\<^sup>#\<close>.\<close>
lemma tf_sound_combine_collect_at_call_forD[intro]:
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_collect gs (ci_dst ci) s t
           \<in> \<lbrakk>tf_combine_collect_abs tf ci (caller_cont\<^sup># tf ci \<sigma>c) \<sigma>e\<rbrakk>"
  by (rule tf_sound_combine_collect_forD[OF tf_sound_caller_cont_forD[OF sc] se])

end

lemma sound_transferI_for:
  fixes gs :: "vname => bool"
    and tf :: "'a::sound_domain domain_transfer"
  assumes assign[intro]:
    "\<And>x a \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
    and special[intro]:
    "\<And>sc x \<sigma> s v. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> special_result sc s v \<Longrightarrow>
       s(x := v) \<in> \<lbrakk>special\<^sup># tf sc x \<sigma>\<rbrakk>"
    and branch[intro]:
    "\<And>b pol \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow>
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
    and caller_cont[intro]:
    "\<And>ci \<sigma> s. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>caller_cont\<^sup># tf ci \<sigma>\<rbrakk>"
    and combine[intro]:
    "\<And>ci \<sigma>cont \<sigma>e s t. s \<in> \<lbrakk>\<sigma>cont\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
       combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
  shows "sound_transfer_for gs tf"
proof unfold_locales
  show "\<forall>x a \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
      s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
    using assign by blast
  show "\<forall>sc x \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. \<forall>v. special_result sc s v \<longrightarrow>
      s(x := v) \<in> \<lbrakk>special\<^sup># tf sc x \<sigma>\<rbrakk>"
    using special by blast
  show "\<forall>b pol \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. truthy (aval b s) = pol \<longrightarrow>
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
  show "\<forall>xs (es::exp list) \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>.
      bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
        \<in> \<lbrakk>tf_enter tf xs es \<sigma>\<rbrakk>"
    using enter by blast
  show "\<forall>ev \<sigma>. \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
    using event by blast
  show "\<forall>ci \<sigma> . \<forall>s \<in> \<lbrakk>\<sigma>\<rbrakk>. s \<in> \<lbrakk>caller_cont\<^sup># tf ci \<sigma>\<rbrakk>"
    using caller_cont by blast
  show "\<forall>ci \<sigma>cont \<sigma>e. \<forall>s \<in> \<lbrakk>\<sigma>cont\<rbrakk>. \<forall>t \<in> \<lbrakk>\<sigma>e\<rbrakk>.
      combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
    using combine by blast
qed

text \<open>The structural instance discharges both call-boundary obligations of
  @{thm [source] sound_transferI_for} outright: an identity continuation keeps the caller
  state, and \<^const>\<open>combine_env_abs\<close> is sound by @{thm [source] combine_env_sound}.\<close>
lemma sound_transfer_caller_cont_idI:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes eq: "tf_caller_cont tf = (\<lambda>_ \<sigma>. \<sigma>)" and sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>caller_cont\<^sup># tf ci \<sigma>\<rbrakk>"
  unfolding eq using sv by simp

lemma sound_transfer_combine_env_absI:
  fixes \<sigma>cont \<sigma>e :: "'a::sound_domain abs_state"
  assumes eq: "tf_combine_env tf = (\<lambda>_. combine_env_abs gs)"
    and sc: "s \<in> \<lbrakk>\<sigma>cont\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
  unfolding eq by (rule combine_env_sound[OF sc se])



end

