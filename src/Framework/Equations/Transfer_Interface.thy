theory Transfer_Interface
  imports CFG_Enumeration "Voblint_CFG.CFG_Transfer" "Voblint_Domain.Nonrelational_State"
    "Voblint_VIMP.VIMP_Globals" "Voblint_VIMP.VIMP_Expr" "Voblint_VIMP.VIMP_Proc"
begin

section \<open>CFG transfer interface\<close>

text \<open>
  Given:
    - A CFG  g
    - An abstract domain  D  (instance of sound_domain)
    - Per-domain transfer functions for each edge action

  this theory fixes the per-edge/per-domain transfer interface
  (\<open>domain_transfer\<close>, \<open>apply_tf\<close>) and its soundness contract
  (\<open>sound_transfer_for\<close>) that every concrete
  equation-system generator is built from. The generators themselves --
  the side-effecting D/G equation system (the keyed seeded generator)
  solved by the verified top-down solver -- live downstream, in
  \<open>Solver/Context/DG\<close>.

  The record is intentionally specialized to the pointwise \<open>abs_state\<close> carrier
  used by Base analyses. Its \<open>'a\<close> parameter selects the abstract value domain,
  so the same \<open>domain_transfer\<close> record works for Sign, Interval, etc. The D/G
  framework remains carrier-generic through \<open>dg_spec\<close>; analyses with other
  local or global carriers instantiate that interface directly. Soundness is
  packaged separately in the \<open>sound_transfer_for\<close> locale.
\<close>

subsection \<open>Abstract transfer function record\<close>

text \<open>
  A domain_transfer bundles ordinary CFG-action transformers together with the
  interprocedural call-entry and return-combination operations.
  Parameterised by the abstract value type 'a.
\<close>

text \<open>
  \<open>tf_branch\<close> is the single, polarity-parametrized branch transfer, matching Goblint's
  \<open>Spec.branch : man -> exp -> bool -> D.t\<close> (one operation taking a boolean outcome, not two
  independently-named callbacks). \<open>tf_branch tf b True\<close> takes the branch where \<open>b\<close> evaluates
  true; \<open>tf_branch tf b False\<close> takes the branch where \<open>b\<close> evaluates false.
\<close>

text \<open>
  An \<open>analysis_event\<close> is an analyzer-visible occurrence distinct from an ordinary
  control-flow transfer: a domain may observe it, but it must not by itself refine
  execution (see the note on \<open>tf_event\<close>'s dispatch below). This matches Goblint's
  own separation of its ordinary
  \<open>Spec\<close> transfer methods (\<open>assign\<close>/\<open>branch\<close>/\<open>skip\<close>/...) from \<open>Spec.event\<close>, which
  handles \<open>Events.Assert\<close> and similar occurrences outside the ordinary transfer
  vocabulary. Voblint's sole current event is a check's condition; the vocabulary is
  deliberately left open rather than pre-populated, so that a future VIMP source
  construct with no current counterpart (e.g. a diagnostic-only annotation) adds a
  constructor here instead of a new domain-transfer field. A construct that narrows
  feasible execution, such as \<open>assume\<close>, is not a candidate: it belongs on \<open>tf_branch\<close>
  or a new refining field, not here.
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
  tf_enter     :: "call_info \<Rightarrow> ('a abs_state) \<Rightarrow> ('a abs_state) \<times> ('a abs_state)" ("enter\<^sup>#")
  tf_event     :: "analysis_event => ('a abs_state) => ('a abs_state)" ("event\<^sup>#")
  tf_combine_env :: "call_info => ('a abs_state) => ('a abs_state) => ('a abs_state)" ("combine'_env\<^sup>#")

subsection \<open>Apply transfer function to one edge\<close>

text \<open>
  \<open>EA_Nop\<close>, \<open>EA_Ret\<close>, and (via \<^const>\<open>tf_body\<close>, at procedure entry rather than
  through this dispatcher) function-body entry are each a distinct transfer operation
  with its own transfer field, matching Goblint's \<open>skip\<close>/\<open>return\<close>/entry-then-body split,
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
text \<open>Stated point-free (no abstract state on either side): simp already rewrites an
  applied occurrence \<open>apply_tf tf a \<sigma>\<close> via these same equations, matching them on the
  \<open>apply_tf tf a\<close> subterm, so a call site that carries \<open>apply_tf tf a\<close> itself as an
  unapplied function value needs no separate lemma family to reach the underlying
  \<open>domain_transfer\<close> field.\<close>
fun apply_tf :: "'a domain_transfer
                 => edge_action
                 => ('a abs_state)
                 => ('a abs_state)" where
    "apply_tf tf EA_Nop              = skip\<^sup># tf"
  | "apply_tf tf (EA_Assign x a)     = assign\<^sup># tf x a"
  | "apply_tf tf (EA_Special sc x)   = special\<^sup># tf sc x"
  | "apply_tf tf (EA_Assume b)       = branch\<^sup># tf b True"
  | "apply_tf tf (EA_AssumeNot b)    = branch\<^sup># tf b False"
  | "apply_tf tf (EA_Ret e p)        = return\<^sup># tf e p"
  | "apply_tf tf (EA_Check c)        = event\<^sup># tf (Check_Event c)"

subsection \<open>The structural environment combine\<close>

lemma combine_env_mono:
  fixes sc1 sc2 se1 se2 :: "'a::order abs_state"
  assumes "sc1 \<le> sc2" and "se1 \<le> se2"
  shows "combine_env gs sc1 se1 \<le> combine_env gs sc2 se2"
  using assms by (auto simp: combine_env_def le_fun_def)

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for \<open>combine_env gs sc se\<close>.
  A pure sound_domain fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
  \<open>combine_env\<close> is the fixed structural default; the \<open>combine_env\<^sup>#\<close> notation
  belongs to the domain-supplied \<open>tf_combine_env\<close>, not to this helper.
\<close>
lemma combine_env_sound:
  fixes \<sigma>c \<sigma>e :: "'a::sound_domain abs_state"
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env gs \<sigma>c \<sigma>e\<rbrakk>"
  using assms by (auto simp: gamma_state_def le_fun_def)

subsection \<open>Generic soundness and monotonicity helpers\<close>

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
  using assms apply (induction xs arbitrary: vs avs s \<sigma>)
  apply simp
  apply (case_tac vs; case_tac avs)
  by (auto simp add: gamma_state_upd)

lemma bind_formals_mono:
  fixes \<sigma>1 \<sigma>2 :: "'a::order abs_state"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) avs1 avs2"
  shows "bind_formals xs avs1 \<sigma>1 \<le> bind_formals xs avs2 \<sigma>2"
  using assms apply (induction xs arbitrary: avs1 avs2 \<sigma>1 \<sigma>2)
  apply simp
  apply (case_tac avs1; case_tac avs2)
  by (auto simp add: le_fun_def)

subsection \<open>Procedure entry: binding formals and resetting the frame\<close>

text \<open>
  Generic procedure-entry frame: reset locals to a fixed, fully-imprecise
  \<open>top_val\<close>, keep globals, then bind the formals via @{const bind_formals}.
  Every domain's own enter-frame construction (Sign's @{text enter_frame_sign},
  Interval's @{text enter_frame_ivl}) is this same shape, differing only in
  which value stands for "unknown" -- so this is parameterised over that one
  value rather than duplicated per domain. \<^const>\<open>enter_frame\<close> is the same
  structural selector \<open>enter_state\<close> already reuses at the concrete reset
  value \<open>0\<close>; the two never diverge because both read the same definition.
\<close>

lemma enter_frame_sound:
  fixes top_val :: "'a::sound_domain"
  assumes sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and top_full: "gamma top_val = UNIV"
  shows "enter_state gs s \<in> \<lbrakk>enter_frame gs top_val \<sigma>\<rbrakk>"
  unfolding gamma_state_def enter_state_def
  using gamma_stateD[OF sv] top_full by auto

lemma enter_frame_mono:
  fixes top_val :: "'a::order"
  assumes "\<sigma>1 \<le> \<sigma>2"
  shows "enter_frame gs top_val \<sigma>1 \<le> enter_frame gs top_val \<sigma>2"
  by (simp add: assms le_funD le_funI)

definition enter_D ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a) \<Rightarrow> vname list \<Rightarrow> exp list
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "enter_D gs top_val aval_abs xs es \<sigma> =
     bind_formals xs (map (\<lambda>e. aval_abs e \<sigma>) es) (enter_frame gs top_val \<sigma>)"

lemma enter_D_sound:
  fixes top_val :: "'a::sound_domain"
  assumes sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and top_full: "gamma top_val = UNIV"
    and vals: "list_all2 (\<lambda>v a. v \<in> gamma a)
                 (map (\<lambda>e. aval e s) es) (map (\<lambda>e. aval_abs e \<sigma>) es)"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state gs s)
           \<in> \<lbrakk>enter_D gs top_val aval_abs xs es \<sigma>\<rbrakk>"
  by (simp add: bind_formals_sound enter_D_def enter_frame_sound sv top_full vals)

lemma enter_D_mono:
  fixes top_val :: "'a::order"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) (map (\<lambda>e. aval_abs e \<sigma>1) es) (map (\<lambda>e. aval_abs e \<sigma>2) es)"
  shows "enter_D gs top_val aval_abs xs es \<sigma>1 \<le> enter_D gs top_val aval_abs xs es \<sigma>2"
  by (simp add: bind_formals_mono enter_D_def enter_frame_mono local.base vals)

text \<open>
  The whole call-boundary answer a domain_transfer's \<open>tf_enter\<close> field supplies: the
  caller continuation (first component, identity here -- the caller's own store is kept
  verbatim) paired with the callee entry (second component, \<^const>\<open>enter_D\<close>'s frame
  reset and formal binding read off \<^typ>\<open>call_info\<close> instead of separate formals/args
  arguments). Every current domain instantiates \<open>tf_enter\<close> with this combinator
  directly; a domain that ever needs a non-identity continuation would supply its own
  first component instead of reusing it.
\<close>
definition enter_pair_D ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a) \<Rightarrow> call_info \<Rightarrow> 'a abs_state
   \<Rightarrow> 'a abs_state \<times> 'a abs_state" where
  "enter_pair_D gs top_val aval_abs ci \<sigma> =
     (\<sigma>, enter_D gs top_val aval_abs (ci_formals ci) (ci_args ci) \<sigma>)"

lemma enter_pair_D_sound:
  fixes top_val :: "'a::sound_domain"
  assumes sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>" and top_full: "gamma top_val = UNIV"
    and vals: "list_all2 (\<lambda>v a. v \<in> gamma a)
                 (map (\<lambda>e. aval e s) (ci_args ci)) (map (\<lambda>e. aval_abs e \<sigma>) (ci_args ci))"
  shows "s \<in> \<lbrakk>fst (enter_pair_D gs top_val aval_abs ci \<sigma>)\<rbrakk>"
    and "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state gs s)
           \<in> \<lbrakk>snd (enter_pair_D gs top_val aval_abs ci \<sigma>)\<rbrakk>"
  using assms unfolding enter_D_def enter_pair_D_def by (auto simp add: bind_formals_sound enter_frame_sound top_full)

lemma enter_pair_D_mono:
  fixes top_val :: "'a::order"
  assumes base: "\<sigma>1 \<le> \<sigma>2"
    and vals: "list_all2 (\<le>) (map (\<lambda>e. aval_abs e \<sigma>1) (ci_args ci)) (map (\<lambda>e. aval_abs e \<sigma>2) (ci_args ci))"
  shows "fst (enter_pair_D gs top_val aval_abs ci \<sigma>1) \<le> fst (enter_pair_D gs top_val aval_abs ci \<sigma>2)"
    and "snd (enter_pair_D gs top_val aval_abs ci \<sigma>1) \<le> snd (enter_pair_D gs top_val aval_abs ci \<sigma>2)"
  using assms unfolding enter_pair_D_def by (auto simp add: enter_D_mono) 

subsection \<open>The structural return combine\<close>

text \<open>The return-value write is a single-slot update, hence monotone in both the
  written value and the state it writes into.  Any combine built over it inherits
  monotonicity from this one fact.\<close>

lemma combine_assign_mono:
  fixes s1 s2 :: "'a::order abs_state"
  assumes v: "v1 \<le> v2" and s: "s1 \<le> s2"
  shows "combine_assign dst v1 s1 \<le> combine_assign dst v2 s2"
  using assms by (cases dst) (auto simp: le_fun_def)

text \<open>
  Return combination joins caller locals with callee globals and then assigns the
  callee's @{const ret_var} to the optional destination.  The ordinary abstract
  state update publishes the result without domain-specific return machinery.
\<close>
definition combine_collect_abs ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    ("combine\<^sup>#") where
  "combine_collect_abs gs dst \<sigma>c \<sigma>e =
     combine_assign dst (\<sigma>e ret_var) (combine_env gs \<sigma>c \<sigma>e)"

lemma combine_collect_abs_mono:
  fixes \<sigma>c1 \<sigma>c2 \<sigma>e1 \<sigma>e2 :: "'a::order abs_state"
  assumes c: "\<sigma>c1 \<le> \<sigma>c2" and e: "\<sigma>e1 \<le> \<sigma>e2"
  shows "combine\<^sup># gs dst \<sigma>c1 \<sigma>e1 \<le> combine\<^sup># gs dst \<sigma>c2 \<sigma>e2"
  unfolding combine_collect_abs_def
  by (rule combine_assign_mono[OF le_funD[OF e] combine_env_mono[OF c e]])

text \<open>
  The binary env-combine is the destination-free instance of the
  return-threaded combine: with no destination the return slot is not written.
\<close>
lemma combine_collect_abs_None[simp]:
  "combine\<^sup># gs None a b = combine_env gs a b"
  by (simp add: combine_collect_abs_def)

subsection \<open>The analysis-supplied call boundary\<close>

text \<open>
  Per-analysis return combine.  \<^const>\<open>combine_collect_abs\<close> fixes the environment
  merge to \<^const>\<open>combine_env\<close>; \<open>tf_combine_collect_abs\<close> instead reads the merge
  from the \<^typ>\<open>'a domain_transfer\<close> in scope, so each analysis may supply its own
  sound over-approximation of \<^const>\<open>combine_env\<close> instead of the structural
  local/global split.  The return-value write stays \<^const>\<open>combine_assign\<close>: it is
  already domain-agnostic under the function-based \<^typ>\<open>'a abs_state\<close> representation,
  so only the merge step is a per-analysis choice.  In Goblint both \<open>Spec.combine_env\<close>
  and \<open>Spec.combine_assign\<close> are analysis-supplied; here the split is nominal, not a
  faithful reproduction of that pair -- the field names match Goblint's, but only
  \<open>combine_env\<^sup>#\<close> is actually per-analysis, because this representation already makes
  the return-value write generic.
\<close>
text \<open>
  \<^const>\<open>fst\<close> \<open>(enter\<^sup># tf ci \<sigma>)\<close> is Goblint's \<open>Spec.enter\<close>'s caller-continuation half:
  Goblint's \<open>enter\<close> returns \<open>(D.t * D.t) list\<close> and \<open>constraints.ml\<close> hands the first
  component of the (here, single) pair -- the caller continuation -- to \<open>combine_env\<close> as
  \<open>cd\<close>, while the second seeds the callee entry.  \<open>enter\<^sup>#\<close> models that same caller/callee
  pair directly, as one field returning exactly one pair rather than a list: no domain in
  this tree needs more than one entry state, so the list is not carried (a recorded,
  deferred simplification, not an oversight).  The combine operations accordingly take the
  \<^emph>\<open>continuation\<close> as their caller operand, never the raw call-site state: nothing in
  \<open>combine_env\<^sup>#\<close> or \<open>tf_combine_collect_abs\<close> reapplies \<open>fst (enter\<^sup># tf ci \<sigma>)\<close>.

  Its contract is continuation-specific rather than a preservation law: the first component
  over-approximates the pre-call concrete caller store, retaining only the information meant
  to stay usable once the call returns, and may forget abstract facts a callee could
  invalidate -- exactly Goblint's \<open>varEq\<close>, whose \<open>combine_env\<close> meets the callee exit with a
  taint-filtered caller state.  Forgetting is sound because it moves up the abstract order,
  where \<open>gamma\<close> only grows.  The obligation is stated against the same concrete store because
  VIMP has no concrete caller-side transition at a call; a language that gained one would
  generalize the obligation's concrete side, not this field's role.
\<close>

text \<open>The whole return operation: \<open>combine_env\<^sup>#\<close> on the continuation and the callee exit,
  then the generic \<^const>\<open>combine_assign\<close> writing the callee's @{const ret_var} into the
  destination.  \<open>\<sigma>cont\<close> is \<^emph>\<open>already\<close> the first component \<^const>\<open>fst\<close> \<open>(enter\<^sup># tf ci \<sigma>)\<close>
  would produce.\<close>
definition tf_combine_collect_abs ::
    "'a domain_transfer \<Rightarrow> call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" where
  "tf_combine_collect_abs tf ci \<sigma>cont \<sigma>e =
     combine_assign (ci_dst ci) (\<sigma>e ret_var) (combine_env\<^sup># tf ci \<sigma>cont \<sigma>e)"

text \<open>The fixed structural merge is the special case where \<open>tf_combine_env\<close> is
  \<^const>\<open>combine_env\<close>: the general definition specializes to the old one by
  instantiation, rather than duplicating it.\<close>
lemma tf_combine_collect_abs_combine_env:
  assumes "tf_combine_env tf = (\<lambda>_. combine_env gs)"
  shows "tf_combine_collect_abs tf ci = combine\<^sup># gs (ci_dst ci)"
  unfolding tf_combine_collect_abs_def combine_collect_abs_def assms ..

text \<open>Monotonicity of the analysis-supplied combine reduces to monotonicity of its
  merge: the return-value write is \<^const>\<open>combine_assign\<close>, monotone in both the
  written value and the state it updates.  The caller operand here is already the
  continuation, so no monotonicity of \<open>fst (enter\<^sup># tf ci \<sigma>)\<close> enters: that obligation
  belongs to whatever supplies the continuation.\<close>
lemma tf_combine_collect_abs_mono:
  fixes \<sigma>c1 \<sigma>c2 \<sigma>e1 \<sigma>e2 :: "'a::order abs_state"
  assumes merge: "\<And>a1 a2 b1 b2 :: 'a abs_state.
      a1 \<le> a2 \<Longrightarrow> b1 \<le> b2 \<Longrightarrow> combine_env\<^sup># tf ci a1 b1 \<le> combine_env\<^sup># tf ci a2 b2"
    and c: "\<sigma>c1 \<le> \<sigma>c2" and e: "\<sigma>e1 \<le> \<sigma>e2"
  shows "tf_combine_collect_abs tf ci \<sigma>c1 \<sigma>e1 \<le> tf_combine_collect_abs tf ci \<sigma>c2 \<sigma>e2"
  unfolding tf_combine_collect_abs_def
  by (rule combine_assign_mono[OF le_funD[OF e] merge[OF c e]])

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
  unfolding combine_collect_def combine_collect_abs_def
  using combine_env_sound[OF sc se] gamma_stateD[OF se]
  by (cases dst) (auto simp add: gamma_state_upd)

text \<open>
  Discharge the concrete return combine from an abstract bound: given
  \<open>combine\<^sup># dst sc se \<le> sr\<close>, any concrete return assembled from a
  caller store sound for \<open>sc\<close> and a callee-exit store sound for \<open>se\<close> lies in
  \<open>\<lbrakk>sr\<rbrakk>\<close>.  @{thm combine_collect_sound} carried to the bound by
  @{thm gamma_state_mono}.  The order-theoretic \<open>combine_bound\<close> shape is
  checkable against a post-solution, so no raw \<open><s|t>\<close> obligation reaches callers.
\<close>
lemma combine_collect_abs_bound_sound:
  fixes sc se sr :: "'a::sound_domain abs_state"
  assumes bound: "combine\<^sup># gs dst sc se \<le> sr"
    and sc: "s \<in> \<lbrakk>sc\<rbrakk>" and se: "t \<in> \<lbrakk>se\<rbrakk>"
  shows "combine_collect gs dst s t \<in> \<lbrakk>sr\<rbrakk>"
  using bound combine_collect_sound gamma_state_mono sc se subset_eq by metis

subsection \<open>The C-faithful initial store set\<close>

text \<open>
  \<^const>\<open>cinit_stores\<close> (\<^theory>\<open>Voblint_VIMP.VIMP_Globals\<close>) is the C-faithful initial
  store set. Any analysis that uses a domain-specific abstract seed \<open>s0\<close>
  satisfying \<open>cinit_stores gs \<subseteq> gamma_state s0\<close> may state its soundness
  theorem against \<open>cinit_stores gs\<close> rather than \<open>UNIV\<close>, matching VIMP's
  C-like initialization semantics.
\<close>

subsection \<open>The sound-transfer contract\<close>

text \<open>
  Sound transfer function: a domain_transfer tf that soundly over-approximates
  the concrete edge actions w.r.t. a sound_domain's concretization, relative to
  an explicit classifier gs.  Bundles the soundness obligations for each
  transfer operation as locale assumptions; \<open>tf_enter\<close>'s two components
  (caller continuation, callee entry) each get their own obligation.
  Concrete domains discharge these once via `interpretation`.
\<close>
locale sound_transfer_for =
  fixes gs :: "vname => bool"
    and tf :: "'a::sound_domain domain_transfer"
  assumes tf_sound_assign_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign\<^sup># tf x a \<sigma>\<rbrakk>"
  assumes tf_sound_special_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> special_result sc s v \<Longrightarrow> s(x := v) \<in> \<lbrakk>special\<^sup># tf sc x \<sigma>\<rbrakk>"
  assumes tf_sound_branch_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = pol \<Longrightarrow> s \<in> \<lbrakk>branch\<^sup># tf b pol \<sigma>\<rbrakk>"
  assumes tf_sound_skip_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip\<^sup># tf \<sigma>\<rbrakk>"
  assumes tf_sound_body_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body\<^sup># tf p \<sigma>\<rbrakk>"
  assumes tf_sound_return_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s))
         \<in> \<lbrakk>return\<^sup># tf e p \<sigma>\<rbrakk>"
  assumes tf_sound_enter_entry_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
       bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state gs s)
         \<in> \<lbrakk>snd (enter\<^sup># tf ci \<sigma>)\<rbrakk>"
  assumes tf_sound_event_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event\<^sup># tf ev \<sigma>\<rbrakk>"
  assumes tf_sound_enter_cont_for[intro]:
    "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>fst (enter\<^sup># tf ci \<sigma>)\<rbrakk>"
  assumes tf_sound_combine_env_for[intro]:
    "s \<in> \<lbrakk>\<sigma>cont\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
       combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"

text \<open>Each obligation above is stated directly as an inference rule (\<open>P\<^sub>1 \<Longrightarrow> \<dots> \<Longrightarrow> P\<^sub>n \<Longrightarrow> Q\<close>).
  Variables not fixed by the locale are implicitly generalized, so the assumptions compose
  directly with \<open>rule\<close>, \<open>OF\<close>, and \<open>auto\<close>; no separate Horn-clause restatement is needed.\<close>

context sound_transfer_for
begin

text \<open>The two halves composed at a call site: the caller's own state goes through
  \<open>fst (enter\<^sup># tf ci \<sigma>c)\<close> first, exactly as \<^const>\<open>tf_enter\<close> produces it, and the merge
  is then sound at that continuation.  This is the form a combine tree needs, since the tree
  reconstructs the raw call-site state rather than a stored continuation.\<close>
lemma tf_sound_combine_env_at_call_for[intro]:
  "s \<in> \<lbrakk>\<sigma>c\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>e\<rbrakk> \<Longrightarrow>
     combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci (fst (enter\<^sup># tf ci \<sigma>c)) \<sigma>e\<rbrakk>"
  by auto

text \<open>Soundness of the analysis-supplied whole combine.  The merge obligation is the
  locale's own \<open>tf_sound_combine_env_for\<close>; the destination slot is sound because the
  callee's @{const ret_var} slot is.  No extra assumption on the analysis is needed:
  a sound \<open>combine_env\<^sup>#\<close> already makes \<^const>\<open>tf_combine_collect_abs\<close> sound.\<close>
lemma tf_sound_combine_collect_for[intro]:
  assumes sc: "s \<in> \<lbrakk>\<sigma>cont\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_collect gs (ci_dst ci) s t
           \<in> \<lbrakk>tf_combine_collect_abs tf ci \<sigma>cont \<sigma>e\<rbrakk>"
  using assms apply (cases "ci_dst ci")
  by (auto simp add: combine_collect_None tf_sound_combine_env_for combine_collect_def gamma_stateD gamma_state_upd tf_combine_collect_abs_def)

text \<open>The same statement at a call site, where the caller operand is the raw call-site
  state and the continuation is produced on the spot by \<open>fst (enter\<^sup># tf ci \<sigma>c)\<close>.\<close>
lemma tf_sound_combine_collect_at_call_for[intro]:
  assumes sc: "s \<in> \<lbrakk>\<sigma>c\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_collect gs (ci_dst ci) s t
           \<in> \<lbrakk>tf_combine_collect_abs tf ci (fst (enter\<^sup># tf ci \<sigma>c)) \<sigma>e\<rbrakk>"
  using sc se by auto

end

text \<open>The structural instance discharges the continuation and environment-combine
  obligations of \<^locale>\<open>sound_transfer_for\<close> outright: an identity continuation keeps
  the caller state, and \<^const>\<open>combine_env\<close> is sound by @{thm [source] combine_env_sound}.\<close>
lemma sound_transfer_enter_cont_idI[intro]:
  fixes \<sigma> :: "'a::sound_domain abs_state"
  assumes eq: "\<And>ci \<sigma>. fst (tf_enter tf ci \<sigma>) = \<sigma>" and sv: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s \<in> \<lbrakk>fst (enter\<^sup># tf ci \<sigma>)\<rbrakk>"
  unfolding eq using sv by simp

lemma sound_transfer_combine_envI[intro]:
  fixes \<sigma>cont \<sigma>e :: "'a::sound_domain abs_state"
  assumes eq: "tf_combine_env tf = (\<lambda>_. combine_env gs)"
    and sc: "s \<in> \<lbrakk>\<sigma>cont\<rbrakk>" and se: "t \<in> \<lbrakk>\<sigma>e\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env\<^sup># tf ci \<sigma>cont \<sigma>e\<rbrakk>"
  unfolding eq by (rule combine_env_sound[OF sc se])

subsection \<open>Per-edge transfer soundness\<close>

text \<open>
  Generic transfer facts for \<^locale>\<open>sound_transfer_for\<close>: the D/G equation-system
  soundness proof cites these to discharge its per-step obligations from a domain's
  transfer soundness alone.
\<close>

context sound_transfer_for
begin

lemma edge_collect_apply_tf_sound_for[intro]:
  "edge_collect a \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>apply_tf tf a \<sigma>\<rbrakk>"
proof (cases a)
  case (EA_Special sc x)
  then show ?thesis by (cases sc) auto
qed auto

text \<open>A \<open>dg_spec\<close> instance dispatches its own \<open>EA_Check\<close> case through its own
  \<open>dgs_event\<close> field, matching \<^const>\<open>apply_tf\<close>'s own \<open>event\<^sup>#\<close>
  dispatch: this is the per-domain soundness bound each such instance needs at
  that dispatch point.\<close>
lemma edge_collect_check_sound_for[intro]:
  "edge_collect (EA_Check c) \<lbrakk>\<sigma>\<rbrakk> \<subseteq> \<lbrakk>event\<^sup># tf (Check_Event c) \<sigma>\<rbrakk>"
  by auto

end



end

