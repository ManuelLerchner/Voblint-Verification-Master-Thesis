theory Interval_Transfer
  imports Interval_Backward Interval_Special "Voblint_Framework.DG_Local_State_Spec"
    "Voblint_VIMP.VIMP_Globals"
begin

section \<open>Interval transfer functions\<close>

subsection \<open>Abstract branch and assignment\<close>

text \<open>
  Guard refinement delegates to the generic @{text bfilter} proved sound in
  @{locale backward_domain}. @{const bfilter_ivl} narrows on the branch selected
  by its boolean polarity argument (@{text True} for @{text "truthy (aval b s)"},
  @{text False} for @{text "\<not> truthy (aval b s)"}) -- this is Interval's branch
  operation directly, matching Goblint's single polarity-parametrized
  @{text Spec.branch}.
\<close>

lemma bfilter_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>bfilter_ivl b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.bfilter_sound by simp

text \<open>
  @{const branch_ivl} is Interval's registered branch operation: a forward
  @{const interval_tobool} feasibility check ahead of @{const bfilter_ivl},
  matching Goblint's \<open>Base.branch\<close> structure. Proved once, generically, as
  @{thm [source] backward_domain.branch_sound}.
\<close>

lemma branch_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> truthy (aval b s) = res \<Longrightarrow> s \<in> \<lbrakk>branch_ivl b res \<sigma>\<rbrakk>"
  using ivl_backward_domain.branch_sound by simp

definition assign_ivl ::
    "vname => exp => (vname => ivl) => (vname => ivl)"
where
  "assign_ivl x a \<sigma> = \<sigma>(x := aval_ivl a \<sigma>)"

lemma assign_ivl_sound:
  "s \<in> \<lbrakk>\<sigma>\<rbrakk>
   \<Longrightarrow> s(x := aval a s) \<in> \<lbrakk>assign_ivl x a \<sigma>\<rbrakk>"
  unfolding gamma_state_def assign_ivl_def
  by (auto simp: aval_ivl_sound)

text \<open>Nondeterministic and other special-call assignment (\<open>special_ivl\<close>) lives
  in \<open>Interval_Special\<close>, reused below.\<close>

lemma assign_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> assign_ivl x a sigma1 \<le> assign_ivl x a sigma2"
  by (simp add: assign_ivl_def aval_ivl_mono le_funD le_funI)

subsection \<open>Skip, body-entry, and return\<close>

text \<open>Interval has no lifecycle-specific abstract information: skip and body entry
  are the identity, and the return operation publishes the returned expression's value
  to \<^const>\<open>ret_var\<close>, which is where the collecting semantics reads it back.\<close>


definition skip_ivl :: "(vname => ivl) => (vname => ivl)" where
  "skip_ivl \<sigma> = \<sigma>"

definition body_ivl :: "pname => (vname => ivl) => (vname => ivl)" where
  "body_ivl p \<sigma> = \<sigma>"

definition return_ivl ::
    "exp option => pname => (vname => ivl) => (vname => ivl)"
where
  "return_ivl e p \<sigma> = (case e of None \<Rightarrow> \<sigma> | Some a \<Rightarrow> assign_ivl ret_var a \<sigma>)"

text \<open>A check observes its condition but never refines the state (that is
  \<open>abstract_check_domain\<close>'s job): Interval has no notion of that observation
  either, so \<open>event_ivl\<close> is the identity like \<open>skip_ivl\<close>/\<open>body_ivl\<close>.\<close>
definition event_ivl :: "analysis_event => (vname => ivl) => (vname => ivl)" where
  "event_ivl ev \<sigma> = \<sigma>"

lemma skip_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>skip_ivl \<sigma>\<rbrakk>"
  by (simp add: skip_ivl_def)

lemma body_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>body_ivl p \<sigma>\<rbrakk>"
  by (simp add: body_ivl_def)

lemma event_ivl_sound: "s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow> s \<in> \<lbrakk>event_ivl ev \<sigma>\<rbrakk>"
  by (simp add: event_ivl_def)

lemma return_ivl_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "s(ret_var := (case e of None \<Rightarrow> s ret_var | Some a \<Rightarrow> aval a s)) \<in> \<lbrakk>return_ivl e p \<sigma>\<rbrakk>"
  using assign_ivl_sound[OF gs] gs
  by (cases e) (simp_all add: return_ivl_def)

lemma skip_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> skip_ivl sigma1 \<le> skip_ivl sigma2"
  by (simp add: skip_ivl_def)

lemma body_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> body_ivl p sigma1 \<le> body_ivl p sigma2"
  by (simp add: body_ivl_def)

lemma event_ivl_mono: "sigma1 \<le> sigma2 \<Longrightarrow> event_ivl ev sigma1 \<le> event_ivl ev sigma2"
  by (simp add: event_ivl_def)

lemma return_ivl_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow> return_ivl e p sigma1 \<le> return_ivl e p sigma2"
  by (cases e) (simp_all add: return_ivl_def assign_ivl_mono)

subsection \<open>Classifier-parametric procedure entry and bundled transfer functions\<close>

text \<open>Procedure entry: keep globals, reset locals to the full interval, then bind
  the formals to the abstract values of the actuals evaluated in the caller.
  Generic via \<open>enter_frame\<close>/\<^const>\<open>enter_binding\<close>, parameterised by
  ivl_top as the domain's fully-imprecise reset value.  Entry and combine are
  the only fields that consult a classifier, so the bundled transfer function
  is parametric in the classifier throughout.\<close>

definition enter_frame_ivl_for ::
    "(vname => bool) => ivl abs_state => ivl abs_state" where
  "enter_frame_ivl_for gs = enter_frame gs ivl_top"

definition enter_ivl_for ::
    "(vname => bool) => vname list => exp list =>
      ivl abs_state => ivl abs_state" where
  "enter_ivl_for gs = enter_binding gs ivl_top aval_ivl"

lemma enter_frame_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "enter_state cls s \<in> \<lbrakk>enter_frame_ivl_for cls \<sigma>\<rbrakk>"
  unfolding enter_frame_ivl_for_def
proof (rule enter_frame_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
qed

lemma enter_ivl_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state cls s)
           \<in> \<lbrakk>enter_ivl_for cls xs es \<sigma>\<rbrakk>"
  unfolding enter_ivl_for_def enter_binding_concrete[symmetric]
proof (rule enter_binding_sound[OF gs])
  show "gamma ivl_top = UNIV" by (simp add: gamma_ivl_top)
next
  fix e
  have V: "\<forall>x. s x \<in> gamma_ivl (\<sigma> x)"
    using gs unfolding gamma_state_def by simp
  show "aval e s \<in> gamma (aval_ivl e \<sigma>)"
    using V by (simp add: aval_ivl_sound)
qed

definition enter_ivl_ci_for ::
    "(vname => bool) => call_info => ivl abs_state => ivl abs_state" where
  "enter_ivl_ci_for gs ci = enter_ivl_for gs (ci_formals ci) (ci_args ci)"

lemma enter_ivl_ci_for_sound:
  assumes gs: "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  shows "bind_formals (ci_formals ci) (map (\<lambda>e. aval e s) (ci_args ci)) (enter_state cls s)
           \<in> \<lbrakk>enter_ivl_ci_for cls ci \<sigma>\<rbrakk>"
  using enter_ivl_for_sound[OF gs, of "ci_formals ci" "ci_args ci"]
  by (simp add: enter_ivl_ci_for_def)

lemma ivl_is_sound_transfer_for:
  "sound_transfer_for gs skip_ivl assign_ivl special_ivl branch_ivl body_ivl return_ivl
     (enter_ivl_ci_for gs) event_ivl"
  by unfold_locales
     (simp_all add: assign_ivl_sound special_ivl_sound
        ivl_backward_domain.branch_sound
        skip_ivl_sound body_ivl_sound return_ivl_sound enter_ivl_ci_for_sound
        event_ivl_sound)

definition ivl_tf_abs :: "edge_action => ivl abs_state => ivl abs_state" where
  "ivl_tf_abs = local_spec_step skip_ivl assign_ivl special_ivl branch_ivl
     body_ivl return_ivl event_ivl"

lemma ivl_tf_abs_simps [simp]:
  "ivl_tf_abs EA_Nop = skip_ivl"
  "ivl_tf_abs (EA_Assign x e) = assign_ivl x e"
  "ivl_tf_abs (EA_Special sc y) = special_ivl sc y"
  "ivl_tf_abs (EA_Assume b) = branch_ivl b True"
  "ivl_tf_abs (EA_AssumeNot b) = branch_ivl b False"
  "ivl_tf_abs (EA_Body p) = body_ivl p"
  "ivl_tf_abs (EA_Ret eo p) = return_ivl eo p"
  "ivl_tf_abs (EA_Check c) = event_ivl (Check_Event c)"
  by (simp_all add: ivl_tf_abs_def)

lemma enter_frame_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_frame_ivl_for gs s1 \<le> enter_frame_ivl_for gs s2"
  unfolding enter_frame_ivl_for_def by (rule enter_frame_mono[OF assms])

lemma enter_ivl_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl_for gs xs es s1 \<le> enter_ivl_for gs xs es s2"
  unfolding enter_ivl_for_def
proof (rule enter_binding_mono[OF assms])
  fix e
  show "aval_ivl e s1 \<le> aval_ivl e s2"
    using assms by (simp add: aval_ivl_mono)
qed

lemma enter_ivl_ci_for_mono:
  assumes "s1 \<le> s2"
  shows "enter_ivl_ci_for gs ci s1 \<le> enter_ivl_ci_for gs ci s2"
  using enter_ivl_for_mono[OF assms, of gs "ci_formals ci" "ci_args ci"]
  by (simp add: enter_ivl_ci_for_def)

lemma ivl_tf_abs_mono:
  "s1 \<le> s2 \<Longrightarrow> ivl_tf_abs a s1 \<le> ivl_tf_abs a s2"
  by (cases a)
     (auto simp: ivl_tf_abs_def assign_ivl_mono special_ivl_mono
                 ivl_backward_domain.branch_mono
                 skip_ivl_mono body_ivl_mono return_ivl_mono
                 event_ivl_mono)

text \<open>
  Reusable simp bundle for post-fixpoint proofs over the interval domain.
  Covers the core evaluation rules shared by all interval examples.
  Examples with multiplication also need @{thm [source] times_ivl_def},
  @{thm [source] ivl_times_core.simps}, @{thm [source] ivl_nonempty.simps};
  examples with branch edges also need @{thm [source] ivl_backward_domain.bfilter.simps};
  examples with procedure calls also need @{thm [source] enter_ivl_for_def},
  @{thm [source] enter_frame_ivl_for_def}, @{thm [source]},
  @{thm [source] combine_env_def}.
\<close>
lemmas ivl_eval_simps =
  ivl_tf_abs_def assign_ivl_def
  aval_ivl.simps
  plus_ivl.simps plus_eint.simps
  less_eq_ivl_def le_fun_def

end
