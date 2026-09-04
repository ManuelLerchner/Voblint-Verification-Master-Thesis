theory DG_Local_State_Exec
  imports "Voblint_Framework.DG_Local_State_Spec" Exec_DG_Generator
begin

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>local_state_dg_spec_for_lifted\<close>: the same
  \<^const>\<open>local_dg_spec\<close> shape, over \<open>'a exec_dg_st lifted\<close> instead of
  \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a bare \<open>edge_action \<Rightarrow> _\<close> dispatcher
  -- the executable side dispatches on the action rather than naming one operation
  per edge kind -- and \<open>enter_st\<close> its enter counterpart. Local-only means it reads no global and
  publishes none, so its compiled equations carry no \<open>QueryG\<close> and no \<open>Side\<close>
  -- exactly as on the mathematical side.

  One field differs from the mathematical construction: the env stage of \<open>combine\<close>
  is not the identity here. \<^const>\<open>combine_assign_resolved_q\<close> (unlike
  \<^const>\<open>combine_collect_abs\<close>) does not itself select
  locals-from-caller/globals-from-callee; that selection is what
  \<^const>\<open>combine_resolved_st_q\<close> computes, so the env stage must compute it
  explicitly before the assign stage writes the return value.
\<close>

definition local_state_dg_spec_st_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('x,'k,unit,'a exec_dg_st lifted,'g::bounded_semilattice_sup_bot) dg_spec"
where
  "local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st = local_dg_spec
     (transfer_lift empty_pred (tf_st EA_Nop))
     (\<lambda>x e. transfer_lift empty_pred (tf_st (EA_Assign x e)))
     (\<lambda>sc x. transfer_lift empty_pred (tf_st (EA_Special sc x)))
     (\<lambda>b pol. transfer_lift empty_pred
        (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))
     (\<lambda>p. transfer_lift empty_pred (tf_st EA_Nop))
     (\<lambda>e p. transfer_lift empty_pred (tf_st (EA_Ret e p)))
     (\<lambda>ci d. [(d, transfer_lift empty_pred (enter_st ci) d)])
     (\<lambda>ev. transfer_lift empty_pred
        (tf_st (case ev of Check_Event bc \<Rightarrow> EA_Check bc)))
     (\<lambda>ci dc de. case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
        (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
     (\<lambda>ci dcM de. transfer_lift2 empty_pred
        (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
             (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
        dcM de)"

text \<open>Consumed at code-generation time like every other specification builder
  (see \<^theory>\<open>Voblint_Framework.DG_Spec\<close>): the executable carrier changes what a
  transfer computes, not whether the specification can be exported.\<close>

declare local_state_dg_spec_st_for_lifted_def [code_unfold]

subsection \<open>Basic equations\<close>

lemma local_spec_step_transfer_lift_tf_st:
  "local_spec_step
     (transfer_lift empty_pred (tf_st EA_Nop))
     (\<lambda>x e. transfer_lift empty_pred (tf_st (EA_Assign x e)))
     (\<lambda>sc x. transfer_lift empty_pred (tf_st (EA_Special sc x)))
     (\<lambda>b pol. transfer_lift empty_pred
        (tf_st (if pol then EA_Assume b else EA_AssumeNot b)))
     (\<lambda>e p. transfer_lift empty_pred (tf_st (EA_Ret e p)))
     (\<lambda>ev. transfer_lift empty_pred
        (tf_st (case ev of Check_Event bc \<Rightarrow> EA_Check bc))) a
     = transfer_lift empty_pred (tf_st a)"
  by (cases a) simp_all

lemma dg_spec_step_local_state_st_for_lifted:
  "dg_spec_step (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) a
     = local_transfer (transfer_lift empty_pred (tf_st a))"
  by (simp add: local_state_dg_spec_st_for_lifted_def dg_spec_step_local_dg_spec
      local_spec_step_transfer_lift_tf_st)

lemma dgs_enter_local_state_st_for_lifted:
  "enter\<^sup># (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci
     = local_enter_transfer (\<lambda>d. [(d, transfer_lift empty_pred (enter_st ci) d)])"
  by (simp add: local_state_dg_spec_st_for_lifted_def)

text \<open>The caller half of \<open>enter\<close> is the identity for the same reason as in the
  abstract Base record: the carrier relates no two locations, so a call has
  nothing in it to invalidate. What the env stage then merges is the raw
  call-site value against the callee exit.\<close>

definition combine_env_st_lifted ::
  "'a::bounded_semilattice_sup_bot exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted
   \<Rightarrow> 'a exec_dg_st lifted"
where
  "combine_env_st_lifted dc de =
     (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
        (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))"

lemma dg_spec_combine_transfer_local_state_st_for_lifted:
  "dg_spec_combine_transfer (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci
     = local_combine_transfer
         (\<lambda>dc de. transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
                 (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (combine_env_st_lifted dc de) de)"
  by (simp add: local_state_dg_spec_st_for_lifted_def combine_env_st_lifted_def
      dg_spec_combine_transfer_local_dg_spec)

subsection \<open>The readback of one return combine\<close>

text \<open>
  The one fact about the executable state representation this theory needs
  that no lifter supplies: merging caller against callee and then writing the
  return value reads back as the mathematical \<^const>\<open>combine_collect_abs\<close> of
  the two readbacks. Everything else transports through
  \<^const>\<open>transfer_lift\<close>/\<^const>\<open>transfer_lift2\<close> naturality.
\<close>

lemma fun_of_resolved_st_q_for_combine_assign:
  "fun_of_resolved_st_q_for gs
     (combine_assign_resolved_q gs dst (lookup_resolved_st_q y (location_of gs ret_var))
        (combine_resolved_st_q x y))
   = combine\<^sup># gs dst (fun_of_resolved_st_q_for gs x) (fun_of_resolved_st_q_for gs y)"
  unfolding fun_of_resolved_st_q_for_def
  by (auto simp add: combine_collect_abs_def fun_eq_iff location_of_def
      split: option.splits)

subsection \<open>Routed-domain compatibility, independent of any routing context\<close>

text \<open>
  Every current routed instance (Sign, Interval, Int) reproves the same shapes
  -- the compiled edge, enter and combine trees commuting under
  \<^const>\<open>fun_of_resolved_st_q_for\<close>, plus \<^locale>\<open>dg_reader_commute_gen\<close> at that
  same reader -- from its own executable/abstract transfer-commute facts,
  citing this theory's packaging theorems verbatim. Nothing in that derivation
  is domain-specific beyond the two primitive commute facts a domain's own
  executable-transfer soundness development already proves
  (\<open>sign_tf_st_for_commute\<close>, \<open>ivl_tf_st_for_commute\<close>, ...): this locale states
  the derivation once, so a domain interprets it instead of restating it. The
  locale is deliberately free of any routing context (\<open>route\<close>, \<open>Seed\<close>,
  \<open>Global\<close>, a solver): those are context-owned and solver-owned respectively,
  not domain-owned.
\<close>

text \<open>
  \<^locale>\<open>dg_reader_commute_gen\<close>'s instance at the same reader on both sides needs no
  domain fact at all: \<^const>\<open>fun_of_resolved_st_q_for\<close> is already carrier-polymorphic and
  \<open>sup\<close>-homomorphic (\<open>fun_of_resolved_st_q_for_sup\<close>, \<^theory>\<open>Voblint_Exec.Exec_St\<close>), so this
  is a free-standing fact, not part of the \<open>routed_dg_domain_exec\<close> locale below -- keeping it
  outside means citing it never drags in that locale's \<open>empty_pred\<close>/transfer obligations.
\<close>

lemma dg_reader_commute_gen_lifted_for:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

locale routed_dg_domain_exec =
  fixes gs :: "vname \<Rightarrow> bool"
    and empty_pred :: "'a::sound_domain exec_dg_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and sk :: "'a abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes tf_st_commute:
      "\<And>a s. live_resolved_st_q gs s \<Longrightarrow>
         fun_of_resolved_st_q_for gs (tf_st a s)
           = local_spec_step sk asn sp br rt ev a (fun_of_resolved_st_q_for gs s)"
    and enter_st_commute:
      "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                   = en ci (fun_of_resolved_st_q_for gs s)"
    and empty_pred_exact:
      "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

abbreviation reader :: "'a exec_dg_st lifted \<Rightarrow> 'a abs_state lifted" where
  "reader \<equiv> map_lift (fun_of_resolved_st_q_for gs)"

text \<open>Each field's readback equation, once. These are the only inputs the tree
  commutes below take: a local-only transfer compiles to a single answer, so
  its transport is exactly the pure equation on the function it wraps.\<close>

text \<open>
  Unlike \<open>enter_st_commute\<close>/\<open>combine\<close>'s field equations, \<open>tf_st_commute\<close> only
  holds on live inputs (a domain's \<open>branch_st\<close>-style raw result need not
  match its abstract \<open>branch\<close>'s on a dead one), so this cannot go through the
  blanket \<open>transfer_lift_commute\<close>. \<open>normalized_lift\<close> supplies liveness
  directly instead: production only ever feeds \<open>tf_st\<close> a \<open>d\<close> that is
  itself \<open>Bot\<close> or the (always-normalized, \<open>transfer_lift_normalized\<close>) result
  of a prior step.
\<close>

lemma step_lift_commute:
  assumes norm: "normalized_lift empty_pred d"
  shows "reader (transfer_lift empty_pred (tf_st a) d)
     = transfer_lift is_empty_state (local_spec_step sk asn sp br rt ev a) (reader d)"
using norm proof (cases d)
  case Bot
  then show ?thesis by (simp add: transfer_lift_def)
next
  case (Lifted s)
  with norm have "live_resolved_st_q gs s"
    by (simp add: live_resolved_st_q_def empty_pred_exact)
  then show ?thesis
    unfolding Lifted
    by (simp add: transfer_lift_def normalize_lift_def tf_st_commute empty_pred_exact)
qed

lemma enter_lift_commute:
  "reader (transfer_lift empty_pred (enter_st ci) d)
     = transfer_lift is_empty_state (en ci) (reader d)"
proof (rule transfer_lift_commute)
  show "\<And>s. fun_of_resolved_st_q_for gs (enter_st ci s)
              = en ci (fun_of_resolved_st_q_for gs s)"
    by (simp add: enter_st_commute)
  show "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    by (rule empty_pred_exact)
qed

text \<open>The env stage merges into the assign stage: both collapse on the same two
  \<^const>\<open>Bot\<close> cases, so the composed combine is a single \<^const>\<open>transfer_lift2\<close>
  and transports by the same naturality lemma as every other field.\<close>

lemma transfer_lift2_combine_env_st_lifted:
  "transfer_lift2 empty_pred g (combine_env_st_lifted dc de) de
     = transfer_lift2 empty_pred (\<lambda>x y. g (combine_resolved_st_q x y) y) dc de"
  by (cases dc; cases de) (simp_all add: combine_env_st_lifted_def transfer_lift2_def)

lemma combine_lift_commute:
  "reader (transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs dst
                 (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (combine_env_st_lifted dc de) de)
     = transfer_lift2 is_empty_state (combine\<^sup># gs dst) (reader dc) (reader de)"
  unfolding transfer_lift2_combine_env_st_lifted
proof (rule transfer_lift2_commute)
  show "\<And>x y. fun_of_resolved_st_q_for gs
      (combine_assign_resolved_q gs dst (lookup_resolved_st_q y (location_of gs ret_var))
         (combine_resolved_st_q x y))
        = combine\<^sup># gs dst (fun_of_resolved_st_q_for gs x) (fun_of_resolved_st_q_for gs y)"
    by (rule fun_of_resolved_st_q_for_combine_assign)
  show "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
    by (rule empty_pred_exact)
qed


subsection \<open>Tree-level transport of the two specifications\<close>

text \<open>
  The routed spine's transport hypotheses are commutes of compiled sub-trees,
  not equations on a retired pair-shaped transfer. Both specifications are
  local-only, so each such commute reduces to the corresponding field equation
  above -- and \<open>caller_cont\<close> needs no hypothesis at all, since
  \<^const>\<open>dg_spec_combine_transfer\<close> already runs it inside the combine sub-tree.
\<close>

abbreviation spec_st :: "('x,'k,unit,'a exec_dg_st lifted,'a exec_dg_st lifted) dg_spec" where
  "spec_st \<equiv> local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"

abbreviation spec_abs :: "('x,'k,unit,'a abs_state lifted,'a abs_state lifted) dg_spec" where
  "spec_abs \<equiv> local_state_dg_spec_for_lifted gs is_empty_state sk asn sp br bd rt en ev"

lemma Hstep_lifted_for:
  assumes "normalized_lift empty_pred d"
  shows "dg_reader_commute_gen.dg_tree_st_commute reader reader \<sigma>_st
     (sp_compile_with (\<lambda>x. DG x bot) (dg_spec_step spec_st a (mk_dg_man d (\<lambda>_. gk))))
     (sp_compile_with (\<lambda>x. DG x bot) (dg_spec_step spec_abs a (mk_dg_man (reader d) (\<lambda>_. gk))))"
  unfolding dg_spec_step_local_state_st_for_lifted dg_spec_step_local_state_for_lifted
  using dg_reader_commute_gen.dg_tree_st_commute_local_transfer dg_reader_commute_gen_lifted_for
    step_lift_commute[OF assms] by fastforce

lemma Henter_lifted_for:
  "dg_reader_commute_gen.dg_enter_st_commute reader reader \<sigma>_st
     (enter\<^sup># spec_st ci (mk_dg_man d (\<lambda>_. gk)))
     (enter\<^sup># spec_abs ci (mk_dg_man (reader d) (\<lambda>_. gk)))"
  unfolding dgs_enter_local_state_st_for_lifted dgs_enter_local_state_for_lifted
  by (rule dg_reader_commute_gen.dg_enter_st_commute_local_enter_transfer
        [OF dg_reader_commute_gen_lifted_for])
     (simp add: enter_lift_commute)

lemma Hcomb_lifted_for:
  "dg_reader_commute_gen.dg_tree_st_commute reader reader \<sigma>_st
     (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer spec_st ci (mk_dg_man d (\<lambda>_. gk)) de))
     (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer spec_abs ci (mk_dg_man (reader d) (\<lambda>_. gk)) (reader de)))"
  unfolding dg_spec_combine_transfer_local_state_st_for_lifted
    dg_spec_combine_transfer_local_state_for_lifted
  by (rule dg_reader_commute_gen.dg_tree_st_commute_local_combine_transfer
        [OF dg_reader_commute_gen_lifted_for,
         where F = "transfer_lift2 is_empty_state (combine\<^sup># gs (ci_dst ci))"])
     (rule combine_lift_commute)

subsection \<open>Soundness at the executable carrier, pulled back along the readback\<close>

text \<open>
  The framework is carrier-agnostic, so nothing forces it to be instantiated at
  \<open>'a abs_state lifted\<close>: with the concretization read through
  \<^const>\<open>fun_of_resolved_st_q_for\<close>, the executable Base-style spec is itself a
  \<^locale>\<open>sound_dg_spec\<close>, and the field equations above are all that the proof
  needs. An instance that interprets the routed spine at \<open>spec_st\<close> with this
  concretization feeds it the solver's own table and never transports a solved
  system between carriers.
\<close>

definition gamma_exec :: "'a exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> store set" where
  "gamma_exec d g = gamma_state_lift (reader d)"

lemma gamma_exec_Bot [simp]: "gamma_exec Bot g = {}"
  by (simp add: gamma_exec_def)

text \<open>
  Entry is no longer part of \<^locale>\<open>sound_dg_spec\<close>, so a routed instance needs it
  separately. This is the same fact the collapse below proves for its own entry
  obligation, exported once because every routed instance over this carrier
  discharges its entry coverage from it.
\<close>

theorem entry_pairs_cover_st:
  assumes tf_sound: "sound_transfer_for gs sk asn sp br bd rt en ev"
    and sin: "s \<in> gamma_state_lift (reader d)"
  shows "entry_pairs_cover (\<lambda>d'. gamma_state_lift (reader d')) s
           (call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (enter_st ci) d)]"
proof -
  have entered: "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
      \<in> gamma_state_lift (reader (transfer_lift empty_pred (enter_st ci) d))"
    unfolding enter_lift_commute
  proof (rule transfer_lift_sound_mem
        [where h = "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"])
    show "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
        call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> \<lbrakk>en ci \<sigma>\<rbrakk>"
      by (simp add: call_enter_CallEdge
          sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound])
    show "\<And>\<sigma>. is_empty_state \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
      by (rule is_empty_state_gamma_state_empty)
    show "s \<in> gamma_state_lift (reader d)" by (rule sin)
  qed
  show ?thesis
    by (rule entry_pairs_coverI
          [where cont = d and entry = "transfer_lift empty_pred (enter_st ci) d"])
       (simp_all add: sin entered)
qed

theorem sound_dg_spec_st:
  assumes tf_sound: "sound_transfer_for gs sk asn sp br bd rt en ev"
  shows "sound_dg_spec spec_st gamma_exec gs"
proof -
  have geq: "gamma_exec = (\<lambda>d g. gamma_state_lift (reader d))"
    by (simp add: fun_eq_iff gamma_exec_def)
  show ?thesis
    unfolding local_state_dg_spec_st_for_lifted_def geq
  proof (rule sound_local_dg_spec.local_spec_sound, unfold_locales, goal_cases)
    case 1
    then show ?case
      by (meson gamma_lift_mono gamma_state_mono map_lift_fun_of_resolved_st_q_for_mono)
  next
    case (2 a d)
    have step: "edge_collect a (gamma_state_lift (reader d))
                  \<subseteq> gamma_state_lift (reader (transfer_lift empty_pred (tf_st a) d))"
    proof (cases "normalized_lift empty_pred d")
      case True
      then have eq: "reader (transfer_lift empty_pred (tf_st a) d)
                       = transfer_lift is_empty_state (local_spec_step sk asn sp br rt ev a) (reader d)"
        by (rule step_lift_commute)
      show ?thesis
        unfolding eq
        by (rule transfer_lift_sound_collect
              [OF sound_transfer_for.step_sound_for[OF tf_sound]
                  edge_collect_empty_set is_empty_state_gamma_state_empty])
    next
      case False
      then obtain s where "d = Lifted s" "empty_pred s"
        by (cases d) simp_all
      then have "gamma_state_lift (reader d) = {}"
        by (simp add: empty_pred_exact is_empty_state_gamma_state_empty)
      then show ?thesis
        by (simp add: edge_collect_empty_set)
    qed
    then show ?case
      by (simp add: local_spec_step_transfer_lift_tf_st)
  next
    case (3 s d ci)
    have entered: "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
        \<in> gamma_state_lift (reader (transfer_lift empty_pred (enter_st ci) d))"
      unfolding enter_lift_commute
    proof (rule transfer_lift_sound_mem
          [where h = "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"])
      show "\<And>\<sigma>. s \<in> \<lbrakk>\<sigma>\<rbrakk> \<Longrightarrow>
          call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
            \<in> \<lbrakk>en ci \<sigma>\<rbrakk>"
        by (simp add: call_enter_CallEdge
            sound_transfer_for.tf_sound_enter_entry_for[OF tf_sound])
      show "\<And>\<sigma>. is_empty_state \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
        by (rule is_empty_state_gamma_state_empty)
      show "s \<in> gamma_state_lift (reader d)" by (rule 3)
    qed
    show ?case
      by (rule entry_pairs_coverI
            [where cont = d and entry = "transfer_lift empty_pred (enter_st ci) d"])
         (simp_all add: 3 entered)
  next
    case (4 s dc t de ci)
    show ?case
      unfolding combine_env_st_lifted_def[symmetric] combine_lift_commute
    proof (rule transfer_lift2_sound_mem[where h = "combine_collect gs (ci_dst ci)"])
      show "\<And>\<sigma>1 \<sigma>2. s \<in> \<lbrakk>\<sigma>1\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>\<sigma>2\<rbrakk> \<Longrightarrow>
          combine_collect gs (ci_dst ci) s t \<in> \<lbrakk>combine\<^sup># gs (ci_dst ci) \<sigma>1 \<sigma>2\<rbrakk>"
        by (rule combine_collect_sound)
      show "\<And>\<sigma>. is_empty_state \<sigma> \<Longrightarrow> \<lbrakk>\<sigma>\<rbrakk> = {}"
        by (rule is_empty_state_gamma_state_empty)
      show "s \<in> gamma_state_lift (reader dc)" by (rule 4(1))
      show "t \<in> gamma_state_lift (reader de)" by (rule 4(2))
    qed
  qed
qed

subsection \<open>A generic exec-level formal-entry route, and its commute to the abstract one\<close>

text \<open>
  \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close> (\<^theory>\<open>Voblint_Framework.Routed_Context\<close>)
  are already domain-generic at the abstract carrier \<open>'a abs_state lifted\<close> -- the shape
  \<^locale>\<open>routed_context_base_hetero\<close>'s own \<open>route\<close> parameter needs. The executable equation
  system a solver actually runs needs the same construction at the exec carrier
  \<open>'a exec_dg_st lifted\<close> instead, built from this locale's own \<open>enter_st\<close>/\<open>empty_pred\<close>
  rather than the mathematical \<open>enter#\<close>/\<open>tf\<close>: every current EntryState-style routed
  instance (Interval's own \<open>entry_state_route\<close>, \<open>Interval_Analyses\<close>)
  reproves this exact projection and its commute lemma; stating it here once lets a
  domain interpret it instead of restating it, mirroring how \<open>Hstep_lifted_for\<close> etc.
  already generalize the step/enter/combine commute facts.

  The route is a pure projection of the state it is handed: the routed generator
  enters the callee frame once and routes on that entered state, so entering again
  here would key the seed on a doubly-entered frame.
\<close>

definition entry_exec_route :: "'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "entry_exec_route d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars (fun_of_resolved_st_q_for gs
          (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

definition entry_exec_route_gen :: "pp \<Rightarrow> 'a list \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "entry_exec_route_gen u ctx d ca = entry_exec_route d ca"

lemma entry_exec_route_commute:
  "formals_route_lifted (reader s) ca = entry_exec_route s ca"
  by (cases ca; cases s)
     (simp_all add: formals_route_lifted_def entry_exec_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_exec_route_gen_commute:
  "formals_route_lifted_gen u ctx (reader s) ca = entry_exec_route_gen u ctx s ca"
  by (simp add: formals_route_lifted_gen_def entry_exec_route_gen_def entry_exec_route_commute)

end

end
