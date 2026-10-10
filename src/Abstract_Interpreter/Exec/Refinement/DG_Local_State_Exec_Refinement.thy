theory DG_Local_State_Exec_Refinement
  imports
    DG_Local_State_Exec
    "Voblint_Framework.DG_Reader_Transport"
begin

unbundle default_st_syntax

section \<open>The mathematical run an executable D/G run represents\<close>

text \<open>
  The executable construction above computes on association-list states; the
  soundness statements are about function-valued ones. This theory is the
  bridge: it fixes a domain whose executable transfer agrees with its abstract
  transfer on the represented functions (\<open>dg_domain_exec\<close>) and derives, from
  those three agreements alone, that a whole D/G specification is sound at the
  executable carrier -- with no separate abstract-carrier run to compare against.
\<close>

subsection \<open>The function one return combine represents\<close>

text \<open>
  The one fact about the executable state representation this theory needs
  that no lifter supplies: merging caller against callee and then writing the
  return value represents the mathematical \<^const>\<open>combine_collect_abs\<close> of
  the two represented functions. Everything else transports through
  \<^const>\<open>transfer_lift\<close>/\<^const>\<open>transfer_lift2\<close> naturality.
\<close>

lemma default_st_to_fun_combine_assign:
  "\<rho>\<^bsub>\<G>\<^esub>
     (combine_assign_default_st \<G> dst y\<langle>location_of \<G> ret_var\<rangle>
        (combine_default_st x y))
   = combine\<^sup>\<sharp> \<G> dst (\<rho>\<^bsub>\<G>\<^esub> x) (\<rho>\<^bsub>\<G>\<^esub> y)"
  unfolding default_st_to_fun_def
  by (auto simp add: combine_collect_abs_def fun_eq_iff location_of_def
      split: option.splits)

subsection \<open>Routed-domain compatibility, independent of any routing context\<close>

text \<open>
  Every routed domain instance needs the same shapes
  -- the compiled edge, enter and combine trees commuting under
  \<^const>\<open>default_st_to_fun\<close>, plus \<^locale>\<open>dg_reader_commute_gen\<close> at that
  same reader -- from its own executable/abstract transfer-commute facts,
  citing this theory's packaging theorems verbatim. Nothing in that derivation
  is domain-specific beyond the two primitive commute facts a domain's own
  executable-transfer soundness development already proves
  (\<open>sign_tf.tf_st_for_commute\<close>, \<open>ivl_tf.tf_st_for_commute\<close>, ...): this locale states
  the derivation once, so a domain interprets it instead of restating it. The
  locale is deliberately free of any routing context (\<open>route\<close>, \<open>Seed\<close>,
  \<open>Global\<close>, a solver): those are context-owned and solver-owned respectively,
  not domain-owned.
\<close>

text \<open>
  \<^locale>\<open>dg_reader_commute_gen\<close>'s instance at the same reader on both sides needs no
  domain fact at all: \<^const>\<open>default_st_to_fun\<close> is already carrier-polymorphic and
  \<open>sup\<close>-homomorphic (\<open>default_st_to_fun_sup\<close>,
  \<open>Voblint_Exec.Default_St_Transfer\<close>), so this
  is a free-standing fact, not part of the \<open>dg_domain_exec\<close> locale below -- keeping it
  outside means citing it never drags in that locale's \<open>empty_pred\<close>/transfer obligations.
\<close>

lemma dg_reader_commute_gen_lifted_for:
  "dg_reader_commute_gen
     (\<rho>\<^bsub>\<G>\<^esub> :: _ default_st lifted \<Rightarrow> _) (\<rho>\<^bsub>\<G>\<^esub> :: _ default_st lifted \<Rightarrow> _)"
  by unfold_locales (simp_all add: map_lift_sup)

text \<open>
  \<open>dg_domain_exec\<close> relates an executable transfer on \<open>default_st\<close>
  to the abstract state specification: on live states the step, the entry
  transfer and the emptiness test agree with their abstract counterparts after
  readback through \<open>default_st_to_fun\<close>.
\<close>

locale dg_domain_exec =
  fixes \<G> :: "vname \<Rightarrow> bool"
    and empty_pred :: "'a::numeric_domain default_st \<Rightarrow> bool"
    and tf_st :: "edge_action \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st"
    and enter_st :: "call_info \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st"
    and sk :: "'a abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
  assumes tf_st_commute:
      "\<And>a s. live_default_st \<G> s \<Longrightarrow>
         \<rho>\<^bsub>\<G>\<^esub> (tf_st a s)
           = local_spec_step sk asn sp br bd rt ev a (\<rho>\<^bsub>\<G>\<^esub> s)"
    and enter_st_commute:
      "\<And>ci s. \<rho>\<^bsub>\<G>\<^esub> (enter_st ci s)
                   = en ci (\<rho>\<^bsub>\<G>\<^esub> s)"
    and empty_pred_exact:
      "\<And>s. empty_pred s = is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s)"
begin

text \<open>With \<open>\<G>\<close> fixed, \<open>\<gamma> s\<close> is the carrier's concretization, for a plain and
  for a lifted carrier state alike.\<close>

adhoc_overloading gamma_S == "default_st_gamma \<G>"
adhoc_overloading gamma_S == "gamma_lift (default_st_gamma \<G>)"

abbreviation reader :: "'a default_st lifted \<Rightarrow> 'a abs_state lifted" where
  "reader \<equiv> map_lift \<rho>\<^bsub>\<G>\<^esub>"

text \<open>Each field's equation on the represented function, once. These are the only inputs the tree
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
     = transfer_lift is_empty_state (local_spec_step sk asn sp br bd rt ev a) (reader d)"
using norm proof (cases d)
  case Bot
  then show ?thesis by (simp add: transfer_lift_def)
next
  case (Lifted s)
  with norm have "live_default_st \<G> s"
    by (simp add: live_default_st_def empty_pred_exact)
  then show ?thesis
    unfolding Lifted
    by (simp add: transfer_lift_def normalize_lift_def tf_st_commute empty_pred_exact)
qed

lemma enter_lift_commute:
  "reader (transfer_lift empty_pred (enter_st ci) d)
     = transfer_lift is_empty_state (en ci) (reader d)"
proof (rule transfer_lift_commute)
  show "\<And>s. \<rho>\<^bsub>\<G>\<^esub> (enter_st ci s)
              = en ci (\<rho>\<^bsub>\<G>\<^esub> s)"
    by (simp add: enter_st_commute)
  show "\<And>s. empty_pred s = is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s)"
    by (rule empty_pred_exact)
qed

text \<open>The env stage merges into the assign stage: both collapse on the same two
  \<^const>\<open>Bot\<close> cases, so the composed combine is a single \<^const>\<open>transfer_lift2\<close>
  and transports by the same naturality lemma as every other field.\<close>

lemma transfer_lift2_combine_env_st_lifted:
  "transfer_lift2 empty_pred g (combine_env_st_lifted dc de) de
     = transfer_lift2 empty_pred (\<lambda>x y. g (combine_default_st x y) y) dc de"
  by (cases dc; cases de) (simp_all add: combine_env_st_lifted_def transfer_lift2_def)

lemma combine_lift_commute:
  "reader (transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_default_st \<G> dst
                 de0\<langle>location_of \<G> ret_var\<rangle> env0)
            (combine_env_st_lifted dc de) de)
     = transfer_lift2 is_empty_state (combine\<^sup>\<sharp> \<G> dst) (reader dc) (reader de)"
  unfolding transfer_lift2_combine_env_st_lifted
proof (rule transfer_lift2_commute)
  show "\<And>x y. \<rho>\<^bsub>\<G>\<^esub>
      (combine_assign_default_st \<G> dst y\<langle>location_of \<G> ret_var\<rangle>
         (combine_default_st x y))
        = combine\<^sup>\<sharp> \<G> dst (\<rho>\<^bsub>\<G>\<^esub> x) (\<rho>\<^bsub>\<G>\<^esub> y)"
    by (rule default_st_to_fun_combine_assign)
  show "\<And>s. empty_pred s = is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s)"
    by (rule empty_pred_exact)
qed


subsection \<open>Tree-level transport of the two specifications\<close>

text \<open>
  The routed spine's transport hypotheses are commutes of compiled sub-trees.
  Both specifications are
  local-only, so each such commute reduces to the corresponding field equation
  above.
\<close>

abbreviation spec_st :: "('x,'k,unit,'a default_st lifted,'a default_st lifted) dg_spec" where
  "spec_st \<equiv> exec_dg_spec \<G> empty_pred tf_st enter_st"

abbreviation spec_abs :: "('x,'k,unit,'a abs_state lifted,'a abs_state lifted) dg_spec" where
  "spec_abs \<equiv> lifted_state_dg_spec \<G> is_empty_state sk asn sp br bd rt en ev"

lemma Henter_lifted_for:
  "dg_reader_commute_gen.dg_enter_st_commute reader reader \<sigma>_st
     (enter\<^sup>\<sharp> spec_st ci (mk_dg_man d (\<lambda>_. gk)))
     (enter\<^sup>\<sharp> spec_abs ci (mk_dg_man (reader d) (\<lambda>_. gk)))"
  unfolding dgs_enter_exec_dg_spec dgs_enter_lifted_state_dg_spec
  by (rule dg_reader_commute_gen.dg_enter_st_commute_local_enter_transfer
        [OF dg_reader_commute_gen_lifted_for])
     (simp add: enter_lift_commute)

lemma Hcomb_lifted_for:
  "dg_reader_commute_gen.dg_tree_st_commute reader reader \<sigma>_st
     (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer spec_st ci (mk_dg_man d (\<lambda>_. gk)) de))
     (sp_compile_with (\<lambda>x. DG x bot)
        (dg_spec_combine_transfer spec_abs ci (mk_dg_man (reader d) (\<lambda>_. gk)) (reader de)))"
  unfolding dg_spec_combine_transfer_exec_dg_spec
    dg_spec_combine_transfer_lifted_state_dg_spec
  by (rule dg_reader_commute_gen.dg_tree_st_commute_local_combine_transfer
        [OF dg_reader_commute_gen_lifted_for,
         where F = "transfer_lift2 is_empty_state (combine\<^sup>\<sharp> \<G> (ci_dst ci))"])
     (rule combine_lift_commute)

subsection \<open>Soundness at the executable carrier, pulled back through its functions\<close>

text \<open>
  The framework is carrier-agnostic, so nothing forces it to be instantiated at
  \<open>'a abs_state lifted\<close>: with the carrier's own concretization
  \<^const>\<open>default_st_gamma\<close>, the executable Base-style spec is itself a
  \<^locale>\<open>analysis_contract\<close>, and the field equations above are all that the proof
  needs. An instance that interprets the routed spine at \<open>spec_st\<close> with this
  concretization feeds it the solver's own table and never transports a solved
  system between carriers.
\<close>

definition gamma_exec :: "'a default_st lifted \<Rightarrow> 'a default_st lifted \<Rightarrow> store set" where
  "gamma_exec d g = \<gamma> d"

lemma gamma_exec_Bot [simp]: "gamma_exec Bot g = {}"
  by (simp add: gamma_exec_def)

text \<open>
  Entry is not part of \<^locale>\<open>analysis_contract\<close>, so a routed instance needs it
  separately. This is the same fact the collapse below proves for its own entry
  obligation, exported once because every routed instance over this carrier
  discharges its entry coverage from it.
\<close>

lemma entered_st:
  assumes tf_sound: "sound_nonrelational_transfer \<G> sk asn sp br bd rt en ev"
    and s: "s \<in> \<gamma> d"
  shows "call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
           \<in> \<gamma> (transfer_lift empty_pred (enter_st ci) d)"
  using s unfolding gamma_lift_default_st_gamma_to_fun enter_lift_commute
  by (intro transfer_lift_sound_mem[OF _ is_empty_state_gamma_state_empty])
     (simp add: call_enter_CallEdge
       sound_nonrelational_transfer.tf_sound_enter_entry_for[OF tf_sound])

theorem entry_pairs_cover_st:
  assumes tf_sound: "sound_nonrelational_transfer \<G> sk asn sp br bd rt en ev"
    and sin: "s \<in> \<gamma> d"
  shows "entry_pairs_cover (\<lambda>d'. \<gamma> d') s
           (call_enter \<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, transfer_lift empty_pred (enter_st ci) d)]"
  by (rule entry_pairs_coverI
        [where cont = d and entry = "transfer_lift empty_pred (enter_st ci) d"])
     (simp_all add: sin entered_st[OF tf_sound sin])

text \<open>
  The executable analysis as a component, sound for the carrier's
  concretization. The proof maps each state to its function through \<open>reader\<close>; the
  contract below is its one-line consequence.
\<close>

theorem exec_local_spec_sound:
  assumes tf_sound: "sound_nonrelational_transfer \<G> sk asn sp br bd rt en ev"
  shows "sound_local_spec \<G> (\<lambda>d. \<gamma> d) (exec_local_spec \<G> empty_pred tf_st enter_st)"
proof -
  have step: "edge_collect a (\<gamma>\<^sub>\<bottom> (reader d)) \<subseteq> \<gamma>\<^sub>\<bottom> (reader (transfer_lift empty_pred (tf_st a) d))"
    for a d
  proof (cases "normalized_lift empty_pred d")
    case True
    show ?thesis
      unfolding step_lift_commute[OF True]
      by (rule transfer_lift_sound_collect
            [OF sound_nonrelational_transfer.step_sound_for[OF tf_sound]
                edge_collect_empty_set is_empty_state_gamma_state_empty])
  next
    case False
    then obtain s where "d = Lifted s" "empty_pred s" by (cases d) simp_all
    then show ?thesis by (simp add: empty_pred_exact is_empty_state_gamma_state_empty)
  qed
  have comb: "combine_collect \<G> (ci_dst ci) s t \<in> \<gamma>\<^sub>\<bottom> (reader (transfer_lift2 empty_pred
        (\<lambda>env0 de0. combine_assign_default_st \<G> (ci_dst ci)
           de0\<langle>location_of \<G> ret_var\<rangle> env0)
        (combine_env_st_lifted dc de) de))"
    if "s \<in> \<gamma>\<^sub>\<bottom> (reader dc)" "t \<in> \<gamma>\<^sub>\<bottom> (reader de)" for s t dc de ci
    unfolding combine_lift_commute
    by (rule
      transfer_lift2_sound_mem[OF combine_collect_sound is_empty_state_gamma_state_empty that])
  have mono: "\<forall>x y. x \<le> y \<longrightarrow> \<gamma>\<^sub>\<bottom> (reader x) \<subseteq> \<gamma>\<^sub>\<bottom> (reader y)"
    by (meson gamma_lift_mono gamma_state_mono map_lift_default_st_to_fun_mono)
  show ?thesis
    unfolding sound_local_spec_def gamma_lift_default_st_gamma_to_fun
    using mono subset_trans[OF edge_collect_mono[OF Int_lower1] step]
      entered_st[OF tf_sound, unfolded gamma_lift_default_st_gamma_to_fun] comb
    by (auto simp: exec_local_spec_def)
qed

theorem analysis_contract_st:
  assumes tf_sound: "sound_nonrelational_transfer \<G> sk asn sp br bd rt en ev"
  shows "analysis_contract spec_st (\<lambda>d e. gamma_exec d (e ())) \<G>"
  unfolding exec_dg_spec_def gamma_exec_def[abs_def]
  by (rule dg_spec_of_contract[OF exec_local_spec_sound[OF tf_sound]])

end

unbundle no default_st_syntax

end
