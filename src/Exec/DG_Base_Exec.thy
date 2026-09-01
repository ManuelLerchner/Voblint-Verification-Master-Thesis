theory DG_Base_Exec
  imports "Voblint_Core.DG_Base" Exec_DG_Generator
begin

section \<open>Executable Base-style DG construction\<close>

text \<open>
  Executable mirror of \<^const>\<open>base_dg_spec_for_lifted\<close>: same shape, over
  \<open>'a exec_dg_st lifted\<close> instead of \<open>'a abs_state lifted\<close>, with \<open>tf_st\<close> a bare
  \<open>edge_action \<Rightarrow> _\<close> dispatcher (the executable representation has no
  \<^type>\<open>domain_transfer\<close> record) and \<open>enter_st\<close> its enter counterpart.

  Unlike the mathematical side, \<open>dgs_combine_env\<close> here is \<^emph>\<open>not\<close> the identity:
  \<^const>\<open>combine_assign_resolved_q\<close> (unlike \<^const>\<open>combine_collect_abs\<close> on the
  mathematical side) does not itself select locals-from-caller/globals-from-callee
  -- that selection is exactly what \<^const>\<open>combine_resolved_st_q\<close> already computes
  (\<open>fun_of_resolved_st_q_for_combine\<close>: it agrees with \<^const>\<open>combine_env\<close> under
  the executable/mathematical correspondence), so the env stage must compute it
  explicitly here before the assign stage writes the return value.
\<close>

definition base_dg_spec_st_for_lifted ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st lifted, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st = (|
    dgs_skip       = (\<lambda>d g. (g, transfer_lift empty_pred (tf_st EA_Nop) d)),
    dgs_assign     = (\<lambda>x e d g. (g, transfer_lift empty_pred (tf_st (EA_Assign x e)) d)),
    dgs_special    = (\<lambda>sc x d g. (g, transfer_lift empty_pred (tf_st (EA_Special sc x)) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, transfer_lift empty_pred
      (tf_st (if pol then EA_Assume b else EA_AssumeNot b)) d)),
    dgs_body       = (\<lambda>p d g. (g, transfer_lift empty_pred (tf_st EA_Nop) d)),
    dgs_return     = (\<lambda>e p d g. (g, transfer_lift empty_pred (tf_st (EA_Ret e p)) d)),
    dgs_enter      = (\<lambda>ci d g. (g, transfer_lift empty_pred (enter_st ci) d)),
    dgs_event      = (\<lambda>ev d g. (g, case ev of Check_Event bc \<Rightarrow>
                                      transfer_lift empty_pred (tf_st (EA_Check bc)) d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
                                            (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))),
    dgs_combine_assign = (\<lambda>ci de g merged.
      (g, transfer_lift2 empty_pred
            (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
                (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
            (snd merged) de))
  |)"

subsection \<open>Basic equations\<close>

lemma dg_spec_step_base_st_for_lifted:
  "dg_spec_step (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) a d g =
     (g, transfer_lift empty_pred (tf_st a) d)"
  unfolding base_dg_spec_st_for_lifted_def
  by (cases a) simp_all

lemma dgs_enter_base_st_for_lifted:
  "dgs_enter (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci d g =
     (g, transfer_lift empty_pred (enter_st ci) d)"
  unfolding base_dg_spec_st_for_lifted_def by simp

text \<open>The caller half of \<open>enter\<close> is the identity here for the same reason as in the
  abstract Base record: the carrier relates no two locations, so a call has
  nothing in it to invalidate.\<close>

lemma dgs_caller_cont_base_st_for_lifted [simp]:
  "dgs_caller_cont (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc g = dc"
  unfolding base_dg_spec_st_for_lifted_def by simp

lemma dgs_combine_base_st_for_lifted:
  "dgs_combine (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc de g =
     (g, transfer_lift2 empty_pred
           (\<lambda>env0 de0. combine_assign_resolved_q gs (ci_dst ci)
               (lookup_resolved_st_q de0 (location_of gs ret_var)) env0)
           (case dc of Bot \<Rightarrow> Bot | Lifted x \<Rightarrow>
              (case de of Bot \<Rightarrow> Bot | Lifted y \<Rightarrow> Lifted (combine_resolved_st_q x y)))
           de)"
  unfolding dgs_combine_def base_dg_spec_st_for_lifted_def by simp

subsection \<open>The unlifted executable core and its commute\<close>

text \<open>
  The executable mirror of \<^const>\<open>base_dg_spec_for\<close>: the bare dispatcher
  runs on \<open>'a exec_dg_st\<close> with neither reachability tracking nor
  normalization. One \<^locale>\<open>dg_spec_commute\<close> instance relates it to the
  unlifted semantic record from the two primitive commute facts; the frozen
  lifted record then agrees with the normalized dead-code lift of this core
  on every composed operation, so its commute with the lifted semantic
  record is the lifter naturality theorems, not per-field case analysis.
\<close>

definition base_dg_spec_st_for ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> 'a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st)
   \<Rightarrow> ('a exec_dg_st, 'g::bounded_semilattice_sup_bot) dg_spec"
where
  "base_dg_spec_st_for gs tf_st enter_st = (|
    dgs_skip       = (\<lambda>d g. (g, tf_st EA_Nop d)),
    dgs_assign     = (\<lambda>x e d g. (g, tf_st (EA_Assign x e) d)),
    dgs_special    = (\<lambda>sc x d g. (g, tf_st (EA_Special sc x) d)),
    dgs_branch     = (\<lambda>b pol d g. (g, tf_st (if pol then EA_Assume b else EA_AssumeNot b) d)),
    dgs_body       = (\<lambda>p d g. (g, tf_st EA_Nop d)),
    dgs_return     = (\<lambda>e p d g. (g, tf_st (EA_Ret e p) d)),
    dgs_enter      = (\<lambda>ci d g. (g, enter_st ci d)),
    dgs_event      = (\<lambda>ev d g. (g, case ev of Check_Event bc \<Rightarrow> tf_st (EA_Check bc) d)),
    dgs_caller_cont    = (\<lambda>ci dc g. dc),
    dgs_combine_env    = (\<lambda>ci dc de g. (g, combine_resolved_st_q dc de)),
    dgs_combine_assign = (\<lambda>ci de g m.
      (g, combine_assign_resolved_q gs (ci_dst ci)
            (lookup_resolved_st_q de (location_of gs ret_var)) (snd m)))
  |)"

lemma dg_spec_step_base_st_for:
  "dg_spec_step (base_dg_spec_st_for gs tf_st enter_st) a d g = (g, tf_st a d)"
  unfolding base_dg_spec_st_for_def by (cases a) simp_all

lemma dgs_enter_base_st_for:
  "dgs_enter (base_dg_spec_st_for gs tf_st enter_st) ci d g = (g, enter_st ci d)"
  unfolding base_dg_spec_st_for_def by simp

lemma dgs_caller_cont_base_st_for [simp]:
  "dgs_caller_cont (base_dg_spec_st_for gs tf_st enter_st) ci dc g = dc"
  unfolding base_dg_spec_st_for_def by simp

lemma dgs_combine_base_st_for:
  "dgs_combine (base_dg_spec_st_for gs tf_st enter_st) ci dc de g =
     (g, combine_assign_resolved_q gs (ci_dst ci)
           (lookup_resolved_st_q de (location_of gs ret_var))
           (combine_resolved_st_q dc de))"
  unfolding dgs_combine_def base_dg_spec_st_for_def by simp

theorem base_dg_spec_st_for_commute:
  assumes tf_commute:
      "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s)
                = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_commute:
      "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
  shows "dg_spec_commute (fun_of_resolved_st_q_for gs) fg
           (base_dg_spec_st_for gs tf_st enter_st) (base_dg_spec_for gs tf)"
proof (rule dg_spec_commute.intro)
  show "\<And>a d g. map_prod fg (fun_of_resolved_st_q_for gs)
      (dg_spec_step (base_dg_spec_st_for gs tf_st enter_st) a d g)
        = dg_spec_step (base_dg_spec_for gs tf) a (fun_of_resolved_st_q_for gs d) (fg g)"
    by (simp add: dg_spec_step_base_st_for dg_spec_step_base_for tf_commute)
  show "\<And>ci dc g. fun_of_resolved_st_q_for gs
      (dgs_caller_cont (base_dg_spec_st_for gs tf_st enter_st) ci dc g)
        = dgs_caller_cont (base_dg_spec_for gs tf) ci (fun_of_resolved_st_q_for gs dc) (fg g)"
    by simp
  show "\<And>ci dc de g. map_prod fg (fun_of_resolved_st_q_for gs)
      (dgs_combine (base_dg_spec_st_for gs tf_st enter_st) ci dc de g)
        = dgs_combine (base_dg_spec_for gs tf) ci (fun_of_resolved_st_q_for gs dc)
            (fun_of_resolved_st_q_for gs de) (fg g)"
    unfolding dgs_combine_base_st_for dgs_combine_base_for map_prod_def
      fun_of_resolved_st_q_for_def
    by (auto simp add: combine_collect_abs_def fun_eq_iff location_of_def
        split: option.splits)
  show "\<And>ci dc g. map_prod fg (fun_of_resolved_st_q_for gs)
      (dgs_enter (base_dg_spec_st_for gs tf_st enter_st) ci dc g)
        = dgs_enter (base_dg_spec_for gs tf) ci (fun_of_resolved_st_q_for gs dc) (fg g)"
    by (simp add: dgs_enter_base_st_for dgs_enter_base_for enter_commute)
qed

text \<open>The frozen lifted record agrees with the normalized dead-code lift of
  the core on every composed operation. The raw \<open>dgs_combine_env\<close> stages
  differ (this record's computes the env-merge eagerly, the generic lifter's
  is strict); the composed \<^const>\<open>dgs_combine\<close> erases the difference.\<close>

lemma dg_spec_step_base_st_lift_agree:
  "dg_spec_step (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) a d g =
   dg_spec_step
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st))) a d g"
  unfolding dg_spec_step_base_st_for_lifted
  by (cases d) (simp_all add: dg_spec_step_base_st_for transfer_lift_def)

lemma dgs_caller_cont_base_st_lift_agree:
  "dgs_caller_cont (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc g =
   dgs_caller_cont
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st))) ci dc g"
  by (cases dc) (simp_all add: base_dg_spec_st_for_lifted_def)

lemma dgs_combine_base_st_lift_agree:
  "dgs_combine (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc de g =
   dgs_combine
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st))) ci dc de g"
  unfolding dgs_combine_base_st_for_lifted
  by (cases dc; cases de)
     (simp_all add: dgs_combine_base_st_for transfer_lift2_def)

lemma dgs_enter_base_st_lift_agree:
  "dgs_enter (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc g =
   dgs_enter
     (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st))) ci dc g"
  unfolding dgs_enter_base_st_for_lifted
  by (cases dc) (simp_all add: dgs_enter_base_st_for transfer_lift_def)

subsection \<open>Routed-domain compatibility, independent of any routing context\<close>

text \<open>
  Every current routed instance (Sign, Interval, Int) reproves the same three
  shapes -- \<open>dg_spec_step\<close>/\<open>dgs_enter\<close>/\<open>dgs_combine\<close> commuting under
  \<^const>\<open>fun_of_resolved_st_q_for\<close>, plus \<^locale>\<open>dg_reader_commute_gen\<close> at that
  same reader -- from its own executable/abstract transfer-commute facts,
  citing this theory's packaging theorems verbatim. Nothing in that derivation
  is domain-specific beyond the three primitive commute facts a domain's own
  executable-transfer soundness development already proves (\<open>sign_tf_st_for_commute\<close>,
  \<open>ivl_tf_st_for_commute\<close>, ...): this locale states the derivation once, so a
  domain interprets it instead of restating it. The locale is deliberately free
  of any routing context (\<open>route\<close>, \<open>Seed\<close>, \<open>Global\<close>, a solver): those are
  context-owned and solver-owned respectively, not domain-owned.
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
    and tf :: "'a domain_transfer"
  assumes tf_st_commute:
      "\<And>a s. fun_of_resolved_st_q_for gs (tf_st a s) = apply_tf tf a (fun_of_resolved_st_q_for gs s)"
    and enter_st_commute:
      "\<And>ci s. fun_of_resolved_st_q_for gs (enter_st ci s)
                   = snd (enter\<^sup># tf ci (fun_of_resolved_st_q_for gs s))"
    and empty_pred_exact:
      "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
begin

text \<open>
  One \<^locale>\<open>dg_spec_commute\<close> instance packages what the four theorems below
  used to prove separately: the naturality theorems give commute for the
  unlifted core's dead-code lift once (\<open>base_dg_spec_st_for_commute\<close> composed
  with \<open>dead_code_lift_commute\<close> and \<open>dead_code_normalize_commute\<close>), and the
  composed-operation agreement lemmas on both the executable and the
  semantic side (the latter from \<^theory>\<open>Voblint_Core.DG_Base\<close>) carry that
  onto the two frozen records. No per-field case split is proved twice.
\<close>

lemma dg_spec_commute_lifted:
  "dg_spec_commute (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
     (base_dg_spec_for_lifted gs is_empty_state tf)"
proof -
  have core: "dg_spec_commute (fun_of_resolved_st_q_for gs) (map_lift (fun_of_resolved_st_q_for gs))
      (base_dg_spec_st_for gs tf_st enter_st) (base_dg_spec_for gs tf)"
    by (rule base_dg_spec_st_for_commute[OF tf_st_commute enter_st_commute])
  have lifted: "dg_spec_commute (map_lift (fun_of_resolved_st_q_for gs))
      (map_lift (fun_of_resolved_st_q_for gs))
      (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st)) (dead_code_lift (base_dg_spec_for gs tf))"
    by (rule dead_code_lift_commute[OF core])
  have normalized: "dg_spec_commute (map_lift (fun_of_resolved_st_q_for gs))
      (map_lift (fun_of_resolved_st_q_for gs))
      (dead_code_normalize empty_pred (dead_code_lift (base_dg_spec_st_for gs tf_st enter_st)))
      (dead_code_normalize is_empty_state (dead_code_lift (base_dg_spec_for gs tf)))"
    by (rule dead_code_normalize_commute[OF lifted]) (simp add: empty_pred_exact)
  have exec_side: "dg_spec_commute (map_lift (fun_of_resolved_st_q_for gs))
      (map_lift (fun_of_resolved_st_q_for gs))
      (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
      (dead_code_normalize is_empty_state (dead_code_lift (base_dg_spec_for gs tf)))"
    by (rule dg_spec_commute_cong_left
          [OF dg_spec_step_base_st_lift_agree dgs_caller_cont_base_st_lift_agree
              dgs_combine_base_st_lift_agree dgs_enter_base_st_lift_agree normalized])
  show ?thesis
    by (rule dg_spec_commute_cong_right
          [OF dg_spec_step_base_lift_agree dgs_caller_cont_base_lift_agree
              dgs_combine_base_lift_agree dgs_enter_base_lift_agree exec_side])
qed

lemma Hstep_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dg_spec_step (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) a d g)
   = dg_spec_step (base_dg_spec_for_lifted gs is_empty_state tf) a
       (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule dg_spec_commute.step_commute[OF dg_spec_commute_lifted])

lemma Henter_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dgs_enter (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci d g)
   = dgs_enter (base_dg_spec_for_lifted gs is_empty_state tf) ci
       (map_lift (fun_of_resolved_st_q_for gs) d) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule dg_spec_commute.enter_commute[OF dg_spec_commute_lifted])

lemma Hcomb_lifted_for:
  "map_prod (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))
     (dgs_combine (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) dst dc de g)
   = dgs_combine (base_dg_spec_for_lifted gs is_empty_state tf) dst
       (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) de)
       (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule dg_spec_commute.combine_commute[OF dg_spec_commute_lifted])

lemma Hcont_lifted_for:
  "map_lift (fun_of_resolved_st_q_for gs)
     (caller_cont (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ci dc g)
   = caller_cont (base_dg_spec_for_lifted gs is_empty_state tf) ci
       (map_lift (fun_of_resolved_st_q_for gs) dc) (map_lift (fun_of_resolved_st_q_for gs) g)"
  by (rule dg_spec_commute.cont_commute[OF dg_spec_commute_lifted])

lemma dg_reader_commute_gen_lifted:
  "dg_reader_commute_gen
     (map_lift (fun_of_resolved_st_q_for gs)) (map_lift (fun_of_resolved_st_q_for gs))"
  by unfold_locales (simp_all add: map_lift_sup fun_of_resolved_st_q_for_sup)

subsection \<open>Soundness at the executable carrier, pulled back along the readback\<close>

text \<open>
  The framework is carrier-agnostic, so nothing forces it to be instantiated at
  \<open>'a abs_state lifted\<close>: with the concretization read through
  \<^const>\<open>fun_of_resolved_st_q_for\<close>, the executable Base-style spec is itself a
  \<^locale>\<open>sound_dg_spec\<close>, and the three commute facts above are all that the proof
  needs. An instance that interprets the routed spine at \<open>spec_st\<close> with this
  concretization feeds it the solver's own table and never transports a solved
  system between carriers.
\<close>

definition gamma_exec :: "'a exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> store set" where
  "gamma_exec d g =
     gamma_dg_base (map_lift (fun_of_resolved_st_q_for gs) d)
                   (map_lift (fun_of_resolved_st_q_for gs) g)"

lemma gamma_exec_Bot [simp]: "gamma_exec Bot g = {}"
  by (simp add: gamma_exec_def gamma_dg_base_def)

theorem sound_dg_spec_st:
  assumes abs: "sound_dg_spec
     (base_dg_spec_for_lifted gs is_empty_state tf :: ('a abs_state lifted, 'a abs_state lifted) dg_spec)
     gamma_dg_base gs"
  shows "sound_dg_spec (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) gamma_exec gs"
proof unfold_locales
  let ?f = "map_lift (fun_of_resolved_st_q_for gs)"
  fix d d' g g' :: "'a exec_dg_st lifted"
  assume "d \<le> d'" "g \<le> g'"
  then show "gamma_exec d g \<subseteq> gamma_exec d' g'"
    unfolding gamma_exec_def
    by (intro sound_dg_spec.gammaDG_mono[OF abs] map_lift_fun_of_resolved_st_q_for_mono)
next
  let ?f = "map_lift (fun_of_resolved_st_q_for gs)"
  let ?S = "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"
  let ?A = "base_dg_spec_for_lifted gs is_empty_state tf"
  fix a :: edge_action and d g :: "'a exec_dg_st lifted"
  obtain g1 d1 where st: "dg_spec_step ?S a d g = (g1, d1)"
    by (cases "dg_spec_step ?S a d g")
  have "dg_spec_step ?A a (?f d) (?f g) = (?f g1, ?f d1)"
    using Hstep_lifted_for[of a d g] st by simp
  with sound_dg_spec.step_sound[OF abs, of a "?f d" "?f g"]
  show "edge_collect a (gamma_exec d g)
          \<subseteq> (case dg_spec_step ?S a d g of (g', d') \<Rightarrow> gamma_exec d' g')"
    unfolding gamma_exec_def st by simp
next
  let ?f = "map_lift (fun_of_resolved_st_q_for gs)"
  let ?S = "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"
  fix s :: store and dc g :: "'a exec_dg_st lifted" and ci :: call_info
  assume "s \<in> gamma_exec dc g"
  then show "s \<in> gamma_exec (dgs_caller_cont ?S ci dc g) g"
    unfolding gamma_exec_def
    using sound_dg_spec.caller_cont_sound[OF abs, of s "?f dc" "?f g" ci]
      Hcont_lifted_for[of ci dc g] by simp
next
  let ?f = "map_lift (fun_of_resolved_st_q_for gs)"
  let ?S = "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"
  let ?A = "base_dg_spec_for_lifted gs is_empty_state tf"
  fix s t :: store and dcont de g :: "'a exec_dg_st lifted" and ci :: call_info
  assume s: "s \<in> gamma_exec dcont g" and t: "t \<in> gamma_exec de g"
  obtain g1 d1 where cmb: "dgs_combine ?S ci dcont de g = (g1, d1)"
    by (cases "dgs_combine ?S ci dcont de g")
  have "dgs_combine ?A ci (?f dcont) (?f de) (?f g) = (?f g1, ?f d1)"
    using Hcomb_lifted_for[of ci dcont de g] cmb by simp
  with sound_dg_spec.combine_sound[OF abs, of s "?f dcont" "?f g" t "?f de" ci] s t
  show "combine_collect gs (ci_dst ci) s t
          \<in> (case dgs_combine ?S ci dcont de g of (g', d') \<Rightarrow> gamma_exec d' g')"
    unfolding gamma_exec_def cmb by simp
next
  let ?f = "map_lift (fun_of_resolved_st_q_for gs)"
  let ?S = "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st"
  let ?A = "base_dg_spec_for_lifted gs is_empty_state tf"
  fix s :: store and dc g :: "'a exec_dg_st lifted" and ci :: call_info
  assume s: "s \<in> gamma_exec dc g"
  obtain g1 d1 where en: "dgs_enter ?S ci dc g = (g1, d1)"
    by (cases "dgs_enter ?S ci dc g")
  have "dgs_enter ?A ci (?f dc) (?f g) = (?f g1, ?f d1)"
    using Henter_lifted_for[of ci dc g] en by simp
  with sound_dg_spec.enter_sound[OF abs, of s "?f dc" "?f g" ci] s
  show "call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
          \<in> (case dgs_enter ?S ci dc g of (g', d') \<Rightarrow> gamma_exec d' g')"
    unfolding gamma_exec_def en by simp
qed

subsection \<open>A generic exec-level formal-entry route, and its commute to the abstract one\<close>

text \<open>
  \<open>formals_route_lifted\<close>/\<open>formals_route_lifted_gen\<close> (\<^theory>\<open>Voblint_Core.Routed_Context\<close>)
  are already domain-generic at the abstract carrier \<open>'a abs_state lifted\<close> -- the shape
  \<^locale>\<open>routed_context_base_hetero\<close>'s own \<open>route\<close> parameter needs. The executable equation
  system a solver actually runs needs the same construction at the exec carrier
  \<open>'a exec_dg_st lifted\<close> instead, built from this locale's own \<open>enter_st\<close>/\<open>empty_pred\<close>
  rather than the mathematical \<open>enter#\<close>/\<open>tf\<close>: every current EntryState-style routed
  instance (Interval's own \<open>entry_state_route\<close>, \<open>Interval_Ctx_Entry_State_Sound\<close>)
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
  "formals_route_lifted (base_dg_spec_for_lifted gs is_empty_state tf)
     (map_lift (fun_of_resolved_st_q_for gs) s) ca = entry_exec_route s ca"
  by (cases ca; cases s)
     (simp_all add: formals_route_lifted_def entry_exec_route_def
                    formals_context_def fun_of_resolved_st_q_for_def)

lemma entry_exec_route_gen_commute:
  "formals_route_lifted_gen (base_dg_spec_for_lifted gs is_empty_state tf) u ctx
     (map_lift (fun_of_resolved_st_q_for gs) s) ca = entry_exec_route_gen u ctx s ca"
  by (simp add: formals_route_lifted_gen_def entry_exec_route_gen_def entry_exec_route_commute)

end

end

