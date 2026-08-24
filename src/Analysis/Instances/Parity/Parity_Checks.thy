theory Parity_Checks
  imports Parity_Numeric_Queries "Voblint_Core.Abstract_Checks" Parity_Exec
    "Voblint_Core.Analysis_Result"
    "Voblint_Core.DG_Analysis_Adapter"
    "Voblint_Core.Monovariant_Analysis_Result"
    Parity_Ctx_None_Sound
begin

hide_const phase.N
hide_const (open) \<sigma>
  \<comment> \<open>\<open>TD_side\<close> defines a record field \<open>\<sigma>\<close>; hide the short name so
      this theory's own \<open>\<sigma>\<close> abstract-state variables stay unambiguous.\<close>

section \<open>Parity instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here, exactly as Voblint_Analysis.Sign_Checks
  and Voblint_Analysis.Interval_Checks: the Parity lattice comparison
  tables (\<open>parity_less_true\<close>/\<open>parity_less_false\<close>/\<open>parity_eq_true\<close>/
  \<open>parity_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Parity_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Parity expression
  evaluator \<open>aval_parity\<close> lives in \<^theory>\<open>Voblint_Analysis.Parity_Domain\<close>. The
  Boolean recursion over \<^typ>\<open>exp\<close>, the three-way classification, and the
  node-indexed bridge to \<^const>\<open>checks_proven\<close> come from interpreting
  \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>) once, below,
  reusing the numeric-query facts already proved sound in
  \<open>parity_numeric_queries\<close> --- no Boolean recursion or classification logic
  is restated.
\<close>

text \<open>
  \<open>esyn default_tyenv\<close> always synthesizes \<open>I32\<close> (or nothing, and \<open>opk\<close> then
  defaults to \<open>I32\<close> too): every declared kind is \<open>I32\<close>, and \<open>ik_promote I32 =
  I32\<close>. Every \<open>elaborate default_tyenv ik e\<close> therefore elaborates \<open>e\<close> at
  \<open>I32\<close> throughout, regardless of the outer \<open>ik\<close> -- \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/
  \<open>Or\<close>'s own recomputed kind is always \<open>I32\<close> too, the same one \<open>Plus\<close>/
  \<open>Minus\<close>/\<open>Times\<close> propagate unchanged. (Restated locally from
  \<open>Sign_Checks\<close>; both domains need the same domain-independent fact about
  \<open>esyn\<close>/\<open>kjoin\<close>/\<open>default_tyenv\<close>.)
\<close>

lemma esyn_default_tyenv_cases:
  "esyn default_tyenv e = None \<or> esyn default_tyenv e = Some I32"
  by (induction e) (auto simp: default_tyenv_def ik_promote_pins)

lemma esyn_default_tyenv_I32 [simp]: "opk (esyn default_tyenv e) = I32"
  using esyn_default_tyenv_cases[of e] by (auto simp: opk_def)

lemma kjoin_default_tyenv_I32 [simp]:
  "opk (kjoin (esyn default_tyenv e1) (esyn default_tyenv e2)) = I32"
  using esyn_default_tyenv_cases[of e1] esyn_default_tyenv_cases[of e2]
  by (auto simp: opk_def)

text \<open>
  \<open>aval\<close>'s arithmetic is genuinely unbounded (no \<open>ik_norm\<close> truncation at any
  node), while \<open>aval_parity_t\<close> casts at every arithmetic node -- but
  \<open>parity_cast\<close> is the identity, so that cast is a no-op at the abstract
  level: it never invokes \<open>ik_norm\<close>. The two evaluators therefore agree
  exactly, by a direct structural homomorphism (\<open>parity_plus_sound\<close> etc.),
  with no wraparound reasoning needed at all.
\<close>

lemma aval_parity_t_default_agree:
  assumes H: "\<forall>x. s x \<in> gamma_parity (\<sigma> x)"
  shows "aval e s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e) \<sigma>)"
using H proof (induction e)
  case (N n)
  show ?case by (simp add: parity_cast_def parity_of_int_gamma)
next
  case (V x)
  from H show ?case by (simp add: parity_cast_def)
next
  case (Plus e1 e2)
  from Plus.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Plus.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case using parity_plus_sound[OF h1 h2] by (simp add: parity_cast_def)
next
  case (Minus e1 e2)
  from Minus.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Minus.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case using parity_minus_sound[OF h1 h2] by (simp add: parity_cast_def)
next
  case (Times e1 e2)
  from Times.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Times.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case using parity_times_sound[OF h1 h2] by (simp add: parity_cast_def)
next
  case (Less e1 e2)
  from Less.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Less.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bottom_parity_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bottom_parity_correct)
  have shape: "aval_parity_t (elaborate default_tyenv I32 (Less e1 e2)) \<sigma> = PTop"
    using nb1 nb2 by (simp add: kjoin_default_tyenv_I32 Let_def)
  show ?case by (simp add: shape)
next
  case (Eq e1 e2)
  from Eq.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Eq.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bottom_parity_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bottom_parity_correct)
  have shape: "aval_parity_t (elaborate default_tyenv I32 (exp.Eq e1 e2)) \<sigma> =
      (if parity_eqb ?c1 ?c2 = Some True then POdd
       else if parity_eqb ?c1 ?c2 = Some False then PEven
       else PTop)"
    using nb1 nb2 by (simp add: kjoin_default_tyenv_I32 Let_def)
  show ?case
  proof (cases "parity_eqb ?c1 ?c2")
    case (Some b)
    then show ?thesis
      using parity_eqb_sound[OF Some h1 h2] by (cases b) (simp_all add: shape)
  next
    case None
    then show ?thesis by (simp add: shape)
  qed
next
  case (Not e)
  from Not.IH[OF H] have h: "aval e s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e) \<sigma>)"
    by auto
  let ?c = "aval_parity_t (elaborate default_tyenv I32 e) \<sigma>"
  have nb: "\<not> is_bot ?c" using h by (auto simp: is_bottom_parity_correct)
  have shape: "aval_parity_t (elaborate default_tyenv I32 (exp.Not e)) \<sigma> =
      (if parity_tobool ?c = Some True then PEven
       else if parity_tobool ?c = Some False then POdd
       else PTop)"
    using nb by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "parity_tobool ?c")
    case (Some b)
    then show ?thesis
      using parity_tobool_sound[OF Some h] by (cases b) (simp_all add: shape truthy_def)
  next
    case None
    then show ?thesis by (simp add: shape)
  qed
next
  case (And e1 e2)
  from And.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from And.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bottom_parity_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bottom_parity_correct)
  have shape: "aval_parity_t (elaborate default_tyenv I32 (And e1 e2)) \<sigma> =
      (if parity_tobool ?c1 = Some False \<or> parity_tobool ?c2 = Some False then PEven
       else if parity_tobool ?c1 = Some True \<and> parity_tobool ?c2 = Some True then POdd
       else PTop)"
    using nb1 nb2 by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "parity_tobool ?c1 = Some False \<or> parity_tobool ?c2 = Some False")
    case True
    then have "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using parity_tobool_sound h1 h2 by fastforce
    with True show ?thesis by (simp add: shape truthy_def)
  next
    case False
    show ?thesis
    proof (cases "parity_tobool ?c1 = Some True \<and> parity_tobool ?c2 = Some True")
      case True
      then have "truthy (aval e1 s) \<and> truthy (aval e2 s)"
        using parity_tobool_sound h1 h2 by auto
      with True False show ?thesis by (simp add: shape truthy_def)
    next
      case False
      show ?thesis by (simp add: shape)
    qed
  qed
next
  case (Or e1 e2)
  from Or.IH[OF H] have h1: "aval e1 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Or.IH[OF H] have h2: "aval e2 s \<in> gamma_parity (aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_parity_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_parity_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bottom_parity_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bottom_parity_correct)
  have shape: "aval_parity_t (elaborate default_tyenv I32 (Or e1 e2)) \<sigma> =
      (if parity_tobool ?c1 = Some True \<or> parity_tobool ?c2 = Some True then POdd
       else if parity_tobool ?c1 = Some False \<and> parity_tobool ?c2 = Some False then PEven
       else PTop)"
    using nb1 nb2 by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "parity_tobool ?c1 = Some True \<or> parity_tobool ?c2 = Some True")
    case True
    then have "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using parity_tobool_sound h1 h2 by fastforce
    with True show ?thesis by (simp add: shape truthy_def)
  next
    case False
    show ?thesis
    proof (cases "parity_tobool ?c1 = Some False \<and> parity_tobool ?c2 = Some False")
      case True
      then have "\<not> truthy (aval e1 s) \<and> \<not> truthy (aval e2 s)"
        using parity_tobool_sound h1 h2 by auto
      with True False show ?thesis by (simp add: shape truthy_def)
    next
      case False
      show ?thesis by (simp add: shape)
    qed
  qed
qed

global_interpretation parity_check_domain:
  abstract_check_domain gamma_parity parity_less_true parity_less_false
    parity_eq_true parity_eq_false gamma_state "aval_parity default_tyenv I32"
  defines
    parity_check_true = parity_check_domain.check_true
    and parity_check_false = parity_check_domain.check_false
    and parity_classify_check = parity_check_domain.classify_check
    and parity_checks_proven = parity_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "parity abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have H: "\<forall>x. s x \<in> gamma_parity (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_parity (aval_parity default_tyenv I32 e \<sigma>)"
    using aval_parity_t_default_agree[OF H] by (simp add: aval_parity_def)
qed

text \<open>
  Only the consumer-facing aliases get a short Parity-prefixed name, matching
  Voblint_Analysis.Sign_Checks naming convention:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by the worked check-discharge example. The lower-level
  facts \<open>classify_check\<close>'s own soundness is built from stay reachable under
  the qualified \<open>parity_check_domain.\<close> name.
\<close>

lemmas parity_classify_check_proved = parity_check_domain.classify_check_proved
lemmas parity_classify_check_refuted = parity_check_domain.classify_check_refuted
lemmas parity_checks_provenI = parity_check_domain.abstract_checks_provenI
lemmas parity_checks_proven_sound = parity_check_domain.abstract_checks_proven_sound

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>PTop\<close>) environment, so each test exercises exactly the comparison it
  names.\<close>

definition test_env_eo :: "parity abs_state" where
  "test_env_eo = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

text \<open>
  Disjoint parity classes at the variable's own declared kind:
  \<^const>\<open>parity_cast\<close> is the identity (parity's modulus, \<open>2\<close>, divides every
  machine-width wraparound modulus, so evenness/oddness survives truncation
  unconditionally), so casting through a concrete \<open>ikind\<close> loses no
  information here.
\<close>

lemma parity_classify_eq_refuted:
  "parity_classify_check (Eq (V (STR ''x'')) (V (STR ''y''))) test_env_eo = Check_Refuted"
  unfolding test_env_eo_def by eval

lemma parity_classify_not_eq_proved:
  "parity_classify_check (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) test_env_eo = Check_Proved"
  unfolding test_env_eo_def by eval

text \<open>Same abstract value on both sides: \<open>x\<close> is \<open>PEven\<close> and the literal \<open>4\<close>
  is also \<open>PEven\<close>, but Parity has no singleton representation, so the
  equality stays unknown rather than falsely proved.\<close>

lemma parity_classify_eq_unknown:
  "parity_classify_check (Eq (V (STR ''x'')) (N 4)) test_env_eo = Check_Unknown"
  unfolding test_env_eo_def by eval

text \<open>Nested \<open>Or\<close> with disjoint operand parities: the left disjunct alone
  already proves the whole \<open>Or\<close>.\<close>

definition test_env_nested_proved :: "parity abs_state" where
  "test_env_nested_proved = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := POdd)"

lemma parity_classify_nested_proved:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Proved"
  unfolding test_env_nested_proved_def by eval

text \<open>Nested \<open>Or\<close>, unknown: neither branch resolves when both sides share a
  parity class.\<close>

definition test_env_nested_unknown :: "parity abs_state" where
  "test_env_nested_unknown = (\<lambda>_. PTop)((STR ''x'') := PEven, (STR ''y'') := PEven)"

lemma parity_classify_nested_unknown:
  "parity_classify_check
     (Or (Not (Eq (V (STR ''x'')) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

section \<open>The generic report adapter, at the routed-unit context\<close>
section \<open>The generic report adapter, at the routed-unit context\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at \<open>Parity_Ctx_None_Sound\<close>'s own routed-unit
  solved system, mirroring \<open>Sign_Checks\<close>'s own interpretation exactly. Every obligation is
  either one that theory's \<open>pctx_dg\<close>/\<open>pctx_routed\<close> interpretations already discharge, or
  one that collapses at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>; only
  \<open>classify_proved\<close>/\<open>classify_refuted\<close> are Parity's own, and both are the pre-existing
  \<^const>\<open>parity_classify_check\<close> soundness facts above. No Parity-specific result, report,
  or node-soundness construction appears anywhere below --- the adapter derives all three
  generically.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "parity exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "pctx_terminates gs \<Gamma> is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ())
                      \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
begin

text \<open>
  @{thm [source] base_dg_spec_sound}'s third premise, \<open>ret_ok: (\<And>x v. ik_norm (\<Gamma> x) v = v)\<close>,
  is unresolved below -- the same pre-existing well-typedness gap flagged in
  \<open>Parity_Ctx_None_Sound.pctx_dg_base\<close>.
\<close>
interpretation pctx_dg_base: sound_dg_spec "pctx_abs_spec gs \<Gamma>" gamma_dg_base gs \<Gamma>
  unfolding pctx_abs_spec_def
  apply (rule base_dg_spec_sound[OF parity_is_sound_transfer_for is_bot_state_gamma_state_empty])
  sorry

interpretation pctx_adapter: dg_analysis_adapter enterc_unit "pctx_abs_spec gs \<Gamma>" gs \<Gamma>
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_parity_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::parity exec_dg_st lifted)"
    "pctx_sigma_abs gs \<Gamma> is_bot_pred Pi ps mnm main" "fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" "pctx_sg gs \<Gamma> is_bot_pred Pi ps mnm main"
    Seed parity_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case
    using compile_prog_finite by auto
next
  case PP show ?case
    by (simp only: pctx_sigma_abs_def[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok]
        pctx_sigma_abs_exec_def)
      (rule pctx_pp_abs[OF solves exact])
next
  case (SgCov v c)
  note mem = this
  have eq1: "pctx_sg gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (v, c))
               = locals (pctx_sigma_abs gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (v, c)))"
    by (rule pctx_sg_covered[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem])
  show ?case
    using eq1 gamma_dg_base_def by auto
next
  case (SgUncov v c)
  note nmem = this
  show ?case
    by (rule pctx_sg_uncovered_empty[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok nmem])
next
  case (Fwd u a v c)
  thus ?case by (rule fwd_ok)
next
  case FinC show ?case
    by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case by (simp add: static_resolve_iff compile_prog_finite)
next
  case (RouteEnterc u ctx dst pars args p cont s)
  show ?case by (simp add: route_unit_def enterc_unit_def)
next
  case (CallFwd u ctx dst pars args p cont)
  show ?case
    using CallFwd(1,2) call_fwd_ok unfolding route_unit_def by blast
next
  case (CombFwd cl c1 dst pars args p cont)
  show ?case using CombFwd(1,2) comb_fwd_ok by blast
next
  case (EnterAgree cl s es dst pars args p cont)
  note ces = EnterAgree(1) and ce = EnterAgree(2)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter \<Gamma> gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule parity_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule parity_classify_check_refuted)
qed

text \<open>
  The generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives once and for all,
  re-exported so a caller cites them without naming the interpretation.
\<close>

lemmas pctx_report_ctx_proved_sound = pctx_adapter.analyse_report_ctx_proved_sound
lemmas pctx_report_ctx_refuted_sound = pctx_adapter.analyse_report_ctx_refuted_sound
lemmas pctx_result_node_sound = pctx_adapter.analyse_result_node_sound

text \<open>
  \<open>pctx_analyse_result_eq\<close> identifies the adapter's own result reading with the
  raw-tuple shape \<^const>\<open>analyse_parity_ctx_result_for\<close> (\<open>Parity_Ctx_None_Sound\<close>)
  builds directly from \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close>: both
  collapse the same \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split on the same projected
  local unknown, one via \<open>is_bot_state\<close> after projecting, the other via
  \<open>is_bot_pred\<close> before projecting -- \<open>exact\<close> is what identifies the two orders.
  Composing it with \<open>pctx_result_node_sound\<close> gives
  \<^const>\<open>analyse_parity_ctx_result_for\<close>'s node-soundness bridge without
  re-deriving \<open>routed_context_hetero\<close>'s coverage/sigma-projection argument.
\<close>

lemma pctx_analyse_result_eq:
  "lookup_context pctx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
      then normalize_point gs
             (canonicalize_lift is_bot_pred
               (locals (snd (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding pctx_adapter.lookup_context_analyse_result
  apply (simp only: pctx_sigma_abs_def[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok]
                     pctx_sigma_abs_exec_def o_apply fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (pctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

section \<open>Solved-result table and whole-program check report\<close>

text \<open>
  The public surface, in the same shape Sign's own
  \<open>analyse_sign_result_for\<close>/\<open>analyse_sign_report_for\<close> take: one-line partial
  applications of \<open>Parity_Ctx_None_Sound\<close>'s tables at \<^const>\<open>prog_main_name\<close>, and a report
  reading per-node state through \<^const>\<open>lookup_context\<close> rather than a raw
  solver-environment lookup. An \<^const>\<open>Unreachable\<close> point classifies at \<^const>\<open>bot\<close>, the
  same value \<^const>\<open>classify_checks\<close> always fed such a node, so \<open>check_result\<close>'s existing
  three-way verdict is preserved rather than gaining a fourth outcome.
\<close>

definition analyse_parity_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_for gs \<Gamma> p = analyse_parity_ctx_result_for gs \<Gamma> prog_main_name p"

definition analyse_parity_result :: "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result p = analyse_parity_result_for (declared_global p) (prog_tyenv p) p"

definition analyse_parity_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin_for gs \<Gamma> p =
     analyse_parity_ctx_result_per_origin_for gs \<Gamma> prog_main_name p"

definition analyse_parity_result_per_origin ::
    "imp_prog \<Rightarrow> (unit, parity abs_state) analysis_result" where
  "analyse_parity_result_per_origin p =
     analyse_parity_result_per_origin_for (declared_global p) (prog_tyenv p) p"

text \<open>\<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so the single
  routed solve is shared across every check rather than repeated per check.\<close>

definition analyse_parity_report_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_for gs \<Gamma> p =
     analysis_surface.report (analyse_parity_result_for gs \<Gamma>) bot parity_classify_check p"

definition analyse_parity_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report p = analyse_parity_report_for (declared_global p) (prog_tyenv p) p"

definition analyse_parity_report_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin_for gs \<Gamma> p =
     analysis_surface.report (analyse_parity_result_per_origin_for gs \<Gamma>) bot
       parity_classify_check p"

definition analyse_parity_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_parity_report_per_origin p =
     analyse_parity_report_per_origin_for (declared_global p) (prog_tyenv p) p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Parity's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. Like Sign, it has
  no warrowing interpretation: the four-element lattice has finite height, so widening has
  nothing to accelerate and no solved table of its own.
\<close>

interpretation parity_join: analysis_surface
  analyse_parity_result bot parity_classify_check
  by unfold_locales

interpretation parity_per_origin: analysis_surface
  analyse_parity_result_per_origin bot parity_classify_check
  by unfold_locales

lemma parity_report_join_eq: "analyse_parity_report p = parity_join.report p"
  by (simp add: analyse_parity_report_def analyse_parity_report_for_def
      analyse_parity_result_def surface_unfold)

lemma parity_report_per_origin_eq:
  "analyse_parity_report_per_origin p = parity_per_origin.report p"
  by (simp add: analyse_parity_report_per_origin_def
      analyse_parity_report_per_origin_for_def analyse_parity_result_per_origin_def
      surface_unfold)

text \<open>
  State-carrying sibling, via \<^const>\<open>classify_checks_with_state\<close>: the same result table,
  with the per-check Parity environment attached to each entry instead of discarded, and
  an exact \<open>unreachable\<close> flag read straight off \<^const>\<open>lookup_context\<close>'s
  \<^const>\<open>Unreachable\<close>/\<^const>\<open>Reachable\<close> case split. Mirrors
  \<open>analyse_sign_report_for_with_state\<close> exactly.
\<close>

definition analyse_parity_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> parity)) list" where
  "analyse_parity_report_for_with_state gs \<Gamma> p =
     (let r = analyse_parity_result_for gs \<Gamma> p
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of
                  Unreachable \<Rightarrow> (True, bot)
                | Reachable st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). parity_classify_check c s))"

definition analyse_parity_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> parity)) list" where
  "analyse_parity_report_with_state p =
     analyse_parity_report_for_with_state (declared_global p) (prog_tyenv p) p"

end
