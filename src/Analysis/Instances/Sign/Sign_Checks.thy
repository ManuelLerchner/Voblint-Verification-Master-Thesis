theory Sign_Checks
  imports Sign_Numeric_Queries "Voblint_Core.Abstract_Checks"
    "Voblint_Core.Analysis_Result" Sign_Exec
    "Voblint_Core.Monovariant_Analysis_Result"
    "Voblint_Core.DG_Analysis_Adapter"
    Sign_Ctx_None_Sound
begin

hide_const phase.N
hide_const (open) \<sigma>
  \<comment> \<open>\<open>TD_side\<close> defines a record field \<open>\<sigma>\<close>; hide the short name so
      this theory's own \<open>\<sigma>\<close> abstract-state variables stay unambiguous.\<close>

section \<open>Sign instance of the generic check-discharge interface\<close>

text \<open>
  Only composition lives here: the Sign lattice comparison tables
  (\<open>sign_less_true\<close>/\<open>sign_less_false\<close>/\<open>sign_eq_true\<close>/\<open>sign_eq_false\<close>) and their
  \<^theory>\<open>Voblint_Analysis.Sign_Numeric_Queries\<close> interpretation of
  \<open>abstract_numeric_queries\<close> live in that theory. The Sign expression
  evaluator \<open>aval_sign\<close> lives in \<^theory>\<open>Voblint_Analysis.Sign_Arithmetic\<close>. The
  Boolean recursion over \<^typ>\<open>exp\<close> (\<open>Not\<close>, \<open>And\<close>, \<open>Or\<close>), the three-way
  classification, and the node-indexed bridge to \<^const>\<open>checks_proven\<close> come
  from interpreting \<open>abstract_check_domain\<close> (\<^theory>\<open>Voblint_Core.Abstract_Checks\<close>)
  once, below, reusing the numeric-query facts already proved sound in
  \<open>sign_numeric_queries\<close> rather than re-deriving the comparison tables ---
  the same way \<open>sign_backward_domain\<close> in \<open>Sign_Backward\<close> interprets
  \<open>backward_domain\<close> for guard narrowing.
\<close>

text \<open>
  \<open>esyn default_tyenv\<close> always synthesizes \<open>I32\<close> (or nothing, and \<open>opk\<close> then
  defaults to \<open>I32\<close> too): every declared kind is \<open>I32\<close>, and \<open>ik_promote I32 =
  I32\<close>. Every \<open>elaborate default_tyenv ik e\<close> therefore elaborates \<open>e\<close> at
  \<open>I32\<close> throughout, regardless of the outer \<open>ik\<close> -- \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/
  \<open>Or\<close>'s own recomputed kind is always \<open>I32\<close> too, the same one \<open>Plus\<close>/
  \<open>Minus\<close>/\<open>Times\<close> propagate unchanged.
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
  \<open>sign_cast\<close> at a signed kind never needs \<^const>\<open>ik_norm\<close> to justify
  membership: it is either \<open>bot\<close> (vacuous), the identity at \<open>SZero\<close> (\<open>0\<close>
  needs no wraparound to fit any kind), or \<open>top\<close> (trivially sound). A raw,
  un-normed concrete value therefore survives the cast too, not only its
  \<open>ik_norm\<close>'d image.
\<close>

lemma sign_cast_signed_raw:
  assumes "v \<in> gamma_sign a" and "ik_signed ik"
  shows "v \<in> gamma_sign (sign_cast ik a)"
proof (cases "is_bot a")
  case True
  with assms show ?thesis by (simp add: is_bot_sign is_bottom_sign_correct)
next
  case False
  show ?thesis
  proof (cases "a = SZero")
    case True
    with assms have "v = 0" by simp
    with True show ?thesis by (simp add: sign_cast_def is_bot_sign is_bottom_sign_correct)
  next
    case False
    with \<open>\<not> is_bot a\<close> \<open>ik_signed ik\<close> show ?thesis
      by (simp add: sign_cast_def gamma_sign_top)
  qed
qed

text \<open>
  The same fact bundled with the \<open>SZero\<close>-implies-exactly-zero half, matching
  \<open>sign_cast_signed_combine\<close>'s binary shape for a unary cast.
\<close>

lemma sign_cast_signed_agree:
  assumes "v \<in> gamma_sign a" and "ik_signed ik"
  shows "v \<in> gamma_sign (sign_cast ik a) \<and> (sign_cast ik a = SZero \<longrightarrow> v = 0)"
proof (cases "is_bot a")
  case True
  with assms show ?thesis by (simp add: is_bot_sign is_bottom_sign_correct)
next
  case False
  show ?thesis
  proof (cases "a = SZero")
    case True
    with assms have "v = 0" by simp
    with True show ?thesis by (simp add: sign_cast_def is_bot_sign is_bottom_sign_correct)
  next
    case False
    with \<open>\<not> is_bot a\<close> \<open>ik_signed ik\<close> show ?thesis
      by (simp add: sign_cast_def gamma_sign_top top_sign_def)
  qed
qed

text \<open>
  A binary combinator cast at \<open>I32\<close> after the fact: either it lands exactly
  at \<open>SZero\<close> (forcing the concrete combined value to be exactly \<open>0\<close>,
  immune to wraparound regardless of kind), or it widens to \<open>top\<close>
  (trivially sound for any value at all).
\<close>

lemma sign_cast_signed_combine:
  fixes op :: "sign \<Rightarrow> sign \<Rightarrow> sign" and cop :: "int \<Rightarrow> int \<Rightarrow> int"
  assumes combine_sound: "\<And>i j p q. i \<in> gamma_sign p \<Longrightarrow> j \<in> gamma_sign q \<Longrightarrow> cop i j \<in> gamma_sign (op p q)"
    and h1: "i \<in> gamma_sign p" and h2: "j \<in> gamma_sign q"
  shows "cop i j \<in> gamma_sign (sign_cast I32 (op p q)) \<and>
         (sign_cast I32 (op p q) = SZero \<longrightarrow> cop i j = 0)"
proof -
  have v: "cop i j \<in> gamma_sign (op p q)" using combine_sound[OF h1 h2] .
  show ?thesis
  proof (cases "is_bot (op p q)")
    case True
    with v show ?thesis by (simp add: is_bot_sign is_bottom_sign_correct)
  next
    case False
    show ?thesis
    proof (cases "op p q = SZero")
      case True
      with v have "cop i j = 0" by simp
      with True show ?thesis by (simp add: sign_cast_def is_bot_sign is_bottom_sign_correct)
    next
      case False
      with \<open>\<not> is_bot (op p q)\<close> show ?thesis
        by (simp add: sign_cast_def gamma_sign_top top_sign_def)
    qed
  qed
qed

text \<open>
  \<open>aval\<close>'s arithmetic is genuinely unbounded (no \<open>ik_norm\<close> truncation at any
  node), while \<open>aval_sign_t\<close> casts at every arithmetic node. At \<open>I32\<close> (a
  signed kind) the two evaluators agree exactly, not merely approximate one
  another: every node's abstract result collapses to either an exact
  \<open>SZero\<close> (forcing the underlying concrete value to be exactly \<open>0\<close>, immune
  to wraparound) or \<open>STop\<close> (trivially sound for any value at all).
\<close>

lemma aval_sign_t_default_agree:
  assumes H: "\<forall>x. s x \<in> gamma_sign (\<sigma> x)"
  shows "aval e s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e) \<sigma>) \<and>
         (aval_sign_t (elaborate default_tyenv I32 e) \<sigma> = SZero \<longrightarrow> aval e s = 0)"
using H proof (induction e)
  case (N n)
  have v: "n \<in> gamma_sign (sign_of_int n)" by (rule sign_of_int_gamma)
  show ?case using sign_cast_signed_agree[OF v, of I32] by simp
next
  case (V x)
  from H have hx: "s x \<in> gamma_sign (\<sigma> x)" by simp
  show ?case using sign_cast_signed_agree[OF hx, of I32] by simp
next
  case (Plus e1 e2)
  from Plus.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Plus.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case
    using sign_cast_signed_combine[OF sign_plus_sound h1 h2] by simp
next
  case (Minus e1 e2)
  from Minus.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Minus.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case
    using sign_cast_signed_combine[OF sign_minus_sound h1 h2] by simp
next
  case (Times e1 e2)
  from Times.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Times.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  show ?case
    using sign_cast_signed_combine[OF sign_times_sound h1 h2] by simp
next
  case (Less e1 e2)
  from Less.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Less.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have shape: "aval_sign_t (elaborate default_tyenv I32 (Less e1 e2)) \<sigma> =
      (if sign_lt ?c1 ?c2 = Some True then SPos
       else if sign_lt ?c1 ?c2 = Some False then SZero
       else SNonNeg)"
    using nb1 nb2 by (simp add: kjoin_default_tyenv_I32 Let_def)
  show ?case
  proof (cases "sign_lt ?c1 ?c2")
    case (Some b)
    then show ?thesis
      using sign_lt_sound[OF Some h1 h2] by (cases b) (simp_all add: shape)
  next
    case None
    then show ?thesis by (auto simp: shape)
  qed
next
  case (Eq e1 e2)
  from Eq.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Eq.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have shape: "aval_sign_t (elaborate default_tyenv I32 (exp.Eq e1 e2)) \<sigma> =
      (if sign_eqb ?c1 ?c2 = Some True then SPos
       else if sign_eqb ?c1 ?c2 = Some False then SZero
       else SNonNeg)"
    using nb1 nb2 by (simp add: kjoin_default_tyenv_I32 Let_def)
  show ?case
  proof (cases "sign_eqb ?c1 ?c2")
    case (Some b)
    then show ?thesis
      using sign_eqb_sound[OF Some h1 h2] by (cases b) (simp_all add: shape)
  next
    case None
    then show ?thesis by (auto simp: shape)
  qed
next
  case (Not e)
  from Not.IH[OF H] have h: "aval e s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e) \<sigma>)"
    by auto
  let ?c = "aval_sign_t (elaborate default_tyenv I32 e) \<sigma>"
  have nb: "\<not> is_bot ?c" using h by (auto simp: is_bot_sign is_bottom_sign_correct)
  have shape: "aval_sign_t (elaborate default_tyenv I32 (exp.Not e)) \<sigma> =
      (if sign_tobool ?c = Some True then SZero
       else if sign_tobool ?c = Some False then SPos
       else SNonNeg)"
    using nb by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "sign_tobool ?c")
    case (Some b)
    then show ?thesis
      using sign_tobool_sound[OF Some h] by (cases b) (simp_all add: shape truthy_def)
  next
    case None
    then show ?thesis by (auto simp: shape)
  qed
next
  case (And e1 e2)
  from And.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from And.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have shape: "aval_sign_t (elaborate default_tyenv I32 (And e1 e2)) \<sigma> =
      (if sign_tobool ?c1 = Some False \<or> sign_tobool ?c2 = Some False then SZero
       else if sign_tobool ?c1 = Some True \<and> sign_tobool ?c2 = Some True then SPos
       else SNonNeg)"
    using nb1 nb2 by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "sign_tobool ?c1 = Some False \<or> sign_tobool ?c2 = Some False")
    case True
    then have "\<not> truthy (aval e1 s) \<or> \<not> truthy (aval e2 s)"
      using sign_tobool_sound h1 h2 by fastforce
    with True show ?thesis by (simp add: shape truthy_def)
  next
    case False
    note and_outer_false = False
    show ?thesis
    proof (cases "sign_tobool ?c1 = Some True \<and> sign_tobool ?c2 = Some True")
      case True
      then have "truthy (aval e1 s) \<and> truthy (aval e2 s)"
        using sign_tobool_sound h1 h2 by auto
      with True and_outer_false show ?thesis by (simp add: shape truthy_def)
    next
      case False
      show ?thesis by (simp add: shape)
    qed
  qed
next
  case (Or e1 e2)
  from Or.IH[OF H] have h1: "aval e1 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>)"
    by auto
  from Or.IH[OF H] have h2: "aval e2 s \<in> gamma_sign (aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>)"
    by auto
  let ?c1 = "aval_sign_t (elaborate default_tyenv I32 e1) \<sigma>"
  let ?c2 = "aval_sign_t (elaborate default_tyenv I32 e2) \<sigma>"
  have nb1: "\<not> is_bot ?c1" using h1 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have nb2: "\<not> is_bot ?c2" using h2 by (auto simp: is_bot_sign is_bottom_sign_correct)
  have shape: "aval_sign_t (elaborate default_tyenv I32 (Or e1 e2)) \<sigma> =
      (if sign_tobool ?c1 = Some True \<or> sign_tobool ?c2 = Some True then SPos
       else if sign_tobool ?c1 = Some False \<and> sign_tobool ?c2 = Some False then SZero
       else SNonNeg)"
    using nb1 nb2 by (simp add: esyn_default_tyenv_I32)
  show ?case
  proof (cases "sign_tobool ?c1 = Some True \<or> sign_tobool ?c2 = Some True")
    case True
    then have "truthy (aval e1 s) \<or> truthy (aval e2 s)"
      using sign_tobool_sound h1 h2 by fastforce
    with True show ?thesis by (simp add: shape truthy_def)
  next
    case False
    note or_outer_false = False
    show ?thesis
    proof (cases "sign_tobool ?c1 = Some False \<and> sign_tobool ?c2 = Some False")
      case True
      then have "\<not> truthy (aval e1 s) \<and> \<not> truthy (aval e2 s)"
        using sign_tobool_sound h1 h2 by auto
      with True or_outer_false show ?thesis by (simp add: shape truthy_def)
    next
      case False
      show ?thesis by (simp add: shape)
    qed
  qed
qed

global_interpretation sign_check_domain:
  abstract_check_domain gamma_sign sign_less_true sign_less_false sign_eq_true sign_eq_false
    gamma_state "aval_sign default_tyenv I32"
  defines
    sign_check_true = sign_check_domain.check_true
    and sign_check_false = sign_check_domain.check_false
    and sign_classify_check = sign_check_domain.classify_check
    and sign_checks_proven = sign_check_domain.abstract_checks_proven
proof unfold_locales
  fix s :: store and e :: exp and \<sigma> :: "sign abs_state"
  assume "s \<in> \<lbrakk>\<sigma>\<rbrakk>"
  then have "\<forall>x. s x \<in> gamma (\<sigma> x)" by (rule gamma_stateD)
  then have H: "\<forall>x. s x \<in> gamma_sign (\<sigma> x)" by simp
  then show "aval e s \<in> gamma_sign (aval_sign default_tyenv I32 e \<sigma>)"
    using aval_sign_t_default_agree[OF H] by (simp add: aval_sign_def)
qed

text \<open>
  Only the consumer-facing aliases get a short Sign-prefixed name:
  \<open>classify_check\<close>'s two directions and the \<open>checks_proven\<close> bridge, both
  exercised below and by \<open>Example_Checks_Store_Only\<close>.
  \<open>sign_check_domain.check_true_sound\<close>/\<open>check_false_sound\<close>/
  \<open>check_true_false_vacuous\<close> are the lower-level facts \<open>classify_check\<close>'s
  own soundness is built from; no caller needs them directly, so they stay
  reachable under the qualified \<open>sign_check_domain.\<close> name instead of a
  dedicated alias here.
\<close>

lemmas sign_classify_check_proved = sign_check_domain.classify_check_proved
lemmas sign_classify_check_refuted = sign_check_domain.classify_check_refuted
lemmas sign_checks_provenI = sign_check_domain.abstract_checks_provenI
lemmas sign_checks_proven_sound = sign_check_domain.abstract_checks_proven_sound

subsection \<open>The generic report adapter, at the routed-unit context\<close>

text \<open>
  Interpreting \<^locale>\<open>dg_analysis_adapter\<close> at \<open>Sign_Ctx_None_Sound\<close>'s own routed-unit
  solved system reuses every obligation that theory's own \<open>sctx_dg\<close>/\<open>sctx_routed\<close>
  interpretations already discharge: the five \<^locale>\<open>dg_ctx_activation_base\<close> obligations
  are exactly \<open>sctx_dg\<close>'s own (cited here via the exported \<open>sctx_pp_abs\<close>/\<open>sctx_sg_covered\<close>/
  \<open>sctx_sg_uncovered_empty\<close>/\<open>sctx_fin\<close>), and the routed obligations collapse the same way
  \<^locale>\<open>unit_routed_context\<close>'s did, at \<^const>\<open>route_unit\<close>/\<^const>\<open>enterc_unit\<close>. Only
  \<open>classify_proved\<close>/\<open>classify_refuted\<close> are genuinely new here, discharged by
  \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close> above. This context re-opens
  \<open>Sign_Ctx_None_Sound\<close>'s own six coverage hypotheses (\<open>solves\<close>/\<open>exact\<close>/\<open>entry_cov\<close>/
  \<open>fwd_ok\<close>/\<open>call_fwd_ok\<close>/\<open>comb_fwd_ok\<close>) rather than reusing that theory's context directly,
  since the classify obligations need \<open>sign_classify_check_proved\<close>/\<open>sign_classify_check_refuted\<close>,
  which live in this theory, downstream of \<open>Sign_Ctx_None_Sound\<close>.
\<close>

context
  fixes gs :: "vname \<Rightarrow> bool" and \<Gamma> :: tyenv and is_bot_pred :: "sign exec_dg_st \<Rightarrow> bool"
    and Pi :: proc_table and ps :: "pname list" and mnm :: pname and main :: com
  assumes solves: "sctx_terminates gs \<Gamma> is_bot_pred Pi ps mnm main"
    and exact: "\<And>s. is_bot_pred s = is_bot_state (fun_of_resolved_st_q_for gs s)"
    and entry_cov: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
                   \<Longrightarrow> (u, a, v) \<in> intra (compile_prog Pi ps mnm main)
                   \<Longrightarrow> (v, ctx) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and call_fwd_ok: "\<And>u ctx dst pars args p cont.
        (u, ctx) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (FunctionEntry p, ()) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    and comb_fwd_ok: "\<And>cl c1 dst pars args p cont.
        (cl, c1) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps mnm main)
        \<Longrightarrow> (cont, c1) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
begin

text \<open>
  @{thm [source] base_dg_spec_sound}'s third premise, \<open>ret_ok: (\<And>x v. ik_norm (\<Gamma> x) v = v)\<close>,
  is unresolved below -- the same pre-existing well-typedness gap flagged in
  \<open>Sign_Ctx_None_Sound.sctx_dg_base\<close>.
\<close>
interpretation sctx_dg_base: sound_dg_spec "sctx_abs_spec gs \<Gamma>" gamma_dg_base gs \<Gamma>
  unfolding sctx_abs_spec_def
  apply (rule base_dg_spec_sound[OF sign_is_sound_transfer_for is_bot_state_gamma_state_empty])
  sorry

interpretation sctx_adapter: dg_analysis_adapter enterc_unit "sctx_abs_spec gs \<Gamma>" gs \<Gamma>
    "compile_prog Pi ps mnm main" Global route_unit
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "map_lift (fun_of_resolved_st_q_for gs) (Lifted cinit_sign_st)"
    "map_lift (fun_of_resolved_st_q_for gs) (Bot::sign exec_dg_st lifted)"
    "sctx_sigma_abs gs \<Gamma> is_bot_pred Pi ps mnm main" "fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)"
    "(cfg_exit (compile_prog Pi ps mnm main), ())" "sctx_sg gs \<Gamma> is_bot_pred Pi ps mnm main"
    Seed sign_classify_check
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC SeedKey ResolveSound
    RouteEnterc CallFwd CombFwd EnterAgree ClProved ClRefuted)
  case FinE show ?case
    using compile_prog_finite by auto
next
  case PP show ?case
    by (simp only: sctx_sigma_abs_def[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok]
        sctx_sigma_abs_exec_def)
      (rule sctx_pp_abs[OF solves exact])
next
  case (SgCov v c)
  note mem = this
  have eq1: "sctx_sg gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (v, c))
               = locals (sctx_sigma_abs gs \<Gamma> is_bot_pred Pi ps mnm main (Inl (v, c)))"
    by (rule sctx_sg_covered[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok mem])
  show ?case
    using eq1 gamma_dg_base_def by auto
next
  case (SgUncov v c)
  note nmem = this
  show ?case
    by (rule sctx_sg_uncovered_empty[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok nmem])
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
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls (compile_prog Pi ps mnm main)"
    and es_eq: "es = call_enter \<Gamma> gs (CallEdge dst' pars' args') s"
    using ces unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' ce] by simp
  thus ?case using es_eq by simp
next
  case (ClProved c d s)
  thus ?case by (rule sign_classify_check_proved)
next
  case (ClRefuted c d s)
  thus ?case by (rule sign_classify_check_refuted)
qed

text \<open>
  The two generic soundness corollaries \<^locale>\<open>dg_analysis_adapter\<close> derives once and for
  all, re-exported here so a caller cites them without naming the interpretation.
\<close>

lemmas sctx_report_ctx_proved_sound = sctx_adapter.analyse_report_ctx_proved_sound
lemmas sctx_report_ctx_refuted_sound = sctx_adapter.analyse_report_ctx_refuted_sound

text \<open>
  \<open>sctx_result_node_sound\<close> re-exports the adapter's generic node-soundness bridge
  (\<^theory>\<open>Voblint_Core.DG_Analysis_Adapter\<close>), phrased against \<open>sctx_adapter.analyse_result\<close>.
  \<open>sctx_analyse_result_eq\<close> identifies that reading with the raw-tuple shape
  \<^const>\<open>analyse_sign_ctx_result_for\<close> (\<open>Sign_Ctx_None_Sound\<close>) already builds by hand from
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>canonicalize_lift\<close> directly: both collapse the same
  \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> case split on the same projected local unknown, one via
  \<open>is_bot_state\<close> after projecting (the adapter), the other via \<open>is_bot_pred\<close> before
  projecting (\<open>analyse_sign_ctx_result_for\<close>) --- \<open>exact\<close> is exactly what identifies the
  two orders. A caller composing \<open>sctx_result_node_sound\<close> with \<open>sctx_analyse_result_eq\<close>
  gets \<^const>\<open>analyse_sign_ctx_result_for\<close>'s own node-soundness bridge without
  re-deriving \<open>routed_context_hetero\<close>'s coverage/sigma-projection argument by hand.
\<close>

lemmas sctx_result_node_sound = sctx_adapter.analyse_result_node_sound

lemma sctx_analyse_result_eq:
  "lookup_context sctx_adapter.analyse_result v ctx =
     (if (v, ctx) \<in> fst (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main)
      then normalize_point gs
             (canonicalize_lift is_bot_pred (locals (snd (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main) (Inl (v, ctx)))))
      else Unreachable)"
  unfolding sctx_adapter.lookup_context_analyse_result
  apply (simp only: sctx_sigma_abs_def[OF solves exact entry_cov fwd_ok call_fwd_ok comb_fwd_ok]
                     sctx_sigma_abs_exec_def o_apply fun_of_dg_st_gen_simps(1))
  by (cases "locals (snd (sctx_sol gs \<Gamma> is_bot_pred Pi ps mnm main) (Inl (v, ctx)))")
     (simp_all add: exact normalize_lift_def)

end

subsection \<open>Executable classification tests\<close>

text \<open>One state per test, built as an override of an otherwise-unconstrained
  (\<open>STop\<close>) environment, so each test exercises exactly the comparison it names.

  Every check below that reads a plain \<open>SPos\<close>/\<open>SNonNeg\<close> variable now resolves to
  \<open>Check_Unknown\<close> rather than the \<open>Check_Proved\<close>/\<open>Check_Refuted\<close> it demonstrated before
  \<open>aval_sign\<close> gained ikind-aware casting: sign carries no magnitude, so an unbounded
  \<open>SPos\<close>/\<open>SNonNeg\<close> value genuinely cannot be shown to fit inside \<open>I32\<close>'s range at cast
  time -- @{const sign_cast} widens to \<open>STop\<close> for any signed target other than an exact
  \<open>SZero\<close>, and \<open>default_tyenv\<close>/\<open>I32\<close> is the only concrete instantiation this interpretation
  can supply -- the same gap flagged at the \<open>sign_check_domain\<close> soundness obligation
  above, now visible in these executable witnesses too.\<close>

definition test_env_pos :: "sign abs_state" where
  "test_env_pos = (\<lambda>_. STop)((STR ''x'') := SPos)"

lemma sign_classify_less_proved:
  "sign_classify_check (Less (N 0) (V (STR ''x''))) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

lemma sign_classify_less_refuted:
  "sign_classify_check (Less (V (STR ''x'')) (N 0)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

lemma sign_classify_eq_unknown:
  "sign_classify_check (Eq (V (STR ''x'')) (N 1)) test_env_pos = Check_Unknown"
  unfolding test_env_pos_def by eval

text \<open>Negation: \<open>!(x < 0)\<close> is provable under \<open>SNonNeg\<close>, going through
  \<open>check_false\<close> on the un-negated \<open>x < 0\<close> rather than a one-sided
  negation of \<open>check_true\<close>.\<close>

definition test_env_nonneg :: "sign abs_state" where
  "test_env_nonneg = (\<lambda>_. STop)((STR ''x'') := SNonNeg)"

lemma sign_classify_not_proved:
  "sign_classify_check (Not (Less (V (STR ''x'')) (N 0))) test_env_nonneg = Check_Unknown"
  unfolding test_env_nonneg_def by eval

text \<open>Nested \<open>And\<close>/\<open>Or\<close>: proved through the \<open>And\<close> branch alone, and unknown
  when neither branch resolves.\<close>

definition test_env_nested_proved :: "sign abs_state" where
  "test_env_nested_proved = (\<lambda>_. STop)((STR ''x'') := SPos, (STR ''y'') := SPos)"

lemma sign_classify_nested_proved:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_proved = Check_Unknown"
  unfolding test_env_nested_proved_def by eval

definition test_env_nested_unknown :: "sign abs_state" where
  "test_env_nested_unknown = (\<lambda>_. STop)((STR ''x'') := SNonNeg, (STR ''y'') := SPos)"

lemma sign_classify_nested_unknown:
  "sign_classify_check
     (Or (And (Less (N 0) (V (STR ''x''))) (Less (N 0) (V (STR ''y'')))) (Eq (V (STR ''z'')) (N 1)))
     test_env_nested_unknown = Check_Unknown"
  unfolding test_env_nested_unknown_def by eval

subsection \<open>Solved-result table\<close>
subsection \<open>Solved-result table\<close>

text \<open>
  \<open>analyse_sign_result_for\<close> is the canonical solved D/G system, read as a
  \<^typ>\<open>(unit, sign abs_state) analysis_result\<close>: a one-line partial
  application of \<^const>\<open>analyse_sign_ctx_result_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>), fixed at \<^const>\<open>prog_main_name\<close>,
  which already binds the single routed-unit solve and
  canonicalizes/normalizes each local key. Every report below reads
  through this table via \<^const>\<open>lookup_context\<close> rather than a raw
  solver-environment lookup.
\<close>

definition analyse_sign_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_for gs \<Gamma> p = analyse_sign_ctx_result_for gs \<Gamma> prog_main_name p"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_result :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result p = analyse_sign_result_for (declared_global p) (prog_tyenv p) p"

subsection \<open>Solved-result table: per-origin update rule\<close>

text \<open>
  \<open>analyse_sign_result_per_origin_for\<close> is \<^const>\<open>analyse_sign_result_for\<close>'s
  sibling under the per-origin rule: a one-line partial application of
  \<^const>\<open>analyse_sign_ctx_result_per_origin_for\<close>
  (\<^theory>\<open>Voblint_Analysis.Sign_Ctx_None_Sound\<close>), fixed at \<^const>\<open>prog_main_name\<close>,
  reading \<^const>\<open>sctx_sol_prog_per_origin\<close> instead of \<^const>\<open>sctx_sol_prog\<close>.
  Experimental: no dedicated soundness theorem is proved for this
  combination here -- \<open>analyse\<close> and its soundness corollaries are
  unaffected, and this definition exists solely so \<open>Analyse_Dispatch\<close>'s
  \<open>analyse_with_solver\<close> can compare solver choices on the routed-unit
  equation system (issue #131).
\<close>

definition analyse_sign_result_per_origin_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin_for gs \<Gamma> p =
     analyse_sign_ctx_result_per_origin_for gs \<Gamma> prog_main_name p"

definition analyse_sign_result_per_origin :: "imp_prog \<Rightarrow> (unit, sign abs_state) analysis_result" where
  "analyse_sign_result_per_origin p =
     analyse_sign_result_per_origin_for (declared_global p) (prog_tyenv p) p"

subsection \<open>Whole-program check report: the native D/G runtime API\<close>

text \<open>
  \<open>analyse_sign_report_for\<close> is the report function the exported \<open>analyse\<close>
  API actually dispatches to (see \<open>Analyse_Dispatch\<close>, downstream in
  Examples), fixed at \<open>prog_main_name\<close> since \<^const>\<open>analyse_sign_result_for\<close>
  already is. It reads its per-node state through
  \<^const>\<open>analyse_sign_result_for\<close>'s \<^type>\<open>analysis_result\<close> table --
  \<^const>\<open>lookup_context\<close>, not a raw solver-environment lookup -- so a
  \<^const>\<open>Reachable\<close> point classifies at its projected state exactly as
  before, and an \<^const>\<open>Unreachable\<close> one (dead or never covered; the two are
  no longer distinguishable, matching \<^const>\<open>classify_checks\<close>'s original
  \<^const>\<open>Bot\<close>-collapsing \<open>env\<close> reads) classifies at \<^const>\<open>bot\<close>, the same
  value \<^const>\<open>classify_checks\<close> always fed it for such a node: this
  preserves \<open>check_result\<close>'s existing three-way verdict exactly, rather
  than introducing a fourth, \<open>Dead\<close> outcome the type does not carry (that
  distinction belongs to \<^const>\<open>classify_checks_verdicts\<close>/\<open>contextual_verdict\<close>,
  the shape the entry-state check report already uses).

  \<open>r\<close> is bound once, outside \<^const>\<open>classify_checks\<close>'s per-check closure, so
  the single D/G solve \<^const>\<open>analyse_sign_result_for\<close> performs is shared
  across every check in the report rather than repeated per check.
\<close>

definition analyse_sign_report_for :: "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_for gs \<Gamma> p =
     analysis_surface.report (analyse_sign_result_for gs \<Gamma>) bot sign_classify_check p"

text \<open>
  Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, the classifier every
  caller with only an \<^typ>\<open>imp_prog\<close> in hand recomputes anyway.
\<close>

definition analyse_sign_report :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report p = analyse_sign_report_for (declared_global p) (prog_tyenv p) p"

subsection \<open>Solver-choice variant report: per-origin update rule\<close>

text \<open>
  \<open>analyse_sign_report_per_origin\<close>'s sibling relationship to
  \<^const>\<open>analyse_sign_report\<close> mirrors \<^const>\<open>analyse_sign_result_per_origin\<close>'s
  to \<^const>\<open>analyse_sign_result\<close>: same report shape, reading through the
  per-origin result table instead of the default one.
\<close>

definition analyse_sign_report_per_origin :: "imp_prog \<Rightarrow> check_report_entry list" where
  "analyse_sign_report_per_origin p =
     analysis_surface.report analyse_sign_result_per_origin bot sign_classify_check p"

subsection \<open>The published surface, one interpretation per discipline\<close>

text \<open>
  Sign's two disciplines through the shared \<^locale>\<open>analysis_surface\<close>. There is no
  warrowing interpretation because there is no warrowing table to name: Sign's carrier has
  finite height and carries no widen instance, so warrowing has nothing to accelerate and
  no solved table of its own. The absent interpretation and the absent solver route agree
  by construction rather than by a separately maintained legality table.
\<close>

interpretation sign_join: analysis_surface
  analyse_sign_result bot sign_classify_check
  by unfold_locales

interpretation sign_per_origin: analysis_surface
  analyse_sign_result_per_origin bot sign_classify_check
  by unfold_locales

lemma sign_report_join_eq: "analyse_sign_report p = sign_join.report p"
  by (simp add: analyse_sign_report_def analyse_sign_report_for_def
      analyse_sign_result_def surface_unfold)

lemma sign_report_per_origin_eq:
  "analyse_sign_report_per_origin p = sign_per_origin.report p"
  by (simp add: analyse_sign_report_per_origin_def surface_unfold)

subsection \<open>Whole-program check report with state\<close>

text \<open>
  State-carrying sibling of \<open>analyse_sign_report_for\<close>/\<open>analyse_sign_report\<close>,
  via \<^const>\<open>classify_checks_with_state\<close>: same result table, with the
  per-check Sign environment attached to each report entry instead of
  discarded, and an exact \<open>unreachable\<close> flag read straight off
  \<^const>\<open>lookup_context\<close>'s \<^const>\<open>Unreachable\<close>/\<^const>\<open>Reachable\<close> case split --
  exact because \<open>normalize_point_canonicalize_lift_eq_old\<close>
  (\<^theory>\<open>Voblint_Core.Analysis_Result\<close>) is precisely the fact that this
  reading agrees with the older \<^const>\<open>resolved_st_q_lifted_is_bot_for\<close>
  test on the same raw local unknown.
\<close>

definition analyse_sign_report_for_with_state ::
    "(vname \<Rightarrow> bool) \<Rightarrow> tyenv \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_for_with_state gs \<Gamma> p =
     (let r = analyse_sign_result_for gs \<Gamma> p
      in classify_checks_with_state (prog_cfg prog_main_name p)
           (\<lambda>v. case lookup_context r v () of
                  Unreachable \<Rightarrow> (True, bot)
                | Reachable st \<Rightarrow> (False, st))
           (\<lambda>c (_, s). sign_classify_check c s))"

text \<open>Convenience instance at \<^const>\<open>declared_global\<close> \<open>p\<close>, matching
  \<open>analyse_sign_report\<close>'s shape.\<close>

definition analyse_sign_report_with_state ::
    "imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> (vname \<Rightarrow> sign)) list" where
  "analyse_sign_report_with_state p =
     analyse_sign_report_for_with_state (declared_global p) (prog_tyenv p) p"

end

