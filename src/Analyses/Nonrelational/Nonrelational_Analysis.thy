theory Nonrelational_Analysis
  imports
    Nonrelational_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Solver.Globals_Rule"
    "Voblint_Framework.Call_String_Context"
begin

unbundle default_st_syntax

section \<open>The typed non-relational analysis\<close>

text \<open>
  The executable typed component at any kind-aware integer domain, run by the shared
  D/G pipeline over the typed CFG. The kind declarations \<open>ds\<close> are a parameter of the
  instance: they fix the kind environment the concretization, the transfer and the
  initial state read, and the program varies under them. The domain is a type
  parameter, so every constant of the instance takes the domain's \<open>TYPE\<close> first.
\<close>

subsection \<open>Verdicts\<close>

definition nonrel_classify :: "sem_conf \<Rightarrow> kenv \<Rightarrow> exp \<Rightarrow> 'a::kind_int_domain tabs \<Rightarrow> check_result"
  where
  "nonrel_classify sem \<kappa> c d =
     (case truth_ik (aeval sem \<kappa> (\<lambda>_. \<top>) c d) of
        Some True \<Rightarrow> Check_Proved
      | Some False \<Rightarrow> Check_Refuted
      | None \<Rightarrow> Check_Unknown)"

lemma nonrel_classify_sound:
  assumes s: "s \<in> gamma_tabs \<kappa> d"
  shows nonrel_classify_proved: "nonrel_classify sem \<kappa> c d = Check_Proved \<Longrightarrow> truthy (eval c s)"
    and nonrel_classify_refuted: "nonrel_classify sem \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
proof -
  have truth: "truthy (eval c s) = b"
    if "truth_ik (aeval sem \<kappa> (\<lambda>_. \<top>) c d) = Some b" for b
    using s by (rule truth_ik_sound[OF that aeval_sound]) simp
  show "nonrel_classify sem \<kappa> c d = Check_Proved \<Longrightarrow> truthy (eval c s)"
    using truth by (auto simp: nonrel_classify_def split: option.splits bool.splits)
  show "nonrel_classify sem \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (eval c s)"
    using truth by (auto simp: nonrel_classify_def split: option.splits bool.splits)
qed

subsection \<open>The initial state\<close>

text \<open>Every global starts at zero at its declared kind; every local is unconstrained.\<close>

definition nonrel_init_st :: "kind_decls \<Rightarrow> 'a::kind_int_domain tst" where
  "nonrel_init_st ds =
     \<llangle>(KTop, []), (KD I32 (of_int_ik I32 0), map (\<lambda>(v, k). (v, KD k (of_int_ik k 0))) ds)\<rrangle>"

lemma nonrel_rd_init_st:
  "nonrel_rd (nonrel_init_st ds :: 'a::kind_int_domain tst)
     = (\<lambda>v. if is_global v then KD (kenv_of ds v) (of_int_ik (kenv_of ds v) 0) else KTop)"
  by (auto simp: nonrel_init_st_def default_st_to_fun_def location_of_def kenv_of_def map_of_map
      fun_eq_iff split: option.splits)

lemma nonrel_init_sound:
  "init_stores (kenv_of ds)
     \<subseteq> gamma_tabs (kenv_of ds) (nonrel_rd (nonrel_init_st ds :: 'a::kind_int_domain tst))"
proof
  fix t assume t: "t \<in> init_stores (kenv_of ds)"
  have rng: "t v \<in> ik_range (kenv_of ds v)" for v
    using t by (simp add: init_stores_def all_in_kindsD del: ik_range_iff)
  show "t \<in> gamma_tabs (kenv_of ds) (nonrel_rd (nonrel_init_st ds))"
    unfolding nonrel_rd_init_st
  proof (rule gamma_tabsI[OF init_stores_in_kinds[OF t]], goal_cases)
    case (1 v)
    show ?case
    proof (cases v)
      case (GlobalId x)
      then have "t v = 0" using t by (simp add: init_stores_def)
      then show ?thesis
        using of_int_ik_sound[of "kenv_of ds v" "t v"] rng[of v] GlobalId
        by (simp del: ik_range_iff)
    qed simp_all
  qed
qed

subsection \<open>The pipeline instance\<close>

text \<open>
  Call-string contexts of bound \<open>k\<close>, after Goblint's \<^verbatim>\<open>callstring.ml\<close>: a call pushes its
  call site and keeps the \<open>k\<close> most recent. At \<open>k = 0\<close> every activation shares the empty
  string, the context-insensitive analysis. The joined global unknown and the certified
  solver run at any update rule \<open>r\<close>. The component reads no global, so every variable
  lives in a point's own state.
\<close>

lemma elab_cfg_calls_source_unique: "calls_source_unique (elab_cfg p ds)"
  unfolding calls_source_unique_def elab_cfg_def using compile_prog_calls_source_unique by blast

lemma nonrel_exec_spec_sound_rd:
  "mcp_sem.gsound_local_spec eval ReturnVar (kind_conv \<kappa>) is_global
     (\<lambda>d. gamma_lift (gamma_tabs \<kappa>) (map_lift nonrel_rd d))
     (nonrel_exec_spec sem \<kappa> :: (var_id, exp, 'a::kind_int_domain tst lifted) glocal_spec)"
  using nonrel_exec_spec_sound[of \<kappa> sem, where 'a = 'a] by (simp add: gamma_exec_def[abs_def])

text \<open>What the component owes the pipeline does not depend on the context policy, so it
  is proved once, for any route and root context.\<close>

lemma nonrel_routed:
  "gdg_analysis
    eval ReturnVar (\<lambda>_. kind_conv (kenv_of ds)) (\<lambda>_. is_global) (\<lambda>_. init_stores (kenv_of ds))
    (\<lambda>_ _. nonrel_exec_spec sem (kenv_of ds) :: (var_id, exp, 'a::kind_int_domain tst lifted) glocal_spec)
    (\<lambda>_. st_is_bot) (\<lambda>\<G>. \<rho>\<^bsub>\<G>\<^esub>) (nonrel_init_st ds)
    (Analysis_Global ()) Analysis_Global Activation_Seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE((unit, 'c) global_unknown)
       TYPE(('a tst lifted, 'a tst lifted) dg_state) r)
    \<bottom> (nonrel_classify sem (kenv_of ds)) (gamma_tabs (kenv_of ds)) t_empty
    (TD_side_rule_Interp_solve_c r)
    (\<lambda>_ c. dg_spec_of c) (\<lambda>p d e. d) (\<lambda>_ d. d) (\<lambda>_ d. Bot) (\<lambda>_ p. []) (\<lambda>p ci d e. d)
    (\<lambda>p. elab_cfg p ds) (\<lambda>_. FunctionEntry prog_main_name)"
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p) show ?case by (rule nonrel_exec_spec_sound_rd)
next
  case (EnterSingle p ci d) show ?case
    by (simp add: nonrel_exec_spec_def dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (simp add: st_is_bot_iff t_empty_def)
next
  case EmptyV show ?case by (rule sound_emptinessI) (rule t_empty_sound)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro nonrel_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro nonrel_classify_refuted)
next
  case BotState show ?case by simp
next
  case (InitSound p) show ?case by (rule nonrel_init_sound)
next
  case (SeedNeGlobal v ctx n) show ?case by simp
next
  case (PEntry p) show ?case by (simp add: elab_cfg_def)
next
  case (FinIntra p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (FinCalls p) show ?case by (simp add: elab_cfg_def compile_prog_finite)
next
  case (CallsUnique p) show ?case by (rule elab_cfg_calls_source_unique)
qed

global_interpretation nonrel: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "\<lambda>_ _. nonrel_exec_spec sem (kenv_of ds) :: (var_id, exp, 'a::kind_int_domain tst lifted) glocal_spec"
    "\<lambda>_. st_is_bot" "\<lambda>\<G>. \<rho>\<^bsub>\<G>\<^esub>" "nonrel_init_st ds"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, cfg_node list) global_unknown)
       TYPE(('a tst lifted, 'a tst lifted) dg_state) r"
    \<bottom> "nonrel_classify sem (kenv_of ds)" "gamma_tabs (kenv_of ds)" t_empty
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds r k
  by (rule nonrel_routed)

subsection \<open>Entry-state contexts\<close>

text \<open>
  A call's context is the abstract values of the callee's formals in the state the call
  enters. Goblint's default context is the whole entry state
  (\<^verbatim>\<open>DefaultSpec.context\<close>); the formals are the part of it a call determines, since
  the callee's other locals start unconstrained.
\<close>

definition nonrel_es_ctx ::
    "(var_id \<Rightarrow> bool) \<Rightarrow> 'a::kind_int_domain tst lifted \<Rightarrow> (var_id, exp) gcall_action
       \<Rightarrow> 'a kd list" where
  "nonrel_es_ctx \<G> d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (case d of Lifted st \<Rightarrow> map (\<rho>\<^bsub>\<G>\<^esub> st) pars
         | Bot \<Rightarrow> map (\<lambda>_. \<bottom>) pars))"

global_interpretation nonrel_es: gdg_analysis
    eval ReturnVar "\<lambda>_. kind_conv (kenv_of ds)" "\<lambda>_. is_global" "\<lambda>_. init_stores (kenv_of ds)"
    "\<lambda>_ _. nonrel_exec_spec sem (kenv_of ds) :: (var_id, exp, 'a::kind_int_domain tst lifted) glocal_spec"
    "\<lambda>_. st_is_bot" "\<lambda>\<G>. \<rho>\<^bsub>\<G>\<^esub>" "nonrel_init_st ds"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>\<G> u ctx d ca. nonrel_es_ctx \<G> d ca" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, 'a kd list) global_unknown)
       TYPE(('a tst lifted, 'a tst lifted) dg_state) r"
    \<bottom> "nonrel_classify sem (kenv_of ds)" "gamma_tabs (kenv_of ds)" t_empty
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. elab_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for sem ds r
  by (rule nonrel_routed)

unbundle no default_st_syntax

end
