theory Typed_Nonrel_Analysis
  imports
    Typed_Exec
    "Voblint_Result.DG_Live_Unknowns"
    "Voblint_Solver.Globals_Rule"
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

definition tclassify :: "kenv \<Rightarrow> texp \<Rightarrow> 'a::kind_int_domain tabs toplift \<Rightarrow> check_result" where
  "tclassify \<kappa> c d =
     (case d of TTop \<Rightarrow> Check_Unknown
      | TL \<sigma> \<Rightarrow> (case truth_ik (taeval \<kappa> c \<sigma>) of
                  Some True \<Rightarrow> Check_Proved
                | Some False \<Rightarrow> Check_Refuted
                | None \<Rightarrow> Check_Unknown))"

lemma tclassify_sound:
  assumes s: "s \<in> gamma_tt \<kappa> d"
  shows tclassify_proved: "tclassify \<kappa> c d = Check_Proved \<Longrightarrow> truthy (teval c s)"
    and tclassify_refuted: "tclassify \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
proof -
  have truth: "truthy (teval c s) = b"
    if "d = TL \<sigma>" "truth_ik (taeval \<kappa> c \<sigma>) = Some b" for \<sigma> b
  proof -
    from s that(1) have "s \<in> gamma_tabs \<kappa> \<sigma>" by simp
    then show ?thesis by (rule truth_ik_sound[OF that(2) taeval_sound])
  qed
  show "tclassify \<kappa> c d = Check_Proved \<Longrightarrow> truthy (teval c s)"
    using truth by (auto simp: tclassify_def split: toplift.splits option.splits bool.splits)
  show "tclassify \<kappa> c d = Check_Refuted \<Longrightarrow> \<not> truthy (teval c s)"
    using truth by (auto simp: tclassify_def split: toplift.splits option.splits bool.splits)
qed

subsection \<open>The initial state\<close>

text \<open>Every global starts at zero at its declared kind; every local is unconstrained.\<close>

definition tinit_st :: "kind_decls \<Rightarrow> 'a::kind_int_domain tst toplift" where
  "tinit_st ds =
     TL \<llangle>(KTop, []), (KD I32 (of_int_ik I32 0), map (\<lambda>(v, k). (v, KD k (of_int_ik k 0))) ds)\<rrangle>"

lemma map_trd_tinit_st:
  "map_toplift trd (tinit_st ds :: 'a::kind_int_domain tst toplift)
     = TL (\<lambda>v. if tglobal v then KD (kenv_of ds v) (of_int_ik (kenv_of ds v) 0) else KTop)"
  by (auto simp: tinit_st_def default_st_to_fun_def location_of_def kenv_of_def map_of_map
      fun_eq_iff split: option.splits)

lemma tinit_sound:
  "tinit_stores (kenv_of ds)
     \<subseteq> gamma_tt (kenv_of ds) (map_toplift trd (tinit_st ds :: 'a::kind_int_domain tst toplift))"
proof
  fix t assume t: "t \<in> tinit_stores (kenv_of ds)"
  have rng: "t v \<in> ik_range (kenv_of ds v)" for v
    using t by (simp add: tinit_stores_def stypedD del: ik_range_iff)
  show "t \<in> gamma_tt (kenv_of ds) (map_toplift trd (tinit_st ds))"
    unfolding map_trd_tinit_st gamma_tt.simps
  proof (rule gamma_tabsI[OF tinit_stores_tstyped[OF t]], goal_cases)
    case (1 v)
    show ?case
    proof (cases v)
      case (GlobalId x)
      then have "t v = 0" using t by (simp add: tinit_stores_def)
      then show ?thesis
        using of_int_ik_sound[of "kenv_of ds v" "t v"] rng[of v] GlobalId
        by (simp del: ik_range_iff)
    qed simp_all
  qed
qed

subsection \<open>The pipeline instance\<close>

text \<open>
  One context, the joined global unknown of the unit-context analyses, and the
  certified solver at any update rule \<open>r\<close>. The component reads no global, so every
  variable lives in a point's own state.
\<close>

lemma typed_cfg_calls_source_unique: "calls_source_unique (typed_cfg p ds)"
  unfolding calls_source_unique_def typed_cfg_def using compile_prog_calls_source_unique by blast

lemma typed_exec_spec_sound_rd:
  "mcp_sem.gsound_local_spec teval ReturnVar (tconv \<kappa>) tglobal
     (\<lambda>d. gamma_lift (gamma_tt \<kappa>) (map_lift (map_toplift trd) d))
     (typed_exec_spec \<kappa> :: (var_id, texp, 'a::kind_int_domain tst toplift lifted) glocal_spec)"
  using typed_exec_spec_sound[of \<kappa>, where 'a = 'a] by (simp add: gamma_exec_def[abs_def])

global_interpretation typed_nonrel: gdg_analysis
    teval ReturnVar "\<lambda>_. tconv (kenv_of ds)" "\<lambda>_. tglobal" "\<lambda>_. tinit_stores (kenv_of ds)"
    "\<lambda>_ _. typed_exec_spec (kenv_of ds) :: (var_id, texp, 'a::kind_int_domain tst toplift lifted) glocal_spec"
    "\<lambda>_. tst_empty" "\<lambda>\<G>. map_toplift (default_st_to_fun \<G>)" "tinit_st ds"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_ _ _ _ _. ()" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE(('a tst toplift lifted, 'a tst toplift lifted) dg_state) r"
    "TL \<bottom>" "tclassify (kenv_of ds)" "gamma_tt (kenv_of ds)" tt_empty
    "TD_side_rule_Interp_solve_c r"
    "\<lambda>_ c. dg_spec_of c" "\<lambda>p d e. d" "\<lambda>_ d. d" "\<lambda>_ d. Bot" "\<lambda>_ p. []" "\<lambda>p ci d e. d"
    "\<lambda>p. typed_cfg p ds" "\<lambda>_. FunctionEntry prog_main_name"
  for ds r
proof (rule gdg_analysis_whole_stateI[OF td_certified_solver], goal_cases CompSound EnterSingle
    EmptyRd EmptyV SeedNe ClProved ClRefuted BotState InitSound SeedNeGlobal PEntry FinIntra
    FinCalls CallsUnique)
  case (CompSound p) show ?case by (rule typed_exec_spec_sound_rd)
next
  case (EnterSingle p ci d) show ?case
    by (simp add: typed_exec_spec_def dg_pipeline.comp_entry_def)
next
  case (EmptyRd p s) show ?case by (rule tst_empty_iff)
next
  case EmptyV show ?case by (rule sound_emptinessI) (rule tt_empty_sound)
next
  case (SeedNe v ctx) show ?case by simp
next
  case (ClProved c d s) then show ?case by (intro tclassify_proved)
next
  case (ClRefuted c d s) then show ?case by (intro tclassify_refuted)
next
  case BotState show ?case by simp
next
  case (InitSound p) show ?case by (rule tinit_sound)
next
  case (SeedNeGlobal v ctx n) show ?case by simp
next
  case (PEntry p) show ?case by (simp add: typed_cfg_def)
next
  case (FinIntra p) show ?case by (simp add: typed_cfg_def compile_prog_finite)
next
  case (FinCalls p) show ?case by (simp add: typed_cfg_def compile_prog_finite)
next
  case (CallsUnique p) show ?case by (rule typed_cfg_calls_source_unique)
qed

subsection \<open>End-to-end soundness\<close>

text \<open>
  A terminating solve of the typed analysis bounds every store a typed run of
  the program reaches. The run starts in a store whose globals are zero at their kinds;
  the analysis has one context, so the bound is the state published at the run's node.
  Termination is a premise about this program, as for the untyped analyses.
\<close>

context
  fixes ds :: kind_decls and r :: globals_rule
begin

lemma typed_nonrel_node_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_nonrel.terminates TYPE('a::kind_int_domain) ds r tglobal p"
  shows "tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v
           \<subseteq> gamma_tt (kenv_of ds) (typed_nonrel.state_at ds r tglobal p () v :: 'a tabs toplift)"
  using typed_nonrel.gfun_route_result_node_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves, of "\<lambda>_ _ _. ()" v]
  by (simp add: tnode_collect_def UNIV_unit)

theorem typed_nonrel_source_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_nonrel.terminates TYPE('a::kind_int_domain) ds r tglobal p"
    and s0: "s0 \<in> tinit_stores (kenv_of ds)"
    and run: "star (tpstep (kenv_of ds) (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. typed_ptable p ds, typed_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> gamma_tt (kenv_of ds) (typed_nonrel.state_at ds r tglobal p () v :: 'a tabs toplift)"
  using typed_source_reaches_node_collect[OF wf s0 run] typed_nonrel_node_sound[OF wf solves]
  by blast

text \<open>A proved check holds at every typed store reaching its node; a refuted one fails at
  every such store. Neither verdict says the node is reached.\<close>

theorem typed_nonrel_report_proved_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_nonrel.terminates TYPE('a::kind_int_domain) ds r tglobal p"
    and mem: "(v, c, Check_Proved) \<in> set (typed_nonrel.report TYPE('a) ds r tglobal p ())"
  shows "\<forall>s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v.
           truthy (teval c s)"
  using typed_nonrel.gfun_route_report_proved_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves mem, of "\<lambda>_ _ _. ()"]
    typed_nonrel.fun_route_node_collect_eq_Union[of ds p v "\<lambda>_ _ _. ()"]
  by (simp add: tnode_collect_def)

theorem typed_nonrel_report_refuted_sound:
  assumes wf: "wf_program_compile_input p"
    and solves: "typed_nonrel.terminates TYPE('a::kind_int_domain) ds r tglobal p"
    and mem: "(v, c, Check_Refuted) \<in> set (typed_nonrel.report TYPE('a) ds r tglobal p ())"
  shows "\<forall>s \<in> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v.
           \<not> truthy (teval c s)"
  using typed_nonrel.gfun_route_report_refuted_sound
      [OF typed_cfg_def _ typed_wf_compile_input[OF wf] solves mem, of "\<lambda>_ _ _. ()"]
    typed_nonrel.fun_route_node_collect_eq_Union[of ds p v "\<lambda>_ _ _. ()"]
  by (simp add: tnode_collect_def)

end

unbundle no default_st_syntax

end
