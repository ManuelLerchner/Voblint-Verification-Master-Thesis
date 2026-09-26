theory MCP_Analyses
  imports MCP_Carrier
begin

section \<open>The registered analyses, run as one\<close>

text \<open>
  \<^theory>\<open>Voblint_CLI.MCP_Carrier\<close> lays out one field per registered analysis
  and states how each field runs, describes, reads back and answers. This theory
  runs the active fields as one component, proves the combination sound whatever
  analyses are registered, and registers it at every context policy. Every proof
  here goes by cases over the registered analyses, so a new analysis in the
  manifest needs nothing new here.
\<close>

subsection \<open>Each analysis on its own field\<close>

lemma mcp_component_of_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (mcp_component_of \<G> p a) (part_gamma \<G> b)"
  by (cases a; cases b; simp only: part_gamma.simps mcp_component_of.simps;
      rule field_frame; simp add: lift_get_put_other)

subsection \<open>The active analyses, run as one\<close>

text \<open>
  The combined state is unreachable as soon as one active analysis says its
  field is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close> when one component does. The
  normalization changes no concretization: a field that describes nothing
  empties the intersection already.
\<close>


definition mcp_norm :: "analysis_domain list \<Rightarrow> mcp_st lifted \<Rightarrow> mcp_st lifted" where
  "mcp_norm as x =
     (case x of Bot \<Rightarrow> Bot | Lifted r \<Rightarrow> if list_all (\<lambda>a. part_live a r) as then x else Bot)"

lemma part_gamma_Bot [simp]: "part_gamma \<G> a Bot = {}"
  by (cases a) simp_all

lemma part_gamma_dead: "\<not> part_live a r \<Longrightarrow> part_gamma \<G> a (Lifted r) = {}"
  by (cases a) simp_all

lemma mcp_gamma_norm:
  "mcp_gamma (map (part_gamma \<G>) as) (mcp_norm as x) = mcp_gamma (map (part_gamma \<G>) as) x"
  by (cases x) (auto simp: mcp_norm_def mcp_gamma_def list_all_iff dest: part_gamma_dead)

definition mcp_comp ::
  "analysis_domain list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_comp as \<G> p = map_component (mcp_norm as) (mcp_combine (map (mcp_component_of \<G> p) as))"

theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "mcp_component_sound (declared_global p)
           (mcp_gamma (map (part_gamma (declared_global p)) as))
           (mcp_comp as (declared_global p) p)"
proof -
  let ?gcs = "map (\<lambda>a. (part_gamma (declared_global p) a,
                         mcp_component_of (declared_global p) p a)) as"
  have "mcp_component_sound (declared_global p) (mcp_gamma (map fst ?gcs))
          (mcp_combine (map snd ?gcs))"
    by (rule mcp_combine_sound)
       (auto simp: mcp_component_of_sound assms
         intro!: mcp_independent_map mcp_component_of_frame)
  then show ?thesis
    unfolding mcp_comp_def
    by (intro map_component_sound) (simp_all add: comp_def mcp_gamma_norm)
qed

text \<open>
  Where no active analysis answers queries, the combined state answers every query
  with \<^term>\<open>\<top>\<close>. A field that asks at its assignments then steps exactly as its
  analysis alone (\<open>ask_assign_top\<close>): asking changes a run only once an analysis
  that answers is active.
\<close>

theorem mcp_comp_silent:
  assumes "\<And>a. a \<in> set as \<Longrightarrow> mc_qry (mcp_component_of \<G> p a) x q = \<top>"
  shows "mc_qry (mcp_comp as \<G> p) x q = \<top>"
  unfolding mcp_comp_def map_component_def
  using assms by (auto intro!: mcp_combine_qry_top)

lemma single_entry_mcp_comp: "as \<noteq> [] \<Longrightarrow> single_entry (mcp_comp as \<G> p)"
  unfolding mcp_comp_def
  by (intro single_entry_map_component single_entry_mcp_combine)
     (auto simp: single_entry_mcp_component_of)


subsection \<open>What the combined state publishes\<close>

text \<open>
  A solved combined state is published field by field, each through its
  analysis's own readback. Its concretization is the intersection over the
  active fields, and a check is decided from the meet of the active analyses'
  answers.
\<close>

lemma part_gamma_rd: "part_gamma \<G> a x = gamma_lift (val_gamma a) (map_lift (mcp_rd \<G>) x)"
  by (cases a; cases x) (simp_all add: mcp_rd_def)

lemma mcp_gamma_rd:
  "as \<noteq> [] \<Longrightarrow> mcp_gamma (map (part_gamma \<G>) as) x
                  = gamma_lift (mcp_gamma_v as) (map_lift (mcp_rd \<G>) x)"
  by (cases x) (auto simp: mcp_gamma_def mcp_gamma_v_def part_gamma_rd)

lemma mcp_gamma_v_bot: "as \<noteq> [] \<Longrightarrow> mcp_gamma_v as \<bottom> = {}"
proof -
  have "val_gamma a \<bottom> = {}" for a by (cases a) simp_all
  then show "as \<noteq> [] \<Longrightarrow> ?thesis" by (auto simp: mcp_gamma_v_def)
qed

definition mcp_emp :: "analysis_domain list \<Rightarrow> imp_prog \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "mcp_emp as p r = list_ex (\<lambda>a. part_empty (declared_global_vars p) a r) as"

definition mcp_empty_v :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> bool" where
  "mcp_empty_v as v = list_ex (\<lambda>a. val_empty a v) as"

lemma part_empty_rd:
  "part_empty (declared_global_vars p) a r = val_empty a (mcp_rd (declared_global p) r)"
  by (cases a)
     (simp_all add: mcp_rd_def
        resolved_st_q_is_bot_for_iff[where \<G> = "declared_global p", OF declared_global_iff]
        split: lifted.split)

lemma mcp_emp_rd: "mcp_emp as p r = mcp_empty_v as (mcp_rd (declared_global p) r)"
  by (simp add: mcp_emp_def mcp_empty_v_def part_empty_rd)

lemma val_empty_gamma: "val_empty a v \<Longrightarrow> val_gamma a v = {}"
  by (cases a) (auto split: lifted.splits dest: is_empty_state_gamma_state_empty)

lemma mcp_empty_v_gamma: "mcp_empty_v as v \<Longrightarrow> mcp_gamma_v as v = {}"
  by (auto simp: mcp_empty_v_def mcp_gamma_v_def list_ex_iff dest: val_empty_gamma)

definition mcp_answer :: "analysis_domain list \<Rightarrow> mcp_val \<Rightarrow> query \<Rightarrow> answer" where
  "mcp_answer as v q = fold (\<lambda>a r. r \<sqinter> val_answer a v q) as \<top>"

lemma mcp_answer_fold_sound:
  "\<forall>a \<in> set as. s \<in> val_gamma a v \<Longrightarrow> eval_holds q r s
   \<Longrightarrow> eval_holds q (fold (\<lambda>a r. r \<sqinter> val_answer a v q) as r) s"
  by (induction as arbitrary: r) (auto intro: eval_query.inf_sound val_answer_sound)

lemma mcp_answer_sound: "s \<in> mcp_gamma_v as v \<Longrightarrow> eval_holds q (mcp_answer as v q) s"
  unfolding mcp_answer_def mcp_gamma_v_def by (rule mcp_answer_fold_sound) auto

definition mcp_classify :: "analysis_domain list \<Rightarrow> exp \<Rightarrow> mcp_val \<Rightarrow> check_result" where
  "mcp_classify as = answer_check (mcp_answer as)"

lemma mcp_classify_proved:
  "mcp_classify as e v = Check_Proved \<Longrightarrow> s \<in> mcp_gamma_v as v \<Longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  unfolding mcp_classify_def by (erule answer_check_proved) (rule mcp_answer_sound)

lemma mcp_classify_refuted:
  "mcp_classify as e v = Check_Refuted \<Longrightarrow> s \<in> mcp_gamma_v as v
   \<Longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  unfolding mcp_classify_def by (erule answer_check_refuted) (rule mcp_answer_sound)

text \<open>
  A caller activates a distinct, nonempty list of analyses. The registrations
  below take any list and run it as \<open>activation\<close> normalizes it, so they hold
  unconditionally; \<open>activation\<close> is the identity on every list a caller may
  pass.
\<close>

definition activation :: "analysis_domain list \<Rightarrow> analysis_domain list" where
  "activation as = (if as = [] then [Int_Analysis] else remdups as)"

lemma activation_ne [simp]: "activation as \<noteq> []"
  by (simp add: activation_def)

lemma distinct_activation [simp]: "distinct (activation as)"
  by (simp add: activation_def)

lemma activation_id: "distinct as \<Longrightarrow> as \<noteq> [] \<Longrightarrow> activation as = as"
  by (simp add: activation_def)

section \<open>Registering the active analyses\<close>

text \<open>
  The active analyses run through the shared pipeline once per context
  policy, as one registered analysis does. What they owe the pipeline does not
  depend on the policy, beyond its seeds being apart from the analysis-wide
  global, so it is proved once here. Each registration leaves the activation
  list and the global update rule as parameters.
\<close>

lemma mcp_routed_dg_analysis:
  fixes gk0 :: 'k
  assumes "\<And>v ctx. seed v ctx \<noteq> gk0"
  shows "routed_dg_analysis (mcp_comp (activation as)) (mcp_emp (activation as)) mcp_rd
    (mcp_init (activation as)) gk0 seed (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE('k) TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify (activation as)) (mcp_gamma_v (activation as))
    (mcp_empty_v (activation as)) (TD_side_rule_Interp_solve_c r)"
proof (unfold_locales, goal_cases CompSound EnterSingle EmptyRd EmptyVSound SeedNe
    SolvePP SolveFin ClProved ClRefuted BotState Init DomC)
  case (CompSound p)
  have eq: "mcp_gamma (map (part_gamma (declared_global p)) (activation as))
      = (\<lambda>d. gamma_lift (mcp_gamma_v (activation as)) (map_lift (mcp_rd (declared_global p)) d))"
    by (rule ext) (rule mcp_gamma_rd[OF activation_ne])
  show ?case using mcp_comp_sound[of "activation as" p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF single_entry_mcp_comp[OF activation_ne],
        of as "declared_global p" p ci "(d, d)"]
    by (simp add: routed_dg_pipeline.entry_of_def)
next
  case (EmptyRd p s) show ?case by (rule mcp_emp_rd)
next
  case (EmptyVSound v) then show ?case by (rule mcp_empty_v_gamma)
next
  case (SeedNe v ctx) show ?case by (rule assms)
next
  case (SolvePP eqs x) then show ?case
    by (rule TD_side_rule_Interp.partial_post_solution[OF _ surjective_pairing])
next
  case (SolveFin eqs x) then show ?case by (rule TD_side_rule_Interp.finite_stabl_solve)
next
  case (ClProved e d s) then show ?case by (rule mcp_classify_proved)
next
  case (ClRefuted e d s) then show ?case by (rule mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp_gamma_v_bot[OF activation_ne])
next
  case (Init p) show ?case by (rule mcp_init_sound)
next
  case (DomC eqs x) then show ?case by (rule TD_side_rule_Interp.solve_dom_of_solve_c)
qed

subsection \<open>At the unit context\<close>

global_interpretation mcp_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    "Analysis_Global ()" Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) routed_gk)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as r
  by (rule mcp_routed_dg_analysis) simp

subsection \<open>At the entry-state context\<close>

text \<open>
  An activation is keyed by the values the active analyses give its formals
  on entry. The context has a list per field; a field no active analysis
  runs keys nothing.
\<close>

global_interpretation mcp_es_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    "Analysis_Global ()" Activation_Seed "mcp_formals_route (activation as)" mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, mcp_ctx) routed_gk)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as r
  by (rule mcp_routed_dg_analysis) simp

subsection \<open>At the call-string context\<close>

global_interpretation mcp_cs_rule: routed_dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Call_String_Context.Global Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE(call_string_gk)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
  for as k r
  by (rule mcp_routed_dg_analysis) simp

end
