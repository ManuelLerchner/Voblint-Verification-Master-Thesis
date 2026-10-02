theory Analysis_Report
  imports Analysis_Run_Ctx_Sound
begin

section \<open>What a report claims\<close>

text \<open>
  A report is read through three sets of stores at a point \<open>v\<close>. \<open>\<C> v\<close> holds the
  stores the program reaches at \<open>v\<close>. \<open>\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>\<close> holds the stores the report's states
  at \<open>v\<close> describe, over all of its contexts. \<open>\<V>(res, v)\<close> holds the stores in which
  every definite verdict the report gives at \<open>v\<close> is valid. The report is sound when

    \<open>\<C> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>(res, v)\<close>

  and a point the report calls dead has \<open>\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = {}\<close>, so no execution reaches it.
  The first inclusion needs the run that built the report; the second and the dead
  case follow from the report alone, once its verdicts agree with its states.
\<close>

subsection \<open>The stores a report describes\<close>

definition report_gamma :: "analysis_report \<Rightarrow> mcp_val \<Rightarrow> store set" where
  "report_gamma res = mcp_gamma_v (activation (config_analyses (report_config res)))"

definition report_classify :: "analysis_report \<Rightarrow> exp \<Rightarrow> mcp_val \<Rightarrow> check_result" where
  "report_classify res = mcp_classify (activation (config_analyses (report_config res)))"

text \<open>The states a report holds at a point, one per context it was solved at.\<close>

definition report_rows :: "analysis_report \<Rightarrow> pp \<Rightarrow> mcp_val lifted set" where
  "report_rows res v = state_value ` {st \<in> set (report_states res). state_point st = v}"

lemma finite_report_rows [simp]: "finite (report_rows res v)"
  by (simp add: report_rows_def)

definition report_sem :: "analysis_report \<Rightarrow> pp \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>" [0, 0] 1000) where
  "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = (\<Union>\<sigma> \<in> report_rows res v. gamma_lift (report_gamma res) \<sigma>)"

lemma mem_report_sem [simp]:
  "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<longleftrightarrow> (\<exists>d. Lifted d \<in> report_rows res v \<and> s \<in> report_gamma res d)"
  unfolding report_sem_def
proof
  assume "s \<in> (\<Union>\<sigma> \<in> report_rows res v. gamma_lift (report_gamma res) \<sigma>)"
  then obtain \<sigma> where "\<sigma> \<in> report_rows res v" and "s \<in> gamma_lift (report_gamma res) \<sigma>"
    by blast
  then show "\<exists>d. Lifted d \<in> report_rows res v \<and> s \<in> report_gamma res d" by (cases \<sigma>) auto
qed (metis UN_I gamma_lift_Lifted)

lemma report_semI [intro]:
  "Lifted d \<in> report_rows res v \<Longrightarrow> s \<in> report_gamma res d \<Longrightarrow> s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  unfolding report_sem_def by (rule UN_I[of "Lifted d"]) simp_all

lemma report_semE [elim]:
  assumes "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  obtains d where "Lifted d \<in> report_rows res v" and "s \<in> report_gamma res d"
proof -
  from assms obtain \<sigma> where "\<sigma> \<in> report_rows res v" and "s \<in> gamma_lift (report_gamma res) \<sigma>"
    unfolding report_sem_def by blast
  then show ?thesis by (cases \<sigma>) (auto intro: that)
qed

subsection \<open>Verdicts\<close>

definition report_checks_at :: "analysis_report \<Rightarrow> pp \<Rightarrow> result_check set" where
  "report_checks_at res v = {c \<in> set (report_checks res). check_point c = v}"

lemma mem_report_checks_at [simp]:
  "c \<in> report_checks_at res v \<longleftrightarrow> c \<in> set (report_checks res) \<and> check_point c = v"
  by (simp add: report_checks_at_def)

definition verdict_stores :: "analysis_report \<Rightarrow> pp \<Rightarrow> store set" where
  "verdict_stores res v =
     {s. \<forall>c \<in> report_checks_at res v.
           (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>check_exp c\<rbrakk>\<^sub>e s))
         \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>check_exp c\<rbrakk>\<^sub>e s))}"

definition PROVED :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "PROVED res v e \<longleftrightarrow>
     (\<exists>c \<in> report_checks_at res v. check_exp c = e \<and> check_verdict c = Decided Check_Proved)"

definition REFUTED :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "REFUTED res v e \<longleftrightarrow>
     (\<exists>c \<in> report_checks_at res v. check_exp c = e \<and> check_verdict c = Decided Check_Refuted)"

definition UNKNOWN :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "UNKNOWN res v e \<longleftrightarrow>
     (\<exists>c \<in> report_checks_at res v. check_exp c = e \<and> check_verdict c = Decided Check_Unknown)"

text \<open>
  \<open>DEAD\<close> is a property of a point, not of a condition: every state the report holds
  there is \<^const>\<open>Bot\<close>. The states are canonical --- the table they come from
  collapses a state its emptiness test rejects to \<^const>\<open>Bot\<close> --- so \<open>DEAD\<close> reads
  that canonical form instead of running a test. The test is sound and incomplete
  for a product of analyses, so the converse of \<open>analysis_report_dead\<close> does not hold.
\<close>

definition DEAD :: "analysis_report \<Rightarrow> pp \<Rightarrow> bool" where
  "DEAD res v \<longleftrightarrow> (\<forall>\<sigma> \<in> report_rows res v. \<sigma> = Bot)"

subsection \<open>A consistent report\<close>

text \<open>
  A report is consistent when each check's verdict is the aggregate of the
  report's own classifier over the report's own states at the check's point. Every
  report \<^const>\<open>run_voblint\<close> returns is consistent.
\<close>

definition consistent_report :: "analysis_report \<Rightarrow> bool" where
  "consistent_report res \<longleftrightarrow>
     (\<forall>c \<in> set (report_checks res).
        check_verdict c
          = aggregate_verdicts
              (classify_point (report_classify res) (check_exp c)
                 ` report_rows res (check_point c)))"

lemma consistent_report_decided:
  assumes cons: "consistent_report res"
    and c: "c \<in> report_checks_at res v"
    and verdict: "check_verdict c = Decided r" and known: "r \<noteq> Check_Unknown"
    and row: "Lifted d \<in> report_rows res v"
  shows "report_classify res (check_exp c) d = r"
proof -
  from c have mem: "c \<in> set (report_checks res)" and pt: "check_point c = v"
    by (simp_all add: report_checks_at_def)
  have agg: "aggregate_verdicts
               (classify_point (report_classify res) (check_exp c) ` report_rows res v)
             = Decided r"
    using cons mem verdict pt unfolding consistent_report_def by auto
  from aggregate_verdicts_decided_dest[OF agg known] row
  show ?thesis by fastforce
qed

subsection \<open>What a consistent report claims about its own states\<close>

theorem analysis_report_verdicts_sound:
  assumes "consistent_report res"
  shows "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> verdict_stores res v"
proof
  fix s
  assume "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  then obtain d where row: "Lifted d \<in> report_rows res v" and s: "s \<in> report_gamma res d"
    by (rule report_semE)
  show "s \<in> verdict_stores res v"
    unfolding verdict_stores_def
  proof (intro CollectI ballI conjI impI)
    fix c
    assume c: "c \<in> report_checks_at res v" and pv: "check_verdict c = Decided Check_Proved"
    from consistent_report_decided[OF assms c pv _ row]
    have "report_classify res (check_exp c) d = Check_Proved" by simp
    then show "truthy (\<lbrakk>check_exp c\<rbrakk>\<^sub>e s)"
      using s unfolding report_classify_def report_gamma_def by (rule mcp_classify_proved)
  next
    fix c
    assume c: "c \<in> report_checks_at res v" and rv: "check_verdict c = Decided Check_Refuted"
    from consistent_report_decided[OF assms c rv _ row]
    have "report_classify res (check_exp c) d = Check_Refuted" by simp
    then show "\<not> truthy (\<lbrakk>check_exp c\<rbrakk>\<^sub>e s)"
      using s unfolding report_classify_def report_gamma_def by (rule mcp_classify_refuted)
  qed
qed

corollary analysis_report_proved:
  assumes "consistent_report res" and "PROVED res v e" and "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  shows "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using analysis_report_verdicts_sound[OF assms(1)] assms(2,3)
  unfolding PROVED_def verdict_stores_def by blast

corollary analysis_report_refuted:
  assumes "consistent_report res" and "REFUTED res v e" and "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  shows "\<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using analysis_report_verdicts_sound[OF assms(1)] assms(2,3)
  unfolding REFUTED_def verdict_stores_def by blast

theorem analysis_report_dead: "DEAD res v \<Longrightarrow> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = {}"
  unfolding DEAD_def report_sem_def by auto

text \<open>A check printed dead is one presentation of a dead point.\<close>

lemma analysis_report_check_dead:
  assumes "consistent_report res" and "c \<in> set (report_checks res)"
    and "check_verdict c = Dead"
  shows "DEAD res (check_point c)"
proof -
  have "aggregate_verdicts
          (classify_point (report_classify res) (check_exp c) ` report_rows res (check_point c))
        = Dead"
    using assms unfolding consistent_report_def by auto
  then have "\<forall>\<sigma> \<in> report_rows res (check_point c).
               classify_point (report_classify res) (check_exp c) \<sigma> = Dead"
    by (simp add: aggregate_verdicts_eq_Dead_iff)
  then show ?thesis
    unfolding DEAD_def by (metis classify_point.elims lifted.distinct(1))
qed

text \<open>
  An \<open>UNKNOWN\<close> check makes no claim about the stores, and its point is not dead: the
  report holds a state there that its classifier read.
\<close>

lemma analysis_report_unknown:
  assumes "consistent_report res" and "UNKNOWN res v e"
  shows "\<not> DEAD res v"
proof
  assume dead: "DEAD res v"
  from assms(2) obtain c where c: "c \<in> set (report_checks res)" "check_point c = v"
    and verdict: "check_verdict c = Decided Check_Unknown"
    unfolding UNKNOWN_def report_checks_at_def by blast
  have "\<forall>\<sigma> \<in> report_rows res v. classify_point (report_classify res) (check_exp c) \<sigma> = Dead"
    using dead unfolding DEAD_def by auto
  then have "aggregate_verdicts
               (classify_point (report_classify res) (check_exp c) ` report_rows res v) = Dead"
    by (simp add: aggregate_verdicts_eq_Dead_iff)
  with assms(1) c verdict show False unfolding consistent_report_def by auto
qed

section \<open>A report built from a sound table\<close>

text \<open>
  \<^const>\<open>report_of\<close> lists the contexts of the table in the order of an injective
  key, so it lists every one, and files every covered key as a row. Its rows at a
  point are therefore exactly the table's entries there.
\<close>

lemma ordered_by_key_set:
  assumes fin: "finite S" and inj: "inj_on rank S"
  shows "set (ordered_by_key rank S) = S"
proof -
  have pick: "the_elem (Set.filter (\<lambda>x. rank x = rank y) S) = y" if "y \<in> S" for y
  proof -
    have "Set.filter (\<lambda>x. rank x = rank y) S = {y}"
      using that inj by (auto simp: inj_on_def)
    then show ?thesis by simp
  qed
  have "set (ordered_by_key rank S) = (\<lambda>k. the_elem (Set.filter (\<lambda>x. rank x = k) S)) ` rank ` S"
    unfolding ordered_by_key_def using fin by simp
  also have "\<dots> = S"
    using pick by (force simp: image_comp)
  finally show ?thesis .
qed

lemma row_in_rows:
  assumes "(i, ctx) \<in> set xs" and "v \<in> set ns" and "P v ctx"
  shows "f i ctx v \<in> set (concat (map (\<lambda>(i, ctx). map (f i ctx) (filter (\<lambda>v. P v ctx) ns)) xs))"
  using assms by force

lemma report_rows_report_of:
  assumes fin: "finite (result_unknowns (run_table sr))" and inj: "inj ctx_key"
  shows "report_rows (report_of config ctx_key ctx_tag classify sr p) v
           = lookup_context (run_table sr) v ` contexts_at (run_table sr) v"
proof -
  define r where "r = run_table sr"
  define ctxs where "ctxs = ordered_by_key ctx_key (snd ` result_unknowns r)"
  define nodes where "nodes = cfg_node_list (prog_cfg p)
    @ sorted_list_of_set (fst ` result_unknowns r - set (cfg_node_list (prog_cfg p)))"
  have ctxs: "set ctxs = snd ` result_unknowns r"
    unfolding ctxs_def r_def
    by (rule ordered_by_key_set) (use fin inj in \<open>auto intro: inj_on_subset\<close>)
  have nodes: "w \<in> set nodes" if "(w, ctx) \<in> result_unknowns r" for w ctx
  proof (cases "w \<in> set (cfg_node_list (prog_cfg p))")
    case False
    with that fin show ?thesis unfolding nodes_def r_def by (force intro: rev_image_eqI)
  qed (simp add: nodes_def)
  have indexed: "\<exists>i. (i, ctx) \<in> set (enumerate 0 ctxs)" if "ctx \<in> set ctxs" for ctx
  proof -
    from that obtain i where "i < length ctxs" and "ctxs ! i = ctx"
      by (auto simp: in_set_conv_nth)
    then have "(i, ctx) \<in> set (enumerate 0 ctxs)"
      by (metis add_0 length_enumerate nth_enumerate_eq nth_mem)
    then show ?thesis ..
  qed
  show ?thesis
  proof (intro equalityI subsetI)
    fix \<sigma>
    assume "\<sigma> \<in> report_rows (report_of config ctx_key ctx_tag classify sr p) v"
    then show "\<sigma> \<in> lookup_context (run_table sr) v ` contexts_at (run_table sr) v"
      unfolding report_rows_def report_of_def Let_def by (auto simp: contexts_at_iff)
  next
    fix \<sigma>
    assume "\<sigma> \<in> lookup_context (run_table sr) v ` contexts_at (run_table sr) v"
    then obtain ctx where cov: "(v, ctx) \<in> result_unknowns r"
      and \<sigma>: "\<sigma> = lookup_context r v ctx"
      by (auto simp: r_def contexts_at_iff)
    from cov ctxs have "ctx \<in> set ctxs" by force
    then obtain i where i: "(i, ctx) \<in> set (enumerate 0 ctxs)" using indexed by blast
    have w: "v \<in> set nodes" using nodes[OF cov] .
    show "\<sigma> \<in> report_rows (report_of config ctx_key ctx_tag classify sr p) v"
      unfolding report_rows_def report_of_def Let_def r_def[symmetric] ctxs_def[symmetric]
        nodes_def[symmetric]
      apply (simp only: analysis_report.select_convs)
      apply (rule image_eqI[rotated], rule CollectI, rule conjI, rule row_in_rows[OF i w])
      using cov \<sigma> by (simp_all add: r_def)
  qed
qed

lemma report_of_simps [simp]:
  "report_config (report_of config ctx_key ctx_tag classify sr p) = config"
  "report_cfg (report_of config ctx_key ctx_tag classify sr p) = prog_cfg p"
  "report_checks (report_of config ctx_key ctx_tag classify sr p)
     = result_checks_of (prog_cfg p) (run_table sr) classify"
  "report_diagnostics (report_of config ctx_key ctx_tag classify sr p)
     = arithmetic_diagnostics (prog_cfg p) (run_table sr) classify"
  by (simp_all add: report_of_def Let_def)

text \<open>
  What a report built from a run of a program owes: its verdicts agree with its
  states, its states cover the collecting semantics, its diagnostics name every
  point where a divisor may be zero, and its check column lists the program's checks.
\<close>

definition sound_report :: "imp_prog \<Rightarrow> analysis_report \<Rightarrow> bool" where
  "sound_report p res \<longleftrightarrow>
     consistent_report res
   \<and> (\<forall>v. \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>)
   \<and> (\<forall>v s. s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v
        \<longrightarrow> (\<forall>d \<in> set (report_diagnostics res). diagnostic_point d \<noteq> v)
        \<longrightarrow> arithmetic_safe_at (prog_cfg p) v s)
   \<and> map (\<lambda>c. (check_point c, check_label c, check_exp c)) (report_checks res)
       = check_sites (prog_cfg p)"

lemma report_of_sound:
  assumes st: "sound_table p (run_table sr) classify gm"
    and fin: "finite (result_unknowns (run_table sr))" and inj: "inj ctx_key"
    and cl: "classify = mcp_classify (activation (config_analyses config))"
    and gm: "gm = mcp_gamma_v (activation (config_analyses config))"
  shows "sound_report p (report_of config ctx_key ctx_tag classify sr p)"
proof -
  let ?res = "report_of config ctx_key ctx_tag classify sr p"
  note rows = report_rows_report_of[OF fin inj]
  have cons: "consistent_report ?res"
    unfolding consistent_report_def
    by (auto simp: result_checks_of_def rows report_classify_def cl image_comp comp_def)
  have covers: "s \<in> \<lbrakk>?res\<rbrakk>\<^bsub>v\<^esub>"
    if "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v" for v s
  proof -
    from sound_table.covers[OF st that] obtain ctx d
      where look: "lookup_context (run_table sr) v ctx = Lifted d" and s: "s \<in> gm d"
      unfolding table_covers_def by blast
    then have "Lifted d \<in> report_rows ?res v"
      unfolding rows by (metis image_eqI lookup_context_LiftedD)
    with s show ?thesis by (auto simp: report_gamma_def gm)
  qed
  have safe: "arithmetic_safe_at (prog_cfg p) v s"
    if "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
      and "\<forall>d \<in> set (report_diagnostics ?res). diagnostic_point d \<noteq> v" for v s
    using sound_table.arithmetic_safe[OF st _ that(1)] that(2) by simp
  show ?thesis
    unfolding sound_report_def
    using cons covers safe by (auto simp: result_checks_of_sites)
qed

text \<open>
  The one argument that reads the context policy. Each policy's report comes from
  its registration's executable solve, whose answer is the solve the registration's
  soundness theorem is about; the rest is \<open>report_of_sound\<close>.
\<close>

lemma inj_call_string_key: "inj (\<lambda>ctx. Key_List (map Key_Node ctx))"
  by (rule injI) (simp add: inj_def)

lemma inj_entry_ctx_key: "inj (entry_ctx_key as)"
  by (rule injI) (rule entry_ctx_key_inject)

lemma analysis_report_of_sound:
  assumes wf: "wf_program_compile_input p"
    and some: "analysis_report_of config p = Some res"
  shows "sound_report p res"
proof (cases config)
  case (Analysis_Config as r ctx)
  show ?thesis
  proof (cases ctx)
    case Ctx_None
    from some obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (mcp_rule.equations as (declared_global p) p)
              (mcp_rule.root_query p) = Some sol"
      and res: "res = report_of config (\<lambda>_. Key_List []) (\<lambda>_. Report_Unit)
                  (mcp_classify (activation as))
                  (mcp_rule.solved_run_of as (declared_global p) p sol) p"
      by (auto simp: Analysis_Config Ctx_None dg_pipeline.root_query_def)
    note run = mcp_rule.solve_c_run[OF sol]
    show ?thesis
      unfolding res run(2)
      by (rule report_of_sound[OF _ _ _ _ refl])
         (use mcp_rule_table[OF wf run(1)] mcp_rule.vars_finite_of_terminates[OF run(1)] in
           \<open>simp_all add: Analysis_Config finite_analysis_result_def dg_pipeline.result_def
              dg_pipeline.sol_vars_def inj_def\<close>)
  next
    case Ctx_EntryState
    from some obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (mcp_es_rule.equations as (declared_global p) p)
              (mcp_es_rule.root_query p) = Some sol"
      and res: "res = report_of config (entry_ctx_key (activation as)) Report_Entry
                  (mcp_classify (activation as))
                  (mcp_es_rule.solved_run_of as (declared_global p) p sol) p"
      by (auto simp: Analysis_Config Ctx_EntryState dg_pipeline.root_query_def)
    note run = mcp_es_rule.solve_c_run[OF sol]
    show ?thesis
      unfolding res run(2)
      by (rule report_of_sound[OF _ _ inj_entry_ctx_key _ refl])
         (use mcp_es_rule_table[OF wf run(1)] mcp_es_rule.vars_finite_of_terminates[OF run(1)] in
           \<open>simp_all add: Analysis_Config finite_analysis_result_def dg_pipeline.result_def
              dg_pipeline.sol_vars_def\<close>)
  next
    case (Ctx_CallString k)
    from some obtain sol where
      sol: "TD_side_rule_Interp_solve_c r (mcp_cs_rule.equations as k (declared_global p) p)
              (mcp_cs_rule.root_query p) = Some sol"
      and res: "res = report_of config (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
                  (mcp_classify (activation as))
                  (mcp_cs_rule.solved_run_of as k (declared_global p) p sol) p"
      by (auto simp: Analysis_Config Ctx_CallString dg_pipeline.root_query_def)
    note run = mcp_cs_rule.solve_c_run[OF sol]
    show ?thesis
      unfolding res run(2)
      by (rule report_of_sound[OF _ _ inj_call_string_key _ refl])
         (use mcp_cs_rule_table[OF wf run(1)] mcp_cs_rule.vars_finite_of_terminates[OF run(1)] in
           \<open>simp_all add: Analysis_Config finite_analysis_result_def dg_pipeline.result_def
              dg_pipeline.sol_vars_def\<close>)
  qed
qed

end
