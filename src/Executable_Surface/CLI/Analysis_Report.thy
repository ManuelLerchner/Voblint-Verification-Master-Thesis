theory Analysis_Report
  imports Analysis_Run_Ctx_Sound Analysis_Render
begin

section \<open>What a report claims\<close>

text \<open>
  A report is read through three sets of stores at a point \<open>v\<close>. \<open>\<C> v\<close> holds the
  stores the program reaches at \<open>v\<close>. \<open>\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>\<close> holds the stores the report's states
  at \<open>v\<close> describe, over all of its contexts. \<open>\<V>\<^bsub>res\<^esub> v\<close> holds the stores in which
  every definite verdict the report gives at \<open>v\<close> is valid. The report is sound when

    \<open>\<C> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v\<close>

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

definition report_states_at :: "analysis_report \<Rightarrow> pp \<Rightarrow> mcp_val lifted set" where
  "report_states_at res v = state_value ` {st \<in> set (report_states res). state_point st = v}"

lemma finite_report_states_at [simp]: "finite (report_states_at res v)"
  by (simp add: report_states_at_def)

text \<open>The stores one such state describes; \<open>Bot\<close> describes none.\<close>

abbreviation report_conc :: "analysis_report \<Rightarrow> mcp_val lifted \<Rightarrow> store set" ("\<gamma>\<^bsub>_\<^esub>") where
  "\<gamma>\<^bsub>res\<^esub> \<equiv> gamma_lift (report_gamma res)"

definition report_sem :: "analysis_report \<Rightarrow> pp \<Rightarrow> store set" ("\<lbrakk>_\<rbrakk>\<^bsub>_\<^esub>" [0, 0] 1000) where
  "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = (\<Union>d \<in> report_states_at res v. \<gamma>\<^bsub>res\<^esub> d)"

lemma mem_report_sem [simp]:
  "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<longleftrightarrow> (\<exists>d. Lifted d \<in> report_states_at res v \<and> s \<in> report_gamma res d)"
  unfolding report_sem_def
proof
  assume "s \<in> (\<Union>dl \<in> report_states_at res v. \<gamma>\<^bsub>res\<^esub> dl)"
  then obtain dl where "dl \<in> report_states_at res v" and "s \<in> \<gamma>\<^bsub>res\<^esub> dl"
    by blast
  then show "\<exists>d. Lifted d \<in> report_states_at res v \<and> s \<in> report_gamma res d" by (cases dl) auto
qed (metis UN_I gamma_lift_Lifted)

lemma report_semI [intro]:
  "Lifted d \<in> report_states_at res v \<Longrightarrow> s \<in> report_gamma res d \<Longrightarrow> s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  unfolding report_sem_def by (rule UN_I[of "Lifted d"]) simp_all

lemma report_semE [elim]:
  assumes "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  obtains d where "Lifted d \<in> report_states_at res v" and "s \<in> report_gamma res d"
proof -
  from assms
  obtain dl where "dl \<in> report_states_at res v" and "s \<in> \<gamma>\<^bsub>res\<^esub> dl"
    unfolding report_sem_def by blast
  then show ?thesis by (cases dl) (auto intro: that)
qed

subsection \<open>One state per point\<close>

text \<open>
  \<^const>\<open>report_point_join\<close> joins the states a report holds at a point over its
  contexts. Every store the report describes at the point, the joined state describes,
  since each component's concretization is monotone.
\<close>

lemma gamma_lift_state_mono: "x \<le> y \<Longrightarrow> \<lbrakk>x\<rbrakk> \<subseteq> \<lbrakk>y :: _ abs_state lifted\<rbrakk>"
  by (rule gamma_lift_mono[where gam = gamma_state]) (use gamma_state_mono in blast)

lemma val_gamma_mono: "v \<le> v' \<Longrightarrow> val_gamma a v \<subseteq> val_gamma a v'"
  by (cases "(a, v)" rule: val_gamma.cases)
    (auto simp: less_eq_analysis_product_def
      intro: gamma_lift_state_mono[THEN subsetD] gamma_relc_mono[THEN subsetD])

lemma mcp_gamma_v_mono: "v \<le> v' \<Longrightarrow> mcp_gamma_v as v \<subseteq> mcp_gamma_v as v'"
  unfolding mcp_gamma_v_def using val_gamma_mono by blast

lemma fold_sup_ge: "x \<in> set xs \<or> x \<le> acc \<Longrightarrow> x \<le> fold (\<squnion>) xs (acc :: 'a::semilattice_sup)"
  by (induction xs arbitrary: acc) (auto intro: le_supI1 le_supI2)

lemma report_states_at_le_point_join: "d \<in> report_states_at res v \<Longrightarrow> d \<le> report_point_join res v"
  unfolding report_states_at_def report_point_join_sup by (auto intro!: fold_sup_ge)

text \<open>Every store the report describes at a point, the joined state describes.\<close>

theorem report_sem_point_join:
  "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<gamma>\<^bsub>res\<^esub> (report_point_join res v)"
proof
  fix s assume "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  then obtain d where row: "Lifted d \<in> report_states_at res v" and s: "s \<in> report_gamma res d"
    by blast
  have "\<gamma>\<^bsub>res\<^esub> (Lifted d)
          \<subseteq> \<gamma>\<^bsub>res\<^esub> (report_point_join res v)"
    by (rule gamma_lift_mono[OF _ report_states_at_le_point_join[OF row]])
      (simp add: report_gamma_def mcp_gamma_v_mono)
  with s show "s \<in> \<gamma>\<^bsub>res\<^esub> (report_point_join res v)" by auto
qed

subsection \<open>Verdicts\<close>

text \<open>
  \<open>report_checks_at\<close> selects the checks a report records at one program point.
\<close>

definition report_checks_at :: "analysis_report \<Rightarrow> pp \<Rightarrow> result_check set" where
  "report_checks_at res v = {c \<in> set (report_checks res). check_point c = v}"

lemma mem_report_checks_at [simp]:
  "c \<in> report_checks_at res v \<longleftrightarrow> c \<in> set (report_checks res) \<and> check_point c = v"
  by (simp add: report_checks_at_def)

text \<open>
  What a decided verdict says about a store: \<open>Check_Proved\<close> that the condition
  holds, \<open>Check_Refuted\<close> that it fails, \<open>Check_Unknown\<close> nothing.
\<close>

fun verdict_holds :: "check_result \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> bool" where
  "verdict_holds Check_Proved e s = truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
| "verdict_holds Check_Refuted e s = (\<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
| "verdict_holds Check_Unknown e s = True"

text \<open>
  The stores a check's verdict admits. A \<open>Dead\<close> check claims nothing about stores;
  its claim, that the point is unreached, is \<open>DEAD\<close> below.
\<close>

definition check_stores :: "result_check \<Rightarrow> store set" where
  "check_stores c = (case check_verdict c of
                       Decided r \<Rightarrow> {s. verdict_holds r (check_exp c) s}
                     | Dead \<Rightarrow> UNIV)"

definition verdict_stores :: "analysis_report \<Rightarrow> pp \<Rightarrow> store set" ("\<V>\<^bsub>_\<^esub>") where
  "\<V>\<^bsub>res\<^esub> v = (\<Inter>c \<in> report_checks_at res v. check_stores c)"

lemma verdict_stores_eq:
  "\<V>\<^bsub>res\<^esub> v =
     {s. \<forall>c \<in> report_checks_at res v. \<forall>r.
           check_verdict c = Decided r \<longrightarrow> verdict_holds r (check_exp c) s}"
  unfolding verdict_stores_def check_stores_def by (auto split: lifted.splits)

definition HAS_VERDICT :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> check_result \<Rightarrow> bool" where
  "HAS_VERDICT res v e r \<longleftrightarrow>
     (\<exists>c \<in> report_checks_at res v. check_exp c = e \<and> check_verdict c = Decided r)"

abbreviation PROVED :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "PROVED res v e \<equiv> HAS_VERDICT res v e Check_Proved"

abbreviation REFUTED :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "REFUTED res v e \<equiv> HAS_VERDICT res v e Check_Refuted"

abbreviation UNKNOWN :: "analysis_report \<Rightarrow> pp \<Rightarrow> exp \<Rightarrow> bool" where
  "UNKNOWN res v e \<equiv> HAS_VERDICT res v e Check_Unknown"

lemma verdict_storesD:
  "s \<in> \<V>\<^bsub>res\<^esub> v \<Longrightarrow> HAS_VERDICT res v e r \<Longrightarrow> verdict_holds r e s"
  unfolding verdict_stores_eq HAS_VERDICT_def by blast

text \<open>
  \<open>DEAD\<close> is a property of a point, not of a condition: every state the report holds
  there is \<^const>\<open>Bot\<close>. The states are canonical --- the table they come from
  collapses a state its emptiness test rejects to \<^const>\<open>Bot\<close> --- so \<open>DEAD\<close> reads
  that canonical form instead of running a test. The test is sound and incomplete
  for a product of analyses, so the converse of \<open>analysis_report_dead\<close> does not hold.
\<close>

definition DEAD :: "analysis_report \<Rightarrow> pp \<Rightarrow> bool" where
  "DEAD res v \<longleftrightarrow> (\<forall>d \<in> report_states_at res v. d = Bot)"

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
                 ` report_states_at res (check_point c)))"

lemma consistent_report_decided:
  assumes cons: "consistent_report res"
    and c: "c \<in> report_checks_at res v"
    and verdict: "check_verdict c = Decided r" and known: "r \<noteq> Check_Unknown"
    and row: "Lifted d \<in> report_states_at res v"
  shows "report_classify res (check_exp c) d = r"
proof -
  from c have mem: "c \<in> set (report_checks res)" and pt: "check_point c = v"
    by (simp_all add: report_checks_at_def)
  have agg: "aggregate_verdicts
               (classify_point (report_classify res) (check_exp c) ` report_states_at res v)
             = Decided r"
    using cons mem verdict pt unfolding consistent_report_def by auto
  from aggregate_verdicts_decided_dest[OF agg known] row
  show ?thesis by fastforce
qed

subsection \<open>What a consistent report claims about its own states\<close>

text \<open>
  A sound classifier's verdict holds at every store its abstract value admits:
  both directions of \<open>sound_classifier\<close> at once, which is what lets a report
  vouch for a \<open>Check_Refuted\<close> row as much as for a \<open>Check_Proved\<close> one.
\<close>

lemma (in sound_classifier) classify_verdict_holds:
  "t \<in> gm d \<Longrightarrow> verdict_holds (classify cnd d) cnd t"
  by (cases "classify cnd d") (auto dest: proved refuted)

theorem analysis_report_verdicts_sound:
  assumes "consistent_report res"
  shows "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
proof
  fix s
  assume "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  then obtain d where row: "Lifted d \<in> report_states_at res v" and s: "s \<in> report_gamma res d"
    by (rule report_semE)
  show "s \<in> \<V>\<^bsub>res\<^esub> v"
    unfolding verdict_stores_eq
  proof (intro CollectI ballI allI impI)
    fix c r
    assume c: "c \<in> report_checks_at res v" and verdict: "check_verdict c = Decided r"
    have holds: "verdict_holds (report_classify res (check_exp c) d) (check_exp c) s"
      using s unfolding report_classify_def report_gamma_def
      by (rule sound_classifier.classify_verdict_holds [OF mcp_sound_classifier])
    show "verdict_holds r (check_exp c) s"
    proof (cases "r = Check_Unknown")
      case False
      with consistent_report_decided[OF assms c verdict False row] holds show ?thesis by simp
    qed simp
  qed
qed

corollary analysis_report_proved:
  assumes "consistent_report res" and "PROVED res v e" and "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  shows "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using verdict_storesD[OF subsetD[OF analysis_report_verdicts_sound[OF assms(1)] assms(3)]
    assms(2)]
  by simp

corollary analysis_report_refuted:
  assumes "consistent_report res" and "REFUTED res v e" and "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  shows "\<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using verdict_storesD[OF subsetD[OF analysis_report_verdicts_sound[OF assms(1)] assms(3)]
    assms(2)]
  by simp

theorem analysis_report_dead: "DEAD res v \<Longrightarrow> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = {}"
  unfolding DEAD_def report_sem_def by auto

text \<open>Read as an emptiness test on points, \<open>DEAD\<close> is sound.\<close>

corollary sound_emptiness_DEAD: "sound_emptiness (DEAD res) (report_sem res)"
  by (rule sound_emptinessI) (rule analysis_report_dead)

text \<open>
  It is not exact. A report holding one state at a point, the combined state
  \<^const>\<open>mcp_contradiction\<close> of Interval and Parity, describes no store there, yet
  that state is not \<^const>\<open>Bot\<close>, so the point is not \<open>DEAD\<close>. The witness is a
  report, not one a run is shown to return.
\<close>

definition contradiction_report :: "pp \<Rightarrow> analysis_report" where
  "contradiction_report v =
     \<lparr> report_config = Analysis_Config [Interval_Analysis, Parity_Analysis] Globals_Join Ctx_None
         Program_Globals_Flow_Sensitive,
       report_vars = [], report_cfg = undefined, report_contexts = [Report_Unit],
       report_states = [\<lparr> state_point = v, state_context = 0, state_value = Lifted mcp_contradiction,
                          state_checks = [], state_diagnostics = [], state_steps = [] \<rparr>],
       report_routes = [], report_checks = [], report_globals = [], report_diagnostics = [] \<rparr>"

lemma DEAD_not_exact:
  "\<not> exact_emptiness (DEAD (contradiction_report v)) (report_sem (contradiction_report v))"
proof -
  have rows: "report_states_at (contradiction_report v) v = {Lifted mcp_contradiction}"
    by (auto simp: report_states_at_def contradiction_report_def)
  have live: "\<not> DEAD (contradiction_report v) v"
    by (simp add: DEAD_def rows)
  have "report_config (contradiction_report v)
                   = Analysis_Config [Interval_Analysis, Parity_Analysis] Globals_Join Ctx_None
                       Program_Globals_Flow_Sensitive"
    by (simp add: contradiction_report_def)
  then have empty: "\<lbrakk>contradiction_report v\<rbrakk>\<^bsub>v\<^esub> = {}"
    using mcp_contradiction_no_store by (auto simp: rows report_gamma_def activation_id)
  show ?thesis
  proof
    assume "exact_emptiness (DEAD (contradiction_report v)) (report_sem (contradiction_report v))"
    from exact_emptinessD [OF this, of v] live empty show False by simp
  qed
qed

text \<open>A check printed dead is one presentation of a dead point.\<close>

lemma analysis_report_check_dead:
  assumes "consistent_report res" and "c \<in> set (report_checks res)"
    and "check_verdict c = Dead"
  shows "DEAD res (check_point c)"
proof -
  have "aggregate_verdicts
          (classify_point (report_classify res) (check_exp c) ` report_states_at res (check_point c))
        = Dead"
    using assms unfolding consistent_report_def by auto
  then have "\<forall>d \<in> report_states_at res (check_point c).
               classify_point (report_classify res) (check_exp c) d = Dead"
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
    unfolding HAS_VERDICT_def report_checks_at_def by blast
  have "\<forall>d \<in> report_states_at res v. classify_point (report_classify res) (check_exp c) d = Dead"
    using dead unfolding DEAD_def by auto
  then have "aggregate_verdicts
               (classify_point (report_classify res) (check_exp c) ` report_states_at res v) = Dead"
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

lemma report_states_at_report_of:
  assumes fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
  shows "report_states_at (report_of config ctx_key ctx_tag classify sr p) v
           = lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
proof -
  define r where "r = run_table sr"
  define ctxs where "ctxs = ordered_by_key ctx_key (snd ` covered_keys r)"
  define nodes where "nodes = cfg_node_list (prog_cfg p)
    @ sorted_list_of_set (fst ` covered_keys r - set (cfg_node_list (prog_cfg p)))"
  have ctxs: "set ctxs = snd ` covered_keys r"
    unfolding ctxs_def r_def
    by (rule ordered_by_key_set) (use fin inj in \<open>auto intro: inj_on_subset\<close>)
  have nodes: "w \<in> set nodes" if "(w, ctx) \<in> covered_keys r" for w ctx
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
    fix d
    assume "d \<in> report_states_at (report_of config ctx_key ctx_tag classify sr p) v"
    then show "d \<in> lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
      unfolding report_states_at_def report_of_def Let_def by (auto simp: table_contexts_iff)
  next
    fix d
    assume "d \<in> lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
    then obtain ctx where cov: "(v, ctx) \<in> covered_keys r"
      and d: "d = lookup_table r v ctx"
      by (auto simp: r_def table_contexts_iff)
    from cov ctxs have "ctx \<in> set ctxs" by force
    then obtain i where i: "(i, ctx) \<in> set (enumerate 0 ctxs)" using indexed by blast
    have w: "v \<in> set nodes" using nodes[OF cov] .
    show "d \<in> report_states_at (report_of config ctx_key ctx_tag classify sr p) v"
      unfolding report_states_at_def report_of_def Let_def r_def[symmetric] ctxs_def[symmetric]
        nodes_def[symmetric]
      apply (simp only: analysis_report.select_convs)
      apply (rule image_eqI[rotated], rule CollectI, rule conjI, rule row_in_rows[OF i w])
      using cov d by (simp_all add: r_def)
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
   \<and> (\<forall>d \<in> set (report_diagnostics res). diagnostic_verdict d = Check_Refuted
        \<longrightarrow> (\<forall>s \<in> \<lbrakk>res\<rbrakk>\<^bsub>diagnostic_point d\<^esub>.
              \<not> truthy (\<lbrakk>arithmetic_condition (diagnostic_obligation d)\<rbrakk>\<^sub>e s)))
   \<and> map (\<lambda>c. (check_point c, check_label c, check_exp c)) (report_checks res)
       = check_sites (prog_cfg p)"

lemma report_of_sound:
  assumes cov: "covered_table p (run_table sr) gm"
    and fin: "finite (covered_keys (run_table sr))" and inj: "inj ctx_key"
    and cl: "classify = mcp_classify (activation (config_analyses config))"
    and gm: "gm = mcp_gamma_v (activation (config_analyses config))"
  shows "sound_report p (report_of config ctx_key ctx_tag classify sr p)"
proof -
  have st: "sound_table p (run_table sr) classify gm"
    by (rule sound_table.intro [OF cov]) (unfold cl gm, rule mcp_sound_classifier)
  let ?res = "report_of config ctx_key ctx_tag classify sr p"
  note rows = report_states_at_report_of[OF fin inj]
  have cons: "consistent_report ?res"
    unfolding consistent_report_def
    by (auto simp: result_checks_of_def point_verdict_def rows report_classify_def cl image_comp
        comp_def)
  have covers: "s \<in> \<lbrakk>?res\<rbrakk>\<^bsub>v\<^esub>"
    if "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v" for v s
  proof -
    from covered_table.covers[OF cov that] obtain ctx d
      where look: "lookup_table (run_table sr) v ctx = Lifted d" and s: "s \<in> gm d"
      unfolding table_covers_def by blast
    then have "Lifted d \<in> report_states_at ?res v"
      unfolding rows by (metis image_eqI lookup_table_LiftedD)
    with s show ?thesis by (auto simp: report_gamma_def gm)
  qed
  have safe: "arithmetic_safe_at (prog_cfg p) v s"
    if "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
      and "\<forall>d \<in> set (report_diagnostics ?res). diagnostic_point d \<noteq> v" for v s
    using sound_table.arithmetic_safe[OF st _ that(1)] that(2) by simp
  have refuted: "\<not> truthy (\<lbrakk>arithmetic_condition (diagnostic_obligation d)\<rbrakk>\<^sub>e s)"
    if d: "d \<in> set (report_diagnostics ?res)" and r: "diagnostic_verdict d = Check_Refuted"
      and s: "s \<in> \<lbrakk>?res\<rbrakk>\<^bsub>diagnostic_point d\<^esub>" for d s
  proof -
    let ?e = "arithmetic_condition (diagnostic_obligation d)"
    have pv: "point_verdict (run_table sr) classify (diagnostic_point d) ?e = Decided Check_Refuted"
      using arithmetic_diagnostics_refuted d r by simp
    from s obtain st where row: "Lifted st \<in> report_states_at ?res (diagnostic_point d)"
      and sg: "s \<in> report_gamma ?res st"
      by (rule report_semE)
    then obtain ctx where "lookup_table (run_table sr) (diagnostic_point d) ctx = Lifted st"
      unfolding rows by force
    then have "classify ?e st = Check_Refuted"
      by (rule point_verdict_decided[OF pv, rotated]) simp
    with sg show ?thesis
      unfolding cl report_gamma_def report_of_simps by (blast dest: mcp_classify_refuted)
  qed
  show ?thesis
    unfolding sound_report_def
    using cons covers safe refuted by (auto simp: result_checks_of_sites)
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
  case (Analysis_Config as r ctx pg)
  show ?thesis
  proof (cases ctx)
    case Ctx_None
    show ?thesis
    proof (cases pg)
      case Program_Globals_Flow_Sensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_rule.equations as (declared_global p) p)
                (mcp_rule.root_query p) = Some sol"
        and res: "res = report_of config (\<lambda>_. Key_List []) (\<lambda>_. Report_Unit)
                    (mcp_classify (activation as))
                    (mcp_rule.solved_run_of as (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_None Program_Globals_Flow_Sensitive
          dg_pipeline.root_query_def
            mcp_wrappers mcp_place_defs)
      note run = mcp_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ _ _ refl])
           (use mcp_rule_table[OF wf run(1)] mcp_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def inj_def\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_split_rule.equations as (declared_global p) p)
                (mcp_split_rule.root_query p) = Some sol"
        and res: "res = report_of config (\<lambda>_. Key_List []) (\<lambda>_. Report_Unit)
                    (mcp_classify (activation as))
                    (mcp_split_rule.solved_run_of as (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_None Program_Globals_Flow_Insensitive
          dg_pipeline.root_query_def
            mcp_wrappers mcp_place_defs)
      note run = mcp_split_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ _ _ refl])
           (use mcp_split_rule_table[OF wf run(1)]
              mcp_split_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def inj_def\<close>)
    qed
  next
    case Ctx_EntryState
    show ?thesis
    proof (cases pg)
      case Program_Globals_Flow_Sensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_es_rule.equations as (declared_global p) p)
                (mcp_es_rule.root_query p) = Some sol"
        and res: "res = report_of config (entry_ctx_key (activation as)) Report_Entry
                    (mcp_classify (activation as))
                    (mcp_es_rule.solved_run_of as (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_EntryState Program_Globals_Flow_Sensitive
            dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
      note run = mcp_es_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ inj_entry_ctx_key _ refl])
           (use mcp_es_rule_table[OF wf run(1)] mcp_es_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_split_es_rule.equations as (declared_global p) p)
                (mcp_split_es_rule.root_query p) = Some sol"
        and res: "res = report_of config (entry_ctx_key (activation as)) Report_Entry
                    (mcp_classify (activation as))
                    (mcp_split_es_rule.solved_run_of as (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_EntryState Program_Globals_Flow_Insensitive
            dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
      note run = mcp_split_es_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ inj_entry_ctx_key _ refl])
           (use mcp_split_es_rule_table[OF wf run(1)]
              mcp_split_es_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def\<close>)
    qed
  next
    case (Ctx_CallString k)
    show ?thesis
    proof (cases pg)
      case Program_Globals_Flow_Sensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_cs_rule.equations as k (declared_global p) p)
                (mcp_cs_rule.root_query p) = Some sol"
        and res: "res = report_of config (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
                    (mcp_classify (activation as))
                    (mcp_cs_rule.solved_run_of as k (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_CallString Program_Globals_Flow_Sensitive
            dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
      note run = mcp_cs_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ inj_call_string_key _ refl])
           (use mcp_cs_rule_table[OF wf run(1)] mcp_cs_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def\<close>)
    next
      case Program_Globals_Flow_Insensitive
      from some obtain sol where
        sol: "TD_side_rule_Interp_solve_c r (mcp_split_cs_rule.equations as k (declared_global p) p)
                (mcp_split_cs_rule.root_query p) = Some sol"
        and res: "res = report_of config (\<lambda>ctx. Key_List (map Key_Node ctx)) Report_Call_String
                    (mcp_classify (activation as))
                    (mcp_split_cs_rule.solved_run_of as k (declared_global p) p sol) p"
        by (auto simp: Analysis_Config Ctx_CallString Program_Globals_Flow_Insensitive
            dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
      note run = mcp_split_cs_rule.solve_c_run[OF sol]
      show ?thesis
        unfolding res run(2)
        by (rule report_of_sound[OF _ _ inj_call_string_key _ refl])
           (use mcp_split_cs_rule_table[OF wf run(1)]
              mcp_split_cs_rule.vars_finite_of_terminates[OF run(1)] in
             \<open>simp_all add: Analysis_Config finite_solved_table_def dg_pipeline.result_def
                dg_pipeline.sol_vars_def\<close>)
    qed
  qed
qed

subsection \<open>A well-formed report\<close>

text \<open>
  What a reader of the report relies on beyond its verdicts: every context index
  names a listed context, a point has at most one row per context, and a row's check
  and obligation columns list exactly the report's checks and the graph's arithmetic
  obligations at the row's point, each with the verdict of the row's own state. No
  soundness theorem needs this; a renderer does.
\<close>

definition obligations_at :: "cfg \<Rightarrow> pp \<Rightarrow> arithmetic_obligation list" where
  "obligations_at g v = concat (map snd (filter (\<lambda>(u, obs). u = v) (arithmetic_sites g)))"

lemma group_lookup_arithmetic_sites:
  "concat (group_lookup (group_by_key fst (Some \<circ> snd) (arithmetic_sites g)) v)
     = obligations_at g v"
proof -
  have "List.map_filter (\<lambda>x. if fst x = v then (Some \<circ> snd) x else None) xs
          = map snd (filter (\<lambda>(u, obs). u = v) xs)"
    for xs :: "(pp \<times> arithmetic_obligation list) list"
    by (induction xs) (auto simp: List.map_filter_simps)
  then show ?thesis unfolding group_lookup_group_by_key obligations_at_def by simp
qed

definition well_formed_report :: "analysis_report \<Rightarrow> bool" where
  "well_formed_report res \<longleftrightarrow>
     (\<forall>st \<in> set (report_states res). state_context st < length (report_contexts res))
   \<and> distinct (map (\<lambda>st. (state_point st, state_context st)) (report_states res))
   \<and> (\<forall>rt \<in> set (report_routes res).
        route_context rt < length (report_contexts res)
      \<and> (\<forall>i \<in> set (route_targets rt). i < length (report_contexts res)))
   \<and> (\<forall>st \<in> set (report_states res).
        state_checks st
          = map (\<lambda>c. (check_exp c,
                       classify_point (report_classify res) (check_exp c) (state_value st)))
              (filter (\<lambda>c. check_point c = state_point st) (report_checks res))
      \<and> state_diagnostics st
          = map (\<lambda>ob. (ob,
                        classify_point (report_classify res) (arithmetic_condition ob)
                          (state_value st)))
              (obligations_at (report_cfg res) (state_point st)))"

text \<open>
  With a consistent report, the check column is the aggregate of the rows: a check's
  verdict joins the verdicts the rows at its point give its condition.
\<close>

lemma well_formed_check_verdict:
  assumes cons: "consistent_report res" and wf: "well_formed_report res"
    and c: "c \<in> set (report_checks res)"
  shows "check_verdict c
           = aggregate_verdicts
               {verdict | st verdict. st \<in> set (report_states res)
                  \<and> state_point st = check_point c \<and> (check_exp c, verdict) \<in> set (state_checks st)}"
proof -
  let ?cl = "classify_point (report_classify res) (check_exp c)"
  have rows: "state_checks st
                = map (\<lambda>c. (check_exp c, classify_point (report_classify res) (check_exp c)
                                           (state_value st)))
                    (filter (\<lambda>c'. check_point c' = state_point st) (report_checks res))"
    if "st \<in> set (report_states res)" for st
    using wf that unfolding well_formed_report_def by blast
  have "{verdict | st verdict. st \<in> set (report_states res)
           \<and> state_point st = check_point c \<and> (check_exp c, verdict) \<in> set (state_checks st)}
          = ?cl ` report_states_at res (check_point c)"
  proof (intro equalityI subsetI)
    fix x
    assume "x \<in> {verdict | st verdict. st \<in> set (report_states res)
              \<and> state_point st = check_point c \<and> (check_exp c, verdict) \<in> set (state_checks st)}"
    then obtain st where st: "st \<in> set (report_states res)" and pt: "state_point st = check_point c"
      and mem: "(check_exp c, x) \<in> set (state_checks st)" by blast
    from mem rows[OF st] have "x = ?cl (state_value st)" by auto
    with st pt show "x \<in> ?cl ` report_states_at res (check_point c)"
      unfolding report_states_at_def by blast
  next
    fix x
    assume "x \<in> ?cl ` report_states_at res (check_point c)"
    then obtain st where st: "st \<in> set (report_states res)" and pt: "state_point st = check_point c"
      and x: "x = ?cl (state_value st)"
      unfolding report_states_at_def by blast
    have "(check_exp c, x) \<in> set (state_checks st)"
      unfolding rows[OF st] using c pt x by force
    with st pt show "x \<in> {verdict | st verdict. st \<in> set (report_states res)
              \<and> state_point st = check_point c \<and> (check_exp c, verdict) \<in> set (state_checks st)}"
      by blast
  qed
  with cons c show ?thesis unfolding consistent_report_def by simp
qed

lemma distinct_indexed_rows:
  "distinct ns
     \<Longrightarrow> distinct (concat (map (\<lambda>(i, x). map (\<lambda>v. (v, i)) (filter (\<lambda>v. P v x) ns))
                         (enumerate n xs)))"
proof (induction xs arbitrary: n)
  case (Cons x xs)
  have "n < i" if "(w, i) \<in> set (concat (map (\<lambda>(i, x). map (\<lambda>v. (v, i)) (filter (\<lambda>v. P v x) ns))
                                  (enumerate (Suc n) xs)))" for w i
    using that by (auto simp: in_set_enumerate_eq)
  with Cons.IH[of "Suc n"] Cons.prems show ?case
    by (fastforce simp: distinct_map inj_on_def)
qed simp

lemma map_check_exp_result_checks_of:
  "map check_exp (filter (\<lambda>c. check_point c = v) (result_checks_of g r classify))
     = group_lookup (group_by_key (\<lambda>(u, a, w). u)
         (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a) else None) (cfg_intra_list g)) v"
proof -
  have "map check_exp (filter (\<lambda>c. check_point c = v)
          (map (\<lambda>(u, a, w). \<lparr> check_point = u, check_label = ea_check_label a,
                                check_exp = ea_check_cond a, check_verdict = V u a \<rparr>)
             (filter (\<lambda>(u, a, w). is_EA_Check a) es)))
        = List.map_filter (\<lambda>x. if (\<lambda>(u, a, w). u) x = v
                                then (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a)
                                                  else None) x
                                else None) es" for es V
    by (induction es) (auto simp: List.map_filter_simps)
  then show ?thesis
    unfolding result_checks_of_def group_lookup_group_by_key .
qed

lemma report_of_well_formed:
  assumes cl: "classify = mcp_classify (activation (config_analyses config))"
  shows "well_formed_report (report_of config ctx_key ctx_tag classify sr p)"
proof -
  let ?res = "report_of config ctx_key ctx_tag classify sr p"
  define r where "r = run_table sr"
  define g where "g = prog_cfg p"
  define ctxs where "ctxs = ordered_by_key ctx_key (snd ` covered_keys r)"
  define nodes where "nodes = cfg_node_list g
    @ sorted_list_of_set (fst ` covered_keys r - set (cfg_node_list g))"
  define checks where "checks = group_by_key (\<lambda>(u, a, w). u)
    (\<lambda>(u, a, w). if is_EA_Check a then Some (ea_check_cond a) else None) (cfg_intra_list g)"
  define obls where "obls = group_by_key fst (Some \<circ> snd) (arithmetic_sites g)"
  define steps where "steps = group_by_key (\<lambda>(u, a, w). u) (\<lambda>(u, a, w). Some (a, w))
    (cfg_intra_list g)"
  have classify: "report_classify ?res = classify"
    by (simp add: report_classify_def cl)
  have contexts: "length (report_contexts ?res) = length ctxs"
    by (simp add: report_of_def Let_def ctxs_def r_def)
  have states: "report_states ?res
    = concat (map (\<lambda>(i, ctx). map (report_row sr classify checks obls steps i ctx)
                                 (filter (\<lambda>v. (v, ctx) \<in> covered_keys r) nodes))
                (enumerate 0 ctxs))"
    by (simp add: report_of_def Let_def ctxs_def r_def nodes_def g_def checks_def obls_def
                  steps_def)
  have in_range: "state_context st < length ctxs" if "st \<in> set (report_states ?res)" for st
    using that by (auto simp: states in_set_enumerate_eq)
  have "distinct (cfg_node_list g)" by (simp add: cfg_node_list_def)
  then have "distinct nodes"
    unfolding nodes_def by (cases "finite (fst ` covered_keys r - set (cfg_node_list g))") auto
  then have distinct:
    "distinct (map (\<lambda>st. (state_point st, state_context st)) (report_states ?res))"
    using distinct_indexed_rows[of nodes "\<lambda>v ctx. (v, ctx) \<in> covered_keys r" 0 ctxs]
    by (simp add: states map_concat case_prod_unfold comp_def)
  have routes: "route_context rt < length ctxs \<and> (\<forall>i \<in> set (route_targets rt). i < length ctxs)"
    if "rt \<in> set (report_routes ?res)" for rt
    using that
    by (auto simp: report_of_def Let_def ctxs_def r_def context_indices_def in_set_enumerate_eq
             split: lifted.splits)
  have rows: "state_checks st
                = map (\<lambda>c. (check_exp c, classify_point classify (check_exp c) (state_value st)))
                    (filter (\<lambda>c. check_point c = state_point st) (report_checks ?res))
              \<and> state_diagnostics st
                  = map (\<lambda>ob. (ob, classify_point classify (arithmetic_condition ob)
                                     (state_value st)))
                      (obligations_at g (state_point st))"
    if "st \<in> set (report_states ?res)" for st
  proof -
    from that obtain i ctx v where st: "st = report_row sr classify checks obls steps i ctx v"
      by (auto simp: states)
    have "map check_exp (filter (\<lambda>c. check_point c = v) (report_checks ?res))
            = group_lookup checks v" (is "map check_exp ?cs = _")
      by (simp add: map_check_exp_result_checks_of checks_def g_def)
    moreover have "map (\<lambda>c. (check_exp c, classify_point classify (check_exp c) (lookup_table r v ctx)))
                     ?cs
                   = map (\<lambda>cond. (cond, classify_point classify cond (lookup_table r v ctx)))
                       (map check_exp ?cs)"
      by simp
    ultimately have "map (\<lambda>c. (check_exp c, classify_point classify (check_exp c) (lookup_table r v ctx)))
                       ?cs
                     = map (\<lambda>cond. (cond, classify_point classify cond (lookup_table r v ctx)))
                         (group_lookup checks v)"
      by simp
    moreover have "concat (group_lookup obls v) = obligations_at g v"
      unfolding obls_def by (rule group_lookup_arithmetic_sites)
    ultimately show ?thesis unfolding st by (auto simp: report_row_def Let_def r_def)
  qed
  have cfg: "report_cfg ?res = g" by (simp add: g_def)
  show ?thesis
    unfolding well_formed_report_def classify contexts cfg
    using in_range distinct routes rows by blast
qed

lemma analysis_report_of_well_formed:
  "analysis_report_of config p = Some res \<Longrightarrow> well_formed_report res"
  by (induct config p rule: analysis_report_of.induct) (auto intro: report_of_well_formed)

end
