theory Analysis_Report
  imports Analysis_Render
begin

section \<open>What a report claims\<close>

text \<open>
  A report is read point by point: the states it holds at a point, one per context it
  was solved at, the verdicts of the checks it records there, and the arithmetic
  diagnostics it names there. The vocabulary below takes any report, whatever its
  expressions and states; only the evaluator that says what a condition means at a
  store is the language's.
\<close>

subsection \<open>The states a report holds\<close>

definition report_states_at :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 's lifted set"
  where
  "report_states_at res v = state_value ` {st \<in> set (report_states res). state_point st = v}"

lemma finite_report_states_at [simp]: "finite (report_states_at res v)"
  by (simp add: report_states_at_def)

subsection \<open>Verdicts\<close>

text \<open>\<open>report_checks_at\<close> selects the checks a report records at one program point.\<close>

definition report_checks_at ::
    "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 'e result_check set" where
  "report_checks_at res v = {c \<in> set (report_checks res). check_point c = v}"

lemma mem_report_checks_at [simp]:
  "c \<in> report_checks_at res v \<longleftrightarrow> c \<in> set (report_checks res) \<and> check_point c = v"
  by (simp add: report_checks_at_def)

text \<open>
  What a decided verdict says about a store, under an evaluator \<open>ev\<close>:
  \<open>Check_Proved\<close> that the condition holds, \<open>Check_Refuted\<close> that it fails,
  \<open>Check_Unknown\<close> nothing.
\<close>

fun verdict_holds :: "('e \<Rightarrow> 't \<Rightarrow> int) \<Rightarrow> check_result \<Rightarrow> 'e \<Rightarrow> 't \<Rightarrow> bool" where
  "verdict_holds ev Check_Proved e s = truthy (ev e s)"
| "verdict_holds ev Check_Refuted e s = (\<not> truthy (ev e s))"
| "verdict_holds ev Check_Unknown e s = True"

text \<open>
  The stores a check's verdict admits. A \<open>Dead\<close> check claims nothing about stores;
  its claim, that the point is unreached, is \<open>DEAD\<close> below.
\<close>

definition check_stores :: "('e \<Rightarrow> 't \<Rightarrow> int) \<Rightarrow> 'e result_check \<Rightarrow> 't set" where
  "check_stores ev c = (case check_verdict c of
                          Decided r \<Rightarrow> {s. verdict_holds ev r (check_exp c) s}
                        | Dead \<Rightarrow> UNIV)"

text \<open>
  The verdict a report gives a condition at a point. \<open>PROVED res v c\<close> says the
  report proves check \<open>c\<close> at \<open>v\<close>: since a point may carry several checks, the
  condition names the one meant.
\<close>

definition HAS_VERDICT ::
    "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 'e \<Rightarrow> check_result \<Rightarrow> bool" where
  "HAS_VERDICT res v e r \<longleftrightarrow>
     (\<exists>c \<in> report_checks_at res v. check_exp c = e \<and> check_verdict c = Decided r)"

abbreviation PROVED :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 'e \<Rightarrow> bool" where
  "PROVED res v e \<equiv> HAS_VERDICT res v e Check_Proved"

abbreviation REFUTED :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 'e \<Rightarrow> bool" where
  "REFUTED res v e \<equiv> HAS_VERDICT res v e Check_Refuted"

abbreviation UNKNOWN :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> 'e \<Rightarrow> bool" where
  "UNKNOWN res v e \<equiv> HAS_VERDICT res v e Check_Unknown"

text \<open>
  \<open>DEAD\<close> is a property of a point, not of a condition: every state the report holds
  there is \<^const>\<open>Bot\<close>. The states are canonical --- the table they come from
  collapses a state its emptiness test rejects to \<^const>\<open>Bot\<close> --- so \<open>DEAD\<close> reads
  that canonical form instead of running a test.
\<close>

definition DEAD :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> bool" where
  "DEAD res v \<longleftrightarrow> (\<forall>d \<in> report_states_at res v. d = Bot)"

text \<open>
  \<open>SAFE\<close> says the report names no arithmetic diagnostic at a point. What that
  guarantees depends on which obligations the report was built to decide:
  \<open>run_voblint_SAFE\<close> states it for the obligations of core VIMP's expressions, and
  says nothing about a hazard the report does not check.
\<close>

abbreviation SAFE :: "('k, 'x, 'vr, 'e, 'n, 's) analysis_report \<Rightarrow> pp \<Rightarrow> bool" where
  "SAFE res v \<equiv> \<forall>d \<in> set (report_diagnostics res). diagnostic_point d \<noteq> v"

section \<open>A report built from a table\<close>

text \<open>Forgetting the labels, the check column is the contextual verdict report itself.\<close>

lemma result_checks_of_verdicts:
  "map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (result_checks_of g r classify)
     = classify_checks_verdicts g r classify"
  unfolding result_checks_of_def classify_checks_verdicts_def classify_checks_ctx_def
    point_verdict_def
  by (simp add: comp_def case_prod_beta image_image)

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
  shows "report_states_at (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr) v
           = lookup_table (run_table sr) v ` table_contexts (run_table sr) v"
proof -
  define r where "r = run_table sr"
  define ctxs where "ctxs = ordered_by_key ctx_key (snd ` covered_keys r)"
  define nodes where "nodes = cfg_node_list g
    @ sorted_list_of_set (fst ` covered_keys r - set (cfg_node_list g))"
  have ctxs: "set ctxs = snd ` covered_keys r"
    unfolding ctxs_def r_def
    by (rule ordered_by_key_set) (use fin inj in \<open>auto intro: inj_on_subset\<close>)
  have nodes: "w \<in> set nodes" if "(w, ctx) \<in> covered_keys r" for w ctx
  proof (cases "w \<in> set (cfg_node_list g)")
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
    assume "d \<in> report_states_at (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr) v"
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
    show "d \<in> report_states_at (report_of config vars g globals sites cond procs ctx_key ctx_tag classify sr) v"
      unfolding report_states_at_def report_of_def Let_def r_def[symmetric] ctxs_def[symmetric]
        nodes_def[symmetric]
      apply (simp only: analysis_report.select_convs)
      apply (rule image_eqI[rotated], rule CollectI, rule conjI, rule row_in_rows[OF i w])
      using cov d by (simp_all add: r_def)
  qed
qed

text \<open>A call string is listed in the order of the nodes it names.\<close>

lemma inj_call_string_key: "inj (\<lambda>ctx. Key_List (map Key_Node ctx))"
  by (rule injI) (simp add: inj_def)

end
