theory Analysis_Run_Sound
  imports Analysis_Run
begin

section \<open>What a configuration's table owes its report\<close>

text \<open>
  Every configuration hands the table its registration solved to
  \<^const>\<open>report_of\<close>, which takes the check column from one call of
  \<^const>\<open>classify_checks_verdicts\<close> and the diagnostics from one call of
  \<^const>\<open>arithmetic_diagnostics\<close> over that table. So one argument serves every
  configuration.

  The argument asks two things of the table, bundled as \<open>covered_table\<close>. A
  store the program reaches at a point lies in the entry the table filed there under
  \<^emph>\<open>some\<close> context (\<open>table_covers\<close>), and a point has finitely many contexts.
  Of the classifier it asks soundness in both directions (\<open>sound_classifier\<close>),
  which does not depend on the table and is proved once for the combined state.
  Given both, the report built from the table is sound; the theory
  \<open>Analysis_Report\<close> states how. The context-free
  configuration's table is the instance at the end of this theory; the contextual
  ones follow in the theory after it.
\<close>

subsection \<open>Every check column is a contextual verdict report\<close>

lemma finite_intra_prog_cfg [simp]: "finite (intra (prog_cfg p))"
  unfolding prog_cfg_def using compile_prog_finite by simp

text \<open>
  Forgetting the labels, the check column is the contextual verdict report itself.
\<close>

lemma result_checks_of_verdicts:
  "map (\<lambda>chk. (check_point chk, check_exp chk, check_verdict chk)) (result_checks_of g r classify)
     = classify_checks_verdicts g r classify"
  unfolding result_checks_of_def classify_checks_verdicts_def classify_checks_ctx_def
    point_verdict_def
  by (simp add: comp_def case_prod_beta image_image)

text \<open>
  Where a result has checks: one per compiled \<^const>\<open>EA_Check\<close> edge, at that edge's
  source node and with its label and condition, in the order the graph lists its edges.
\<close>

definition check_sites :: "cfg \<Rightarrow> (pp \<times> check_label \<times> exp) list" where
  "check_sites g =
     map (\<lambda>(u, a, v). (u, ea_check_label a, ea_check_cond a))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

lemma result_checks_of_sites:
  "map (\<lambda>chk. (check_point chk, check_label chk, check_exp chk)) (result_checks_of g r classify)
     = check_sites g"
  unfolding result_checks_of_def check_sites_def
  by (simp add: comp_def case_prod_beta)

lemma check_sites_memI [intro]:
  assumes "finite (intra g)" and "(v, EA_Check l cnd, w) \<in> intra g"
  shows "(v, l, cnd) \<in> set (check_sites g)"
  using assms unfolding check_sites_def by force

subsection \<open>A store that reaches a point sits in one of that point's contexts\<close>

text \<open>
  The table claim at a point is existential in the context: a store is described
  by the entry filed under \<^emph>\<open>some\<close> context the point was solved at --- one its
  own call history is admitted at --- and in general not by every such entry,
  since another activation's entry need not describe this store at all.
\<close>

definition table_covers ::
    "('v \<Rightarrow> store set) \<Rightarrow> ('c, 'v) solved_table \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "table_covers gm r v s \<longleftrightarrow> (\<exists>ctx st. lookup_table r v ctx = Lifted st \<and> s \<in> gm st)"

lemma table_coversI [intro]:
  "lookup_table r v ctx = Lifted st \<Longrightarrow> s \<in> gm st \<Longrightarrow> table_covers gm r v s"
  unfolding table_covers_def by blast

text \<open>
  The published contextual soundness bounds one activation bucket by the table
  entry filed under that bucket's context. A caller holding a store knows only
  that the store reaches the point at all, so it needs the buckets to exhaust
  the point --- the union direction, which is where a context policy pays for
  being total. Both readings are settled in
  \<^theory>\<open>Voblint_CFG.Activation_Trace_Collect\<close>: a functional policy has the union outright,
  a relational one --- such as the entry-state policy --- earns it from the
  existence of a context for every valid activation trace. \<^const>\<open>Bot\<close> cannot be the entry
  found, since it concretizes to no store at all.
\<close>

lemma lookup_table_covers_of_activation:
  fixes r :: "('c, 'v) solved_table"
  assumes union: "\<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> (\<Union>c. \<A>\<^bsub>\<G>,R,rc,g,S\<^esub> v c)"
      and sound: "\<And>ctx. \<A>\<^bsub>\<G>,R,rc,g,S\<^esub> v ctx
                    \<subseteq> gamma_lift gm (lookup_table r v ctx)"
      and mem: "s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"
  obtains ctx st where "s \<in> \<A>\<^bsub>\<G>,R,rc,g,S\<^esub> v ctx"
    and "lookup_table r v ctx = Lifted st" and "s \<in> gm st"
proof -
  from mem union obtain ctx where a: "s \<in> \<A>\<^bsub>\<G>,R,rc,g,S\<^esub> v ctx" by blast
  with sound have g: "s \<in> gamma_lift gm (lookup_table r v ctx)" by blast
  show ?thesis
  proof (cases "lookup_table r v ctx")
    case Bot
    with g show ?thesis by simp
  next
    case (Lifted st)
    with g a show ?thesis by (intro that [of ctx st]) simp_all
  qed
qed

subsection \<open>The table contract and the classifier contract\<close>

text \<open>
  What a configuration's table has to satisfy for its report to be sound. Each
  configuration below and in the theory after this one is an instance of
  \<open>covered_table\<close>, and owes nothing but two facts: the table exhausts the
  reachable stores, over finitely many contexts per point. The classifier owes
  soundness in both directions (\<open>sound_classifier\<close>); \<open>sound_table\<close> is the two
  together.
\<close>

definition arithmetic_safe_at :: "cfg \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "arithmetic_safe_at g v s \<longleftrightarrow>
     (\<forall>es. (v, es) \<in> set (arithmetic_expression_sites g) \<longrightarrow>
       (\<forall>e \<in> set es. \<forall>divisor \<in> expression_divisors e. \<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0))"

text \<open>
  A solved table \<open>r\<close> covers program \<open>p\<close>: every store the collecting semantics
  reaches at \<open>v\<close> lies in \<open>gm\<close> of the state \<open>r\<close> holds at \<open>v\<close> in
  some context, and each point has finitely many contexts.
\<close>
locale covered_table =
  fixes p :: imp_prog
    and r :: "('c, 'v) solved_table"
    and gm :: "'v \<Rightarrow> store set"
  assumes finite_contexts: "\<And>v. finite (table_contexts r v)"
      and covers: "\<And>v s. s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v
                      \<Longrightarrow> table_covers gm r v s"

text \<open>
  \<open>classify\<close> is sound for \<open>gm\<close>: \<open>Check_Proved\<close> means the condition holds at
  every store in \<open>gm d\<close>, \<open>Check_Refuted\<close> that it fails at every one.
\<close>
locale sound_classifier =
  fixes classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result"
    and gm :: "'v \<Rightarrow> store set"
  assumes proved: "\<And>cnd d t. classify cnd d = Check_Proved \<Longrightarrow> t \<in> gm d
                      \<Longrightarrow> truthy (\<lbrakk>cnd\<rbrakk>\<^sub>e t)"
      and refuted: "\<And>cnd d t. classify cnd d = Check_Refuted \<Longrightarrow> t \<in> gm d
                      \<Longrightarrow> \<not> truthy (\<lbrakk>cnd\<rbrakk>\<^sub>e t)"

lemma mcp_sound_classifier: "sound_classifier (mcp_classify as) (mcp_gamma_v as)"
  by unfold_locales (fact mcp_classify_proved, fact mcp_classify_refuted)

text \<open>
  A covered table read through a sound classifier. Inside it, verdicts and
  diagnostics computed from \<open>r\<close> hold at every collected store.
\<close>
locale sound_table = covered_table p r gm + sound_classifier classify gm
  for p :: imp_prog and r :: "('c, 'v) solved_table"
    and classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result" and gm :: "'v \<Rightarrow> store set"
begin

text \<open>
  A point the arithmetic diagnostics do not name is safe at every store the
  collecting semantics admits there: no divisor evaluated at it is zero.
\<close>

lemma arithmetic_safe:
  assumes absent: "\<forall>d \<in> set (arithmetic_diagnostics (prog_cfg p) r classify).
      diagnostic_point d \<noteq> v"
    and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
proof -
  from covers[OF mem] obtain ctx st where
    look: "lookup_table r v ctx = Lifted st" and gst: "s \<in> gm st"
    unfolding table_covers_def by blast
  have safe: "\<And>es e divisor. (v, es) \<in> set (arithmetic_expression_sites (prog_cfg p)) \<Longrightarrow>
      e \<in> set es \<Longrightarrow> divisor \<in> expression_divisors e \<Longrightarrow> \<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0"
  proof -
    fix es e divisor
    assume site: "(v, es) \<in> set (arithmetic_expression_sites (prog_cfg p))"
      and expr: "e \<in> set es" and div: "divisor \<in> expression_divisors e"
    obtain obligations obligation where
      obs: "(v, obligations) \<in> set (arithmetic_sites (prog_cfg p))"
      and ob: "obligation \<in> set obligations"
      and divisor: "arithmetic_divisor obligation = divisor"
      by (rule arithmetic_sites_divisor[OF site expr div])
    have verdict: "point_verdict r classify v (arithmetic_condition obligation)
                     = Lifted Check_Proved"
      using arithmetic_diagnostics_absent[OF obs ob absent]
        point_verdict_not_dead[OF finite_contexts look, of classify]
      by blast
    have classified: "classify (arithmetic_condition obligation) st = Check_Proved"
      by (rule point_verdict_decided[OF verdict _ look]) simp
    from proved[OF classified gst] show "\<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0"
      by (auto simp: arithmetic_condition_def divisor split: if_splits)
  qed
  show ?thesis unfolding arithmetic_safe_at_def using safe by blast
qed

end

text \<open>
  The shape every registration publishes its soundness in: each activation bucket
  is bounded by the entry filed under its context, and the buckets exhaust the point.
\<close>

lemma covered_table_of_activation:
  fixes r :: "('c, 'v) solved_table"
  assumes union: "\<And>u. \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> u
                    \<subseteq> (\<Union>c. \<A>\<^bsub>declared_global p,R,rc,prog_cfg p,
                                cinit_stores (declared_global p)\<^esub> u c)"
      and sound: "\<And>u ctx. \<A>\<^bsub>declared_global p,R,rc,prog_cfg p,
                              cinit_stores (declared_global p)\<^esub> u ctx
                    \<subseteq> gamma_lift gm (lookup_table r u ctx)"
      and fin: "finite_solved_table r"
  shows "covered_table p r gm"
proof (rule covered_table.intro)
  show "finite (table_contexts r v)" for v by (rule finite_table_contexts [OF fin])
  show "table_covers gm r v s"
    if "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    for v s
    by (meson lookup_table_covers_of_activation [OF union sound that] table_coversI)
qed

subsection \<open>The context-free configuration\<close>

text \<open>
  The unit registration keys every activation at the one context \<open>()\<close>, a
  function of the call site and the caller's context, so the buckets exhaust a point
  outright and each is bounded by its entry.
\<close>

lemma mcp_rule_table:
  assumes wf: "wf_program_compile_input p"
    and cov: "mcp_rule.terminates as r (declared_global p) p"
  shows "covered_table p (mcp_rule.result as r (declared_global p) p)
           (mcp_gamma_v (activation as))"
proof (rule covered_table_of_activation
    [where R = "call_context_rel_of_fun (\<lambda>u c t. ())" and rc = "()"], goal_cases)
  case (1 u)
  show ?case
    by (rule equalityD1
      [OF mcp_rule.fun_route_node_collect_eq_Union [where ctx_fun = "\<lambda>u c t. ()"]])
next
  case (2 u ctx)
  show ?case
    using mcp_rule.fun_route_activation_collect_sound_of_terminates [OF _ wf cov]
    unfolding mcp_rule.gamma_reader_eq_lookup by (simp add: route_unit_def)
next
  case 3
  show ?case
    using mcp_rule.vars_finite_of_terminates [OF cov]
    by (simp add: finite_solved_table_def dg_pipeline.result_def
        dg_pipeline.sol_vars_def)
qed

end
