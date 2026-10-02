theory Analysis_Certified
  imports Analysis_Report
begin

section \<open>What an analysis report guarantees about the program\<close>

text \<open>
  \<^const>\<open>run_voblint\<close> answers every configuration. Its analysed answer is a report
  that the theorems below read through \<open>\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>\<close>, \<open>verdict_stores\<close> and the CAPS
  queries, and nothing else: no premise asks for termination, coverage of the solve or
  well-formedness, since an analysed answer was only given for a well-formed program
  whose solve the executable solver completed.
\<close>

subsection \<open>An analysed answer is a sound report\<close>

lemma run_voblint_AnalysedE [elim]:
  assumes "run_voblint config p = Analysed res"
  obtains "wf_program_compile_input_exec p" and "analysis_report_of config p = Some res"
  using assms unfolding run_voblint_def by (auto split: if_splits option.splits)

theorem run_voblint_sound:
  assumes "run_voblint config p = Analysed res"
  shows "sound_report p res"
  using assms
  by (auto intro: analysis_report_of_sound wf_program_compile_input_exec_sound)

lemma run_voblint_consistent:
  "run_voblint config p = Analysed res \<Longrightarrow> consistent_report res"
  using run_voblint_sound unfolding sound_report_def by blast

theorem run_voblint_covers:
  assumes "run_voblint config p = Analysed res"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
  using run_voblint_sound[OF assms] unfolding sound_report_def by blast

text \<open>
  Every store the program reaches at a point lies in the report's semantics there,
  and so in its verdict semantics.
\<close>

corollary run_voblint_collect_sound:
  assumes "run_voblint config p = Analysed res"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v
           \<subseteq> verdict_stores res v"
  using run_voblint_covers[OF assms]
    analysis_report_verdicts_sound[OF run_voblint_consistent[OF assms]]
  by blast

corollary run_voblint_proved:
  assumes "run_voblint config p = Analysed res" and "PROVED res v e"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using assms run_voblint_covers[OF assms(1)]
  using analysis_report_proved run_voblint_consistent by blast

corollary run_voblint_refuted:
  assumes "run_voblint config p = Analysed res" and "REFUTED res v e"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "\<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
  using assms run_voblint_covers[OF assms(1)]
  using analysis_report_refuted run_voblint_consistent by blast

corollary run_voblint_dead_unreached:
  assumes "run_voblint config p = Analysed res" and "DEAD res v"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v = {}"
  using run_voblint_covers[OF assms(1)] analysis_report_dead[OF assms(2)] by blast

corollary run_voblint_dead_check_unreached:
  assumes "run_voblint config p = Analysed res"
    and "chk \<in> set (report_checks res)" and "check_verdict chk = Dead"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> (check_point chk) = {}"
  using assms
  by (intro run_voblint_dead_unreached analysis_report_check_dead run_voblint_consistent)

theorem run_voblint_arithmetic_safe:
  assumes "run_voblint config p = Analysed res"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    and "\<forall>d \<in> set (report_diagnostics res). diagnostic_point d \<noteq> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
  using run_voblint_sound[OF assms(1)] assms(2,3) unfolding sound_report_def by blast

corollary run_voblint_arithmetic_intra_safe:
  assumes "run_voblint config p = Analysed res"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    and "\<forall>d \<in> set (report_diagnostics res). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (arithmetic_edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "\<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0"
  using run_voblint_arithmetic_safe[OF assms(1-3)]
    arithmetic_expression_sites_intra[OF finite_intra_prog_cfg assms(4)] assms(5,6)
  unfolding arithmetic_safe_at_def by blast

text \<open>
  Whatever the configuration, the report lists one check per compiled check, at the
  check's node and with its label and condition, in graph order.
\<close>

corollary run_voblint_check_sites:
  assumes "run_voblint config p = Analysed res"
  shows "map (\<lambda>chk. (check_point chk, check_label chk, check_exp chk)) (report_checks res)
           = check_sites (prog_cfg p)"
  using run_voblint_sound[OF assms] unfolding sound_report_def by blast

subsection \<open>The endpoint\<close>

text \<open>
  Run the source program, stop wherever you like, and ask any configuration for a
  report: there is a graph node and frame stack for where you stopped, the store in
  your hands is one the collecting semantics admits there, the report's semantics
  contains it, and every definite verdict the report gives there holds of it.
\<close>

theorem run_voblint_source_sound:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
  shows "\<exists>v stk. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> v
                 \<and> s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
                 \<and> s \<in> verdict_stores res v"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from ans have "wf_program_compile_input_exec p" by (rule run_voblint_AnalysedE)
  from source_reaches_node_collect
         [OF wf_program_compile_input_exec_sound [OF this] s0 [unfolded G_def]
             run [unfolded G_def Pi_def]]
  obtain v stk
    where m: "prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    unfolding cfg by blast
  with run_voblint_covers[OF ans] run_voblint_collect_sound[OF ans] show ?thesis
    unfolding G_def Pi_def g_def by blast
qed

text \<open>
  The same endpoint, read at a check. A run about to execute \<open>Check l e\<close> finds a
  check labelled \<open>l\<close> for \<open>e\<close> in the report, listed at a node this very store
  reaches, and that check's verdict holds of the store.
\<close>

theorem run_voblint_check_sound:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and chk: "next_check residual = Some (l, e)"
      and ans: "run_voblint config p = Analysed res"
  shows "\<exists>c \<in> set (report_checks res). check_label c = l \<and> check_exp c = e
           \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
proof -
  from run_voblint_source_sound [OF s0 [unfolded G_def] run [unfolded G_def Pi_def] ans]
  obtain v stk
    where m: "prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
      and sem: "s \<in> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>"
      and verdicts: "s \<in> verdict_stores res v"
    by blast
  from csim_next_check_edge [OF m chk]
  have "(v, l, e) \<in> set (check_sites (prog_cfg p))" by auto
  then obtain c
    where c: "c \<in> set (report_checks res)" and "check_point c = v"
      and "check_label c = l" and "check_exp c = e"
    unfolding run_voblint_check_sites [OF ans, symmetric] by auto
  moreover have "check_verdict c \<noteq> Dead"
  proof
    assume "check_verdict c = Dead"
    from analysis_report_check_dead[OF run_voblint_consistent[OF ans] c this]
    have "\<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> = {}" using \<open>check_point c = v\<close> analysis_report_dead by blast
    with sem show False by blast
  qed
  ultimately show ?thesis
    using mem verdicts unfolding verdict_stores_def G_def g_def by auto
qed

text \<open>
  Read by label, which is how a report finds a source check's row. When no two rows
  share a label, the row labelled \<open>l\<close> is the one the theorem above found, so its
  verdict holds of the store. Distinct labels are a premise rather than a fact about
  every report: a procedure called from several sites is compiled once, so its
  checks are listed once, but two source checks given the same label would share it.
  The premise is decidable on the report, so a consumer checks it before trusting a
  lookup. What stays outside this development is the label itself: that the parser
  wrote each check's own source position into it.
\<close>

corollary run_voblint_labelled_check_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "declared_global p, prog_table p
                  \<turnstile> (main_body (prog_table p), s0, [])
                    \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and chk: "next_check residual = Some (l, e)"
      and ans: "run_voblint config p = Analysed res"
      and distinct: "distinct (map check_label (report_checks res))"
  shows "\<exists>c \<in> set (report_checks res). check_label c = l"
    and "\<forall>c \<in> set (report_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
proof -
  from run_voblint_check_sound [OF s0 run chk ans]
  obtain c0 where c0: "c0 \<in> set (report_checks res)" "check_label c0 = l" "check_exp c0 = e"
    and v0: "check_verdict c0 \<noteq> Dead"
      "check_verdict c0 = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
      "check_verdict c0 = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
    by blast
  from c0 show "\<exists>c \<in> set (report_checks res). check_label c = l" by blast
  have inj: "inj_on check_label (set (report_checks res))"
    using distinct by (simp add: distinct_map)
  show "\<forall>c \<in> set (report_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
  proof (intro ballI impI)
    fix c
    assume "c \<in> set (report_checks res)" and "check_label c = l"
    with c0 inj have "c = c0" by (metis inj_onD)
    with c0 v0 show "check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
      by blast
  qed
qed

subsection \<open>The semantic spine\<close>

text \<open>
  The endpoint above starts at the collecting semantics. Below the point where a
  report erases its contexts, each policy states the whole chain for a source run: the
  run's store lies in the activation bucket of some context its trace carries, the
  buckets together are the collecting semantics, and the report and its verdicts
  contain that. The context type is the policy's own, so there is one statement per
  policy.
\<close>

theorem run_voblint_call_string_chain:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
      and R_def: "R \<equiv> call_context_rel_of_fun (\<lambda>u ctx t. cs_context k u ctx t)"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r (Ctx_CallString k)) p = Analysed res"
  shows "\<exists>v stk c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> \<A>\<^bsub>\<G>,R,[],g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,R,[],g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> verdict_stores res v"
proof -
  from run_voblint_source_sound [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans]
  obtain v stk
    where m: "\<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def Pi_def g_def S_def by blast
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,R,[],g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def g_def S_def R_def
    by (rule mcp_cs_rule.fun_route_node_collect_eq_Union [where ctx_fun = "cs_context k",
          symmetric])
  from mem buckets obtain c where "s \<in> \<A>\<^bsub>\<G>,R,[],g,S\<^esub> v c" by blast
  with m buckets run_voblint_covers [OF ans]
       analysis_report_verdicts_sound [OF run_voblint_consistent [OF ans]]
  show ?thesis unfolding G_def g_def S_def by blast
qed

theorem run_voblint_unit_chain:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
      and R_def: "R \<equiv> call_context_rel_of_fun (\<lambda>u c t. ())"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r Ctx_None) p = Analysed res"
  shows "\<exists>v stk c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> \<A>\<^bsub>\<G>,R,(),g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,R,(),g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> verdict_stores res v"
proof -
  from run_voblint_source_sound [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans]
  obtain v stk
    where m: "\<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def Pi_def g_def S_def by blast
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,R,(),g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def g_def S_def R_def
    by (rule mcp_rule.fun_route_node_collect_eq_Union [where ctx_fun = "\<lambda>u c t. ()",
          symmetric])
  from mem buckets obtain c where "s \<in> \<A>\<^bsub>\<G>,R,(),g,S\<^esub> v c" by blast
  with m buckets run_voblint_covers [OF ans]
       analysis_report_verdicts_sound [OF run_voblint_consistent [OF ans]]
  show ?thesis unfolding G_def g_def S_def by blast
qed

text \<open>
  Under entry-state routing the buckets cover the collecting semantics because the
  solve terminated, which the answer carries.
\<close>

lemma run_voblint_entry_state_terminates:
  assumes "run_voblint (Analysis_Config as r Ctx_EntryState) p = Analysed res"
  shows "mcp_es_rule.terminates as r (declared_global p) p"
proof -
  from assms have "analysis_report_of (Analysis_Config as r Ctx_EntryState) p = Some res"
    by (rule run_voblint_AnalysedE)
  then obtain sol where
    "TD_side_rule_Interp_solve_c r (mcp_es_rule.equations as (declared_global p) p)
       (mcp_es_rule.root_query p) = Some sol"
    by (auto simp: dg_pipeline.root_query_def mcp_wrappers)
  then show ?thesis by (rule mcp_es_rule.solve_c_run(1))
qed

theorem run_voblint_entry_state_chain:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r Ctx_EntryState) p = Analysed res"
  shows "\<exists>v stk c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> s \<in> \<A>\<^bsub>\<G>,mcp_es_rule.admitted_contexts as r \<G> p,mcp_root_ctx,g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,mcp_es_rule.admitted_contexts as r \<G> p,mcp_root_ctx,g,S\<^esub> v c')
               = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> verdict_stores res v"
proof -
  from ans have wf: "wf_program_compile_input p"
    by (blast intro: wf_program_compile_input_exec_sound)
  from run_voblint_source_sound [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans]
  obtain v stk
    where m: "\<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def Pi_def g_def S_def by blast
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,mcp_es_rule.admitted_contexts as r \<G> p,mcp_root_ctx,g,S\<^esub> v c')
                   = \<C>\<^bsub>\<G>,g,S\<^esub> v"
    unfolding G_def g_def S_def
    using mcp_es_rule.entry_state_node_collect_eq_Union_of_terminates
            [OF wf run_voblint_entry_state_terminates [OF ans]]
    by simp
  from mem buckets obtain c
    where "s \<in> \<A>\<^bsub>\<G>,mcp_es_rule.admitted_contexts as r \<G> p,mcp_root_ctx,g,S\<^esub> v c" by blast
  with m buckets run_voblint_covers [OF ans]
       analysis_report_verdicts_sound [OF run_voblint_consistent [OF ans]]
  show ?thesis unfolding G_def g_def S_def by blast
qed
end
