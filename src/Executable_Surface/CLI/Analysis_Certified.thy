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
  obtains "valid_config config" and "wf_program_compile_input_exec p"
    and "analysis_report_of config p = Some res"
  using assms unfolding run_voblint_def by (auto split: if_splits option.splits)

lemma analysis_report_of_fields:
  "analysis_report_of config p = Some res
     \<Longrightarrow> report_config res = config \<and> report_cfg res = prog_cfg p"
  by (induct config p rule: analysis_report_of.induct) auto

lemma run_voblint_config:
  "run_voblint config p = Analysed res \<Longrightarrow> report_config res = config"
  by (auto dest: analysis_report_of_fields)

lemma run_voblint_cfg:
  "run_voblint config p = Analysed res \<Longrightarrow> report_cfg res = prog_cfg p"
  by (auto dest: analysis_report_of_fields)

theorem run_voblint_sound:
  assumes "run_voblint config p = Analysed res"
  shows "sound_report p res"
  using assms
  by (auto intro: analysis_report_of_sound wf_program_compile_input_exec_sound)

lemma run_voblint_consistent:
  "run_voblint config p = Analysed res \<Longrightarrow> consistent_report res"
  using run_voblint_sound unfolding sound_report_def by blast

lemma run_voblint_well_formed:
  "run_voblint config p = Analysed res \<Longrightarrow> well_formed_report res"
  by (auto intro: analysis_report_of_well_formed)

text \<open>
  The report contract in one statement: an analysed answer was given for a valid
  configuration and a well-formed program, and is a well-formed, sound report for
  exactly that configuration and the program's compiled graph. The theorems below
  are its consequences.
\<close>

theorem run_voblint_report_contract:
  assumes "run_voblint config p = Analysed res"
  shows "valid_config config" "wf_program_compile_input_exec p"
    and "report_config res = config" "report_cfg res = prog_cfg p"
    and "well_formed_report res" "sound_report p res"
  using assms
  by (auto elim: run_voblint_AnalysedE
      simp: run_voblint_config run_voblint_cfg run_voblint_well_formed run_voblint_sound)

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
           \<subseteq> \<V>\<^bsub>res\<^esub> v"
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
    and "e \<in> set (edge_expressions action)"
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
                 \<and> s \<in> \<V>\<^bsub>res\<^esub> v"
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
  The same endpoint without contexts: the state the report holds at the node, joined
  over its contexts, describes the store too.
\<close>

corollary run_voblint_source_sound_joined:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
  shows "\<exists>v stk. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> gamma_lift (report_gamma res) (report_point_join res v)"
  using run_voblint_source_sound[OF s0[unfolded G_def] run[unfolded G_def Pi_def] ans]
    report_sem_point_join
  unfolding Pi_def g_def by blast

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
      and verdicts: "s \<in> \<V>\<^bsub>res\<^esub> v"
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
  moreover have holds: "verdict_holds r e s" if "check_verdict c = Decided r" for r
  proof (rule verdict_storesD [OF verdicts])
    show "HAS_VERDICT res v e r"
      unfolding HAS_VERDICT_def
      using c \<open>check_point c = v\<close> \<open>check_exp c = e\<close> that by auto
  qed
  ultimately show ?thesis
    using mem holds [of Check_Proved] holds [of Check_Refuted] unfolding G_def g_def by auto
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
  run is represented by a valid activation trace \<open>t\<close>, the policy assigns \<open>t\<close> a context
  \<open>c\<close>, the run's store lies in the bucket of \<open>c\<close>, the buckets together are the collecting
  semantics, and the report and its verdicts contain that. The context type is the
  policy's own, so there is one statement per policy.
\<close>

lemma run_voblint_wf:
  "run_voblint config p = Analysed res \<Longrightarrow> wf_program_compile_input p"
  by (blast intro: wf_program_compile_input_exec_sound)

text \<open>
  The chain for any context policy, given what the policy owes: every valid
  activation trace carries some context, and the buckets together are the collecting
  semantics. Each policy below supplies exactly these two facts.
\<close>

theorem run_voblint_spine:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint config p = Analysed res"
      and has_ctx: "\<And>t. t \<in> \<T>\<^bsub>\<G>,g,S\<^esub> \<Longrightarrow> \<exists>c. activation_context_rel \<G> adm c\<^sub>0 g t c"
      and buckets: "\<And>v. (\<Union>c'. \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v"
  shows "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm c\<^sub>0 g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
proof -
  have cfg: "g = compile_prog \<Pi> (prog_procs p)"
    unfolding g_def Pi_def by (rule prog_cfg_def)
  from source_store_in_activation_collect
         [OF run_voblint_wf [OF ans, folded G_def Pi_def] s0 run has_ctx [unfolded cfg]]
  have witness: "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm c\<^sub>0 g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,c\<^sub>0,g,S\<^esub> v c"
    unfolding cfg .
  from witness buckets run_voblint_covers [OF ans]
       analysis_report_verdicts_sound [OF run_voblint_consistent [OF ans]]
  show ?thesis unfolding G_def g_def S_def by blast
qed

theorem run_voblint_call_string_chain:
  fixes p :: imp_prog and s0 s :: store and k :: nat
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
      and R_def: "adm \<equiv> context_policy_of_fun (\<lambda>u ctx t. cs_context k u ctx t)"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r (Ctx_CallString k) pg) p = Analysed res"
  shows "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm [] g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,[],g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,adm,[],g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
proof -
  have has_ctx: "\<exists>c. activation_context_rel \<G> adm [] g t c" if "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>" for t
    unfolding R_def by (rule exI, subst activation_context_rel_of_fun_iff [OF that]) (rule refl)
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,adm,[],g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v" for v
    unfolding G_def g_def S_def R_def
    by (rule mcp_cs_rule.fun_route_node_collect_eq_Union [where ctx_fun = "cs_context k",
          symmetric])
  show ?thesis
    unfolding G_def Pi_def g_def S_def
    by (rule run_voblint_spine [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans
          has_ctx [unfolded G_def g_def S_def] buckets [unfolded G_def g_def S_def]])
qed

theorem run_voblint_unit_chain:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
      and R_def: "adm \<equiv> context_policy_of_fun (\<lambda>u c t. ())"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r Ctx_None pg) p = Analysed res"
  shows "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm () g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,(),g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,adm,(),g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
proof -
  have has_ctx: "\<exists>c. activation_context_rel \<G> adm () g t c" if "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>" for t
    unfolding R_def by (rule exI, subst activation_context_rel_of_fun_iff [OF that]) (rule refl)
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,adm,(),g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v" for v
    unfolding G_def g_def S_def R_def
    by (rule mcp_rule.fun_route_node_collect_eq_Union [where ctx_fun = "\<lambda>u c t. ()",
          symmetric])
  show ?thesis
    unfolding G_def Pi_def g_def S_def
    by (rule run_voblint_spine [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans
          has_ctx [unfolded G_def g_def S_def] buckets [unfolded G_def g_def S_def]])
qed

text \<open>
  Under entry-state routing a trace carries an admitted context, and the buckets cover
  the collecting semantics, because the solve terminated, which the answer carries.
\<close>

text \<open>
  Each placement registers entry-state routing once, so the contexts an answered run
  admits are read off the registration its placement selects.
\<close>

definition mcp_es_admitted where
  "mcp_es_admitted pg as r p = (case pg of
     Program_Globals_Flow_Sensitive \<Rightarrow> mcp_es_rule.admitted_contexts as r (declared_global p) p
   | Program_Globals_Flow_Insensitive \<Rightarrow> mcp_split_es_rule.admitted_contexts as r (declared_global p) p)"

lemma run_voblint_entry_state_terminates:
  assumes "run_voblint (Analysis_Config as r Ctx_EntryState pg) p = Analysed res"
  shows "case pg of
           Program_Globals_Flow_Sensitive \<Rightarrow> mcp_es_rule.terminates as r (declared_global p) p
         | Program_Globals_Flow_Insensitive \<Rightarrow> mcp_split_es_rule.terminates as r (declared_global p) p"
proof -
  from assms have rep: "analysis_report_of (Analysis_Config as r Ctx_EntryState pg) p = Some res"
    by (rule run_voblint_AnalysedE)
  show ?thesis
  proof (cases pg)
    case Program_Globals_Flow_Sensitive
    with rep obtain sol where
      "TD_side_rule_Interp_solve_c r (mcp_es_rule.equations as (declared_global p) p)
         (mcp_es_rule.root_query p) = Some sol"
      by (auto simp: dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
    then show ?thesis
      using Program_Globals_Flow_Sensitive by (simp add: mcp_es_rule.solve_c_run(1))
  next
    case Program_Globals_Flow_Insensitive
    with rep obtain sol where
      "TD_side_rule_Interp_solve_c r (mcp_split_es_rule.equations as (declared_global p) p)
         (mcp_split_es_rule.root_query p) = Some sol"
      by (auto simp: dg_pipeline.root_query_def mcp_wrappers mcp_place_defs)
    then show ?thesis
      using Program_Globals_Flow_Insensitive by (simp add: mcp_split_es_rule.solve_c_run(1))
  qed
qed

theorem run_voblint_entry_state_chain:
  fixes p :: imp_prog and s0 s :: store
    and as :: "analysis_domain list" and r :: globals_rule and pg :: program_globals
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
      and S_def: "S \<equiv> cinit_stores (declared_global p)"
      and R_def: "adm \<equiv> mcp_es_admitted pg as r p"
  assumes s0: "s0 \<in> S"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and ans: "run_voblint (Analysis_Config as r Ctx_EntryState pg) p = Analysed res"
  shows "\<exists>v stk t c. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
           \<and> activation_trace_repr \<G> g S (v, s, stk) t
           \<and> activation_context_rel \<G> adm mcp_root_ctx g t c
           \<and> s \<in> \<A>\<^bsub>\<G>,adm,mcp_root_ctx,g,S\<^esub> v c
           \<and> (\<Union>c'. \<A>\<^bsub>\<G>,adm,mcp_root_ctx,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v
           \<and> \<C>\<^bsub>\<G>,g,S\<^esub> v \<subseteq> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub>
           \<and> \<lbrakk>res\<rbrakk>\<^bsub>v\<^esub> \<subseteq> \<V>\<^bsub>res\<^esub> v"
proof -
  note wf = run_voblint_wf [OF ans]
  note terminates = run_voblint_entry_state_terminates [OF ans]
  have has_ctx: "\<exists>c. activation_context_rel \<G> adm mcp_root_ctx g t c"
    if "t \<in> \<T>\<^bsub>\<G>,g,S\<^esub>" for t
  proof (cases pg)
    case Program_Globals_Flow_Sensitive
    with terminates show ?thesis
      using mcp_es_rule.entry_state_has_context_of_terminates [OF wf] that
      unfolding G_def g_def S_def R_def mcp_es_admitted_def by simp
  next
    case Program_Globals_Flow_Insensitive
    with terminates show ?thesis
      using mcp_split_es_rule.entry_state_has_context_of_terminates [OF wf] that
      unfolding G_def g_def S_def R_def mcp_es_admitted_def by simp
  qed
  have buckets: "(\<Union>c'. \<A>\<^bsub>\<G>,adm,mcp_root_ctx,g,S\<^esub> v c') = \<C>\<^bsub>\<G>,g,S\<^esub> v" for v
  proof (cases pg)
    case Program_Globals_Flow_Sensitive
    with terminates show ?thesis
      using mcp_es_rule.entry_state_node_collect_eq_Union_of_terminates [OF wf]
      unfolding G_def g_def S_def R_def mcp_es_admitted_def by simp
  next
    case Program_Globals_Flow_Insensitive
    with terminates show ?thesis
      using mcp_split_es_rule.entry_state_node_collect_eq_Union_of_terminates [OF wf]
      unfolding G_def g_def S_def R_def mcp_es_admitted_def by simp
  qed
  show ?thesis
    unfolding G_def Pi_def g_def S_def
    by (rule run_voblint_spine [OF s0 [unfolded S_def G_def] run [unfolded G_def Pi_def] ans
          has_ctx [unfolded G_def g_def S_def] buckets [unfolded G_def g_def S_def]])
qed
end
