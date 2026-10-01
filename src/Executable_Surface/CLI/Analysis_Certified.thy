theory Analysis_Certified
  imports Analysis_Run_Ctx_Sound
begin

section \<open>One soundness statement over every configuration the CLI answers\<close>

text \<open>
  The tables so far are one per context policy, each over any activation list and any
  global update rule. This theory states the result once, for an arbitrary
  configuration, over \<^const>\<open>run_voblint\<close> alone.

  The case split lives in two functions over the configuration: \<open>config_terminates\<close>
  names the one per-program fact a configuration needs --- its solver run completed ---
  and \<open>analysis_result_covers\<close> names the table it built. Both are functions for the
  reason a table is: each context policy keys its table by its own context type.

  Coverage of the solve is not a premise: the keys of a terminating solve that a run
  can reach are closed on their own, which \<^theory>\<open>Voblint_Result.DG_Live_Unknowns\<close>
  proves from what the generated equations read. Nor is well-formedness: a malformed
  program answers \<^const>\<open>Malformed_Program\<close>.
\<close>

subsection \<open>What a configuration owes, and what its table claims\<close>

fun config_terminates ::
    "analysis_domain list \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "config_terminates as r Ctx_None p = mcp_rule.terminates as r (declared_global p) p"
| "config_terminates as r Ctx_EntryState p = mcp_es_rule.terminates as r (declared_global p) p"
| "config_terminates as r (Ctx_CallString k) p =
     mcp_cs_rule.terminates as k r (declared_global p) p"

fun analysis_result_covers ::
    "analysis_domain list \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store
       \<Rightarrow> bool" where
  "analysis_result_covers as r Ctx_None p =
     table_covers (mcp_gamma_v (activation as)) (mcp_rule.result as r (declared_global p) p)"
| "analysis_result_covers as r Ctx_EntryState p =
     table_covers (mcp_gamma_v (activation as)) (mcp_es_rule.result as r (declared_global p) p)"
| "analysis_result_covers as r (Ctx_CallString k) p =
     table_covers (mcp_gamma_v (activation as))
       (mcp_cs_rule.result as k r (declared_global p) p)"

lemma analyse_program_AnalysedE [elim]:
  assumes "analyse_program as rule ctx p = Analysed res"
  obtains "wf_program_compile_input_exec p" and "res = analysis_result as rule ctx p"
  using assms unfolding analyse_program_def by (auto split: if_splits)

lemma run_voblint_AnalysedE [elim]:
  assumes "run_voblint as rule ctx p = Analysed res"
  obtains "wf_program_compile_input_exec p"
    and "res = map_run_result string_of_abstract_value (analysis_result as rule ctx p)"
  using assms unfolding run_voblint_def analyse_program_def by (auto split: if_splits)

subsection \<open>Every configuration's result is sound at every collected store\<close>

text \<open>
  The builder a result comes from, read at one store the collecting semantics admits.
  It reads the table half of its solve; the global unknowns beside it carry no claim.
\<close>

lemma run_result_sound:
  assumes "fst solved = r"
      and "sound_table p r classify gm"
      and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "table_covers gm r v s
         \<and> checks_sound_at (case solved of (t, shared, seed_at, step_at, succ) \<Rightarrow>
             run_result_of render ctx_key ctx_view (targets succ) classify t shared seed_at
               step_at p)
             v s
         \<and> diagnostics_sound_at (case solved of (t, shared, seed_at, step_at, succ) \<Rightarrow>
             run_result_of render ctx_key ctx_view (targets succ) classify t shared seed_at
               step_at p)
             p v s"
  unfolding prod.case_eq_if assms(1)
  by (rule sound_table.result_sound_at [OF assms(2) _ _ assms(3)]) simp_all

text \<open>
  One solve and one table per context policy. Every table asks for well-formedness and
  termination, and for nothing else.
\<close>

lemma analysis_result_sound:
  assumes wf: "wf_program_compile_input p"
      and terminates: "config_terminates as rule ctx p"
      and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "analysis_result_covers as rule ctx p v s
         \<and> checks_sound_at (analysis_result as rule ctx p) v s
         \<and> diagnostics_sound_at (analysis_result as rule ctx p) p v s"
  by (insert terminates, cases ctx;
      simp only: config_terminates.simps analysis_result_covers.simps analysis_result.simps;
      rule run_result_sound,
      rule mcp_rule.fst_result_with_globals mcp_es_rule.fst_result_with_globals
        mcp_cs_rule.fst_result_with_globals,
      erule mcp_rule_table [OF wf] mcp_es_rule_table [OF wf] mcp_cs_rule_table [OF wf],
      rule mem)

text \<open>
  Which checks a result lists does not depend on the table behind it: every
  configuration's check column has one entry per compiled check, whatever it concluded.
\<close>

lemma analysis_result_check_sites:
  "map (\<lambda>chk. (check_point chk, check_label chk, check_exp chk))
       (res_checks (analysis_result as rule ctx p))
     = check_sites (prog_cfg p)"
  by (cases ctx) (simp_all add: prod.case_eq_if result_checks_of_sites)

text \<open>
  The same claims read through \<^const>\<open>run_voblint\<close>: an analysed answer was only
  given for a well-formed program, and rendering abstract values changes neither the
  check column nor the diagnostics.
\<close>

lemma run_voblint_sound_at:
  assumes terminates: "config_terminates as rule ctx p"
      and ans: "run_voblint as rule ctx p = Analysed res"
      and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
  shows "analysis_result_covers as rule ctx p v s \<and> checks_sound_at res v s
           \<and> diagnostics_sound_at res p v s"
proof -
  from ans have wfx: "wf_program_compile_input_exec p"
    and res: "res = map_run_result string_of_abstract_value (analysis_result as rule ctx p)"
    by blast+
  from analysis_result_sound [OF wf_program_compile_input_exec_sound [OF wfx] terminates mem]
  show ?thesis unfolding res map_run_result_sound_at .
qed

theorem run_voblint_arithmetic_safe:
  assumes terminates: "config_terminates as rule ctx p"
    and ans: "run_voblint as rule ctx p = Analysed res"
    and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    and absent: "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
  using run_voblint_sound_at[OF terminates ans mem] absent
  unfolding diagnostics_sound_at_def by blast

corollary run_voblint_arithmetic_intra_safe:
  assumes "config_terminates as rule ctx p"
    and "run_voblint as rule ctx p = Analysed res"
    and "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
    and "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (arithmetic_edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "\<lbrakk>divisor\<rbrakk>\<^sub>e s \<noteq> 0"
  using run_voblint_arithmetic_safe[OF assms(1-4)]
    arithmetic_expression_sites_intra[OF finite_intra_prog_cfg assms(5)] assms(6,7)
  unfolding arithmetic_safe_at_def by blast

text \<open>
  Whatever the configuration, the result lists one check per compiled check, at the
  check's node and with its label and condition, in graph order.
\<close>

corollary run_voblint_check_sites:
  assumes "run_voblint as rule ctx p = Analysed res"
  shows "map (\<lambda>chk. (check_point chk, check_label chk, check_exp chk)) (res_checks res)
           = check_sites (prog_cfg p)"
proof -
  from assms have "res = map_run_result string_of_abstract_value (analysis_result as rule ctx p)"
    by blast
  then show ?thesis by (simp add: analysis_result_check_sites)
qed

subsection \<open>The endpoint\<close>

text \<open>
  Run the source program, stop wherever you like, and ask any configuration for a
  result: there is a graph node and frame stack for where you stopped, the store in
  your hands is one the collecting semantics really admits there, the table that
  configuration built describes it, and every check listed there holds of it, with none
  there marked unreachable.
\<close>

theorem run_voblint_certified_source_sound:
  fixes p :: imp_prog and s0 s :: store
  defines G_def: "\<G> \<equiv> declared_global p"
      and Pi_def: "\<Pi> \<equiv> prog_table p"
      and g_def: "g \<equiv> prog_cfg p"
  assumes s0: "s0 \<in> cinit_stores \<G>"
      and run: "\<G>, \<Pi> \<turnstile> (main_body \<Pi>, s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and terminates: "config_terminates as rule ctx p"
      and ans: "run_voblint as rule ctx p = Analysed res"
  shows "\<exists>v stk. \<Pi>, g \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> v
                 \<and> analysis_result_covers as rule ctx p v s
                 \<and> checks_sound_at res v s"
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
  with run_voblint_sound_at [OF terminates ans mem] show ?thesis
    unfolding G_def Pi_def g_def by blast
qed

text \<open>
  The same endpoint, read at a check.  A run about to execute \<open>Check l e\<close> finds a
  check labelled \<open>l\<close> for \<open>e\<close> in the result, listed at a node this very store
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
      and terminates: "config_terminates as rule ctx p"
      and ans: "run_voblint as rule ctx p = Analysed res"
  shows "\<exists>c \<in> set (res_checks res). check_label c = l \<and> check_exp c = e
           \<and> s \<in> \<C>\<^bsub>\<G>,g,cinit_stores \<G>\<^esub> (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted
                \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
proof -
  from run_voblint_certified_source_sound
         [OF s0 [unfolded G_def] run [unfolded G_def Pi_def] terminates ans]
  obtain v stk
    where m: "prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and mem: "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> v"
      and sound: "checks_sound_at res v s"
    by blast
  from csim_next_check_edge [OF m chk]
  have "(v, l, e) \<in> set (check_sites (prog_cfg p))" by auto
  then obtain c
    where "c \<in> set (res_checks res)" and "check_point c = v"
      and "check_label c = l" and "check_exp c = e"
    unfolding run_voblint_check_sites [OF ans, symmetric] by auto
  with mem sound show ?thesis unfolding checks_sound_at_def G_def g_def by blast
qed

text \<open>
  Read by label, which is how a report finds a source check's row.  When no two rows
  share a label, the row labelled \<open>l\<close> is the one the theorem above found, so its
  verdict holds of the store.  Distinct labels are a premise rather than a fact about
  every result: a procedure called from several sites is compiled once, so its
  checks are listed once, but two source checks given the same label would share it.
  The premise is decidable on the result, so a consumer checks it before trusting a
  lookup.  What stays outside this development is the label itself: that the parser
  wrote each check's own source position into it.
\<close>

corollary run_voblint_labelled_check_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "declared_global p, prog_table p
                  \<turnstile> (main_body (prog_table p), s0, [])
                    \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
      and chk: "next_check residual = Some (l, e)"
      and terminates: "config_terminates as rule ctx p"
      and ans: "run_voblint as rule ctx p = Analysed res"
      and distinct: "distinct (map check_label (res_checks res))"
  shows "\<exists>c \<in> set (res_checks res). check_label c = l"
    and "\<forall>c \<in> set (res_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
proof -
  from run_voblint_check_sound [OF s0 run chk terminates ans]
  obtain c0 where c0: "c0 \<in> set (res_checks res)" "check_label c0 = l" "check_exp c0 = e"
    and v0: "check_verdict c0 \<noteq> Dead"
      "check_verdict c0 = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
      "check_verdict c0 = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s)"
    by blast
  from c0 show "\<exists>c \<in> set (res_checks res). check_label c = l" by blast
  have inj: "inj_on check_label (set (res_checks res))"
    using distinct by (simp add: distinct_map)
  show "\<forall>c \<in> set (res_checks res). check_label c = l \<longrightarrow>
           check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
  proof (intro ballI impI)
    fix c
    assume "c \<in> set (res_checks res)" and "check_label c = l"
    with c0 inj have "c = c0" by (metis inj_onD)
    with c0 v0 show "check_exp c = e
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (\<lbrakk>e\<rbrakk>\<^sub>e s))"
      by blast
  qed
qed

text \<open>
  What a dead check claims, stated at the point rather than at a run, and for every
  configuration. The endpoint above is existential in its witness, so reading it
  backwards does not follow from it; this is proved forwards instead, from the claim at
  every collected store.
\<close>

corollary run_voblint_dead_check_unreached:
  assumes terminates: "config_terminates as rule ctx p"
      and ans: "run_voblint as rule ctx p = Analysed res"
      and listed: "chk \<in> set (res_checks res)"
      and dead: "check_verdict chk = Dead"
  shows "\<C>\<^bsub>declared_global p,prog_cfg p,
            cinit_stores (declared_global p)\<^esub> (check_point chk) = {}"
proof (rule equals0I)
  fix s
  assume "s \<in> \<C>\<^bsub>declared_global p,prog_cfg p,cinit_stores (declared_global p)\<^esub> (check_point chk)"
  from run_voblint_sound_at [OF terminates ans this]
  have "checks_sound_at res (check_point chk) s" by blast
  with listed dead show False unfolding checks_sound_at_def by blast
qed

end
