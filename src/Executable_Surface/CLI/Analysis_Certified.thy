theory Analysis_Certified
  imports Analysis_Run_Ctx_Sound
begin

section \<open>One soundness statement over every configuration the CLI answers\<close>

text \<open>
  The tables so far are one per domain and context policy, each over any global update
  rule. This theory states the result once, for an arbitrary configuration, over
  \<^const>\<open>run_voblint\<close> alone.

  The case split lives in two functions over the configuration: \<open>config_terminates\<close>
  names the one per-program fact a configuration needs --- its solver run completed ---
  and \<open>analysis_result_covers\<close> names the table it built. Both are functions for the
  reason a table is: an abstract state's type is the domain's own carrier, so nothing
  polymorphic can hold all five.

  Coverage of the solve is not a premise: the keys of a terminating solve that a run
  can reach are closed on their own, which \<^theory>\<open>Voblint_Result.Routed_Live_Keys\<close>
  proves from what the generated equations read. Nor is well-formedness: a malformed
  program answers \<^const>\<open>Malformed_Program\<close>.
\<close>

subsection \<open>What a configuration owes, and what its table claims\<close>

fun config_terminates ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "config_terminates Sign_Analysis r Ctx_None p = sign_rule.terminates r (declared_global p) p"
| "config_terminates Sign_Analysis r Ctx_EntryState p =
     sign_es_rule.terminates r (declared_global p) p"
| "config_terminates Sign_Analysis r (Ctx_CallString k) p =
     sign_cs_rule.terminates k r (declared_global p) p"
| "config_terminates Interval_Analysis r Ctx_None p =
     interval_rule.terminates r (declared_global p) p"
| "config_terminates Interval_Analysis r Ctx_EntryState p =
     interval_es_rule.terminates r (declared_global p) p"
| "config_terminates Interval_Analysis r (Ctx_CallString k) p =
     interval_cs_rule.terminates k r (declared_global p) p"
| "config_terminates Int_Analysis r Ctx_None p = int_rule.terminates r (declared_global p) p"
| "config_terminates Int_Analysis r Ctx_EntryState p =
     int_es_rule.terminates r (declared_global p) p"
| "config_terminates Int_Analysis r (Ctx_CallString k) p =
     int_cs_rule.terminates k r (declared_global p) p"
| "config_terminates Parity_Analysis r Ctx_None p =
     parity_rule.terminates r (declared_global p) p"
| "config_terminates Parity_Analysis r Ctx_EntryState p =
     parity_es_rule.terminates r (declared_global p) p"
| "config_terminates Parity_Analysis r (Ctx_CallString k) p =
     parity_cs_rule.terminates k r (declared_global p) p"
| "config_terminates Congruence_Analysis r Ctx_None p =
     congruence_rule.terminates r (declared_global p) p"
| "config_terminates Congruence_Analysis r Ctx_EntryState p =
     congruence_es_rule.terminates r (declared_global p) p"
| "config_terminates Congruence_Analysis r (Ctx_CallString k) p =
     congruence_cs_rule.terminates k r (declared_global p) p"

fun analysis_result_covers ::
    "analysis_domain \<Rightarrow> globals_rule \<Rightarrow> context_mode \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store
       \<Rightarrow> bool" where
  "analysis_result_covers Sign_Analysis r Ctx_None p =
     table_covers (sign_rule.result r (declared_global p) p)"
| "analysis_result_covers Sign_Analysis r Ctx_EntryState p =
     table_covers (sign_es_rule.result r (declared_global p) p)"
| "analysis_result_covers Sign_Analysis r (Ctx_CallString k) p =
     table_covers (sign_cs_rule.result k r (declared_global p) p)"
| "analysis_result_covers Interval_Analysis r Ctx_None p =
     table_covers (interval_rule.result r (declared_global p) p)"
| "analysis_result_covers Interval_Analysis r Ctx_EntryState p =
     table_covers (interval_es_rule.result r (declared_global p) p)"
| "analysis_result_covers Interval_Analysis r (Ctx_CallString k) p =
     table_covers (interval_cs_rule.result k r (declared_global p) p)"
| "analysis_result_covers Int_Analysis r Ctx_None p =
     table_covers (int_rule.result r (declared_global p) p)"
| "analysis_result_covers Int_Analysis r Ctx_EntryState p =
     table_covers (int_es_rule.result r (declared_global p) p)"
| "analysis_result_covers Int_Analysis r (Ctx_CallString k) p =
     table_covers (int_cs_rule.result k r (declared_global p) p)"
| "analysis_result_covers Parity_Analysis r Ctx_None p =
     table_covers (parity_rule.result r (declared_global p) p)"
| "analysis_result_covers Parity_Analysis r Ctx_EntryState p =
     table_covers (parity_es_rule.result r (declared_global p) p)"
| "analysis_result_covers Parity_Analysis r (Ctx_CallString k) p =
     table_covers (parity_cs_rule.result k r (declared_global p) p)"
| "analysis_result_covers Congruence_Analysis r Ctx_None p =
     table_covers (congruence_rule.result r (declared_global p) p)"
| "analysis_result_covers Congruence_Analysis r Ctx_EntryState p =
     table_covers (congruence_es_rule.result r (declared_global p) p)"
| "analysis_result_covers Congruence_Analysis r (Ctx_CallString k) p =
     table_covers (congruence_cs_rule.result k r (declared_global p) p)"

lemma analyse_program_AnalysedE [elim]:
  assumes "analyse_program D rule ctx p = Analysed res"
  obtains "wf_program_compile_input_exec p" and "res = analysis_result D rule ctx p"
  using assms unfolding analyse_program_def by (auto split: if_splits)

lemma run_voblint_AnalysedE [elim]:
  assumes "run_voblint D rule ctx p = Analysed res"
  obtains "wf_program_compile_input_exec p"
    and "res = map_run_result string_of_abstract_value (analysis_result D rule ctx p)"
  using assms unfolding run_voblint_def analyse_program_def by (auto split: if_splits)

subsection \<open>Every configuration's result is sound at every collected store\<close>

text \<open>
  The three builders a result comes from, each read at one store the collecting
  semantics admits.
\<close>

lemma run_result_sound:
  assumes "res = run_result_of into ctx_key ctx_view targets classify r shared seed_at step_at p"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  by (rule sound_table.result_sound_at [OF assms(2) _ _ assms(3)]) (simp_all add: assms(1))

text \<open>
  Each builder reads the table half of its solve; the global unknowns beside it carry
  no claim.
\<close>

lemma unit_run_result_sound:
  assumes "fst solved = r"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s
         \<and> checks_sound_at (unit_run_result into enter classify solved p) v s
         \<and> diagnostics_sound_at (unit_run_result into enter classify solved p) p v s"
  unfolding unit_run_result_def prod.case_eq_if assms(1)
  by (rule run_result_sound [OF refl assms(2,3)])

lemma entry_state_run_result_sound:
  assumes "fst solved = r"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s
         \<and> checks_sound_at (entry_state_run_result into enter classify solved p) v s
         \<and> diagnostics_sound_at (entry_state_run_result into enter classify solved p) p v s"
  unfolding entry_state_run_result_def prod.case_eq_if assms(1)
  by (rule run_result_sound [OF refl assms(2,3)])

lemma call_string_run_result_sound:
  assumes "fst solved = r"
      and "sound_table p r classify"
      and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) v"
  shows "table_covers r v s
         \<and> checks_sound_at (call_string_run_result into enter classify solved k p) v s
         \<and> diagnostics_sound_at (call_string_run_result into enter classify solved k p) p v s"
  unfolding call_string_run_result_def prod.case_eq_if assms(1)
  by (rule run_result_sound [OF refl assms(2,3)])

text \<open>
  One line per domain and context policy. Every table asks for well-formedness and
  termination, and for nothing else.
\<close>

lemma analysis_result_sound:
  assumes wf: "wf_program_compile_input p"
      and terminates: "config_terminates D rule ctx p"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "analysis_result_covers D rule ctx p v s
         \<and> checks_sound_at (analysis_result D rule ctx p) v s
         \<and> diagnostics_sound_at (analysis_result D rule ctx p) p v s"
  using terminates
proof (cases D; cases ctx)
  assume "D = Sign_Analysis" "ctx = Ctx_None" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: unit_run_result_sound
          [OF sign_rule.fst_result_with_globals sign_rule_table [OF wf] mem])
next
  assume "D = Sign_Analysis" "ctx = Ctx_EntryState" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: entry_state_run_result_sound
          [OF sign_es_rule.fst_result_with_globals sign_es_rule_table [OF wf] mem])
next
  fix k assume "D = Sign_Analysis" "ctx = Ctx_CallString k" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: call_string_run_result_sound
          [OF sign_cs_rule.fst_result_with_globals sign_cs_rule_table [OF wf] mem])
next
  assume "D = Interval_Analysis" "ctx = Ctx_None" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: unit_run_result_sound
          [OF interval_rule.fst_result_with_globals interval_rule_table [OF wf] mem])
next
  assume "D = Interval_Analysis" "ctx = Ctx_EntryState" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: entry_state_run_result_sound
          [OF interval_es_rule.fst_result_with_globals interval_es_rule_table [OF wf] mem])
next
  fix k
  assume "D = Interval_Analysis" "ctx = Ctx_CallString k" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: call_string_run_result_sound
          [OF interval_cs_rule.fst_result_with_globals interval_cs_rule_table [OF wf] mem])
next
  assume "D = Int_Analysis" "ctx = Ctx_None" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: unit_run_result_sound
          [OF int_rule.fst_result_with_globals int_rule_table [OF wf] mem])
next
  assume "D = Int_Analysis" "ctx = Ctx_EntryState" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: entry_state_run_result_sound
          [OF int_es_rule.fst_result_with_globals int_es_rule_table [OF wf] mem])
next
  fix k assume "D = Int_Analysis" "ctx = Ctx_CallString k" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: call_string_run_result_sound
          [OF int_cs_rule.fst_result_with_globals int_cs_rule_table [OF wf] mem])
next
  assume "D = Parity_Analysis" "ctx = Ctx_None" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: unit_run_result_sound
          [OF parity_rule.fst_result_with_globals parity_rule_table [OF wf] mem])
next
  assume "D = Parity_Analysis" "ctx = Ctx_EntryState" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: entry_state_run_result_sound
          [OF parity_es_rule.fst_result_with_globals parity_es_rule_table [OF wf] mem])
next
  fix k assume "D = Parity_Analysis" "ctx = Ctx_CallString k" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: call_string_run_result_sound
          [OF parity_cs_rule.fst_result_with_globals parity_cs_rule_table [OF wf] mem])
next
  assume "D = Congruence_Analysis" "ctx = Ctx_None" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: unit_run_result_sound
          [OF congruence_rule.fst_result_with_globals congruence_rule_table [OF wf] mem])
next
  assume "D = Congruence_Analysis" "ctx = Ctx_EntryState" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: entry_state_run_result_sound
          [OF congruence_es_rule.fst_result_with_globals congruence_es_rule_table [OF wf] mem])
next
  fix k
  assume "D = Congruence_Analysis" "ctx = Ctx_CallString k" "config_terminates D rule ctx p"
  then show ?thesis
    by (simp add: call_string_run_result_sound
          [OF congruence_cs_rule.fst_result_with_globals congruence_cs_rule_table [OF wf] mem])
qed

text \<open>
  Which checks a result lists does not depend on the table behind it: every
  configuration's check column has one entry per compiled check, whatever it concluded.
\<close>

lemma analysis_result_check_sites:
  "map (\<lambda>chk. (check_point chk, check_exp chk)) (res_checks (analysis_result D rule ctx p))
     = check_sites (prog_cfg p)"
  by (cases D; cases ctx)
     (simp_all add: run_result_builder_defs prod.case_eq_if result_checks_of_sites)

text \<open>
  The same claims read through \<^const>\<open>run_voblint\<close>: an analysed answer was only
  given for a well-formed program, and rendering abstract values changes neither the
  check column nor the diagnostics.
\<close>

lemma run_voblint_sound_at:
  assumes terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "analysis_result_covers D rule ctx p v s \<and> checks_sound_at res v s
           \<and> diagnostics_sound_at res p v s"
proof -
  from ans have wfx: "wf_program_compile_input_exec p"
    and res: "res = map_run_result string_of_abstract_value (analysis_result D rule ctx p)"
    by blast+
  from analysis_result_sound [OF wf_program_compile_input_exec_sound [OF wfx] terminates mem]
  show ?thesis unfolding res map_run_result_sound_at .
qed

theorem run_voblint_arithmetic_safe:
  assumes terminates: "config_terminates D rule ctx p"
    and ans: "run_voblint D rule ctx p = Analysed res"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and absent: "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
  using run_voblint_sound_at[OF terminates ans mem] absent
  unfolding diagnostics_sound_at_def by blast

corollary run_voblint_arithmetic_intra_safe:
  assumes "config_terminates D rule ctx p"
    and "run_voblint D rule ctx p = Analysed res"
    and "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
    and "\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v"
    and "(v, action, w) \<in> intra (prog_cfg p)"
    and "e \<in> set (arithmetic_edge_expressions action)"
    and "divisor \<in> expression_divisors e"
  shows "aval divisor s \<noteq> 0"
  using run_voblint_arithmetic_safe[OF assms(1-4)]
    arithmetic_expression_sites_intra[OF finite_intra_prog_cfg assms(5)] assms(6,7)
  unfolding arithmetic_safe_at_def by blast

text \<open>
  Whatever the configuration, the result lists one check per compiled check, at the
  check's node and with its condition, in graph order.  Pairing those checks with
  source positions happens outside this development.
\<close>

corollary run_voblint_check_sites:
  assumes "run_voblint D rule ctx p = Analysed res"
  shows "map (\<lambda>chk. (check_point chk, check_exp chk)) (res_checks res)
           = check_sites (prog_cfg p)"
proof -
  from assms have "res = map_run_result string_of_abstract_value (analysis_result D rule ctx p)"
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
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> analysis_result_covers D rule ctx p v s
               \<and> checks_sound_at res v s"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from ans have "wf_program_compile_input_exec p" by (rule run_voblint_AnalysedE)
  from source_reaches_ltr_collect
         [OF wf_program_compile_input_exec_sound [OF this] s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  with run_voblint_sound_at [OF terminates ans mem] show ?thesis by blast
qed

text \<open>
  The same endpoint, read at a check.  A run about to execute \<open>Check e\<close> finds a
  check for \<open>e\<close> in the result, listed at a node this very store reaches, and that
  check's verdict holds of the store.  The check is existential and cannot be
  otherwise: a source state does not determine its node.  Two procedures with the
  same body, called on the two branches of a conditional, leave the same source
  state inside either, and each body's check is listed separately; only the node the
  store reaches says which one is this execution's.
\<close>

theorem run_voblint_check_sound:
  fixes p :: imp_prog and s0 s :: store
  assumes s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and chk: "next_check residual = Some e"
      and terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
  shows "\<exists>c \<in> set (res_checks res). check_exp c = e
           \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                   (cinit_stores (declared_global p)) (check_point c)
           \<and> check_verdict c \<noteq> Dead
           \<and> (check_verdict c = Decided Check_Proved \<longrightarrow> truthy (aval e s))
           \<and> (check_verdict c = Decided Check_Refuted \<longrightarrow> \<not> truthy (aval e s))"
proof -
  from run_voblint_certified_source_sound [OF s0 run terminates ans]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
      and sound: "checks_sound_at res v s"
    by blast
  from csim_next_check_edge [OF m chk]
  have "(v, e) \<in> set (check_sites (prog_cfg p))" by auto
  then obtain c
    where "c \<in> set (res_checks res)" and "check_point c = v" and "check_exp c = e"
    unfolding run_voblint_check_sites [OF ans, symmetric] by auto
  with mem sound show ?thesis unfolding checks_sound_at_def by blast
qed

text \<open>
  What a dead check claims, stated at the point rather than at a run, and for every
  configuration. The endpoint above is existential in its witness, so reading it
  backwards does not follow from it; this is proved forwards instead, from the claim at
  every collected store.
\<close>

corollary run_voblint_dead_check_unreached:
  assumes terminates: "config_terminates D rule ctx p"
      and ans: "run_voblint D rule ctx p = Analysed res"
      and listed: "chk \<in> set (res_checks res)"
      and dead: "check_verdict chk = Dead"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (check_point chk) = {}"
proof (rule equals0I)
  fix s
  assume "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                (cinit_stores (declared_global p)) (check_point chk)"
  from run_voblint_sound_at [OF terminates ans this]
  have "checks_sound_at res (check_point chk) s" by blast
  with listed dead show False unfolding checks_sound_at_def by blast
qed

end

