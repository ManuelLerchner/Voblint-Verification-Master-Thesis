theory Analysis_Run_Sound
  imports Analysis_Run
begin

section \<open>What a result's check column proves about a run of the program\<close>

text \<open>
  Every configuration hands the table its plan resolved to to
  \<^const>\<open>run_result_of\<close>, which takes the check column from one call of
  \<^const>\<open>classify_checks_verdicts\<close> and the diagnostics from one call of
  \<^const>\<open>arithmetic_diagnostics\<close> over that table. So one argument serves every
  configuration.

  The argument asks two things of the table, bundled as \<open>sound_table\<close>. A store
  the program reaches at a point lies in the entry the table filed there under
  \<^emph>\<open>some\<close> context (\<open>table_covers\<close>), and a point has finitely many contexts.
  Given those and a sound classifier, a source run stops at a graph node where
  every check the result lists there is true of the store in hand and none is
  dead. The context-free configurations' tables are the instances at the end of
  this theory; the contextual ones follow in the two theories after it.
\<close>

subsection \<open>Every check column is a contextual verdict report\<close>

lemma finite_intra_prog_cfg [simp]: "finite (intra (prog_cfg p))"
  unfolding prog_cfg_def using compile_prog_finite by simp

lemma check_in_result_checks_of:
  assumes "chk \<in> set (result_checks_of verdicts)"
  shows "(check_point chk, check_exp chk, check_verdict chk) \<in> set verdicts"
  using assms by (auto simp: result_checks_of_def)

lemma run_result_of_columns [simp]:
  "res_cfg (run_result_of into ctx_key ctx_view targets classify r globals p) = prog_cfg p"
  "res_checks (run_result_of into ctx_key ctx_view targets classify r globals p)
     = result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
  "res_diagnostics (run_result_of into ctx_key ctx_view targets classify r globals p)
     = arithmetic_diagnostics (prog_cfg p) r classify"
  by (simp_all add: run_result_of_def Let_def)

lemmas run_result_builder_defs =
  unit_run_result_def entry_state_run_result_def call_string_run_result_def

text \<open>
  Where a result has checks: one per compiled \<^const>\<open>EA_Check\<close> edge, at that edge's
  source node and with its condition, in the order the graph lists its edges.
\<close>

definition check_sites :: "cfg \<Rightarrow> (pp \<times> exp) list" where
  "check_sites g =
     map (\<lambda>(u, a, v). (u, ea_check_cond a))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

lemma result_checks_of_sites:
  "map (\<lambda>chk. (check_point chk, check_exp chk))
       (result_checks_of (classify_checks_verdicts g r classify))
     = check_sites g"
  unfolding result_checks_of_def classify_checks_verdicts_def classify_checks_ctx_def
    check_sites_def
  by (simp add: comp_def case_prod_beta)

lemma check_sites_memI [intro]:
  assumes "finite (intra g)" and "(v, EA_Check cnd, w) \<in> intra g"
  shows "(v, cnd) \<in> set (check_sites g)"
  using assms unfolding check_sites_def by force

subsection \<open>What a check claims at the point it was listed for\<close>

text \<open>
  Both claims read only the check column and the diagnostics, which rendering abstract
  values leaves untouched; they are stated for any value type so that the typed result
  and its displayed form make the same claim.
\<close>

definition checks_sound_at :: "'v run_result \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "checks_sound_at res v s =
     (\<forall>chk \<in> set (res_checks res). check_point chk = v \<longrightarrow>
        check_verdict chk \<noteq> Dead
      \<and> (check_verdict chk = Decided Check_Proved \<longrightarrow> truthy (aval (check_exp chk) s))
      \<and> (check_verdict chk = Decided Check_Refuted
           \<longrightarrow> \<not> truthy (aval (check_exp chk) s)))"

text \<open>
  The table claim at a point is existential in the context: a store is described
  by the entry filed under \<^emph>\<open>some\<close> context the point was solved at --- one its
  own call history is admitted at --- and in general not by every such entry,
  since another activation's entry need not describe this store at all.
\<close>

definition table_covers ::
    "('c, 'a::sound_domain abs_state) analysis_result \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "table_covers r v s \<longleftrightarrow> (\<exists>c st. lookup_context r v c = Lifted st \<and> s \<in> \<lbrakk>st\<rbrakk>)"

lemma table_coversI [intro]:
  "lookup_context r v ctx = Lifted st \<Longrightarrow> s \<in> \<lbrakk>st\<rbrakk> \<Longrightarrow> table_covers r v s"
  unfolding table_covers_def by blast

lemma classify_checks_verdicts_Dead_lookup_Bot:
  assumes "(v, cnd, Dead) \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
      and "finite (contexts_at r v)"
  shows "lookup_context r v ctx = Bot"
proof (cases "lookup_context r v ctx")
  case Bot
  then show ?thesis .
next
  case (Lifted st)
  have "aggregate_verdicts
          ((\<lambda>c. classify_point classify cnd (lookup_context r v c)) ` contexts_at r v) = Dead"
    using assms(1) by (simp add: classify_checks_verdicts_mem_iff)
  then have all: "\<forall>x \<in> (\<lambda>c. classify_point classify cnd (lookup_context r v c)) ` contexts_at r v.
                    x = Dead"
    by (simp only: aggregate_verdicts_eq_Dead_iff [OF finite_imageI [OF assms(2)]])
  have "classify_point classify cnd (lookup_context r v ctx) = Dead"
    using bspec [OF all imageI [OF lookup_context_LiftedD [OF Lifted]]] by simp
  with Lifted show ?thesis by simp
qed

text \<open>
  The check column's claim at a point the caller names, given one context whose
  entry describes the store. It does not mention a source execution: a caller
  who can exhibit such a store --- by walking the graph, say --- gets the
  verdict claim at the point the check was listed for.
\<close>

lemma ctx_checks_sound_at:
  fixes r :: "('c, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes fin: "finite (contexts_at r v)"
      and look: "lookup_context r v ctx = Lifted st" and gst: "s \<in> \<lbrakk>st\<rbrakk>"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                        \<Longrightarrow> \<not> truthy (aval c t)"
      and checks: "res_checks res
                     = result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
  shows "checks_sound_at res v s"
proof -
  have mem: "(v, check_exp chk, check_verdict chk)
               \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
    if "chk \<in> set (res_checks res)" and "check_point chk = v" for chk
    using check_in_result_checks_of [OF that(1) [unfolded checks]] that(2) by simp
  show ?thesis
    unfolding checks_sound_at_def
  proof (intro ballI impI conjI)
    fix chk
    assume "chk \<in> set (res_checks res)" and "check_point chk = v"
    note m = mem [OF this]
    show "check_verdict chk \<noteq> Dead"
    proof
      assume "check_verdict chk = Dead"
      with m have "(v, check_exp chk, Dead)
                     \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
        by simp
      from classify_checks_verdicts_Dead_lookup_Bot [OF this fin] look show False by simp
    qed
  next
    fix chk
    assume "chk \<in> set (res_checks res)" and "check_point chk = v"
       and dv: "check_verdict chk = Decided Check_Proved"
    from mem [OF this(1,2)] dv
    have "(v, check_exp chk, Decided Check_Proved)
            \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
      by simp
    from classify_checks_ctx_proved_sound [OF finite_intra_prog_cfg this look]
    show "truthy (aval (check_exp chk) s)" by (rule proved) (rule gst)
  next
    fix chk
    assume "chk \<in> set (res_checks res)" and "check_point chk = v"
       and dv: "check_verdict chk = Decided Check_Refuted"
    from mem [OF this(1,2)] dv
    have "(v, check_exp chk, Decided Check_Refuted)
            \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
      by simp
    from classify_checks_ctx_refuted_sound [OF finite_intra_prog_cfg this look]
    show "\<not> truthy (aval (check_exp chk) s)" by (rule refuted) (rule gst)
  qed
qed

subsection \<open>A store that reaches a point sits in one of that point's contexts\<close>

text \<open>
  The published contextual soundness bounds one activation bucket by the table
  entry filed under that bucket's context. A caller holding a store knows only
  that the store reaches the point at all, so it needs the buckets to exhaust
  the point --- the union direction, which is where a context policy pays for
  being total. Both readings are settled in
  \<^theory>\<open>Voblint_CFG.LTR_Collect\<close>: a functional policy has the union outright,
  a relational one --- such as the entry-state policy --- earns it from the
  existence of a context for every valid trace. \<^const>\<open>Bot\<close> cannot be the entry
  found, since it concretizes to no store at all.
\<close>

lemma lookup_context_covers_of_activation:
  fixes r :: "('c, 'a::sound_domain abs_state) analysis_result"
  assumes union: "ltr_collect gs g S v \<subseteq> (\<Union>c. activation_collect gs R rc g S v c)"
      and sound: "\<And>ctx. activation_collect gs R rc g S v ctx
                    \<subseteq> gamma_point (lookup_context r v ctx)"
      and mem: "s \<in> ltr_collect gs g S v"
  obtains ctx st where "s \<in> activation_collect gs R rc g S v ctx"
    and "lookup_context r v ctx = Lifted st" and "s \<in> \<lbrakk>st\<rbrakk>"
proof -
  from mem union obtain ctx where a: "s \<in> activation_collect gs R rc g S v ctx" by blast
  with sound have g: "s \<in> gamma_point (lookup_context r v ctx)" by blast
  show ?thesis
  proof (cases "lookup_context r v ctx")
    case Bot
    with g show ?thesis by simp
  next
    case (Lifted st)
    with g a show ?thesis by (intro that [of ctx st]) simp_all
  qed
qed

subsection \<open>The endpoint, over an arbitrary sound table\<close>

text \<open>
  What a configuration's table has to satisfy for its result to be sound. Each
  configuration below and in the two theories after this one is an instance, and
  owes nothing but these four facts: the table exhausts the reachable stores,
  over finitely many contexts per point, and its classifier is sound in both
  directions.
\<close>

definition arithmetic_safe_at :: "cfg \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" where
  "arithmetic_safe_at g v s \<longleftrightarrow>
     (\<forall>es. (v, es) \<in> set (arithmetic_expression_sites g) \<longrightarrow>
       (\<forall>e \<in> set es. \<forall>divisor \<in> expression_divisors e. aval divisor s \<noteq> 0))"

definition diagnostics_sound_at :: "'v run_result \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool"
where
  "diagnostics_sound_at res p v s \<longleftrightarrow>
     ((\<forall>d \<in> set (res_diagnostics res). diagnostic_point d \<noteq> v) \<longrightarrow>
       arithmetic_safe_at (prog_cfg p) v s)"

lemma map_run_result_sound_at [simp]:
  "checks_sound_at (map_run_result f res) = checks_sound_at res"
  "diagnostics_sound_at (map_run_result f res) = diagnostics_sound_at res"
  by (simp_all add: checks_sound_at_def diagnostics_sound_at_def fun_eq_iff)

locale sound_table =
  fixes p :: imp_prog
    and r :: "('c, 'a::sound_domain abs_state) analysis_result"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
  assumes finite_contexts: "\<And>v. finite (contexts_at r v)"
      and covers: "\<And>v s. s \<in> ltr_collect (declared_global p) (prog_cfg p)
                               (cinit_stores (declared_global p)) v
                      \<Longrightarrow> table_covers r v s"
      and proved: "\<And>cnd d t. classify cnd d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                      \<Longrightarrow> truthy (aval cnd t)"
      and refuted: "\<And>cnd d t. classify cnd d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                      \<Longrightarrow> \<not> truthy (aval cnd t)"
begin

text \<open>
  The result's claim at any store the collecting semantics admits at a point,
  with no source execution in sight: the table describes the store there, and
  every check listed there is true of it.
\<close>

lemma sound_at:
  assumes checks: "res_checks res
                     = result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s"
proof -
  from covers [OF mem] obtain ctx st
    where look: "lookup_context r v ctx = Lifted st" and gst: "s \<in> \<lbrakk>st\<rbrakk>"
    unfolding table_covers_def by blast
  have "checks_sound_at res v s"
    by (rule ctx_checks_sound_at [OF finite_contexts look gst proved refuted checks])
  with covers [OF mem] show ?thesis ..
qed

lemma arithmetic_safe:
  assumes absent: "\<forall>d \<in> set (arithmetic_diagnostics (prog_cfg p) r classify).
      diagnostic_point d \<noteq> v"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
  shows "arithmetic_safe_at (prog_cfg p) v s"
proof -
  from covers[OF mem] obtain ctx st where
    look: "lookup_context r v ctx = Lifted st" and gst: "s \<in> \<lbrakk>st\<rbrakk>"
    unfolding table_covers_def by blast
  have safe: "\<And>es e divisor. (v, es) \<in> set (arithmetic_expression_sites (prog_cfg p)) \<Longrightarrow>
      e \<in> set es \<Longrightarrow> divisor \<in> expression_divisors e \<Longrightarrow> aval divisor s \<noteq> 0"
  proof -
    fix es e divisor
    assume site: "(v, es) \<in> set (arithmetic_expression_sites (prog_cfg p))"
      and expr: "e \<in> set es" and div: "divisor \<in> expression_divisors e"
    obtain obligations obligation where
      obs: "(v, obligations) \<in> set (arithmetic_sites (prog_cfg p))"
      and ob: "obligation \<in> set obligations"
      and divisor: "arithmetic_divisor obligation = divisor"
      by (rule arithmetic_sites_divisor[OF site expr div])
    have verdict: "arithmetic_site_verdict r classify v obligation = Lifted Check_Proved"
      using arithmetic_diagnostics_absent[OF obs ob absent]
        arithmetic_site_verdict_not_bot[OF finite_contexts look, of classify obligation]
      by blast
    have classified: "classify (arithmetic_condition obligation) st = Check_Proved"
      by (rule arithmetic_site_verdict_classify[OF verdict _ look]) simp
    from proved[OF classified gst] show "aval divisor s \<noteq> 0"
      by (auto simp: arithmetic_condition_def divisor split: if_splits)
  qed
  show ?thesis unfolding arithmetic_safe_at_def using safe by blast
qed

lemma result_sound_at:
  assumes checks: "res_checks res =
      result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
    and diagnostics: "res_diagnostics res = arithmetic_diagnostics (prog_cfg p) r classify"
    and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
      (cinit_stores (declared_global p)) v"
  shows "table_covers r v s \<and> checks_sound_at res v s \<and> diagnostics_sound_at res p v s"
  using sound_at[OF checks mem] arithmetic_safe[OF _ mem]
  unfolding diagnostics_sound_at_def diagnostics by blast

text \<open>
  Compile the program, solve, take the result --- then run the source program
  itself and stop wherever you like. The store in your hands sits at a graph node
  with a frame stack (\<^const>\<open>csim\<close>), so the run and the analysis talk about the
  same place with no separate reachability argument; the table describes it at
  that node; and every check listed there holds of it, with none there marked
  dead.
\<close>

theorem source_sound:
  fixes s0 s :: store
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) (prog_procs p)"
      and s0: "s0 \<in> cinit_stores (declared_global p)"
      and run: "star (pstep (declared_global p) (prog_table p))
                  (main_body (prog_table p), s0, []) (residual, s, frs)"
      and checks: "res_checks res
                     = result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
               \<and> s \<in> ltr_collect (declared_global p) (prog_cfg p)
                         (cinit_stores (declared_global p)) v
               \<and> table_covers r v s \<and> checks_sound_at res v s"
proof -
  have cfg: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)" by (rule prog_cfg_def)
  from source_reaches_ltr_collect [OF wf s0 run]
  obtain v stk
    where m: "csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)"
      and mem: "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                      (cinit_stores (declared_global p)) v"
    unfolding cfg by blast
  with sound_at [OF checks mem] show ?thesis by blast
qed

text \<open>
  What a dead check claims, stated at the point rather than at a run. The endpoint
  above is existential in its witness, so reading it backwards --- ``this check is
  dead, therefore nothing reaches it'' --- does not follow from it. It is proved
  forwards instead: a dead aggregate means no context published a live entry at
  the point, and a store reaching it would have to sit in one.
\<close>

theorem ctx_dead_check_unreached:
  assumes checks: "res_checks res
                     = result_checks_of (classify_checks_verdicts (prog_cfg p) r classify)"
      and chk: "chk \<in> set (res_checks res)"
      and dead: "check_verdict chk = Dead"
  shows "ltr_collect (declared_global p) (prog_cfg p)
           (cinit_stores (declared_global p)) (check_point chk) = {}"
proof -
  have "(check_point chk, check_exp chk, Dead)
          \<in> set (classify_checks_verdicts (prog_cfg p) r classify)"
    using check_in_result_checks_of [OF chk [unfolded checks]] dead by simp
  note bot = classify_checks_verdicts_Dead_lookup_Bot [OF this finite_contexts]
  show ?thesis
  proof (rule equals0I)
    fix s
    assume "s \<in> ltr_collect (declared_global p) (prog_cfg p)
                  (cinit_stores (declared_global p)) (check_point chk)"
    from covers [OF this] obtain c st
      where "lookup_context r (check_point chk) c = Lifted st"
      unfolding table_covers_def by blast
    with bot show False by simp
  qed
qed

end

text \<open>
  The two shapes a published soundness result arrives in. A contextual route
  bounds each activation bucket by its own entry and exhausts the point with the
  buckets; a unit route bounds the point by its one entry directly.
\<close>

lemma sound_table_of_activation:
  fixes r :: "('c, 'a::sound_domain abs_state) analysis_result"
  assumes union: "\<And>u. ltr_collect (declared_global p) (prog_cfg p)
                          (cinit_stores (declared_global p)) u
                    \<subseteq> (\<Union>c. activation_collect (declared_global p) R rc (prog_cfg p)
                                (cinit_stores (declared_global p)) u c)"
      and sound: "\<And>u ctx. activation_collect (declared_global p) R rc (prog_cfg p)
                              (cinit_stores (declared_global p)) u ctx
                    \<subseteq> gamma_point (lookup_context r u ctx)"
      and fin: "finite_analysis_result r"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                        \<Longrightarrow> \<not> truthy (aval c t)"
  shows "sound_table p r classify"
proof (rule sound_table.intro)
  show "finite (contexts_at r v)" for v by (rule finite_contexts_at [OF fin])
  show "table_covers r v s"
    if "s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v"
    for v s
    by (meson lookup_context_covers_of_activation [OF union sound that] table_coversI)
qed (fact proved, fact refuted)

lemma sound_table_of_unit:
  fixes r :: "(unit, 'a::sound_domain abs_state) analysis_result"
  assumes node: "\<And>v. ltr_collect (declared_global p) (prog_cfg p)
                          (cinit_stores (declared_global p)) v
                    \<subseteq> gamma_point (lookup_context r v ())"
      and proved: "\<And>c d t. classify c d = Check_Proved \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c t)"
      and refuted: "\<And>c d t. classify c d = Check_Refuted \<Longrightarrow> t \<in> \<lbrakk>d\<rbrakk>
                        \<Longrightarrow> \<not> truthy (aval c t)"
  shows "sound_table p r classify"
proof (rule sound_table.intro)
  show "finite (contexts_at r v)" for v by simp
  show "table_covers r v s"
    if "s \<in> ltr_collect (declared_global p) (prog_cfg p) (cinit_stores (declared_global p)) v"
    for v s
  proof (cases "lookup_context r v ()")
    case Bot
    from subsetD [OF node [of v] that] Bot show ?thesis by simp
  next
    case (Lifted st)
    from subsetD [OF node [of v] that] Lifted have "s \<in> \<lbrakk>st\<rbrakk>" by simp
    then show ?thesis by (rule table_coversI [OF Lifted])
  qed
qed (fact proved, fact refuted)

subsection \<open>The context-free configurations\<close>

text \<open>
  Every discipline's registration is a \<^verbatim>\<open>global_interpretation\<close> of
  \<open>unit_dg_analysis\<close>, whose \<open>result_node_sound_of_terminates\<close> bounds a point
  once the program is well-formed and the solve terminated, so each table below asks
  for those two facts and nothing else.
\<close>

lemma sign_table:
  assumes "wf_program_compile_input p" and "sign_join.terminates (declared_global p) p"
  shows "sound_table p (analyse_sign_result p) sign_classify_check"
  by (rule sound_table_of_unit [OF _ sign_classify_check_proved sign_classify_check_refuted])
     (auto dest: sign_join.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: sign_join.state_at_unfold analyse_sign_result_def analyse_sign_result_for_def)

lemma interval_table:
  assumes "wf_program_compile_input p" and "interval_warrow_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_interval_result p) interval_classify_check"
  by (rule sound_table_of_unit
        [OF _ interval_classify_check_proved interval_classify_check_refuted])
     (auto dest: interval_warrow_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: interval_warrow_asm.state_at_unfold analyse_interval_result_def
          analyse_interval_result_for_def)

lemma int_table:
  assumes "wf_program_compile_input p" and "int_warrow_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_int_result p) int_classify_check"
  by (rule sound_table_of_unit [OF _ int_classify_check_proved int_classify_check_refuted])
     (auto dest: int_warrow_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: int_warrow_asm.state_at_unfold analyse_int_result_def analyse_int_result_for_def
          analyse_int_ctx_result_warrow_for_eq_pipeline int_unit_result_def)

lemma parity_table:
  assumes "wf_program_compile_input p" and "parity_join.terminates (declared_global p) p"
  shows "sound_table p (analyse_parity_result p) parity_classify_check"
  by (rule sound_table_of_unit
        [OF _ parity_classify_check_proved parity_classify_check_refuted])
     (auto dest: parity_join.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: parity_join.state_at_unfold analyse_parity_result_def analyse_parity_result_for_def)

lemma congruence_table:
  assumes "wf_program_compile_input p" and "congruence_join.terminates (declared_global p) p"
  shows "sound_table p (analyse_congruence_result p) congruence_classify_check"
  by (rule sound_table_of_unit
        [OF _ congruence_classify_check_proved congruence_classify_check_refuted])
     (auto dest: congruence_join.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: congruence_join.state_at_unfold analyse_congruence_result_def
          analyse_congruence_result_for_def)

lemma sign_po_table:
  assumes "wf_program_compile_input p" and "sign_po_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_sign_result_per_origin p) sign_classify_check"
  by (rule sound_table_of_unit [OF _ sign_classify_check_proved sign_classify_check_refuted])
     (auto dest: sign_po_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: sign_po_asm.state_at_unfold analyse_sign_result_per_origin_def
          analyse_sign_result_per_origin_for_def)

lemma parity_po_table:
  assumes "wf_program_compile_input p" and "parity_po_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_parity_result_per_origin p) parity_classify_check"
  by (rule sound_table_of_unit
        [OF _ parity_classify_check_proved parity_classify_check_refuted])
     (auto dest: parity_po_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: parity_po_asm.state_at_unfold analyse_parity_result_per_origin_def
          analyse_parity_result_per_origin_for_def)

lemma congruence_po_table:
  assumes "wf_program_compile_input p" and "congruence_po_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_congruence_result_per_origin p) congruence_classify_check"
  by (rule sound_table_of_unit
        [OF _ congruence_classify_check_proved congruence_classify_check_refuted])
     (auto dest: congruence_po_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: congruence_po_asm.state_at_unfold analyse_congruence_result_per_origin_def
          analyse_congruence_result_per_origin_for_def)

lemma interval_join_table:
  assumes "wf_program_compile_input p" and "interval_join_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_interval_result_join p) interval_classify_check"
  by (rule sound_table_of_unit
        [OF _ interval_classify_check_proved interval_classify_check_refuted])
     (auto dest: interval_join_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: interval_join_asm.state_at_unfold analyse_interval_result_join_def
          analyse_interval_result_join_for_def)

lemma interval_po_table:
  assumes "wf_program_compile_input p" and "interval_po_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_interval_result_per_origin p) interval_classify_check"
  by (rule sound_table_of_unit
        [OF _ interval_classify_check_proved interval_classify_check_refuted])
     (auto dest: interval_po_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: interval_po_asm.state_at_unfold analyse_interval_result_per_origin_def
          analyse_interval_result_per_origin_for_def)

lemma interval_wpo_table:
  assumes "wf_program_compile_input p" and "interval_wpo_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_interval_result_wpo p) interval_classify_check"
  by (rule sound_table_of_unit
        [OF _ interval_classify_check_proved interval_classify_check_refuted])
     (auto dest: interval_wpo_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: interval_wpo_asm.state_at_unfold analyse_interval_result_wpo_def
          analyse_interval_result_wpo_for_def)

lemma int_join_table:
  assumes "wf_program_compile_input p" and "int_join_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_int_join_result p) int_classify_check"
  by (rule sound_table_of_unit [OF _ int_classify_check_proved int_classify_check_refuted])
     (auto dest: int_join_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: int_join_asm.state_at_unfold analyse_int_join_result_def
          analyse_int_join_result_for_def int_join_result_def)

lemma int_po_table:
  assumes "wf_program_compile_input p" and "int_po_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_int_per_origin_result p) int_classify_check"
  by (rule sound_table_of_unit [OF _ int_classify_check_proved int_classify_check_refuted])
     (auto dest: int_po_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: int_po_asm.state_at_unfold analyse_int_per_origin_result_def
          analyse_int_per_origin_result_for_def int_po_result_def)

lemma int_wpo_table:
  assumes "wf_program_compile_input p" and "int_wpo_asm.terminates (declared_global p) p"
  shows "sound_table p (analyse_int_wpo_result p) int_classify_check"
  by (rule sound_table_of_unit [OF _ int_classify_check_proved int_classify_check_refuted])
     (auto dest: int_wpo_asm.result_node_sound_of_terminates [OF assms, THEN subsetD]
        simp: int_wpo_asm.state_at_unfold analyse_int_wpo_result_def
          analyse_int_wpo_result_for_def int_wpo_result_def)
end

