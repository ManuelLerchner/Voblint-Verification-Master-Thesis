theory Unit_DG_Analysis
  imports Routed_Live_Keys
begin

section \<open>The context-insensitive analysis, as the routed one at a single context\<close>

text \<open>
  A context-insensitive run is not a different pipeline; it is the routed
  pipeline at the degenerate policy that sends every call to the one context
  \<^term>\<open>()\<close>. \<open>unit_dg_analysis\<close> below is therefore an instance of
  \<^locale>\<open>routed_dg_analysis\<close> rather than a construction of its own: the equation
  system, the solve, the covered keys, the reader, the result table and the whole
  post-solution transport are inherited, and nothing here rebuilds them.

  What is genuinely unit-only, and all that this theory adds, is the publication
  surface and the source-level endpoints. A single context means a caller reads a
  program point without naming a context at all, so \<open>state_at\<close> and \<open>report\<close> go
  through \<^locale>\<open>analysis_surface\<close>; and it means the activation-indexed
  collecting semantics collapses to \<^const>\<open>ltr_collect\<close>, which is what lets the
  four endpoints below speak about source runs instead of activations. Neither
  statement is available at a policy with more than one context, which is why
  they live here and not in the routed assembly.

  Vocabulary. \<^const>\<open>route_unit\<close> is the routing function that answers \<^term>\<open>()\<close>
  for every call; \<^const>\<open>enterc_unit\<close> is its trace-semantic counterpart, and
  \<open>activation_collect_unit_eq_ltr_collect\<close> is the collapse between the two
  readings of a program point.
\<close>

subsection \<open>The contracts\<close>

text \<open>
  Exactly \<^locale>\<open>routed_dg_analysis\<close>'s, at the unit instantiation. Two of its
  twelve obligations are free here and are discharged by every registration in
  one line each: the routing agreement, because \<^const>\<open>route_unit\<close> answers in
  \<^typ>\<open>unit\<close> on both carriers, and the seed-key distinctness, because
  \<^const>\<open>Activation_Seed\<close> and \<^const>\<open>Analysis_Global\<close> are different
  constructors.
\<close>

locale unit_dg_analysis =
  routed_dg_analysis tf_st enter_st init_st "Analysis_Global ()" Activation_Seed
    "\<lambda>_. route_unit" "()" solve solve_dom bot_state classify
    sk asn spc br bd rt en ev "\<lambda>_. route_unit" solve_c
  for tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                  \<Rightarrow> 'a::sound_domain exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and init_st :: "'a exec_dg_st"
    and solve :: "(pp \<times> unit, (unit, unit) routed_gk,
                     ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                  \<Rightarrow> pp \<times> unit
                  \<Rightarrow> (pp \<times> unit) set
                       \<times> (pp \<times> unit + (unit, unit) routed_gk
                            \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)"
    and solve_dom :: "(pp \<times> unit, (unit, unit) routed_gk,
                        ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                      \<Rightarrow> pp \<times> unit \<Rightarrow> bool"
    and bot_state :: "'a abs_state"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
    and sk :: "'a abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and spc :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and solve_c :: "(pp \<times> unit, (unit, unit) routed_gk,
                      ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                    \<Rightarrow> pp \<times> unit
                    \<Rightarrow> ((pp \<times> unit) set
                          \<times> (pp \<times> unit + (unit, unit) routed_gk
                               \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)) option"
begin

subsection \<open>The publication surface a single context allows\<close>

text \<open>
  A caller reads a program point without naming a context, which is the whole
  difference the unit policy makes to the published surface.
\<close>

definition state_at :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> 'a abs_state" where
  "state_at \<G> = analysis_surface.state_at (result \<G>) bot_state"

lemma state_at_unfold:
  "state_at \<G> p v
     = (case lookup_context (result \<G> p) v () of Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st)"
  by (simp add: state_at_def analysis_surface.state_at_def)

definition report :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "report \<G> = analysis_surface.report (result \<G>) bot_state classify"

definition report_with_state :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 'a abs_state) list" where
  "report_with_state \<G> = analysis_surface.report_with_state (result \<G>) bot_state classify"

subsection \<open>What the assembly derives, for one program\<close>

context
  fixes p :: imp_prog
begin

abbreviation (input) ugs :: "vname \<Rightarrow> bool" where "ugs \<equiv> declared_global p"
  \<comment> \<open>input-only, so interpreted facts print \<open>declared_global p\<close>\<close>

text \<open>
  The four closure facts the routed spine turns on are the four conjuncts of
  \<^const>\<open>vars_cover\<close>, and \<^const>\<open>vars_cover_exec\<close> walks the two edge
  enumerations to decide them, so a caller discharges coverage by evaluation
  rather than by four case analyses over the solved key set.
\<close>

lemma vars_cover_of_exec_prog:
  assumes cover: "vars_cover_exec (prog_cfg p) (sol_vars ugs p)"
  shows "vars_cover (prog_cfg p) (sol_vars ugs p)"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

subsubsection \<open>The published soundness, under termination and coverage\<close>

context
  assumes solves: "terminates ugs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars ugs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars ugs p"
    and call_fwd_ok: "\<And>u ctx dst pars args q cont. (u, ctx) \<in> sol_vars ugs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> sol_vars ugs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars ugs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars ugs p"
    and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> sol_vars ugs p"
begin

text \<open>
  The one routed endpoint this policy needs, and the collapse that turns it into
  a statement about program points. \<^const>\<open>route_unit\<close> never reads the state it
  is handed --- it cannot, since it answers in \<^typ>\<open>unit\<close> --- so the applicable
  endpoint is the one for a route that is a function of the call site alone, at
  \<^const>\<open>enterc_unit\<close>. \<open>activation_collect_unit_eq_ltr_collect\<close> is then the
  identity between the activation-indexed reading and the program-point one.
\<close>

theorem result_node_sound_closure:
  "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v \<subseteq> \<lbrakk>state_at ugs p v\<rbrakk>"
proof -
  have "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v
      = activation_collect ugs (call_context_rel_of_fun enterc_unit) ()
          (prog_cfg p) (cinit_stores ugs) v ()"
    by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  also have "\<dots> \<subseteq> \<lbrakk>map_lift (fun_of_resolved_st_q_for ugs)
                     (reader ugs p (Inl (v, ())))\<rbrakk>\<^sub>\<bottom>"
  proof (rule fun_route_activation_collect_sound
      [where ctx_fun = enterc_unit, OF _ solves fwd_ok _ comb_fwd_ok entry_cov])
    show "\<And>u ctx d ca s. route_unit u ctx d ca = enterc_unit u ctx s" by simp
  next
    fix u ctx dst pars args q cont and d :: "'a exec_dg_st lifted"
    assume "(u, ctx) \<in> sol_vars ugs p"
      and "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    then show "(FunctionEntry q, route_unit u ctx d (CallEdge dst pars args))
                 \<in> sol_vars ugs p"
      using call_fwd_ok by simp
  qed
  finally have "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v
      \<subseteq> gamma_point (lookup_context (result ugs p) v ())"
    unfolding gamma_reader_eq_lookup .
  then show ?thesis
    unfolding state_at_unfold
    unfolding bot_state_eq
    by (simp add: gamma_state_case_eq_point)
qed

theorem report_proved_sound_closure:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved) \<in> set (report ugs p)"
  shows "\<forall>s \<in> \<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v. truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p" and env = "state_at ugs p" and classify = classify
             and reach = "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub>" and v = v
             and gamma_state = "gamma_state :: 'a abs_state \<Rightarrow> store set",
           OF finI _ classify_proved result_node_sound_closure])
       (use mem in \<open>simp add: report_def state_at_def surface_unfold\<close>)
qed

theorem report_refuted_sound_closure:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted) \<in> set (report ugs p)"
  shows "\<forall>s \<in> \<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v. \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p" and env = "state_at ugs p" and classify = classify
             and reach = "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub>" and v = v
             and gamma_state = "gamma_state :: 'a abs_state \<Rightarrow> store set",
           OF finI _ classify_refuted result_node_sound_closure])
       (use mem in \<open>simp add: report_def state_at_def surface_unfold\<close>)
qed

text \<open>
  The source-level endpoint. \<open>source_sound_from_ltr_collecting_cap\<close> turns any
  per-node cap on \<^const>\<open>ltr_collect\<close> into a statement about an actual run, and
  \<open>result_node_sound_closure\<close> is that cap.
\<close>

theorem source_sound_closure:
  fixes s0 s :: store
  assumes wf: "wf_compile_input ugs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores ugs"
    and run: "ugs, prog_table p \<turnstile> (main_body (prog_table p), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<lbrakk>state_at ugs p v\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  show ?thesis
    unfolding cfg_eq
    by (rule source_sound_from_ltr_collecting_cap[OF wf s0 run])
       (use result_node_sound_closure in \<open>simp add: cfg_eq\<close>)
qed

theorem completed_run_sound_closure:
  fixes s0 s :: store
  assumes wf: "wf_compile_input ugs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores ugs"
    and run: "ugs, prog_table p \<turnstile> (main_body (prog_table p), s0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, s, [])"
  shows "s \<in> \<lbrakk>state_at ugs p (cfg_exit (prog_cfg p))\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "s \<in> \<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> (cfg_exit (prog_cfg p))"
    using source_completes_ltr_collect_exit[OF wf s0 run] unfolding cfg_eq .
  then show ?thesis using result_node_sound_closure by blast
qed

end

subsubsection \<open>The same endpoints under the packaged coverage condition\<close>

text \<open>
  \<^const>\<open>vars_cover\<close> packages the four closure facts into one condition a caller
  can decide by evaluation, at the price of asking for closure out of \<^emph>\<open>every\<close>
  node rather than only out of the covered ones. Every endpoint above therefore
  has a \<open>vars_cover\<close> reading, and these are the shapes a whole-program caller
  actually uses.
\<close>

lemma cover_entry:
  "vars_cover (prog_cfg p) (sol_vars ugs p)
     \<Longrightarrow> (cfg_entry (prog_cfg p), ()) \<in> sol_vars ugs p"
  by (rule vars_cover_entryD)

lemma cover_fwd:
  "vars_cover (prog_cfg p) (sol_vars ugs p) \<Longrightarrow> (u, ctx) \<in> sol_vars ugs p
     \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars ugs p"
  by (simp add: vars_cover_def)

lemma cover_call_fwd:
  "vars_cover (prog_cfg p) (sol_vars ugs p) \<Longrightarrow> (u, ctx) \<in> sol_vars ugs p
     \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
     \<Longrightarrow> (FunctionEntry q, ()) \<in> sol_vars ugs p"
  by (simp add: vars_cover_def)

lemma cover_comb_fwd:
  "vars_cover (prog_cfg p) (sol_vars ugs p) \<Longrightarrow> (cl, c1) \<in> sol_vars ugs p
     \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
     \<Longrightarrow> (cont, c1) \<in> sol_vars ugs p"
  by (simp add: vars_cover_def)

theorem result_node_sound:
  assumes solves: "terminates ugs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars ugs p)"
  shows "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v \<subseteq> \<lbrakk>state_at ugs p v\<rbrakk>"
  by (rule result_node_sound_closure[OF solves cover_fwd[OF cover]
        cover_call_fwd[OF cover] cover_comb_fwd[OF cover] cover_entry[OF cover]])

theorem report_proved_sound:
  fixes v :: pp and c :: exp
  assumes solves: "terminates ugs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars ugs p)"
    and mem: "(v, c, Check_Proved) \<in> set (report ugs p)"
  shows "\<forall>s \<in> \<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v. truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  by (rule report_proved_sound_closure[OF solves cover_fwd[OF cover]
        cover_call_fwd[OF cover] cover_comb_fwd[OF cover] cover_entry[OF cover] mem])

theorem report_refuted_sound:
  fixes v :: pp and c :: exp
  assumes solves: "terminates ugs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars ugs p)"
    and mem: "(v, c, Check_Refuted) \<in> set (report ugs p)"
  shows "\<forall>s \<in> \<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v. \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
  by (rule report_refuted_sound_closure[OF solves cover_fwd[OF cover]
        cover_call_fwd[OF cover] cover_comb_fwd[OF cover] cover_entry[OF cover] mem])

theorem source_sound:
  fixes s0 s :: store
  assumes solves: "terminates ugs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars ugs p)"
    and wf: "wf_compile_input ugs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores ugs"
    and run: "ugs, prog_table p \<turnstile> (main_body (prog_table p), s0, []) \<rightarrow>\<^sub>p\<^sup>* (residual, s, frs)"
  shows "\<exists>v stk. prog_table p, prog_cfg p \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> \<lbrakk>state_at ugs p v\<rbrakk>"
  by (rule source_sound_closure[OF solves cover_fwd[OF cover]
        cover_call_fwd[OF cover] cover_comb_fwd[OF cover] cover_entry[OF cover]
        wf s0 run])

theorem completed_run_sound:
  fixes s0 s :: store
  assumes solves: "terminates ugs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars ugs p)"
    and wf: "wf_compile_input ugs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores ugs"
    and run: "ugs, prog_table p \<turnstile> (main_body (prog_table p), s0, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, s, [])"
  shows "s \<in> \<lbrakk>state_at ugs p (cfg_exit (prog_cfg p))\<rbrakk>"
  by (rule completed_run_sound_closure[OF solves cover_fwd[OF cover]
        cover_call_fwd[OF cover] cover_comb_fwd[OF cover] cover_entry[OF cover]
        wf s0 run])

subsubsection \<open>The table of any terminating solve\<close>

theorem result_node_sound_of_terminates:
  assumes wf: "wf_program_compile_input p" and solves: "terminates ugs p"
  shows "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v \<subseteq> \<lbrakk>state_at ugs p v\<rbrakk>"
proof -
  have "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v
      = activation_collect ugs (call_context_rel_of_fun enterc_unit) ()
          (prog_cfg p) (cinit_stores ugs) v ()"
    by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  also have "\<dots> \<subseteq> \<lbrakk>map_lift (fun_of_resolved_st_q_for ugs)
                     (reader ugs p (Inl (v, ())))\<rbrakk>\<^sub>\<bottom>"
    by (rule fun_route_activation_collect_sound_of_terminates
          [where ctx_fun = enterc_unit, OF _ wf solves]) simp
  finally have "\<C>\<^bsub>ugs,prog_cfg p,cinit_stores ugs\<^esub> v
      \<subseteq> gamma_point (lookup_context (result ugs p) v ())"
    unfolding gamma_reader_eq_lookup .
  then show ?thesis
    unfolding state_at_unfold
    unfolding bot_state_eq
    by (simp add: gamma_state_case_eq_point)
qed

end

end

subsection \<open>Executability of the unit-only surface\<close>

text \<open>
  Nothing is declared here, and that is deliberate. \<^locale>\<open>unit_dg_analysis\<close>
  has assumptions, and \<open>state_at\<close>, \<open>report\<close> and \<open>report_with_state\<close> have types
  that omit the domain type variable, so \<open>[code]\<close> would reject their definitions
  with a warning and silently add no equation. An executable use unfolds them at
  the use site instead. The objects inherited from \<^locale>\<open>routed_dg_pipeline\<close>
  keep the equations declared there.
\<close>

end
