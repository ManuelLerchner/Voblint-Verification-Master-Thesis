theory Unit_DG_Analysis
  imports
    DG_Result_Construction
    Analysis_Surface
    "Voblint_Soundness.Run_Analysis_Sound"
    "Voblint_Routing.Compiled_Routed_Equations"
begin

section \<open>One context-insensitive analysis, assembled from its four choices\<close>

text \<open>
  A concrete analysis picks a domain implementation, an initial state, a solver
  and a classifier; everything between those choices and the published report is
  the same work at every domain. This theory does that work once. The
  construction half is \<open>unit_dg_pipeline\<close>, which carries no correctness
  assumptions, so its defining equations are unconditional and can be declared to
  the code generator; the correctness half is \<open>unit_dg_analysis\<close>, which adds the
  domain and solver contracts and derives the published soundness theorems from
  them. Being assumption-free is what makes those equations \<^emph>\<open>eligible\<close> to be
  code equations; it does not make them executable, which is a separate
  declaration and a separate check.

  What this covers, and what it does not. It is the assembly for one family:
  executable non-relational analyses whose local unknown carries a whole
  reachability-lifted store, routed at the single \<^typ>\<open>unit\<close> context, keyed by
  \<^type>\<open>routed_gk\<close>, and read back at the program's own declared globals. A
  relational carrier, a context policy with more than one context, or an entry
  specification that answers with several alternatives does not become an
  instance by supplying different operations.

  Vocabulary used below. A \<^emph>\<open>routed\<close> equation system publishes a callee's entry
  state at a global seed key instead of reading the callee entry directly; the
  \<^emph>\<open>unit\<close> context is the degenerate routing policy that sends every call to the
  single context \<^term>\<open>()\<close>. \<^emph>\<open>Covered\<close> keys are the unknowns the solver actually
  stabilized; an uncovered key is absent from the published table and reads back
  as \<^const>\<open>Bot\<close> without any claim about the program.
\<close>

subsection \<open>The construction\<close>

text \<open>
  \<open>init_st\<close> is the unlifted entry state; the pipeline lifts it, because a
  reachability-lifted carrier is what the routed generator solves over.
  \<open>bot_state\<close> is a parameter rather than the \<^class>\<open>order_bot\<close> operation for the
  same code-generation reason \<^locale>\<open>analysis_surface\<close> states: a sort constraint
  here would demand an executable \<^const>\<open>bot\<close> at a function type.
\<close>

locale unit_dg_pipeline =
  fixes tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                    \<Rightarrow> 'a::executable_domain exec_dg_st \<Rightarrow> 'a exec_dg_st"
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
begin

definition analysis_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, unit,
         'a exec_dg_st lifted, 'a exec_dg_st lifted) dg_spec" where
  "analysis_spec gs p =
     local_state_dg_spec_st_for_lifted gs
       (resolved_st_q_is_bot_for (declared_global_vars p)) (tf_st gs) (enter_st gs)"

text \<open>
  The unknown the solver is asked for. It is the program exit, not the program
  entry: a demand-driven solver is started at the answer a caller wants and
  explores backwards from it, so the root query is the exit and the entry point
  is reached as one of its dependencies.
\<close>

definition root_query :: "imp_prog \<Rightarrow> pp \<times> unit" where
  "root_query p = (cfg_exit (prog_cfg p), ())"

definition equations :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT" where
  "equations gs p =
     compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
       (analysis_spec gs p) (prog_cfg p) (Lifted init_st)"

definition solution :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> unit) set
         \<times> (pp \<times> unit + (unit, unit) routed_gk
              \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)" where
  "solution gs p = solve (equations gs p) (root_query p)"

definition terminates :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "terminates gs p = solve_dom (equations gs p) (root_query p)"

definition sol_vars :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> unit) set" where
  "sol_vars gs p = fst (solution gs p)"

definition sol_env :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> unit + (unit, unit) routed_gk
         \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state" where
  "sol_env gs p = snd (solution gs p)"

definition reader :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> 'a exec_dg_st lifted" where
  "reader gs p = solved_local_reader (sol_vars gs p) (sol_env gs p)"

definition result :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (unit, 'a abs_state) analysis_result" where
  "result gs p = dg_result_for gs (declared_global_vars p) (solution gs p)"

definition globals :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list" where
  "globals gs p =
     dg_globals_for gs (declared_global_vars p) (sol_env gs p)
       (unit_seed_global_keys (Analysis_Global ()) Activation_Seed p)"

text \<open>
  The two published halves of one run. The solve is bound once and both halves
  read that binding, so asking for the table and the globals together costs one
  solve rather than two --- \<^const>\<open>ctx_solved_for\<close> takes the same care, and for
  the same reason.
\<close>

definition solved :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (unit, 'a abs_state) analysis_result
         \<times> (String.literal \<times> 'a abs_state lifted) list" where
  "solved gs p =
     (let sol = solution gs p; gl = declared_global_vars p
      in (dg_result_for gs gl sol,
          dg_globals_for gs gl (snd sol)
            (unit_seed_global_keys (Analysis_Global ()) Activation_Seed p)))"

lemma solved_eq: "solved gs p = (result gs p, globals gs p)"
  by (simp add: solved_def result_def globals_def sol_env_def Let_def)

definition state_at :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> 'a abs_state" where
  "state_at gs = analysis_surface.state_at (result gs) bot_state"

lemma state_at_unfold:
  "state_at gs p v
     = (case lookup_context (result gs p) v () of Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st)"
  by (simp add: state_at_def analysis_surface.state_at_def)

definition report :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> check_report_entry list" where
  "report gs = analysis_surface.report (result gs) bot_state classify"

definition report_with_state :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 'a abs_state) list" where
  "report_with_state gs = analysis_surface.report_with_state (result gs) bot_state classify"

end

subsection \<open>Executability of the derived objects\<close>

text \<open>
  A locale constant carries no code equation of its own, so every object the
  pipeline derives would drop out of the generated code and out of
  \<^theory_text>\<open>eval\<close> alike. Each defining equation is already in executable shape, so
  declaring them is all the code generator needs --- the same step
  \<^locale>\<open>analysis_surface\<close> takes for its own two readings.

  \<open>analysis_spec\<close> is the exception, and it is the project's standing rule for a
  named \<^type>\<open>dg_spec\<close>: its unknown and global-key types occur only inside its
  transfer programs, never in an argument that builds it, so it has no most
  general ML type. Unfolding it at code-generation time is what keeps it out of
  the emitted program.
\<close>

declare unit_dg_pipeline.analysis_spec_def [code_unfold]

declare unit_dg_pipeline.equations_def [code]
declare unit_dg_pipeline.solution_def [code]
declare unit_dg_pipeline.terminates_def [code]
declare unit_dg_pipeline.sol_vars_def [code]
declare unit_dg_pipeline.sol_env_def [code]
declare unit_dg_pipeline.reader_def [code]
declare unit_dg_pipeline.result_def [code]
declare unit_dg_pipeline.globals_def [code]
declare unit_dg_pipeline.solved_def [code]
declare unit_dg_pipeline.state_at_def [code]
declare unit_dg_pipeline.report_def [code]
declare unit_dg_pipeline.report_with_state_def [code]

subsection \<open>The contracts\<close>

text \<open>
  What an instance owes, and nothing more: the abstract transfer it implements is
  sound, its executable mirror reads back to that transfer, its solver answers a
  post-solution over finitely many keys once it terminates, its classifier is
  correct, and its entry state describes every initial store. The equation
  system, the solve, the covered keys, the reader, the result table and the
  report are all fixed by \<^locale>\<open>unit_dg_pipeline\<close> above and appear here only in
  conclusions.
\<close>

locale unit_dg_analysis =
  unit_dg_pipeline tf_st enter_st init_st solve solve_dom bot_state classify
  for tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                  \<Rightarrow> 'a::sound_domain exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and init_st :: "'a exec_dg_st"
    and solve solve_dom
    and bot_state :: "'a abs_state"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result" +
  fixes sk :: "'a abs_state \<Rightarrow> 'a abs_state"
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
  assumes tf_sound: "\<And>gs. sound_transfer_for gs sk asn spc br bd rt (en gs) ev"
    and tf_commute:
      "\<And>gs a s. live_resolved_st_q gs s
         \<Longrightarrow> fun_of_exec_dg_st_for gs (tf_st gs a s)
               = local_spec_step sk asn spc br bd rt ev a (fun_of_exec_dg_st_for gs s)"
    and enter_commute:
      "\<And>gs ci s. fun_of_exec_dg_st_for gs (enter_st gs ci s)
                    = en gs ci (fun_of_exec_dg_st_for gs s)"
    and solve_pp:
      "\<And>eqs x. solve_dom eqs x
         \<Longrightarrow> part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    and solve_fin: "\<And>eqs x. solve_dom eqs x \<Longrightarrow> finite (fst (solve eqs x))"
    and classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk> \<Longrightarrow> truthy (aval c s)"
    and classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
         \<Longrightarrow> \<not> truthy (aval c s)"
    and bot_state_eq: "bot_state = bot"
    and init_sound:
      "\<And>gs. cinit_stores gs
               \<subseteq> gamma_state_lift (map_lift (fun_of_exec_dg_st_for gs) (Lifted init_st))"
    and dom_of_solve_c: "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow> solve_dom eqs x"
begin

text \<open>
  Termination is a per-program side condition, and this is how a caller decides
  it: run the solver's own executable termination check on this program's
  equations. The premise stays \<open>solve_dom\<close> everywhere else, so nothing in the
  soundness argument depends on the check having been run.
\<close>

lemma terminates_of_solve_c:
  assumes "solve_c (equations gs p) (root_query p) \<noteq> None"
  shows "terminates gs p"
  unfolding terminates_def by (rule dom_of_solve_c[OF assms])

text \<open>
  Finitely many covered keys is the solver's other contract, and termination is
  all it needs. Coverage plays no part, so this is stated outside the per-program
  coverage context that the soundness endpoints live in.
\<close>

lemma vars_finite_of_terminates:
  assumes "terminates gs p"
  shows "finite (sol_vars gs p)"
  using solve_fin[OF assms[unfolded terminates_def]]
  by (simp add: sol_vars_def solution_def)

subsection \<open>What the assembly derives, for one program\<close>

text \<open>
  Soundness fixes the classifier at the program's own declaration predicate,
  because that is the only classifier for which the executable bottom test and
  the semantic emptiness test agree. \<open>empty_pred_exact\<close> is that agreement, and
  \<^theory_text>\<open>resolved_st_q_is_bot_for_iff\<close> is what proves it; what the executable test
  actually inspects is that lemma's business, not this header's.
\<close>

context
  fixes p :: imp_prog
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

lemma empty_pred_exact:
  "resolved_st_q_is_bot_for (declared_global_vars p) s
     = is_empty_state (fun_of_resolved_st_q_for pgs s)"
  by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])

text \<open>
  The registered executable analysis this program's choices amount to. Its
  termination oracle is this locale's own \<open>solve_dom\<close>, wrapped as the option the
  registration locale expects, so the premise a caller discharges stays
  \<open>solve_dom\<close> and never strengthens to an executable run of the solver.
\<close>

interpretation base: local_state_dg_exec_analysis
    pgs sk asn spc br bd rt "en pgs" ev "tf_st pgs" "enter_st pgs"
    "resolved_st_q_is_bot_for (declared_global_vars p)"
    solve "\<lambda>eqs x. if solve_dom eqs x then Some (solve eqs x) else None"
proof (rule local_state_dg_exec_analysis.intro)
  show "sound_transfer_for pgs sk asn spc br bd rt (en pgs) ev"
    by (rule tf_sound)
next
  show "\<And>a s. live_resolved_st_q pgs s
      \<Longrightarrow> fun_of_exec_dg_st_for pgs (tf_st pgs a s)
            = local_spec_step sk asn spc br bd rt ev a (fun_of_exec_dg_st_for pgs s)"
    by (rule tf_commute)
next
  show "\<And>ci s. fun_of_exec_dg_st_for pgs (enter_st pgs ci s)
                  = en pgs ci (fun_of_exec_dg_st_for pgs s)"
    by (rule enter_commute)
next
  show "\<And>s. resolved_st_q_is_bot_for (declared_global_vars p) s
               = is_empty_state (fun_of_exec_dg_st_for pgs s)"
    unfolding fun_of_exec_dg_st_for_def by (rule empty_pred_exact)
next
  show "\<And>eqs x. (if solve_dom eqs x then Some (solve eqs x) else None) \<noteq> None
      \<Longrightarrow> part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solve_pp) (simp split: if_split_asm)
qed

text \<open>The pipeline's equation system is the registered analysis's own: the
  routing-generic constructor at the unit context and the unit-specialised one
  are the same term.\<close>

lemma equations_alt:
  "equations pgs p = base.routed_eqs (prog_table p) (prog_procs p) bot (Lifted init_st) bot"
  by (simp add: equations_def analysis_spec_def compiled_routed_eqs_for_def
      unit_routed_eqs_buffered_def prog_cfg_def)

lemma terminates_alt:
  "terminates pgs p
     = solve_dom (base.routed_eqs (prog_table p) (prog_procs p) bot (Lifted init_st) bot)
         (root_query p)"
  by (simp add: terminates_def equations_alt)

lemma solution_alt:
  "solution pgs p
     = solve (base.routed_eqs (prog_table p) (prog_procs p) bot (Lifted init_st) bot)
         (root_query p)"
  by (simp add: solution_def equations_alt)
subsubsection \<open>Coverage as one checkable side condition\<close>

text \<open>
  The four closure facts the routed spine turns on are the four conjuncts of
  \<^const>\<open>vars_cover\<close>, and \<^const>\<open>vars_cover_exec\<close> walks the two edge
  enumerations to decide them, so a caller discharges coverage by evaluation
  rather than by four case analyses over the solved key set.
\<close>

lemma vars_cover_of_exec_prog:
  assumes cover: "vars_cover_exec (prog_cfg p) (sol_vars pgs p)"
  shows "vars_cover (prog_cfg p) (sol_vars pgs p)"
  by (rule vars_cover_of_exec[OF _ _ cover])
     (simp_all add: prog_cfg_def compile_prog_finite)

subsubsection \<open>The published soundness, under termination and coverage\<close>

context
  assumes solves: "terminates pgs p"
    and entry_cov: "(cfg_entry (prog_cfg p), ()) \<in> sol_vars pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and call_fwd_ok: "\<And>u ctx dst pars args q cont. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, ()) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
begin

lemma routed_context_prog:
  "unit_routed_context base.spec_st base.gamma_exec pgs (prog_cfg p)
     (Analysis_Global ()) bot (Lifted init_st) bot (sol_env pgs p) (sol_vars pgs p)
     (root_query p) (reader pgs p) Activation_Seed (\<lambda>d. d = bot)
     (\<lambda>d. gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) d))"
proof -
  let ?eqs = "base.routed_eqs (prog_table p) (prog_procs p) bot (Lifted init_st) bot"
  have vars_alt: "fst (solve ?eqs (root_query p)) = sol_vars pgs p"
    by (simp add: sol_vars_def solution_alt)
  have solvec: "(if solve_dom ?eqs (root_query p)
                 then Some (solve ?eqs (root_query p)) else None) \<noteq> None"
    using solves by (simp add: terminates_alt)
  have finI: "finite (intra (compile_prog (prog_table p) (prog_procs p)))"
    by (simp add: compile_prog_finite)
  have R: "unit_routed_context base.spec_st base.gamma_exec pgs
      (compile_prog (prog_table p) (prog_procs p)) (Analysis_Global ()) bot
      (Lifted init_st) bot
      (snd (solve ?eqs (root_query p))) (fst (solve ?eqs (root_query p)))
      (root_query p)
      (solved_local_reader (fst (solve ?eqs (root_query p)))
        (snd (solve ?eqs (root_query p))))
      Activation_Seed (\<lambda>d. d = bot) (\<lambda>d. base.gamma_exec d bot)"
  proof (rule base.unit_routed_context_of_solve_closure[OF solvec])
    show "\<And>u a v ctx. (u, ctx) \<in> fst (solve ?eqs (root_query p))
        \<Longrightarrow> (u, a, v) \<in> intra (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (v, ctx) \<in> fst (solve ?eqs (root_query p))"
      unfolding vars_alt using fwd_ok by (simp add: prog_cfg_def)
  next
    show "\<And>u ctx dst pars args q cont. (u, ctx) \<in> fst (solve ?eqs (root_query p))
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont)
              \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (FunctionEntry q, ()) \<in> fst (solve ?eqs (root_query p))"
      unfolding vars_alt using call_fwd_ok by (simp add: prog_cfg_def)
  next
    show "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> fst (solve ?eqs (root_query p))
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont)
              \<in> calls (compile_prog (prog_table p) (prog_procs p))
        \<Longrightarrow> (cont, c1) \<in> fst (solve ?eqs (root_query p))"
      unfolding vars_alt using comb_fwd_ok by (simp add: prog_cfg_def)
  next
    show "finite (intra (compile_prog (prog_table p) (prog_procs p)))" by (rule finI)
  qed
  have gfun: "(\<lambda>d. gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) d))
                = (\<lambda>d. base.gamma_exec d bot)"
    by (simp add: base.gamma_exec_def)
  show ?thesis
    using R unfolding gfun
    by (simp add: sol_vars_def sol_env_def solution_alt reader_def prog_cfg_def)
qed

lemma vars_finite: "finite (sol_vars pgs p)"
  using solve_fin[OF solves[unfolded terminates_def]]
  by (simp add: sol_vars_def solution_def)

lemma init_gamma: "cinit_stores pgs \<subseteq> base.gamma_exec (Lifted init_st) bot"
  using init_sound[of pgs]
  by (simp add: base.gamma_exec_def fun_of_exec_dg_st_for_def)

interpretation published: unit_analysis_sound
    base.spec_st base.gamma_exec pgs "prog_cfg p" "Analysis_Global ()"
    bot "Lifted init_st" bot "sol_env pgs p" "sol_vars pgs p" "root_query p"
    Activation_Seed "\<lambda>d. d = bot"
    "map_lift (fun_of_resolved_st_q_for pgs)" classify
proof (rule unit_analysis_sound.intro)
  show "unit_routed_context base.spec_st base.gamma_exec pgs (prog_cfg p)
      (Analysis_Global ()) bot (Lifted init_st) bot (sol_env pgs p) (sol_vars pgs p)
      (root_query p)
      (solved_local_reader (sol_vars pgs p) (sol_env pgs p)) Activation_Seed
      (\<lambda>d. d = bot)
      (\<lambda>d. gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) d))"
    using routed_context_prog unfolding reader_def .
next
  show "unit_analysis_sound_axioms base.gamma_exec (sol_vars pgs p)
      (map_lift (fun_of_resolved_st_q_for pgs)) classify"
  proof (rule unit_analysis_sound_axioms.intro)
    show "\<And>d g'. base.gamma_exec d g'
        = gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) d)"
      by (simp add: base.gamma_exec_def)
  next
    show "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> truthy (aval c s)"
      by (rule classify_proved)
  next
    show "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<lbrakk>d\<rbrakk>
        \<Longrightarrow> \<not> truthy (aval c s)"
      by (rule classify_refuted)
  next
    show "finite (sol_vars pgs p)" by (rule vars_finite)
  qed
qed

text \<open>
  The published table is the adapter's own. The two equations below are what
  transfers node soundness onto it: the covered keys are literally the same set,
  and at every key the two tables read the solved unknown back the same way ---
  one spelling the emptiness test with the program's declared globals, the other
  with the semantic test, which \<open>empty_pred_exact\<close> identifies.

  Only the second is used below, and it says nothing about which keys are
  covered; a caller that needs to tell an uncovered key from a covered one
  holding \<^const>\<open>Bot\<close> needs the first as well.
\<close>

lemma result_keys_eq_adapter:
  "result_keys (result pgs p) = result_keys published.adapter.analyse_result"
  unfolding result_def published.adapter.analyse_result_def
  by (simp add: sol_vars_def sol_env_def)

lemma lookup_context_eq_adapter:
  "lookup_context (result pgs p) v ctx
     = lookup_context published.adapter.analyse_result v ctx"
  unfolding published.adapter.lookup_context_analyse_result result_def
  by (simp add: sol_vars_def sol_env_def
      readback_canonicalize_lift_eq[OF empty_pred_exact])

lemma state_at_eq:
  "state_at pgs p v
     = (case lookup_context (result pgs p) v () of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st)"
  unfolding state_at_unfold
  unfolding bot_state_eq
  by (rule refl)

theorem result_node_sound_closure:
  "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v \<subseteq> \<lbrakk>state_at pgs p v\<rbrakk>"
proof -
  have "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
      = activation_collect pgs (call_context_rel_of_fun enterc_unit) ()
          (prog_cfg p) (cinit_stores pgs) v ()"
    by (rule activation_collect_unit_eq_ltr_collect[symmetric])
  also have "\<dots> \<subseteq> \<lbrakk>case lookup_context published.adapter.analyse_result v () of
                     Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st\<rbrakk>"
    by (rule published.adapter.analyse_result_node_sound[OF entry_cov init_gamma])
  finally show ?thesis
    unfolding state_at_eq lookup_context_eq_adapter .
qed

theorem report_proved_sound_closure:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Proved) \<in> set (report pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_proved_sound
          [where g = "prog_cfg p" and env = "state_at pgs p" and classify = classify
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)" and v = v
             and gamma_state = "gamma_state :: 'a abs_state \<Rightarrow> store set",
           OF finI _ classify_proved result_node_sound_closure])
       (use mem in \<open>simp add: report_def state_at_def surface_unfold\<close>)
qed

theorem report_refuted_sound_closure:
  fixes v :: pp and c :: exp
  assumes mem: "(v, c, Check_Refuted) \<in> set (report pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
proof -
  have finI: "finite (intra (prog_cfg p))"
    unfolding prog_cfg_def using compile_prog_finite by simp
  show ?thesis
    by (rule classify_checks_refuted_sound
          [where g = "prog_cfg p" and env = "state_at pgs p" and classify = classify
             and reach = "ltr_collect pgs (prog_cfg p) (cinit_stores pgs)" and v = v
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
  assumes wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>state_at pgs p v\<rbrakk>"
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
  assumes wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>state_at pgs p (cfg_exit (prog_cfg p))\<rbrakk>"
proof -
  have cfg_eq: "prog_cfg p = compile_prog (prog_table p) (prog_procs p)"
    by (rule prog_cfg_def)
  have "s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) (cfg_exit (prog_cfg p))"
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
  "vars_cover (prog_cfg p) (sol_vars pgs p)
     \<Longrightarrow> (cfg_entry (prog_cfg p), ()) \<in> sol_vars pgs p"
  by (rule vars_cover_entryD)

lemma cover_fwd:
  "vars_cover (prog_cfg p) (sol_vars pgs p) \<Longrightarrow> (u, ctx) \<in> sol_vars pgs p
     \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
  by (simp add: vars_cover_def)

lemma cover_call_fwd:
  "vars_cover (prog_cfg p) (sol_vars pgs p) \<Longrightarrow> (u, ctx) \<in> sol_vars pgs p
     \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
     \<Longrightarrow> (FunctionEntry q, ()) \<in> sol_vars pgs p"
  by (simp add: vars_cover_def)

lemma cover_comb_fwd:
  "vars_cover (prog_cfg p) (sol_vars pgs p) \<Longrightarrow> (cl, c1) \<in> sol_vars pgs p
     \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
     \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
  by (simp add: vars_cover_def)

lemmas cover_closure =
  cover_entry cover_fwd cover_call_fwd cover_comb_fwd

theorem result_node_sound:
  assumes solves: "terminates pgs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v \<subseteq> \<lbrakk>state_at pgs p v\<rbrakk>"
  by (rule result_node_sound_closure[OF solves cover_entry[OF cover]
        cover_fwd[OF cover] cover_call_fwd[OF cover] cover_comb_fwd[OF cover]])

theorem report_proved_sound:
  fixes v :: pp and c :: exp
  assumes solves: "terminates pgs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars pgs p)"
    and mem: "(v, c, Check_Proved) \<in> set (report pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. truthy (aval c s)"
  by (rule report_proved_sound_closure[OF solves cover_entry[OF cover]
        cover_fwd[OF cover] cover_call_fwd[OF cover] cover_comb_fwd[OF cover] mem])

theorem report_refuted_sound:
  fixes v :: pp and c :: exp
  assumes solves: "terminates pgs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars pgs p)"
    and mem: "(v, c, Check_Refuted) \<in> set (report pgs p)"
  shows "\<forall>s \<in> ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v. \<not> truthy (aval c s)"
  by (rule report_refuted_sound_closure[OF solves cover_entry[OF cover]
        cover_fwd[OF cover] cover_call_fwd[OF cover] cover_comb_fwd[OF cover] mem])

theorem source_sound:
  fixes s0 s :: store
  assumes solves: "terminates pgs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars pgs p)"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. csim (prog_table p) (prog_cfg p) (residual, s, frs) (v, s, stk)
                 \<and> s \<in> \<lbrakk>state_at pgs p v\<rbrakk>"
  by (rule source_sound_closure[OF solves cover_entry[OF cover]
        cover_fwd[OF cover] cover_call_fwd[OF cover] cover_comb_fwd[OF cover]
        wf s0 run])

theorem completed_run_sound:
  fixes s0 s :: store
  assumes solves: "terminates pgs p"
    and cover: "vars_cover (prog_cfg p) (sol_vars pgs p)"
    and wf: "wf_compile_input pgs (prog_table p) (prog_procs p)"
    and s0: "s0 \<in> cinit_stores pgs"
    and run: "star (pstep pgs (prog_table p))
                (main_body (prog_table p), s0, []) (SKIP, s, [])"
  shows "s \<in> \<lbrakk>state_at pgs p (cfg_exit (prog_cfg p))\<rbrakk>"
  by (rule completed_run_sound_closure[OF solves cover_entry[OF cover]
        cover_fwd[OF cover] cover_call_fwd[OF cover] cover_comb_fwd[OF cover]
        wf s0 run])

end

end

end
