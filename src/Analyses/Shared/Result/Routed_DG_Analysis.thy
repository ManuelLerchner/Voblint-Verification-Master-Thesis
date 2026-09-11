theory Routed_DG_Analysis
  imports
    DG_Result_Construction
    Analysis_Surface
    "Voblint_Framework.Contextual_Check_Report"
    "Voblint_Framework.Routed_Analysis_Sound"
    "Voblint_Framework.Seed_Global_Keys"
    "Voblint_Exec.Routed_Exec_Refinement"
    Source_Activation_Sound
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Routing.Entry_State_Routed_Context"
begin

section \<open>One context-sensitive analysis, assembled from its choices\<close>

text \<open>
  A concrete analysis picks a domain implementation, an initial state, a way of
  telling activations apart, a solver and a classifier; everything between those
  choices and the published table is the same work at every domain and at every
  context policy. This theory does that work once.

  The construction half is \<open>routed_dg_pipeline\<close>, which carries no correctness
  assumptions, so its defining equations are unconditional and can be declared to
  the code generator. The correctness half is \<open>routed_dg_analysis\<close>, which adds
  the domain and solver contracts and derives, for one program, the routed
  soundness statement every policy shares.

  Vocabulary. A \<^emph>\<open>routed\<close> equation system publishes a callee's entry state at a
  global seed key instead of reading the callee entry directly; a \<^emph>\<open>context\<close> is
  the value the routing function attaches to a program point so that one point
  can be solved at several unknowns; \<^emph>\<open>covered\<close> keys are the unknowns the solver
  actually visited, which is not the same as the unknowns holding a bottom state.

  What this covers, and what it does not. It is the assembly for executable
  non-relational analyses whose local unknown carries a whole reachability-lifted
  store and whose entry operation answers with a pure list of alternatives. The
  context type, the global-key type, the seed constructor, the routing function
  and the root context are all parameters; the carrier and the entry shape are
  not.
\<close>

subsection \<open>The formals route, once for every domain\<close>

text \<open>
  Keying a callee on the abstract values its formals hold on entry, at the
  executable carrier. \<^const>\<open>formals_route_lifted_gen\<close> is the same decision one
  layer up, on the state a solved table hands out; the equation below is what
  lets a routed instance discharge its routing-agreement obligation without a
  domain-specific lemma. The routed generator enters the callee frame before it
  routes, so the route itself only projects the formals out of the state it is
  handed.
\<close>

definition exec_formals_route ::
    "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'a list
       \<Rightarrow> ('a::bot) exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "exec_formals_route gs u ctx d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (fun_of_resolved_st_q_for gs (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

text \<open>
  The same routing decision taken from a solved \<^emph>\<open>result\<close> instead of from the
  solver's carrier. A rendering that draws one node per activation has to know
  which callee context a call edge enters, and the table it draws from holds
  \<^typ>\<open>'a abs_state\<close> rather than \<^typ>\<open>'a exec_dg_st\<close> --- so the projection
  \<^const>\<open>exec_formals_route\<close> performs is unavailable to it, and the entered
  state has to be recomputed from the caller's. \<open>enter\<close> is the domain's own
  entry transfer and is the only domain-specific value involved; emptiness is
  \<^const>\<open>is_empty\<close>, the \<^class>\<open>executable_domain\<close> operation every domain carries.

  The witness search runs over the formals rather than over the whole state,
  and it has to: \<^const>\<open>is_empty_state\<close> quantifies over every \<^typ>\<open>vname\<close>, so
  its code equation would demand an \<^class>\<open>enum\<close> instance for
  \<^typ>\<open>String.literal\<close> and this constant would not generate code at all.
  Restricting to the formals is also exact rather than merely cheaper ---
  procedure entry resets every non-global variable to top and leaves every
  global at the caller's own value, so no name outside the formals can witness
  emptiness that the caller did not already have.

  \<^const>\<open>None\<close> means the call routes nowhere, because the entered state
  represents no concrete store. It is not a sentinel context: an empty formal
  list is a legitimate context in its own right --- a zero-formal callee's own
  entry is genuinely keyed at \<open>[]\<close> --- so no \<^typ>\<open>'a list\<close> value could carry
  that meaning without colliding with a real one.
\<close>

definition callee_ctx_of ::
    "((vname \<Rightarrow> bool) \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)
       \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> ('a::executable_domain) abs_state
       \<Rightarrow> 'a list option" where
  "callee_ctx_of enter gs ca st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = enter gs pars args st
         in if list_ex (\<lambda>x. is_empty (entered x)) pars then None
            else Some (formals_context pars entered)))"

lemma exec_formals_route_commute:
  "formals_route_lifted_gen u ctx (map_lift (fun_of_resolved_st_q_for gs) d) ca
     = exec_formals_route gs u ctx d ca"
  by (cases d; cases ca)
     (simp_all add: formals_route_lifted_gen_def formals_route_lifted_def
        exec_formals_route_def fun_of_resolved_st_q_for_def)

text \<open>
  Reading a lifted abstract state as a plain one and concretizing agrees with
  concretizing the lifted state directly, because the bottom store describes
  nothing. Every result-table reading takes the first route and every routed
  endpoint the second, so this is the equation between them.
\<close>

lemma gamma_state_case_eq_point:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_state (case x of Bot \<Rightarrow> bot | Lifted st \<Rightarrow> st) = gamma_point x"
  by (cases x) (simp_all add: gamma_point_def)

lemma gamma_point_canonicalize:
  fixes x :: "'a::sound_domain abs_state lifted"
  shows "gamma_point (canonicalize_lift is_empty_state x) = gamma_state_lift x"
  by (cases x)
     (simp_all add: gamma_point_def normalize_lift_def is_empty_state_gamma_state_empty)

subsection \<open>The construction\<close>

text \<open>
  \<open>init_st\<close> is the unlifted entry state; the pipeline lifts it, because a
  reachability-lifted carrier is what the routed generator solves over.
  \<open>bot_state\<close> is a parameter rather than the \<^class>\<open>order_bot\<close> operation for the
  same code-generation reason \<^locale>\<open>analysis_surface\<close> states: a sort constraint
  here would demand an executable \<^const>\<open>bot\<close> at a function type.
\<close>

locale routed_dg_pipeline =
  fixes tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                    \<Rightarrow> 'a::executable_domain exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and init_st :: "'a exec_dg_st"
    and gk0 :: 'k
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and root_ctx :: 'c
    and solve :: "(pp \<times> 'c, 'k,
                     ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                  \<Rightarrow> pp \<times> 'c
                  \<Rightarrow> (pp \<times> 'c) set
                       \<times> (pp \<times> 'c + 'k
                            \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)"
    and solve_dom :: "(pp \<times> 'c, 'k,
                        ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                      \<Rightarrow> pp \<times> 'c \<Rightarrow> bool"
    and bot_state :: "'a abs_state"
    and classify :: "exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result"
begin

definition analysis_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c, 'k, unit, 'a exec_dg_st lifted, 'a exec_dg_st lifted) dg_spec" where
  "analysis_spec gs p =
     local_state_dg_spec_st_for_lifted gs
       (resolved_st_q_is_bot_for (declared_global_vars p)) (tf_st gs) (enter_st gs)"

text \<open>
  The unknown the solver is asked for. It is the program exit at the root
  context: a demand-driven solver is started at the answer a caller wants and
  explores backwards from it, so the root query is the exit and the entry point
  is reached as one of its dependencies.
\<close>

definition root_query :: "imp_prog \<Rightarrow> pp \<times> 'c" where
  "root_query p = (cfg_exit (prog_cfg p), root_ctx)"

text \<open>
  \<open>root_query\<close>'s own type mentions no domain, so a code equation for it carries a
  sort hypothesis the code generator cannot see and silently rejects. The two
  constants that use it inline it instead: their types do mention the domain, so
  their equations are accepted, and \<open>root_query\<close> never has to be executable.
\<close>

definition equations :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c, 'k,
         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT" where
  "equations gs p =
     compiled_routed_eqs_for gk0 seed (route gs)
       (analysis_spec gs p) (prog_cfg p) (Lifted init_st) bot"

definition solution :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c) set
         \<times> (pp \<times> 'c + 'k
              \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)" where
  "solution gs p = solve (equations gs p) (root_query p)"

definition terminates :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "terminates gs p = solve_dom (equations gs p) (root_query p)"

lemma solution_code: "solution gs p = solve (equations gs p) (cfg_exit (prog_cfg p), root_ctx)"
  by (simp add: solution_def root_query_def)

lemma terminates_code:
  "terminates gs p = solve_dom (equations gs p) (cfg_exit (prog_cfg p), root_ctx)"
  by (simp add: terminates_def root_query_def)

definition sol_vars :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> 'c) set" where
  "sol_vars gs p = fst (solution gs p)"

definition sol_env :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state" where
  "sol_env gs p = snd (solution gs p)"

definition reader :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> 'a exec_dg_st lifted" where
  "reader gs p = solved_local_reader (sol_vars gs p) (sol_env gs p)"

definition result :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> ('c, 'a abs_state) analysis_result" where
  "result gs p = dg_result_for gs (declared_global_vars p) (solution gs p)"

text \<open>
  Where a call leads, as a function of the call site and the caller's context
  alone: this route applied to the state this solve published at that site. It
  names no concretization, so it belongs here rather than beside the soundness
  endpoints -- which is what lets a registration that cannot export a binder
  publish it by spelling this out, exactly as it publishes \<^const>\<open>result\<close>.
\<close>

definition ctx_succ :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> 'c
    \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c" where
  "ctx_succ gs p u ctx ca q =
     route gs u ctx
       (transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
          (enter_st gs (call_info_of ca q))
          (locals (sol_env gs p (Inl (u, ctx)))))
       ca"


text \<open>
  Where a call leads when it contributes at all: \<open>None\<close> when the entered state is
  bottom, which is exactly when the routed call tree drops the alternative, and
  otherwise the context \<^const>\<open>ctx_succ\<close> names.
\<close>

definition live_succ :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> 'c
    \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c option" where
  "live_succ gs p u ctx ca q =
     (if transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
           (enter_st gs (call_info_of ca q)) (locals (sol_env gs p (Inl (u, ctx)))) = Bot
      then None else Some (ctx_succ gs p u ctx ca q))"

text \<open>
  The globals beside the table. Which contexts a procedure entry was solved at
  is a policy question -- a single one at the unit context, the solved table's
  own covered contexts elsewhere -- so the enumeration and the label are
  arguments rather than a fixed shape.
\<close>

definition globals_at :: "(pp \<Rightarrow> 'c list) \<Rightarrow> (pname \<Rightarrow> 'c \<Rightarrow> String.literal)
    \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list" where
  "globals_at ctxs label gs p =
     dg_globals_for gs (declared_global_vars p) (sol_env gs p)
       (seed_global_keys gk0 seed ctxs label p)"

text \<open>
  The contextual publication surface: one verdict per context at a check, and
  the aggregate a caller prints. Both are \<^const>\<open>classify_checks_ctx\<close> and
  \<^const>\<open>classify_checks_verdicts\<close> unchanged -- they are generic in the context
  type already -- so nothing here is policy-specific beyond supplying this
  pipeline's own result table.
\<close>

definition check_projection :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> ('c \<times> contextual_verdict) set) list" where
  "check_projection gs p = classify_checks_ctx (prog_cfg p) (result gs p) classify"

definition verdict_report :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "verdict_report gs p = classify_checks_verdicts (prog_cfg p) (result gs p) classify"

lemma verdict_report_proj:
  "verdict_report gs p
     = map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs))) (check_projection gs p)"
  unfolding verdict_report_def check_projection_def
  by (rule classify_checks_verdicts_proj [symmetric])

end

subsection \<open>Executability of the derived objects\<close>

text \<open>
  A locale constant carries no code equation of its own, so every object the
  pipeline derives would drop out of the generated code and out of
  \<^theory_text>\<open>eval\<close> alike. Each defining equation is already in executable shape, so
  declaring them is all the code generator needs.

  \<open>analysis_spec\<close> is the exception, and it is the project's standing rule for a
  named \<^type>\<open>dg_spec\<close>: its unknown and global-key types occur only inside its
  transfer programs, never in an argument that builds it, so it has no most
  general ML type. Unfolding it at code-generation time is what keeps it out of
  the emitted program.
\<close>

declare routed_dg_pipeline.analysis_spec_def [code_unfold]

text \<open>
  \<^const>\<open>routed_dg_pipeline.root_query\<close> gets its code equation restated with HOL
  equality rather than declared from its defining meta-equation: a locale
  definition whose body is a pair, not a function, is not in the shape the code
  generator accepts, and the rejection is a warning rather than an error --- the
  equation is simply absent, and the first \<^theory_text>\<open>eval\<close> that reaches a solve fails
  with "no code equations" naming a constant nobody wrote. A registration that
  renames the pipeline's constants through \<^theory_text>\<open>defines\<close> never notices, because
  each renamed constant carries its own equation; one that applies them directly
  does.
\<close>

declare routed_dg_pipeline.equations_def [code]
declare routed_dg_pipeline.solution_code [code]
declare routed_dg_pipeline.terminates_code [code]
declare routed_dg_pipeline.sol_vars_def [code]
declare routed_dg_pipeline.sol_env_def [code]
declare routed_dg_pipeline.reader_def [code]
declare routed_dg_pipeline.result_def [code]
declare routed_dg_pipeline.globals_at_def [code]
declare routed_dg_pipeline.check_projection_def [code]
declare routed_dg_pipeline.verdict_report_def [code]


subsection \<open>The contracts\<close>

text \<open>
  What an instance owes, and nothing more: the abstract transfer it implements is
  sound, its executable mirror reads back to that transfer, its executable route
  agrees with the route on read-back states, its seed keys are distinct from the
  analysis-wide global, its solver answers a post-solution over finitely many
  keys once it terminates, its classifier is correct, and its entry state
  describes every initial store. The equation system, the solve, the covered
  keys, the reader, the result table and the report are all fixed by
  \<^locale>\<open>routed_dg_pipeline\<close> above and appear here only in conclusions.

  \<open>route_abs\<close> is the same routing decision taken on the abstract carrier. It is a
  parameter and not a derived object because a route may read the state it is
  handed: a call-string policy ignores it and passes the same function twice,
  while an entry-state policy projects the entered formals and the two spellings
  genuinely differ.
\<close>

locale routed_dg_analysis =
  routed_dg_pipeline tf_st enter_st init_st gk0 seed route root_ctx solve solve_dom
    bot_state classify
  for tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                  \<Rightarrow> 'a::sound_domain exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and init_st :: "'a exec_dg_st"
    and gk0 :: 'k
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and root_ctx :: 'c
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
    and route_abs :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and solve_c :: "(pp \<times> 'c, 'k,
                       ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                    \<Rightarrow> pp \<times> 'c
                    \<Rightarrow> ((pp \<times> 'c) set
                          \<times> (pp \<times> 'c + 'k
                               \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)) option"
  assumes tf_sound: "\<And>gs. sound_transfer_for gs sk asn spc br bd rt (en gs) ev"
    and tf_commute:
      "\<And>gs a s. live_resolved_st_q gs s
         \<Longrightarrow> fun_of_exec_dg_st_for gs (tf_st gs a s)
               = local_spec_step sk asn spc br bd rt ev a (fun_of_exec_dg_st_for gs s)"
    and enter_commute:
      "\<And>gs ci s. fun_of_exec_dg_st_for gs (enter_st gs ci s)
                    = en gs ci (fun_of_exec_dg_st_for gs s)"
    and route_agree:
      "\<And>gs u ctx d ca. route gs u ctx d ca
         = route_abs gs u ctx (map_lift (fun_of_exec_dg_st_for gs) d) ca"
    and seed_ne_gk0: "\<And>v ctx. seed v ctx \<noteq> gk0"
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

lemma vars_finite_of_terminates:
  assumes "terminates gs p"
  shows "finite (sol_vars gs p)"
  using solve_fin[OF assms[unfolded terminates_def]]
  by (simp add: sol_vars_def solution_def)

text \<open>
  The contexts a concrete call is admitted at under an entry-state policy: every
  context some covering alternative of the entry answer routes to. This is a
  top-level constant rather than something read out of a per-program
  interpretation, because a domain publishes it -- a caller stating a
  context-indexed collecting fact has to name the relation those contexts are
  indexed by, and an example checking a routing decision has to name it too.

  With one alternative per call it is one context per abstract caller state; it
  is still a relation and not a function because several concrete callers sharing
  one abstract state reach the same context, and because a policy is free to
  answer a call with several alternatives.
\<close>

definition admitted_contexts :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'c call_context_rel" where
  "admitted_contexts gs p =
     routed_entry_context_rel
       (\<lambda>ci d. [(d, transfer_lift (resolved_st_q_is_bot_for (declared_global_vars p))
                      (enter_st gs ci) d)])
       (\<lambda>d g. gamma_state_lift (map_lift (fun_of_resolved_st_q_for gs) d))
       (sol_env gs p) gk0 (route gs)"

subsection \<open>What the assembly derives, for one program\<close>

text \<open>
  Soundness fixes the classifier at the program's own declaration predicate,
  because that is the only classifier for which the executable bottom test and
  the semantic emptiness test agree. \<open>empty_pred_exact\<close> is that agreement.
\<close>

context
  fixes p :: imp_prog
begin

abbreviation pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"

abbreviation pbot :: "'a exec_dg_st \<Rightarrow> bool" where
  "pbot \<equiv> resolved_st_q_is_bot_for (declared_global_vars p)"

lemma empty_pred_exact:
  "pbot s = is_empty_state (fun_of_resolved_st_q_for pgs s)"
  by (rule resolved_st_q_is_bot_for_iff[OF declared_global_iff])

interpretation dom: routed_dg_domain_exec pgs pbot "tf_st pgs" "enter_st pgs"
    sk asn spc br bd rt "en pgs" ev
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def], assumption,
      rule enter_commute[unfolded fun_of_exec_dg_st_for_def],
      rule empty_pred_exact)

interpretation rtd: routed_domain_exec pgs pbot "tf_st pgs" "enter_st pgs"
    sk asn spc br bd rt "en pgs" ev
    gk0 seed "route pgs" "route_abs pgs" static_resolve static_resolve
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def], assumption,
      rule enter_commute[unfolded fun_of_exec_dg_st_for_def],
      rule empty_pred_exact,
      rule seed_ne_gk0,
      rule route_agree[unfolded fun_of_exec_dg_st_for_def],
      simp add: static_resolve_def)

lemma spec_alt: "analysis_spec pgs p = dom.spec_st"
  unfolding analysis_spec_def by (rule refl)

text \<open>
  The published table and the solved reader describe the same stores at every
  key. A caller states soundness against \<^const>\<open>lookup_context\<close> of the result
  table, while the routed endpoints are stated against the reader; this is the
  equation between them, and it needs no coverage premise. At a covered key it
  is the readback commuting with the normalization; at an uncovered one it is
  \<^const>\<open>Bot\<close> against \<^const>\<open>bot\<close>, and both describe nothing.
\<close>

lemma gamma_reader_eq_lookup:
  "gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) (reader pgs p (Inl (v, ctx))))
     = gamma_point (lookup_context (result pgs p) v ctx)"
proof (cases "(v, ctx) \<in> sol_vars pgs p")
  case True
  then show ?thesis
    by (simp add: reader_def result_def sol_vars_def sol_env_def gamma_point_canonicalize
        readback_canonicalize_lift_eq[OF empty_pred_exact])
next
  case False
  then show ?thesis by (simp add: reader_def result_def sol_vars_def)
qed

subsubsection \<open>The solver's answer, in the shape the routed spine consumes\<close>

text \<open>
  A domain solves the buffered generator -- a node with several intra
  predecessors or several returning calls publishes its analysis-wide
  contribution once per evaluation rather than once per contribution -- while the
  framework states its soundness over the unbuffered one. \<open>pp_routed\<close> is that
  reconciliation at this pipeline's own equations, and it is
  \<^locale>\<open>routed_domain_exec\<close>'s theorem applied, not a second argument.
\<close>

lemma pp_buffered:
  assumes solves: "terminates pgs p"
  shows "part_post_solution (equations pgs p) (root_query p)
           (sol_env pgs p) (sol_vars pgs p)"
  using solve_pp[OF solves[unfolded terminates_def]]
  by (simp add: sol_env_def sol_vars_def solution_def)

theorem pp_routed:
  assumes solves: "terminates pgs p"
  shows "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list (\<lambda>_. gk0) (route pgs)
        (\<lambda>ctx' src a. dg_spec_edge_tree (analysis_spec pgs p) a src (\<lambda>_. gk0))
        (routed_call_tree (analysis_spec pgs p) gk0 seed
           (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
        (routed_entry_seed_tree seed)
        (prog_cfg p) Bot (Lifted init_st) Bot)
     (root_query p) (sol_env pgs p) (sol_vars pgs p)"
  unfolding analysis_spec_def
  by (rule rtd.pp_st)
     (use pp_buffered[OF solves] in
        \<open>simp add: equations_def compiled_routed_eqs_for_def analysis_spec_def\<close>)

subsubsection \<open>The one entry alternative this carrier answers with\<close>

text \<open>
  The specification's entry operation is pure -- it reads no solver unknown and
  publishes nothing -- and answers with a single alternative: the caller's own
  state paired with the callee frame entered from it. \<open>entered\<close> names that
  alternative, and \<open>entry_cover\<close> is the only fact about it any routing policy
  needs, namely that a concrete call from a described caller lands in the
  described callee.
\<close>

abbreviation entered :: "call_info \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted" where
  "entered ci d \<equiv> transfer_lift pbot (enter_st pgs ci) d"

lemma entry_cover:
  assumes "s \<in> dom.gamma_exec d g'"
  shows "entry_pairs_cover (\<lambda>d'. dom.gamma_exec d' g'') s
           (call_enter pgs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s)
           [(d, entered ci d)]"
  using dom.entry_pairs_cover_st[OF tf_sound, where d = d and ci = ci] assms
  by (simp add: dom.gamma_exec_def)

subsubsection \<open>The routed soundness statement, at any admitted-context relation\<close>

text \<open>
  Which contexts a concrete call is admitted at is the one thing a context policy
  still chooses, so \<open>R\<close> is a parameter here rather than a derived object. What
  the policy owes about it is exactly two facts: a context \<open>R\<close> admits is the one
  this pipeline's route computes on the entered state, at a covered unknown
  (\<open>cover_R\<close>); and \<open>R\<close> admits at least one context for every concrete call at a
  covered call site (\<open>total_R\<close>). Everything else below is fixed by the pipeline.
\<close>

text \<open>
  The specification is sound at the executable carrier: this is
  \<^locale>\<open>routed_dg_domain_exec\<close>'s own pullback of the abstract transfer's
  soundness, so the routed statement below never re-derives it.
\<close>

interpretation dg_base: sound_dg_spec_core "analysis_spec pgs p" dom.gamma_exec pgs
  unfolding analysis_spec_def by (rule dom.sound_dg_spec_core_st[OF tf_sound])

lemma routed_analysis_sound_of_live:
  fixes R :: "'c call_context_rel"
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> locals (sol_env pgs p (Inl (u, ctx))) \<noteq> Bot
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> entered (call_info_of (CallEdge dst pars args) q)
              (locals (sol_env pgs p (Inl (u, ctx)))) \<noteq> Bot
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (locals (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> dom.gamma_exec (locals (sol_env pgs p (Inl (u, ctx))))
                  (globs (sol_env pgs p (Inr gk0)))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) ctx'"
  shows "routed_analysis_sound (analysis_spec pgs p) dom.gamma_exec pgs (prog_cfg p) gk0
     (route pgs) Bot (Lifted init_st) Bot (sol_env pgs p) (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) R (map_lift (fun_of_resolved_st_q_for pgs)) classify"
proof (unfold_locales, goal_cases FinE PP SgCov SgUncov Fwd FinC CallsUnique SeedKey
    IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd GammaRd
    ClProved ClRefuted VarsFin)
  case FinE show ?case unfolding prog_cfg_def using compile_prog_finite by simp
next
  case PP show ?case by (rule post_bounded_of_part_post_solution[OF pp_routed[OF solves]])
next
  case (SgCov v c) then show ?case by (simp add: dom.gamma_exec_def)
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c)
  have "locals (sol_env pgs p (Inl (u, c))) \<noteq> Bot"
    using Fwd(2) by (auto simp: dom.gamma_exec_def)
  with Fwd(1,3) show ?case by (blast intro: fwd_ok)
next
  case FinC show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def prog_cfg_def
    using compile_prog_calls_source_unique by blast
next
  case (SeedKey q ctx) show ?case by (rule seed_ne_gk0)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by (simp add: dom.gamma_exec_def)
next
  case (ResolveSound u ctx dst pars args q cont s)
  then show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args q cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "locals (sol_env pgs p (Inl (u, ctx)))"
  have cov: "entry_pairs_cover
      (\<lambda>d'. dom.gamma_exec d' (globs (sol_env pgs p (Inr gk0)))) s
      (call_enter pgs (CallEdge dst pars args) s) [(?caller, entered ?ci ?caller)]"
    using entry_cover[OF EnterCover(3), where ci = ?ci] by simp
  have nbE: "entered ?ci ?caller \<noteq> Bot"
  proof
    assume "entered ?ci ?caller = Bot"
    with cov show False by (simp add: entry_pairs_cover_def dom.gamma_exec_def)
  qed
  have req: "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'"
    and covE: "(FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using cover_R[OF EnterCover(1,2,4) nbE] by blast+
  show ?case
    unfolding analysis_spec_def dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov req covE
    by (fastforce simp: entry_pairs_cover_def)
next
  case (EnterTotal u ctx dst pars args q cont s)
  then show ?case by (rule total_R)
next
  case (CombFwd cl c1 dst pars args q cont)
  then show ?case by (rule comb_fwd_ok)
next
  case (GammaRd d g') show ?case by (simp add: dom.gamma_exec_def)
next
  case (ClProved c d s) then show ?case by (rule classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule classify_refuted)
next
  case VarsFin show ?case by (rule vars_finite_of_terminates[OF solves])
qed

lemma routed_analysis_sound_of:
  fixes R :: "'c call_context_rel"
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (locals (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> dom.gamma_exec (locals (sol_env pgs p (Inl (u, ctx))))
                  (globs (sol_env pgs p (Inr gk0)))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) ctx'"
  shows "routed_analysis_sound (analysis_spec pgs p) dom.gamma_exec pgs (prog_cfg p) gk0
     (route pgs) Bot (Lifted init_st) Bot (sol_env pgs p) (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) R (map_lift (fun_of_resolved_st_q_for pgs)) classify"
  by (rule routed_analysis_sound_of_live [where R = R, OF solves _ comb_fwd_ok _ total_R])
     (blast intro: fwd_ok dest: cover_R)+

subsubsection \<open>The published endpoint, under termination and coverage\<close>

lemma cinit_le_init: "cinit_stores pgs \<subseteq> dom.gamma_exec (Lifted init_st) Bot"
  using init_sound[of pgs]
  by (simp add: dom.gamma_exec_def fun_of_exec_dg_st_for_def)

text \<open>
  Every activation the trace semantics admits at a context is described by the
  solved table's entry for that context. The coverage premises are the shape a
  solver's own reachable set supplies: an edge out of an unknown the solve
  visited lands on one it also visited.
\<close>

lemma activation_collect_sound_of:
  fixes R :: "'c call_context_rel"
  assumes solves: "terminates pgs p"
    and entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> R u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s) ctx'
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (locals (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> dom.gamma_exec (locals (sol_env pgs p (Inl (u, ctx))))
                  (globs (sol_env pgs p (Inr gk0)))
        \<Longrightarrow> \<exists>ctx'. R u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) ctx'"
  shows "activation_collect pgs R root_ctx (prog_cfg p) (cinit_stores pgs) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                 (reader pgs p (Inl (v, ctx))))"
proof -
  interpret adapter: routed_analysis_sound "analysis_spec pgs p" dom.gamma_exec pgs
      "prog_cfg p" gk0 "route pgs" Bot "Lifted init_st" Bot
      "sol_env pgs p" "sol_vars pgs p" "root_query p" seed "\<lambda>d. d = Bot" R
      "map_lift (fun_of_resolved_st_q_for pgs)" classify
    by (rule routed_analysis_sound_of
          [where R = R, OF solves fwd_ok comb_fwd_ok cover_R total_R])
  show ?thesis
    unfolding reader_def
    by (rule adapter.routed_activation_collect_sound[OF entry_cov cinit_le_init])
qed

subsubsection \<open>The two context policies this assembly supports\<close>

text \<open>
  \<open>entry_context_rel\<close> is the relation an entry-state policy induces: a concrete
  call is admitted at every context some covering alternative of the entry answer
  routes to. With one alternative per call that is a single context per abstract
  caller state, but several concrete callers sharing an abstract state may still
  reach one context, which is exactly why a relation and not a function.
\<close>

lemma admitted_contexts_alt:
  "admitted_contexts pgs p =
     routed_entry_context_rel (\<lambda>ci d. [(d, entered ci d)]) dom.gamma_exec
       (sol_env pgs p) gk0 (route pgs)"
proof -
  have "(\<lambda>d g. gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs) d))
          = dom.gamma_exec"
    by (simp add: dom.gamma_exec_def fun_eq_iff)
  then show ?thesis by (simp add: admitted_contexts_def)
qed

abbreviation entry_context_rel :: "'c call_context_rel" where
  "entry_context_rel \<equiv> admitted_contexts pgs p"

text \<open>
  How a caller shows that this call is admitted at the context it computed: the
  concrete caller store is described by the solved caller state, and the entered
  store by the callee frame entered from it. The single alternative makes both
  halves the same solved unknown, so a witness never has to name the alternatives
  list.
\<close>

lemma admitted_contextsI:
  assumes caller: "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                        (locals (sol_env pgs p (Inl (u, ctx)))))"
    and entered_in: "s' \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                        (entered ci (locals (sol_env pgs p (Inl (u, ctx))))))"
  shows "entry_context_rel u ctx ci s s'
           (route pgs u ctx (entered ci (locals (sol_env pgs p (Inl (u, ctx)))))
              (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)))"
  unfolding admitted_contexts_alt
  by (rule routed_entry_context_relI
        [where cont = "locals (sol_env pgs p (Inl (u, ctx)))"])
     (use caller entered_in in \<open>simp_all add: dom.gamma_exec_def\<close>)

text \<open>
  The same fact with the call action spelled as the caller has it. A witness
  names a literal \<^const>\<open>CallEdge\<close>, while the rule above reconstructs one from
  the \<^type>\<open>call_info\<close>'s three projections, and \<^theory_text>\<open>rule\<close> does not reduce the
  projections. Every concrete instance wants this shape.
\<close>

lemma admitted_contextsI_call:
  assumes caller: "s \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                        (locals (sol_env pgs p (Inl (u, ctx)))))"
    and entered_in: "s' \<in> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                        (entered (call_info_of (CallEdge dst pars args) q)
                           (locals (sol_env pgs p (Inl (u, ctx))))))"
  shows "entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s s'
           (route pgs u ctx
              (entered (call_info_of (CallEdge dst pars args) q)
                 (locals (sol_env pgs p (Inl (u, ctx)))))
              (CallEdge dst pars args))"
  using admitted_contextsI[OF caller entered_in] by simp

lemma entry_state_routed_analysis_sound:
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and call_fwd_ok: "\<And>u ctx dst pars args q cont. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q,
               route pgs u ctx
                 (entered (call_info_of (CallEdge dst pars args) q)
                    (locals (sol_env pgs p (Inl (u, ctx)))))
                 (CallEdge dst pars args))
              \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
  shows "routed_analysis_sound (analysis_spec pgs p) dom.gamma_exec pgs (prog_cfg p) gk0
     (route pgs) Bot (Lifted init_st) Bot (sol_env pgs p) (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) entry_context_rel (map_lift (fun_of_resolved_st_q_for pgs)) classify"
proof (rule routed_analysis_sound_of
    [where R = entry_context_rel, OF solves fwd_ok comb_fwd_ok])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s
               (call_enter pgs (CallEdge dst pars args) s) ctx'"
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "locals (sol_env pgs p (Inl (u, ctx)))"
  from Rc[unfolded admitted_contexts_alt] obtain cont' entry
    where mem: "(cont', entry) \<in> set [(?caller, entered ?ci ?caller)]"
      and req0: "ctx' = route pgs u ctx entry
                   (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  have "entry = entered ?ci ?caller" using mem by simp
  with req0 have req: "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'"
    by simp
  show "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'
          \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using req call_fwd_ok[OF covV ce] by simp
next
  fix u ctx dst pars args q cont and s :: store
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and sin: "s \<in> dom.gamma_exec (locals (sol_env pgs p (Inl (u, ctx))))
                (globs (sol_env pgs p (Inr gk0)))"
  show "\<exists>ctx'. entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s
                 (call_enter pgs (CallEdge dst pars args) s) ctx'"
    unfolding admitted_contexts_alt
    by (rule routed_entry_context_rel_total)
       (use entry_cover[OF sin, where ci = "call_info_of (CallEdge dst pars args) q"]
         in simp)
qed

text \<open>
  The two endpoints an entry-state caller consumes: the per-context collecting
  bound, and the existence of a context for every valid trace, which a
  source-level caller needs to name a context witness at all. Both are the
  routed spine's own theorems at the interpretation just established.
\<close>

context
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and call_fwd_ok: "\<And>u ctx dst pars args q cont. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q,
               route pgs u ctx
                 (entered (call_info_of (CallEdge dst pars args) q)
                    (locals (sol_env pgs p (Inl (u, ctx)))))
                 (CallEdge dst pars args))
              \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
begin

interpretation entry: routed_analysis_sound "analysis_spec pgs p" dom.gamma_exec pgs
    "prog_cfg p" gk0 "route pgs" Bot "Lifted init_st" Bot
    "sol_env pgs p" "sol_vars pgs p" "root_query p" seed "\<lambda>d. d = Bot"
    entry_context_rel "map_lift (fun_of_resolved_st_q_for pgs)" classify
  by (rule entry_state_routed_analysis_sound
        [OF solves fwd_ok call_fwd_ok comb_fwd_ok])

text \<open>
  The routed protocol at one call, re-exported so a domain cites them without
  naming the routed sublocale: the callee entry state published under an
  admitted context is sound, and a return combine at the caller's own context
  is sound.
\<close>

lemmas entry_state_routed_context_call = entry.routed_context_call
lemmas entry_state_routed_context_comb = entry.routed_context_comb

theorem entry_state_activation_collect_sound:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "activation_collect pgs entry_context_rel root_ctx (prog_cfg p)
           (cinit_stores pgs) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                 (reader pgs p (Inl (v, ctx))))"
  unfolding reader_def
  by (rule entry.routed_activation_collect_sound[OF entry_cov cinit_le_init])

theorem entry_state_has_context:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
    and trace: "t \<in> valid_ltr pgs (prog_cfg p) (cinit_stores pgs)"
  shows "\<exists>c. trace_context pgs entry_context_rel root_ctx (prog_cfg p) t c"
  by (rule entry.routed_valid_ltr_has_context[OF entry_cov cinit_le_init trace])

text \<open>
  The two together: covering the entry is enough for the activation buckets to
  exhaust the context-insensitive collection, so a caller holding only a
  \<^const>\<open>ltr_collect\<close> membership -- which is what a source run delivers -- can
  pass to the bucket its own call history produced.  Without this the per-context
  bounds above say nothing about a run whose context is not known in advance.
\<close>

theorem entry_state_ltr_collect_eq_Union:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           = (\<Union>ctx. activation_collect pgs entry_context_rel root_ctx (prog_cfg p)
                        (cinit_stores pgs) v ctx)"
  by (rule ltr_collect_eq_Union_activation_of_has_context)
     (rule entry_state_has_context [OF entry_cov])

end

text \<open>
  The same two endpoints, with the four positional coverage assumptions replaced
  by the one closure premise a caller can state on its own. Nothing is weakened:
  \<^const>\<open>ctx_succ\<close> names where this solve's routing sends each call, so the
  closure unfolds to those four assumptions and to nothing else. This is the
  pair a source-level contextual statement consumes.
\<close>

theorem entry_state_activation_collect_sound_of_cover:
  assumes solves: "terminates pgs p"
    and cover: "ctx_vars_cover (prog_cfg p) (ctx_succ pgs p) root_ctx (sol_vars pgs p)"
  shows "activation_collect pgs entry_context_rel root_ctx (prog_cfg p)
           (cinit_stores pgs) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                 (reader pgs p (Inl (v, ctx))))"
  by (rule entry_state_activation_collect_sound
        [OF solves ctx_vars_cover_edgeD [OF cover]
            ctx_vars_cover_enterD [OF cover, unfolded ctx_succ_def]
            ctx_vars_cover_combineD [OF cover]
            ctx_vars_cover_entryD [OF cover]])

theorem entry_state_ltr_collect_eq_Union_of_cover:
  assumes solves: "terminates pgs p"
    and cover: "ctx_vars_cover (prog_cfg p) (ctx_succ pgs p) root_ctx (sol_vars pgs p)"
  shows "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
           = (\<Union>ctx. activation_collect pgs entry_context_rel root_ctx (prog_cfg p)
                        (cinit_stores pgs) v ctx)"
  by (rule entry_state_ltr_collect_eq_Union
        [OF solves ctx_vars_cover_edgeD [OF cover]
            ctx_vars_cover_enterD [OF cover, unfolded ctx_succ_def]
            ctx_vars_cover_combineD [OF cover]
            ctx_vars_cover_entryD [OF cover]])

text \<open>
  A route that never reads the state it is handed is a function of the call site
  and the caller's context alone, so the contexts it admits are the graph of a
  context function on concrete stores -- the shape the call-string and
  context-insensitive policies both publish. \<open>route_const\<close> is the whole of what
  such a policy owes; \<open>ctx_fun\<close> is its trace-semantic counterpart.
\<close>

theorem fun_route_activation_collect_sound:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route pgs u ctx d ca = ctx_fun u ctx s"
    and solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and call_fwd_ok: "\<And>u ctx dst pars args q cont d. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (FunctionEntry q, route pgs u ctx d (CallEdge dst pars args))
              \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "activation_collect pgs (call_context_rel_of_fun ctx_fun) root_ctx (prog_cfg p)
           (cinit_stores pgs) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                 (reader pgs p (Inl (v, ctx))))"
proof (rule activation_collect_sound_of[OF solves entry_cov fwd_ok comb_fwd_ok])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "call_context_rel_of_fun ctx_fun u ctx
               (call_info_of (CallEdge dst pars args) q) s
               (call_enter pgs (CallEdge dst pars args) s) ctx'"
  have req: "route pgs u ctx d (CallEdge dst pars args) = ctx'" for d
    using Rc
    by (simp add: route_const[of _ _ _ _ "call_enter pgs (CallEdge dst pars args) s"])
  show "route pgs u ctx
          (entered (call_info_of (CallEdge dst pars args) q)
             (locals (sol_env pgs p (Inl (u, ctx)))))
          (CallEdge dst pars args) = ctx'
        \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using req call_fwd_ok[OF covV ce] by simp
next
  fix u ctx dst pars args q cont and s :: store
  show "\<exists>ctx'. call_context_rel_of_fun ctx_fun u ctx
                 (call_info_of (CallEdge dst pars args) q) s
                 (call_enter pgs (CallEdge dst pars args) s) ctx'"
    by simp
qed

text \<open>
  The functional route's counterpart of the entry-state pair, and the reason a
  source-level statement is available for it too. The union side needs nothing
  at all: \<^const>\<open>key\<close> is total, so every valid trace carries a context without
  any coverage having been established. Only the per-bucket bound depends on the
  solve, and it takes the same single closure premise as the entry-state one.

  The closure is stated at \<^const>\<open>ctx_succ\<close>, which applies the route to the
  state published at the call site, while the bound below quantifies over every
  state the route might have been handed. For a route that ignores that argument
  those coincide, which is what \<open>route_const\<close> says and all this proof uses it for.
\<close>

theorem fun_route_ltr_collect_eq_Union:
  "ltr_collect pgs (prog_cfg p) (cinit_stores pgs) v
     = (\<Union>ctx. activation_collect pgs (call_context_rel_of_fun ctx_fun) root_ctx
                  (prog_cfg p) (cinit_stores pgs) v ctx)"
  by (rule ltr_collect_eq_Union_activation_of_fun)

theorem fun_route_activation_collect_sound_of_cover:
  fixes ctx_fun :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store \<Rightarrow> 'c"
  assumes route_const: "\<And>u ctx d ca s. route pgs u ctx d ca = ctx_fun u ctx s"
    and solves: "terminates pgs p"
    and cover: "ctx_vars_cover (prog_cfg p) (ctx_succ pgs p) root_ctx (sol_vars pgs p)"
  shows "activation_collect pgs (call_context_rel_of_fun ctx_fun) root_ctx (prog_cfg p)
           (cinit_stores pgs) v ctx
           \<subseteq> gamma_state_lift (map_lift (fun_of_resolved_st_q_for pgs)
                 (reader pgs p (Inl (v, ctx))))"
proof (rule fun_route_activation_collect_sound
         [OF route_const solves ctx_vars_cover_edgeD [OF cover] _
             ctx_vars_cover_combineD [OF cover] ctx_vars_cover_entryD [OF cover]])
  fix u ctx dst pars args q cont and d :: "'a exec_dg_st lifted"
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
  have "(FunctionEntry q, ctx_succ pgs p u ctx (CallEdge dst pars args) q) \<in> sol_vars pgs p"
    by (rule ctx_vars_cover_enterD [OF cover covV ce])
  then show "(FunctionEntry q, route pgs u ctx d (CallEdge dst pars args)) \<in> sol_vars pgs p"
    unfolding ctx_succ_def
    by (simp only: route_const [of u ctx _ _ undefined])
qed

end

end

end
