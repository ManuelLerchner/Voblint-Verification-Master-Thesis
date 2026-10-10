theory DG_Analysis
  imports
    DG_Result_Construction
    Analysis_Surface
    "Voblint_Framework.Routed_Analysis_Sound"
    "Voblint_Exec.Routed_Exec_Refinement"
    Source_Activation_Sound
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Routing.Entry_State_Routed_Context"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Framework.DG_Keyed_Split_Spec"
begin

section \<open>One context-sensitive analysis, assembled from its choices\<close>

text \<open>
  A concrete analysis picks a domain implementation, an initial state, a way of
  telling activations apart, a solver and a classifier; everything between those
  choices and the published table is the same work at every domain and at every
  context policy. This theory does that work once.

  The construction half is \<open>dg_pipeline\<close>, which carries no correctness
  assumptions, so its defining equations are unconditional and can be declared to
  the code generator. The correctness half is \<open>dg_analysis\<close>, which adds
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
       \<Rightarrow> ('a::bot) default_st lifted \<Rightarrow> call_action \<Rightarrow> 'a list" where
  "exec_formals_route \<G> u ctx d ca =
     (case ca of CallEdge dst pars args \<Rightarrow>
        formals_context pars
          (\<rho>\<^bsub>\<G>\<^esub> (case d of Bot \<Rightarrow> bot | Lifted d0 \<Rightarrow> d0)))"

text \<open>
  The same routing decision taken from a solved \<^emph>\<open>result\<close> instead of from the
  solver's carrier. A rendering that draws one node per activation has to know
  which callee context a call edge enters, and the table it draws from holds
  \<^typ>\<open>'a abs_state\<close> rather than \<^typ>\<open>'a default_st\<close> --- so the projection
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
  "callee_ctx_of enter \<G> ca st =
     (case ca of CallEdge dst pars args \<Rightarrow>
        (let entered = enter \<G> pars args st
         in if list_ex (\<lambda>x. is_empty (entered x)) pars then None
            else Some (formals_context pars entered)))"

lemma exec_formals_route_commute:
  "formals_route_lifted_gen u ctx (\<rho>\<^bsub>\<G>\<^esub> d) ca
     = exec_formals_route \<G> u ctx d ca"
  by (cases d; cases ca)
     (simp_all add: formals_route_lifted_gen_def formals_route_lifted_def
        exec_formals_route_def default_st_to_fun_def)

subsection \<open>The construction\<close>

text \<open>
  The pipeline runs one component, \<open>comp \<G> p\<close>: a single analysis, or the
  combination of several. \<open>init_st\<close> is the unlifted entry state; the pipeline
  lifts it, because a reachability-lifted carrier is what the routed generator
  solves over. \<open>empty p\<close> is the carrier's executable emptiness test and \<open>rd \<G>\<close>
  reads a carrier state back as the value the result table publishes. Nothing
  here fixes what the carrier or the published value is.
  \<open>bot_state\<close> is a parameter rather than the \<^class>\<open>order_bot\<close> operation for the
  same code-generation reason \<^locale>\<open>analysis_surface\<close> states: a sort constraint
  here would demand an executable \<^const>\<open>bot\<close> at a function type.
\<close>

text \<open>
  Everything one solve publishes, read back as values: the result table, the
  solved value of each global name, the seed a call published at a procedure entry under a
  context, what one edge's local step makes of a point's solved state, and where a
  call leads when it contributes at all.
\<close>

record ('c, 'n, 'v) solved_run =
  run_table :: "('c, 'v) solved_table"
  run_shared :: "'n \<Rightarrow> 'v lifted"
  run_seed :: "pname \<Rightarrow> 'c \<Rightarrow> 'v lifted"
  run_step :: "pp \<Rightarrow> 'c \<Rightarrow> edge_action \<Rightarrow> 'v lifted"
  run_succ :: "cfg_node \<Rightarrow> 'c \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c option"

text \<open>
  \<open>dg_pipeline\<close> only fixes parameters: the component \<open>comp\<close>, the carrier
  operations \<open>emp\<close>, \<open>rd\<close> and \<open>init_st\<close>, the key a node buffers its own
  global part at and the key \<open>global_of n\<close> each global name lives at, the
  context policy \<open>seed\<close>/\<open>route\<close>/
  \<open>root_ctx\<close>, the solver \<open>solve\<close> with its domain, the check classifier, and the
  placement of program state between the two halves of a solver unknown.
  The soundness assumptions live in the locales built on it.

  The placement is six operations. \<open>place_spec\<close> builds the D/G specification
  the equations run, from the component. \<open>place_cmb\<close> recombines a local value
  with the solved global environment into the state a point describes, and
  \<open>place_rl\<close> and \<open>place_rg\<close> project a state onto the part each half keeps.
  \<open>place_inits\<close> lists the initial value of each global name, which the program
  entry publishes at that name's key \<open>global_of n\<close>. \<open>place_enter\<close> is the caller
  state a call enters from: it may describe more than \<open>place_cmb\<close>, so a call reads
  only the globals it needs. An analysis that keeps all of its state in the local
  half builds the specification with \<^const>\<open>dg_spec_of\<close>, recombines by ignoring
  the environment, keeps every state locally, publishes \<^const>\<open>Bot\<close>, lists no
  initial values and enters from the caller's state as it is.
\<close>

locale dg_pipeline =
  fixes comp :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 's::semilattice_sup lifted local_spec"
    and emp :: "imp_prog \<Rightarrow> 's \<Rightarrow> bool"
    and rd :: "(vname \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 'v"
    and init_st :: 's
    and buffer_key :: 'k
    and global_of :: "'n \<Rightarrow> 'k"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 's lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and root_ctx :: 'c
    and solve :: "(pp \<times> 'c, 'k, ('s lifted, 's lifted) dg_state) eqsT
                  \<Rightarrow> pp \<times> 'c
                  \<Rightarrow> (pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 's lifted) dg_state)"
    and solve_dom :: "(pp \<times> 'c, 'k, ('s lifted, 's lifted) dg_state) eqsT \<Rightarrow> pp \<times> 'c \<Rightarrow> bool"
    and bot_state :: 'v
    and classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result"
    and place_spec :: "imp_prog \<Rightarrow> 's lifted local_spec
                        \<Rightarrow> (pp \<times> 'c, 'k, 'n, 's lifted, 's lifted) dg_spec"
    and place_cmb :: "imp_prog \<Rightarrow> 's lifted \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted"
    and place_rl :: "(vname \<Rightarrow> bool) \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
    and place_rg :: "(vname \<Rightarrow> bool) \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
    and place_inits :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ('n \<times> 's lifted) list"
    and place_enter :: "imp_prog \<Rightarrow> call_info \<Rightarrow> 's lifted \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted"
begin

definition analysis_spec :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c, 'k, 'n, 's lifted, 's lifted) dg_spec" where
  "analysis_spec \<G> p = place_spec p (comp \<G> p)"

text \<open>
  The state the component enters a callee with, from a whole caller state. The
  pipeline supports components whose entry answers one alternative, the caller's
  state paired with this one.
\<close>

definition comp_entry :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> call_info \<Rightarrow> 's lifted
    \<Rightarrow> 's lifted" where
  "comp_entry \<G> p ci w = snd (hd (ls_enter (comp \<G> p) (ls_channel (comp \<G> p) w) ci (w, w)))"

text \<open>
  The alternative a call enters its callee with, as the solver stores it: the
  component enters from the caller state \<open>place_enter\<close> recombines, and each
  half of the answer keeps its local part.
\<close>

definition entry_alt :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> call_info \<Rightarrow> 's lifted
    \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted \<times> 's lifted" where
  "entry_alt \<G> p ci d g =
     (let w = place_enter p ci d g in (place_rl \<G> w, place_rl \<G> (comp_entry \<G> p ci w)))"

text \<open>The state a call enters its callee with.\<close>

definition entry_of :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> call_info \<Rightarrow> 's lifted
    \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted"
  where "entry_of \<G> p ci d g = snd (entry_alt \<G> p ci d g)"

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

text \<open>
  The initial value of each global name is a side effect like any other: the
  program entry publishes it, once, at the name's key, as a run's initialization
  happens before its first statement. A placement that keeps its initial global
  part at the node's own key passes no such values.
\<close>

definition init_publications :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> 'c \<Rightarrow> ('k \<times> ('s lifted, 's lifted) dg_state) list" where
  "init_publications \<G> p x =
     (if x = (cfg_entry (prog_cfg p), root_ctx)
      then map (\<lambda>(n, d). (global_of n, DG Bot d)) (place_inits \<G> p) else [])"

text \<open>
  The generated code evaluates this test at every equation evaluation, so the code
  equation names the entry node directly instead of compiling the program each time.
\<close>

lemma init_publications_code:
  "init_publications \<G> p x =
     (if x = (FunctionEntry prog_main_name, root_ctx)
      then map (\<lambda>(n, d). (global_of n, DG Bot d)) (place_inits \<G> p) else [])"
  by (simp add: init_publications_def prog_cfg_def)

text \<open>
  The initial global environment a run starts from: what the entry node buffers at
  its own key, read at every name living there, together with the root's initial
  publications.
\<close>

definition init_env :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'n \<Rightarrow> 's lifted" where
  "init_env \<G> p n =
     (if global_of n = buffer_key then place_rg \<G> (Lifted init_st) else Bot)
       \<squnion> (\<Squnion>(m, d)\<leftarrow>filter (\<lambda>(m, d). m = n) (place_inits \<G> p). d)"

definition equations :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c, 'k,
         ('s lifted, 's lifted) dg_state) eqsT" where
  "equations \<G> p =
     with_init (init_publications \<G> p)
       (compiled_routed_eqs_for buffer_key global_of seed (route \<G>)
          (analysis_spec \<G> p) (prog_cfg p) (Lifted init_st) (place_rg \<G> (Lifted init_st)))"

definition solution :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c) set
         \<times> (pp \<times> 'c + 'k
              \<Rightarrow> ('s lifted, 's lifted) dg_state)" where
  "solution \<G> p = solve (equations \<G> p) (root_query p)"

definition terminates :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "terminates \<G> p = solve_dom (equations \<G> p) (root_query p)"

lemma solution_code: "solution \<G> p = solve (equations \<G> p) (cfg_exit (prog_cfg p), root_ctx)"
  by (simp add: solution_def root_query_def)

lemma terminates_code:
  "terminates \<G> p = solve_dom (equations \<G> p) (cfg_exit (prog_cfg p), root_ctx)"
  by (simp add: terminates_def root_query_def)

definition sol_vars :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> 'c) set" where
  "sol_vars \<G> p = fst (solution \<G> p)"

definition sol_env :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 's lifted) dg_state" where
  "sol_env \<G> p = snd (solution \<G> p)"

definition reader :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> pp \<times> 'c + 'k \<Rightarrow> 's lifted" where
  "reader \<G> p = solved_local_reader (sol_vars \<G> p) (sol_env \<G> p)"

definition result :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> ('c, 'v) solved_table" where
  "result \<G> p = dg_result_for (rd \<G>) (emp p) (place_cmb p) global_of (solution \<G> p)"

text \<open>The solved global environment every recombination reads.\<close>

definition sol_global :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'n \<Rightarrow> 's lifted" where
  "sol_global \<G> p = genv global_of (sol_env \<G> p)"

text \<open>
  Where a call leads, as a function of the call site and the caller's context
  alone: this route applied to the state this solve published at that site. It
  names no concretization, so it belongs here rather than beside the soundness
  endpoints -- which is what lets a registration that cannot export a binder
  publish it by spelling this out, exactly as it publishes \<^const>\<open>result\<close>.
\<close>

definition ctx_succ :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> 'c
    \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c" where
  "ctx_succ \<G> p u ctx ca q =
     route \<G> u ctx (entry_of \<G> p (call_info_of ca q) (dg_local (sol_env \<G> p (Inl (u, ctx))))
                      (sol_global \<G> p)) ca"


text \<open>
  Where a call leads when it contributes at all: \<open>None\<close> when the entered state is
  bottom, which is exactly when the routed call program drops the alternative, and
  otherwise the context \<^const>\<open>ctx_succ\<close> names.
\<close>

definition live_succ :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> 'c
    \<Rightarrow> call_action \<Rightarrow> pname \<Rightarrow> 'c option" where
  "live_succ \<G> p u ctx ca q =
     (if entry_of \<G> p (call_info_of ca q) (dg_local (sol_env \<G> p (Inl (u, ctx))))
           (sol_global \<G> p) = Bot
      then None else Some (ctx_succ \<G> p u ctx ca q))"


text \<open>
  The values one solution publishes. The seeds are read exactly as a table entry is,
  so an unwritten key reads as \<^const>\<open>Bot\<close>. The shared global is read
  without that canonicalization: its local half is bottom by construction, which
  would make every value it holds read as \<^const>\<open>Bot\<close>.

  A step is what one edge's local step makes of a point's solved state: the term
  that edge contributes to its target's equation, re-evaluated on the solution. A
  target with several incoming edges stores only their join, so this is the one
  place the contribution of a single edge can be read. It is the component's own
  step, run with the answers its handler gives on the recombined state, as the
  edge transfer runs it, and published with the state it describes.

  The successor is \<^const>\<open>live_succ\<close> read off the same solution, so a caller
  listing where every call leads does not solve the system again for each call.

  The solution is an argument, so a caller holding the executable solver's answer
  reads it without solving again; \<open>run\<close> below reads the specification's solve.
\<close>

definition solved_run_of :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 's lifted) dg_state)
    \<Rightarrow> ('c, 'n, 'v) solved_run" where
  "solved_run_of \<G> p sol =
     (let c = comp \<G> p;
          g = genv global_of (snd sol);
          read = (\<lambda>d. map_lift (rd \<G>) (canonicalize_lift (emp p) d))
      in \<lparr> run_table = dg_result_for (rd \<G>) (emp p) (place_cmb p) global_of sol,
           run_shared = (\<lambda>n. map_lift (rd \<G>) (g n)),
           run_seed = (\<lambda>f ctx. read (place_cmb p
                         (dg_local (snd sol (Inr (seed (FunctionEntry f) ctx)))) g)),
           run_step = (\<lambda>v ctx a. read (let d = place_cmb p (dg_local (snd sol (Inl (v, ctx)))) g
                                       in closed_step c a d)),
           run_succ = (\<lambda>u ctx ca q.
             let d = entry_of \<G> p (call_info_of ca q) (dg_local (snd sol (Inl (u, ctx)))) g
             in if d = Bot then None else Some (route \<G> u ctx d ca)) \<rparr>)"

definition run :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ('c, 'n, 'v) solved_run" where
  "run \<G> p = solved_run_of \<G> p (solution \<G> p)"

lemma run_table_run [simp]: "run_table (run \<G> p) = result \<G> p"
  by (simp add: run_def solved_run_of_def result_def Let_def)

lemma run_succ_run: "run_succ (run \<G> p) = live_succ \<G> p"
  by (simp add: run_def solved_run_of_def live_succ_def ctx_succ_def sol_env_def sol_global_def
      Let_def fun_eq_iff)

text \<open>
  The contextual publication surface: one verdict per context at a check, and
  the aggregate a caller prints. Both are \<^const>\<open>classify_checks_ctx\<close> and
  \<^const>\<open>classify_checks_verdicts\<close> unchanged -- they are generic in the context
  type already -- so nothing here is policy-specific beyond supplying this
  pipeline's own result table.
\<close>

definition check_projection :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> ('c \<times> contextual_verdict) set) list" where
  "check_projection \<G> p = classify_checks_ctx (prog_cfg p) (result \<G> p) classify"

definition verdict_report :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "verdict_report \<G> p = classify_checks_verdicts (prog_cfg p) (result \<G> p) classify"

text \<open>
  The same table read at one context: the state published there, and the check
  report off those states. These are \<^locale>\<open>analysis_surface\<close>'s readings of this
  pipeline's result, so every policy publishes the same surface; a
  context-insensitive run reads it at \<open>()\<close>.
\<close>

definition state_at :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'v" where
  "state_at \<G> = analysis_surface.state_at (result \<G>) bot_state"

definition report :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'c \<Rightarrow> check_report_entry list" where
  "report \<G> = analysis_surface.report (result \<G>) bot_state classify"

definition report_with_state :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog
    \<Rightarrow> 'c \<Rightarrow> (pp \<times> exp \<times> check_result \<times> bool \<times> 'v) list" where
  "report_with_state \<G> = analysis_surface.report_with_state (result \<G>) bot_state classify"

lemma state_at_unfold:
  "state_at \<G> p ctx v
     = (case lookup_table (result \<G> p) v ctx of Bot \<Rightarrow> bot_state | Lifted st \<Rightarrow> st)"
  by (simp add: state_at_def analysis_surface.state_at_def)
end

text \<open>Register the exported locale equations for direct calls to the generic pipeline.
  Attributes inside the locale apply through interpretation; code generation here also
  needs equations for the constants with their locale parameters left abstract.\<close>

declare
  dg_pipeline.analysis_spec_def [code]
  dg_pipeline.comp_entry_def [code]
  dg_pipeline.entry_alt_def [code]
  dg_pipeline.entry_of_def [code]
  dg_pipeline.sol_global_def [code]
  dg_pipeline.init_publications_code [code]
  dg_pipeline.equations_def [code]
  dg_pipeline.solution_code [code]
  dg_pipeline.terminates_code [code]
  dg_pipeline.sol_vars_def [code]
  dg_pipeline.sol_env_def [code]
  dg_pipeline.reader_def [code]
  dg_pipeline.result_def [code]
  dg_pipeline.ctx_succ_def [code]
  dg_pipeline.live_succ_def [code]
  dg_pipeline.solved_run_of_def [code]
  dg_pipeline.run_def [code]
  dg_pipeline.check_projection_def [code]
  dg_pipeline.verdict_report_def [code]
  dg_pipeline.state_at_def [code]
  dg_pipeline.report_def [code]
  dg_pipeline.report_with_state_def [code]

subsection \<open>The contracts\<close>

text \<open>
  What an instance owes, and nothing more: its component is sound for the
  concretization its publication map induces, its entry answers one alternative, its two
  emptiness tests are exact, its seed keys are distinct from the analysis-wide
  global, its solver is a \<^locale>\<open>certified_solver\<close> (a post-solution over
  finitely many keys once it terminates), its classifier is correct, and its entry
  state describes every initial store. The equation system, the solve, the covered keys, the reader,
  the result table and the report are all fixed by \<^locale>\<open>dg_pipeline\<close>
  above and appear here only in conclusions. Each obligation is stated at the
  program's own declared globals, the one set the soundness statement uses.
\<close>

locale dg_analysis =
  dg_pipeline comp emp rd init_st buffer_key global_of seed route root_ctx solve solve_dom
    bot_state classify place_spec place_cmb place_rl place_rg place_inits place_enter
  + certified_solver solve solve_dom solve_c
  for comp :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 's::semilattice_sup lifted local_spec"
    and emp :: "imp_prog \<Rightarrow> 's \<Rightarrow> bool"
    and rd :: "(vname \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 'v"
    and init_st :: 's
    and buffer_key :: 'k
    and global_of :: "'n \<Rightarrow> 'k"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 's lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and root_ctx :: 'c
    and solve solve_dom
    and bot_state :: 'v
    and classify :: "exp \<Rightarrow> 'v \<Rightarrow> check_result"
    and \<gamma>\<^sub>V :: "'v \<Rightarrow> store set"
    and empty\<^sub>V :: "'v \<Rightarrow> bool"
    and solve_c :: "(pp \<times> 'c, 'k, ('s lifted, 's lifted) dg_state) eqsT
                    \<Rightarrow> pp \<times> 'c
                    \<Rightarrow> ((pp \<times> 'c) set
                          \<times> (pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 's lifted) dg_state)) option"
    and place_spec :: "imp_prog \<Rightarrow> 's lifted local_spec
                        \<Rightarrow> (pp \<times> 'c, 'k, 'n, 's lifted, 's lifted) dg_spec"
    and place_cmb :: "imp_prog \<Rightarrow> 's lifted \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted"
    and place_rl :: "(vname \<Rightarrow> bool) \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
    and place_rg :: "(vname \<Rightarrow> bool) \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
    and place_inits :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ('n \<times> 's lifted) list"
    and place_enter :: "imp_prog \<Rightarrow> call_info \<Rightarrow> 's lifted \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> 's lifted" +
  assumes comp_sound:
      "\<And>p. sound_local_spec (declared_global p)
               (\<lambda>d. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) d))
               (comp (declared_global p) p)"
    and enter_single:
      "\<And>p ci d. ls_enter (comp (declared_global p) p) (ls_channel (comp (declared_global p) p) d)
                    ci (d, d)
                  = [(d, comp_entry (declared_global p) p ci d)]"
    and place_contract:
      "\<And>p. analysis_contract (analysis_spec (declared_global p) p)
               (\<lambda>d e. gamma_lift \<gamma>\<^sub>V
                        (map_lift (rd (declared_global p)) (place_cmb p d e)))
               (declared_global p)"
    and place_enter_runs:
      "\<And>p ci d \<sigma>. \<exists>pub. enter_runs (enter\<^sup># (analysis_spec (declared_global p) p) ci)
          (mk_dg_man d global_of) \<sigma>
          [entry_alt (declared_global p) p ci d (genv global_of \<sigma>)] pub"
    and place_enter_deps:
      "\<And>p ci d \<sigma>. \<exists>deps. enter_deps (enter\<^sup># (analysis_spec (declared_global p) p) ci)
          (mk_dg_man d global_of) \<sigma>
          [entry_alt (declared_global p) p ci d (genv global_of \<sigma>)] deps"
    and place_entry_sound:
      "\<And>p ci d \<sigma> pub s.
         enter_runs (enter\<^sup># (analysis_spec (declared_global p) p) ci)
           (mk_dg_man d global_of) \<sigma>
           [entry_alt (declared_global p) p ci d (genv global_of \<sigma>)] pub
         \<Longrightarrow> genv global_of pub \<le> genv global_of \<sigma>
         \<Longrightarrow> s \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
              (place_cmb p d (genv global_of \<sigma>)))
         \<Longrightarrow> s \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
                   (place_cmb p
                      (fst (entry_alt (declared_global p) p ci d (genv global_of \<sigma>)))
                      (genv global_of \<sigma>)))
           \<and> call_enter (declared_global p) (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
               \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
                   (place_cmb p
                      (snd (entry_alt (declared_global p) p ci d (genv global_of \<sigma>)))
                      (genv global_of \<sigma>)))"
    and place_cmb_bot: "\<And>p e. place_cmb p Bot e = Bot"
    and place_init:
      "\<And>p. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) (Lifted init_st))
         \<subseteq> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
              (place_cmb p (Lifted init_st) (init_env (declared_global p) p)))"
    and empty_rd: "\<And>p s. emp p s \<longleftrightarrow> empty\<^sub>V (rd (declared_global p) s)"
    and empty\<^sub>V_sound: "sound_emptiness empty\<^sub>V \<gamma>\<^sub>V"
    and seed_ne_buffer_key: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and seed_ne_global_of: "\<And>v ctx n. seed v ctx \<noteq> global_of n"
    and classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<gamma>\<^sub>V d \<Longrightarrow> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<gamma>\<^sub>V d
         \<Longrightarrow> \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and bot_state_empty: "\<gamma>\<^sub>V bot_state = {}"
    and init_sound:
      "\<And>p. cinit_stores (declared_global p) \<subseteq> \<gamma>\<^sub>V (rd (declared_global p) init_st)"
begin

text \<open>The generic contract asks the published emptiness test only to be sound: a
  product of analyses may describe nothing without any one of them saying so. A
  particular instance may still be exact.\<close>

lemmas empty\<^sub>V_soundD = sound_emptinessD [OF empty\<^sub>V_sound]

text \<open>
  Termination is a per-program side condition, and this is how a caller decides
  it: run the solver's own executable termination check on this program's
  equations. The premise stays \<open>solve_dom\<close> everywhere else, so nothing in the
  soundness argument depends on the check having been run.
\<close>

lemma terminates_of_solve_c:
  assumes "solve_c (equations \<G> p) (root_query p) \<noteq> None"
  shows "terminates \<G> p"
  unfolding terminates_def by (rule dom_of_solve_c[OF assms])

text \<open>
  An answer of the executable solver is the solve itself, so a run built from that
  answer is \<^const>\<open>run\<close>, and its program needs no separate termination premise.
\<close>

lemma solve_c_run:
  assumes "solve_c (equations \<G> p) (root_query p) = Some sol"
  shows "terminates \<G> p" and "solved_run_of \<G> p sol = run \<G> p"
  using assms terminates_of_solve_c solve_of_solve_c[OF assms]
  by (simp_all add: run_def solution_def)

lemma vars_finite_of_terminates:
  assumes "terminates \<G> p"
  shows "finite (sol_vars \<G> p)"
  using solve_fin[OF assms[unfolded terminates_def]]
  by (simp add: sol_vars_def solution_def)

text \<open>
  The contexts a concrete call is admitted at under an entry-state policy: every
  context the entered state routes to. This is a top-level constant rather than
  something read out of a per-program interpretation, because an analysis
  publishes it -- a caller stating a context-indexed collecting fact has to name
  the relation those contexts are indexed by, and an example checking a routing
  decision has to name it too.

  With one alternative per call it is one context per abstract caller state; it
  is still a relation and not a function because several concrete callers sharing
  one abstract state reach the same context.
\<close>

definition admitted_contexts :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 'c context_policy" where
  "admitted_contexts \<G> p =
     routed_entry_context_rel
       (\<lambda>ci d. [entry_alt \<G> p ci d (sol_global \<G> p)])
       (\<lambda>d e. gamma_lift \<gamma>\<^sub>V (map_lift (rd \<G>) (place_cmb p d e)))
       (sol_env \<G> p) global_of (route \<G>)"

subsection \<open>What the assembly derives, for one program\<close>

text \<open>
  Fixing one program \<open>p\<close>, this part equates the published table with the solved
  reader, puts the solver's answer in the routed spine's shape, and states routed
  soundness for any relation of admitted contexts.
\<close>

context
  fixes p :: imp_prog
begin

abbreviation (input) pgs :: "vname \<Rightarrow> bool" where "pgs \<equiv> declared_global p"
  \<comment> \<open>input-only, so interpreted facts print \<open>declared_global p\<close>\<close>

text \<open>What a carrier state describes, published and concretized, and what a point's
  two halves describe once recombined against the solved global.\<close>

abbreviation cgam :: "'s lifted \<Rightarrow> store set" where
  "cgam d \<equiv> gamma_lift \<gamma>\<^sub>V (map_lift (rd pgs) d)"

abbreviation (input) pgam :: "'s lifted \<Rightarrow> ('n \<Rightarrow> 's lifted) \<Rightarrow> store set" where
  "pgam d e \<equiv> cgam (place_cmb p d e)"

abbreviation (input) gsol :: "'n \<Rightarrow> 's lifted" where
  "gsol \<equiv> sol_global pgs p"

abbreviation entered :: "call_info \<Rightarrow> 's lifted \<Rightarrow> 's lifted" where
  "entered ci d \<equiv> entry_of pgs p ci d gsol"

lemma empty_rd_exact: "emp p s = empty\<^sub>V (rd pgs s)"
  by (simp add: empty_rd)

lemma dg_spec_wf_analysis_spec [intro, simp]: "dg_spec_wf (analysis_spec pgs p)"
  by (rule analysis_contract.spec_wf[OF place_contract])

lemma pgam_Bot [simp]: "pgam Bot g = {}"
  by (simp add: place_cmb_bot)

text \<open>
  The published table and the solved reader describe the same stores at every
  key. A caller states soundness against \<^const>\<open>lookup_table\<close> of the result
  table, while the routed endpoints are stated against the reader; this is the
  equation between them, and it needs no coverage premise. At a covered key it
  is publication commuting with the normalization; at an uncovered one it is
  \<^const>\<open>Bot\<close> against \<^const>\<open>Bot\<close>, and both describe nothing.
\<close>

lemma gamma_reader_eq_lookup:
  "pgam (reader pgs p (Inl (v, ctx))) gsol
     = gamma_lift \<gamma>\<^sub>V (lookup_table (result pgs p) v ctx)"
proof -
  have gc: "gamma_lift \<gamma>\<^sub>V (canonicalize_lift empty\<^sub>V x) = gamma_lift \<gamma>\<^sub>V x" for x
    by (rule gamma_lift_canonicalize_lift) (rule empty\<^sub>V_soundD)
  show ?thesis
  proof (cases "(v, ctx) \<in> sol_vars pgs p")
    case True
    then show ?thesis
      by (simp add: reader_def result_def sol_vars_def sol_env_def sol_global_def gc
          map_lift_canonicalize_lift[of "emp p" "empty\<^sub>V" "rd pgs", OF empty_rd_exact])
  next
    case False
    then show ?thesis by (simp add: reader_def result_def sol_vars_def bot_lifted_eq)
  qed
qed

subsubsection \<open>The solver's answer, in the shape the routed spine consumes\<close>

text \<open>
  An analysis solves the buffered generator -- a node with several intra
  predecessors or several returning calls publishes its analysis-wide
  contribution once per evaluation rather than once per contribution -- while the
  framework states its soundness over the unbuffered one. \<open>pp_routed\<close> is that
  reconciliation at this pipeline's own equations, which the placement owes.
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
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. buffer_key) (route pgs)
        (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec pgs p) a src global_of)
        (routed_call_program (analysis_spec pgs p) global_of seed
           (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        (prog_cfg p) Bot (Lifted init_st) (place_rg pgs (Lifted init_st)))
     (root_query p) (sol_env pgs p) (sol_vars pgs p)"
  using part_post_solution_with_init[OF pp_buffered[OF solves, unfolded equations_def]]
  unfolding compiled_routed_eqs_for_def bot_lifted_eq
  by (rule pp_routed_of_buffered[OF dg_spec_wf_analysis_spec seed_ne_buffer_key])

text \<open>
  The run starts below the solved environment once the solve covers the program
  entry: the entry node publishes the placement's initial global part at its own
  key, and each listed initial value at its name's key.
\<close>

lemma init_publication_le_sol:
  assumes solves: "terminates pgs p"
    and entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
    and mem: "(n, d) \<in> set (place_inits pgs p)"
  shows "d \<le> gsol n"
proof -
  have pp: "part_post_solution (equations pgs p) (root_query p) (sol_env pgs p) (sol_vars pgs p)"
    by (rule pp_buffered[OF solves])
  have "DG Bot d \<le> sol_env pgs p (Inr (global_of n))"
    by (rule post_bounded_with_init_at[OF post_bounded_of_part_post_solution[OF pp,
          unfolded equations_def] entry_cov])
       (use mem in \<open>auto simp: init_publications_def\<close>)
  then show ?thesis by (simp add: sol_global_def less_eq_dg_state_def)
qed

lemma foldr_init_le:
  "\<forall>(m, d) \<in> set xs. d \<le> f m
     \<Longrightarrow> (\<Squnion>(m, d)\<leftarrow>filter (\<lambda>(m, d). m = n) xs. d) \<le> (f n :: 's lifted)"
  by (induction xs) auto

lemma init_env_le_sol:
  assumes solves: "terminates pgs p"
    and entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
    and own: "place_rg pgs (Lifted init_st) \<le> dg_global (sol_env pgs p (Inr buffer_key))"
  shows "init_env pgs p \<le> gsol"
proof (rule le_funI)
  fix n
  have "(\<Squnion>(m, d)\<leftarrow>filter (\<lambda>(m, d). m = n) (place_inits pgs p). d) \<le> gsol n"
    by (rule foldr_init_le) (use init_publication_le_sol[OF solves entry_cov] in blast)
  moreover have "(if global_of n = buffer_key then place_rg pgs (Lifted init_st) else Bot)
                   \<le> gsol n"
    using own by (auto simp: sol_global_def)
  ultimately show "init_env pgs p n \<le> gsol n"
    unfolding init_env_def by simp
qed

subsubsection \<open>The one entry alternative this carrier answers with\<close>

text \<open>
  The specification's entry answers with a single alternative, the recombined
  caller state and the callee frame entered from it, each split back by the
  placement. \<open>entry_cover\<close> is the only fact about it any context policy needs,
  namely that a concrete call from a described caller lands in the described
  callee.
\<close>

text \<open>
  What a call publishes on entry is below the solved global, once the node the
  call returns to is solved: that node's equation runs the call, and a
  post-solution bounds what every solved equation publishes.
\<close>

lemma enter_pub_le_sol:
  assumes solves: "terminates pgs p"
    and cont: "(k, ctx) \<in> sol_vars pgs p"
    and ce: "(u, ca, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and R: "enter_runs (enter\<^sup># (analysis_spec pgs p) (call_info_of ca q))
              (mk_dg_man (dg_local (sol_env pgs p (Inl (u, ctx)))) global_of)
              (sol_env pgs p) pairs pub"
  shows "genv global_of pub \<le> gsol"
proof (rule le_funI)
  fix n
  let ?K = "Inr (global_of n)"
  let ?\<sigma> = "sol_env pgs p"
  let ?callee = "routed_callee_call_program (analysis_spec pgs p) global_of seed (route pgs)
                   (\<lambda>d. d = Bot) ctx ca u (dg_local (?\<sigma> (Inl (u, ctx)))) q"
  let ?call = "routed_call_program (analysis_spec pgs p) global_of seed
                 (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot) (route pgs) ctx ca u k"
  let ?contribs = "routed_contribution_programs intra_predecessor_addr_list call_site_list (route pgs)
        (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec pgs p) a src global_of)
        (routed_call_program (analysis_spec pgs p) global_of seed
           (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed) (prog_cfg p) ctx k"
  let ?rhs = "routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. buffer_key) (route pgs)
        (\<lambda>ctx' src a. dg_spec_edge_program (analysis_spec pgs p) a src global_of)
        (routed_call_program (analysis_spec pgs p) global_of seed
           (static_resolve (prog_cfg p)) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs seed)
        (prog_cfg p) Bot (Lifted init_st) (place_rg pgs (Lifted init_st))"
  have fin: "finite (calls (prog_cfg p))"
    unfolding prog_cfg_def by (simp add: compile_prog_finite)
  have wf: "\<forall>t \<in> set ?contribs. sp_wf t"
    by (rule routed_contribution_programs_wf) auto
  have "pub ?K \<le> sides_of_program ?callee ?\<sigma> ?K"
    unfolding routed_callee_call_program_def
    by (simp add: sp_compile_bind sp_wf_observes enter_runsD_sides[OF R] sup_fun_def)
  also have "\<dots> \<le> sides_of_program ?call ?\<sigma> ?K"
    by (rule routed_call_program_sides_ge_at[OF dg_spec_wf_analysis_spec])
       (use ce fin in simp)
  also have "\<dots> \<le> sides_of_program (side_rhs_fold_dg
      (if k = cfg_entry (prog_cfg p) then Bot \<squnion> Lifted init_st else Bot) ?contribs)
      ?\<sigma> ?K"
  proof (rule sides_le_side_rhs_fold_dg[OF wf])
    have "(u, ca) \<in> set (call_site_list (prog_cfg p) k)" using ce fin by auto
    then show "?call \<in> set ?contribs" by (rule routed_contribution_programs_combineI)
  qed
  also have "\<dots> \<le> sides_of_rhs (?rhs (k, ctx)) ?\<sigma> ?K"
    unfolding routed_node_rhs_def Let_def
    by (cases "k = cfg_entry (prog_cfg p)") (auto simp: Let_def)
  also have "\<dots> \<le> ?\<sigma> ?K"
    using pp_routed[OF solves] cont by (blast dest: le_funD)
  finally show "genv global_of pub n \<le> gsol n"
    unfolding sol_global_def by (simp add: less_eq_dg_state_def)
qed

lemma entry_cover:
  assumes solves: "terminates pgs p"
    and cont: "(k, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, k) \<in> calls (prog_cfg p)"
    and sin: "s \<in> pgam (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol"
  shows "entry_pairs_cover (\<lambda>d. pgam d gsol) s (call_enter pgs (CallEdge dst pars args) s)
           [entry_alt pgs p (call_info_of (CallEdge dst pars args) q)
              (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol]"
proof -
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?d = "dg_local (sol_env pgs p (Inl (u, ctx)))"
  let ?alt = "entry_alt pgs p ?ci ?d gsol"
  obtain pub where R: "enter_runs (enter\<^sup># (analysis_spec pgs p) ?ci)
      (mk_dg_man ?d global_of) (sol_env pgs p)
      [entry_alt pgs p ?ci ?d (genv global_of (sol_env pgs p))] pub"
    using place_enter_runs by blast
  have le: "genv global_of pub \<le> genv global_of (sol_env pgs p)"
    using enter_pub_le_sol[OF solves cont ce R] by (simp add: sol_global_def)
  have "s \<in> pgam (fst ?alt) gsol \<and> call_enter pgs (CallEdge dst pars args) s \<in> pgam (snd ?alt) gsol"
    using place_entry_sound[OF R le sin[unfolded sol_global_def]]
    unfolding sol_global_def by (simp del: declared_global_iff)
  then show ?thesis
    by (intro entry_pairs_coverI[of "fst ?alt" "snd ?alt"]) simp_all
qed

subsubsection \<open>The routed soundness statement, at any admitted-context relation\<close>

text \<open>
  Which contexts a concrete call is admitted at is the one thing a context policy
  still chooses, so \<open>adm\<close> is a parameter here rather than a derived object. What
  the policy owes about it is exactly two facts: a context \<open>adm\<close> admits is the one
  this pipeline's route computes on the entered state, at a covered unknown
  (\<open>cover_R\<close>); and \<open>adm\<close> admits at least one context for every concrete call at a
  covered call site (\<open>total_R\<close>). Everything else below is fixed by the pipeline.
\<close>

text \<open>
  The specification is sound for the recombined concretization; the placement
  owes this, so the routed statement below never re-derives it.
\<close>

interpretation dg_base: analysis_contract "analysis_spec pgs p" "\<lambda>d e. pgam d e" pgs
  by (rule place_contract)

lemma routed_analysis_sound_of_live:
  fixes adm :: "'c context_policy"
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> dg_local (sol_env pgs p (Inl (u, ctx))) \<noteq> Bot
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> ctx' \<in> adm u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s)
        \<Longrightarrow> entered (call_info_of (CallEdge dst pars args) q)
              (dg_local (sol_env pgs p (Inl (u, ctx)))) \<noteq> Bot
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (dg_local (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> pgam (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol
        \<Longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) \<noteq> {}"
  shows "routed_analysis (analysis_spec pgs p) (\<lambda>d e. pgam d e) pgs (prog_cfg p)
     buffer_key global_of
     (route pgs) Bot (Lifted init_st) (place_rg pgs (Lifted init_st)) (sol_env pgs p)
     (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) adm (\<lambda>d e. map_lift (rd pgs) (place_cmb p d e)) \<gamma>\<^sub>V empty\<^sub>V
     classify"
proof (unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd FinC CallsUnique
    SeedUnknown SeedNeGlobal IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd GammaRd
    EmptyExact ClProved ClRefuted VarsFin)
  case CmbWf show ?case by (rule sp_wf_routed_call_program[OF dg_spec_wf_analysis_spec])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case unfolding prog_cfg_def using compile_prog_finite by simp
next
  case PP show ?case by (rule post_bounded_of_part_post_solution[OF pp_routed[OF solves]])
next
  case (SgCov v c) then show ?case by simp
next
  case (SgUncov v c) then show ?case by (simp add: bot_lifted_eq)
next
  case (Fwd u a v c)
  have "dg_local (sol_env pgs p (Inl (u, c))) \<noteq> Bot"
    using Fwd(2) by auto
  with Fwd(1,3) show ?case by (blast intro: fwd_ok)
next
  case FinC show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding calls_source_unique_def prog_cfg_def
    using compile_prog_calls_source_unique by blast
next
  case (SeedUnknown q ctx) show ?case by (rule seed_ne_buffer_key)
next
  case (SeedNeGlobal q ctx v) show ?case by (rule seed_ne_global_of)
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d g') then show ?case by simp
next
  case (ResolveSound u ctx dst pars args q cont s)
  then show ?case unfolding prog_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args q cont s ctx')
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env pgs p (Inl (u, ctx)))"
  let ?g = "genv global_of (sol_env pgs p)"
  have sin: "s \<in> pgam ?caller gsol"
    using EnterCover(3) by (simp add: sol_global_def)
  have cov: "entry_pairs_cover (\<lambda>d. pgam d gsol) s
      (call_enter pgs (CallEdge dst pars args) s) [entry_alt pgs p ?ci ?caller gsol]"
    by (rule entry_cover[OF solves comb_fwd_ok[OF EnterCover(1,2)] EnterCover(2) sin])
  obtain c e where ce: "entry_alt pgs p ?ci ?caller gsol = (c, e)"
    by (cases "entry_alt pgs p ?ci ?caller gsol")
  have nbE: "entered ?ci ?caller \<noteq> Bot"
  proof
    assume "entered ?ci ?caller = Bot"
    with cov ce show False by (simp add: entry_pairs_cover_def entry_of_def place_cmb_bot)
  qed
  have req: "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'"
    and covE: "(FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using cover_R[OF EnterCover(1,2,4) nbE] by blast+
  obtain pub where runs: "enter_runs (enter\<^sup># (analysis_spec pgs p) ?ci)
      (mk_dg_man ?caller global_of) (sol_env pgs p)
      [entry_alt pgs p ?ci ?caller ?g] pub"
    using place_enter_runs by blast
  obtain deps where deps: "enter_deps (enter\<^sup># (analysis_spec pgs p) ?ci)
      (mk_dg_man ?caller global_of) (sol_env pgs p)
      [entry_alt pgs p ?ci ?caller ?g] deps"
    using place_enter_deps by blast
  have ce': "entry_alt pgs p ?ci ?caller ?g = (c, e)"
    using ce by (simp add: sol_global_def)
  have sc: "s \<in> pgam c ?g" and ec: "call_enter pgs (CallEdge dst pars args) s \<in> pgam e ?g"
    using cov ce by (simp_all add: entry_pairs_cover_def sol_global_def)
  have re: "route pgs u ctx e (CallEdge dst pars args) = ctx'"
    using req ce by (simp add: entry_of_def)
  show ?case
    using runs deps sc ec re covE unfolding ce' by fastforce
next
  case (EnterTotal u ctx dst pars args q cont s)
  then show ?case by (intro total_R) (simp_all add: sol_global_def)
next
  case (CombFwd cl c1 dst pars args q cont)
  then show ?case by (rule comb_fwd_ok)
next
  case (GammaRd d g') show ?case by simp
next
  case (EmptyExact v) then show ?case by (rule empty\<^sub>V_soundD)
next
  case (ClProved c d s) then show ?case by (rule classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule classify_refuted)
next
  case VarsFin show ?case by (rule vars_finite_of_terminates[OF solves])
qed

lemma routed_analysis_sound_of:
  fixes adm :: "'c context_policy"
  assumes solves: "terminates pgs p"
    and fwd_ok: "\<And>u a v ctx. (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, a, v) \<in> intra (prog_cfg p) \<Longrightarrow> (v, ctx) \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
    and cover_R: "\<And>u ctx dst pars args q cont s ctx'.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> ctx' \<in> adm u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s)
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (dg_local (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> pgam (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol
        \<Longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) \<noteq> {}"
  shows "routed_analysis (analysis_spec pgs p) (\<lambda>d e. pgam d e) pgs (prog_cfg p)
     buffer_key global_of
     (route pgs) Bot (Lifted init_st) (place_rg pgs (Lifted init_st)) (sol_env pgs p)
     (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) adm (\<lambda>d e. map_lift (rd pgs) (place_cmb p d e)) \<gamma>\<^sub>V empty\<^sub>V
     classify"
  by (rule routed_analysis_sound_of_live [where adm = adm, OF solves _ comb_fwd_ok _ total_R])
     (blast intro: fwd_ok dest: cover_R)+

subsubsection \<open>The published endpoint, under termination and coverage\<close>

text \<open>
  Under termination and closure of the solved keys, \<open>activation_collect_sound_of\<close>
  bounds every admitted activation by the solved table's entry at its context.
\<close>

lemma cinit_le_init: "cinit_stores pgs \<subseteq> pgam (Lifted init_st) (init_env pgs p)"
  using init_sound[of p] place_init[of p] by auto

text \<open>
  Every activation the activation-trace semantics admits at a context is described by the
  solved table's entry for that context. The coverage premises are the shape a
  solver's own reachable set supplies: an edge out of an unknown the solve
  visited lands on one it also visited.
\<close>

lemma activation_collect_sound_of:
  fixes adm :: "'c context_policy"
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
        \<Longrightarrow> ctx' \<in> adm u ctx (call_info_of (CallEdge dst pars args) q) s
              (call_enter pgs (CallEdge dst pars args) s)
        \<Longrightarrow> route pgs u ctx
                (entered (call_info_of (CallEdge dst pars args) q)
                   (dg_local (sol_env pgs p (Inl (u, ctx)))))
                (CallEdge dst pars args) = ctx'
            \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    and total_R: "\<And>u ctx dst pars args q cont s.
        (u, ctx) \<in> sol_vars pgs p
        \<Longrightarrow> (u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> s \<in> pgam (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol
        \<Longrightarrow> adm u ctx (call_info_of (CallEdge dst pars args) q) s
                      (call_enter pgs (CallEdge dst pars args) s) \<noteq> {}"
  shows "\<A>\<^bsub>pgs,adm,root_ctx,prog_cfg p,cinit_stores pgs\<^esub> v ctx
           \<subseteq> pgam (reader pgs p (Inl (v, ctx))) gsol"
proof -
  interpret adapter: routed_analysis "analysis_spec pgs p" "\<lambda>d e. pgam d e" pgs
      "prog_cfg p" buffer_key global_of "route pgs" Bot "Lifted init_st"
      "place_rg pgs (Lifted init_st)" "sol_env pgs p" "sol_vars pgs p" "root_query p" seed
      "\<lambda>d. d = Bot" adm "\<lambda>d e. map_lift (rd pgs) (place_cmb p d e)" \<gamma>\<^sub>V empty\<^sub>V classify
    by (rule routed_analysis_sound_of
          [where adm = adm, OF solves fwd_ok comb_fwd_ok cover_R total_R])
  have init_env_le: "init_env pgs p \<le> genv global_of (sol_env pgs p)"
    using init_env_le_sol[OF solves entry_cov adapter.pp_entry_init_global_bound[OF entry_cov]]
    by (simp add: sol_global_def)
  show ?thesis
    using adapter.activation_collect_dg_sound[OF entry_cov _ init_env_le, of "cinit_stores pgs" v
      ctx]
      cinit_le_init
    by (simp add: reader_def sol_global_def)
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
     routed_entry_context_rel (\<lambda>ci d. [entry_alt pgs p ci d gsol]) (\<lambda>d e. pgam d e)
       (sol_env pgs p) global_of (route pgs)"
  by (simp add: admitted_contexts_def)

abbreviation entry_context_rel :: "'c context_policy" where
  "entry_context_rel \<equiv> admitted_contexts pgs p"

text \<open>
  How a caller shows that this call is admitted at the context it computed: the
  concrete caller store is described by the recombined caller, and the entered
  store by the callee frame entered from it, each recombined against the solved
  global. The single alternative means a witness never has to name the
  alternatives list.
\<close>

lemma admitted_contextsI:
  assumes caller: "s \<in> pgam (fst (entry_alt pgs p ci (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol))
                     gsol"
    and entered_in: "s' \<in> pgam (entered ci (dg_local (sol_env pgs p (Inl (u, ctx))))) gsol"
  shows "route pgs u ctx (entered ci (dg_local (sol_env pgs p (Inl (u, ctx)))))
             (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))
           \<in> entry_context_rel u ctx ci s s'"
  unfolding admitted_contexts_alt
  by (rule routed_entry_context_relI
        [where cont = "fst (entry_alt pgs p ci (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol)"])
     (use caller entered_in in \<open>simp_all add: entry_of_def sol_global_def\<close>)

text \<open>
  The same fact with the call action spelled as the caller has it. A witness
  names a literal \<^const>\<open>CallEdge\<close>, while the rule above reconstructs one from
  the \<^type>\<open>call_info\<close>'s three projections, and \<^theory_text>\<open>rule\<close> does not reduce the
  projections. Every concrete instance wants this shape.
\<close>

lemma admitted_contextsI_call:
  assumes caller: "s \<in> pgam (fst (entry_alt pgs p (call_info_of (CallEdge dst pars args) q)
                       (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol)) gsol"
    and entered_in: "s' \<in> pgam (entered (call_info_of (CallEdge dst pars args) q)
                           (dg_local (sol_env pgs p (Inl (u, ctx))))) gsol"
  shows "route pgs u ctx
             (entered (call_info_of (CallEdge dst pars args) q)
                (dg_local (sol_env pgs p (Inl (u, ctx)))))
             (CallEdge dst pars args)
           \<in> entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s s'"
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
                    (dg_local (sol_env pgs p (Inl (u, ctx)))))
                 (CallEdge dst pars args))
              \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
  shows "routed_analysis (analysis_spec pgs p) (\<lambda>d e. pgam d e) pgs (prog_cfg p)
     buffer_key global_of
     (route pgs) Bot (Lifted init_st) (place_rg pgs (Lifted init_st)) (sol_env pgs p)
     (sol_vars pgs p) (root_query p)
     seed (\<lambda>d. d = Bot) entry_context_rel
     (\<lambda>d e. map_lift (rd pgs) (place_cmb p d e)) \<gamma>\<^sub>V empty\<^sub>V classify"
proof (rule routed_analysis_sound_of
    [where adm = entry_context_rel, OF solves fwd_ok comb_fwd_ok])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "ctx' \<in> entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s
               (call_enter pgs (CallEdge dst pars args) s)"
  let ?ci = "call_info_of (CallEdge dst pars args) q"
  let ?caller = "dg_local (sol_env pgs p (Inl (u, ctx)))"
  from Rc[unfolded admitted_contexts_alt] obtain cont' entry
    where mem: "(cont', entry) \<in> set [entry_alt pgs p ?ci ?caller gsol]"
      and req0: "ctx' = route pgs u ctx entry
                   (CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci))"
    by (rule routed_entry_context_relE)
  have "entry = entered ?ci ?caller" using mem by (simp add: entry_of_def) (metis snd_conv)
  with req0 have req: "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'"
    by simp
  show "route pgs u ctx (entered ?ci ?caller) (CallEdge dst pars args) = ctx'
          \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using req call_fwd_ok[OF covV ce] by simp
next
  fix u ctx dst pars args q cont and s :: store
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and sin: "s \<in> pgam (dg_local (sol_env pgs p (Inl (u, ctx)))) gsol"
  show "entry_context_rel u ctx (call_info_of (CallEdge dst pars args) q) s
                 (call_enter pgs (CallEdge dst pars args) s) \<noteq> {}"
    unfolding admitted_contexts_alt
    by (rule routed_entry_context_rel_total)
       (use entry_cover[OF solves comb_fwd_ok[OF covV ce] ce sin]
         in \<open>simp add: sol_global_def del: declared_global_iff\<close>)
qed

text \<open>
  The two endpoints an entry-state caller consumes: the per-context collecting
  bound, and the existence of a context for every valid activation trace, which a
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
                    (dg_local (sol_env pgs p (Inl (u, ctx)))))
                 (CallEdge dst pars args))
              \<in> sol_vars pgs p"
    and comb_fwd_ok: "\<And>cl c1 dst pars args q cont. (cl, c1) \<in> sol_vars pgs p
        \<Longrightarrow> (cl, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)
        \<Longrightarrow> (cont, c1) \<in> sol_vars pgs p"
begin

interpretation entry: routed_analysis "analysis_spec pgs p" "\<lambda>d e. pgam d e" pgs
    "prog_cfg p" buffer_key global_of "route pgs" Bot "Lifted init_st"
    "place_rg pgs (Lifted init_st)" "sol_env pgs p" "sol_vars pgs p" "root_query p" seed
    "\<lambda>d. d = Bot" entry_context_rel "\<lambda>d e. map_lift (rd pgs) (place_cmb p d e)"
    \<gamma>\<^sub>V empty\<^sub>V classify
  by (rule entry_state_routed_analysis_sound [OF solves fwd_ok call_fwd_ok comb_fwd_ok])

lemma entry_init_env_le:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "init_env pgs p \<le> genv global_of (sol_env pgs p)"
  using init_env_le_sol[OF solves entry_cov entry.pp_entry_init_global_bound[OF entry_cov]]
  by (simp add: sol_global_def)

corollary entry_state_activation_collect_sound:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "\<A>\<^bsub>pgs,entry_context_rel,root_ctx,prog_cfg p,cinit_stores pgs\<^esub> v ctx
           \<subseteq> pgam (reader pgs p (Inl (v, ctx))) gsol"
  using entry.activation_collect_dg_sound
      [OF entry_cov _ entry_init_env_le[OF entry_cov], of "cinit_stores pgs" v ctx]
    cinit_le_init
  by (simp add: reader_def sol_global_def)

theorem entry_state_has_context:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
    and trace: "t \<in> \<T>\<^bsub>pgs,prog_cfg p,cinit_stores pgs\<^esub>"
  shows "\<exists>c. activation_context_rel pgs entry_context_rel root_ctx (prog_cfg p) t c"
  using entry.routed_valid_activation_trace_has_context
      [OF entry_cov _ entry_init_env_le[OF entry_cov] trace] cinit_le_init
  by simp

text \<open>
  The two together: covering the entry is enough for the activation buckets to
  exhaust the context-insensitive collection, so a caller holding only a
  \<^const>\<open>node_collect\<close> membership -- which is what a source run delivers -- can
  pass to the bucket its own call history produced.  Without this the per-context
  bounds above say nothing about a run whose context is not known in advance.
\<close>

theorem entry_state_node_collect_eq_Union:
  assumes entry_cov: "(cfg_entry (prog_cfg p), root_ctx) \<in> sol_vars pgs p"
  shows "\<C>\<^bsub>pgs,prog_cfg p,cinit_stores pgs\<^esub> v
           = (\<Union>ctx. \<A>\<^bsub>pgs,entry_context_rel,root_ctx,prog_cfg p,cinit_stores pgs\<^esub> v ctx)"
  by (rule node_collect_eq_Union_activation_of_has_context)
     (rule entry_state_has_context [OF entry_cov])

end

text \<open>
  A route that never reads the state it is handed is a function of the call site
  and the caller's context alone, so the contexts it admits are the graph of a
  context function on concrete stores -- the shape the call-string and
  context-insensitive policies both publish. \<open>route_const\<close> is the whole of what
  such a policy owes; \<open>ctx_fun\<close> is its trace-semantic counterpart.
\<close>

corollary fun_route_activation_collect_sound:
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
  shows "\<A>\<^bsub>pgs,context_policy_of_fun ctx_fun,root_ctx,prog_cfg p,cinit_stores pgs\<^esub> v ctx
           \<subseteq> pgam (reader pgs p (Inl (v, ctx))) gsol"
proof (rule activation_collect_sound_of[OF solves entry_cov fwd_ok comb_fwd_ok])
  fix u ctx dst pars args q cont and s :: store and ctx'
  assume covV: "(u, ctx) \<in> sol_vars pgs p"
    and ce: "(u, CallEdge dst pars args, FunctionEntry q, cont) \<in> calls (prog_cfg p)"
    and Rc: "ctx' \<in> context_policy_of_fun ctx_fun u ctx
               (call_info_of (CallEdge dst pars args) q) s
               (call_enter pgs (CallEdge dst pars args) s)"
  have req: "route pgs u ctx d (CallEdge dst pars args) = ctx'" for d
    using Rc
    by (simp add: route_const[of _ _ _ _ "call_enter pgs (CallEdge dst pars args) s"])
  show "route pgs u ctx
          (entered (call_info_of (CallEdge dst pars args) q)
             (dg_local (sol_env pgs p (Inl (u, ctx)))))
          (CallEdge dst pars args) = ctx'
        \<and> (FunctionEntry q, ctx') \<in> sol_vars pgs p"
    using req call_fwd_ok[OF covV ce] by simp
next
  fix u ctx dst pars args q cont and s :: store
  show "context_policy_of_fun ctx_fun u ctx
                 (call_info_of (CallEdge dst pars args) q) s
                 (call_enter pgs (CallEdge dst pars args) s) \<noteq> {}"
    by simp
qed

text \<open>
  The functional route's counterpart of the entry-state union. It needs nothing
  at all: \<^const>\<open>activation_context_of\<close> is total, so every valid activation trace carries a context without
  any coverage having been established.
\<close>

theorem fun_route_node_collect_eq_Union:
  "\<C>\<^bsub>pgs,prog_cfg p,cinit_stores pgs\<^esub> v
     = (\<Union>ctx. \<A>\<^bsub>pgs,context_policy_of_fun ctx_fun,root_ctx,prog_cfg p,cinit_stores pgs\<^esub> v ctx)"
  by (rule node_collect_eq_Union_activation_of_fun)

end

end

subsection \<open>Every variable in the local half\<close>

text \<open>
  The placement every analysis uses unless it shares program globals: the
  specification is the component's own \<^const>\<open>dg_spec_of\<close>, a point's state is
  its local unknown alone, and nothing is published at the analysis-wide global.
  Its placement obligations follow from the component's soundness and its
  single-alternative entry, so an instance owes exactly what it owed before the
  placement was a parameter.
\<close>

theorem dg_analysis_whole_stateI:
  fixes comp :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 's::semilattice_sup lifted local_spec"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
  assumes solver: "certified_solver solve solve_dom solve_c"
    and comp_sound:
      "\<And>p. sound_local_spec (declared_global p)
               (\<lambda>d. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) d))
               (comp (declared_global p) p)"
    and enter_single:
      "\<And>p ci d. ls_enter (comp (declared_global p) p) (ls_channel (comp (declared_global p) p) d)
                    ci (d, d)
                  = [(d, dg_pipeline.comp_entry comp (declared_global p) p ci d)]"
    and empty_rd: "\<And>p s. emp p s \<longleftrightarrow> empty\<^sub>V (rd (declared_global p) s)"
    and empty\<^sub>V_sound: "sound_emptiness empty\<^sub>V \<gamma>\<^sub>V"
    and seed_ne: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<gamma>\<^sub>V d \<Longrightarrow> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<gamma>\<^sub>V d
         \<Longrightarrow> \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and bot_state_empty: "\<gamma>\<^sub>V bot_state = {}"
    and init_sound:
      "\<And>p. cinit_stores (declared_global p) \<subseteq> \<gamma>\<^sub>V (rd (declared_global p) init_st)"
    and seed_ne_global: "\<And>v ctx n. seed v ctx \<noteq> global_of n"
  shows "dg_analysis comp emp rd init_st buffer_key global_of seed
           solve solve_dom bot_state classify \<gamma>\<^sub>V empty\<^sub>V solve_c
           (\<lambda>\<G> c. dg_spec_of c) (\<lambda>\<G> d e. d) (\<lambda>\<G> d. d) (\<lambda>\<G> d. Bot) (\<lambda>\<G> p. [])
           (\<lambda>p ci d e. d)"
proof (rule dg_analysis.intro[OF solver dg_analysis_axioms.intro], goal_cases CompSound
    EnterSingle Contract Runs Deps EntrySound CmbBot Init EmptyRd EmptyV SeedNe SeedNeGlobal
    ClProved ClRefuted BotState InitSound)
  case (CompSound p) show ?case by (rule comp_sound)
next
  case (EnterSingle p ci d) show ?case by (rule enter_single)
next
  case (Contract p) show ?case
    unfolding dg_pipeline.analysis_spec_def by (rule dg_spec_of_contract[OF comp_sound])
next
  case (Runs p ci d \<sigma>) show ?case
    by (rule exI, simp add: dg_pipeline.analysis_spec_def dg_spec_of_def enter_single
        dg_pipeline.entry_alt_def, rule enter_runs_local_enter_transfer_mk_dg_man)
next
  case (Deps p ci d \<sigma>) show ?case
    by (rule exI, simp add: dg_pipeline.analysis_spec_def dg_spec_of_def enter_single
        dg_pipeline.entry_alt_def, rule enter_deps_local_enter_transfer_mk_dg_man)
next
  case (EntrySound p ci d \<sigma> pub s)
  let ?c = "comp (declared_global p) p"
  obtain q where "q \<in> set (ls_enter ?c (ls_channel ?c d) ci (d, d))"
      "s \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) (fst q))"
      "call_enter (declared_global p) (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
         \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) (snd q))"
    using comp_sound[of p] EntrySound(3) ls_channel_sound[OF comp_sound[of p]]
    unfolding sound_local_spec_def by (metis fst_conv)
  then show ?case
    by (simp add: enter_single dg_pipeline.entry_alt_def)
next
  case (CmbBot p g) show ?case by simp
next
  case (Init p) show ?case by simp
next
  case (EmptyRd p s) show ?case by (rule empty_rd)
next
  case EmptyV show ?case by (rule empty\<^sub>V_sound)
next
  case (SeedNe v ctx) show ?case by (rule seed_ne)
next
  case (SeedNeGlobal v ctx n) show ?case by (rule seed_ne_global)
next
  case (ClProved c d s) then show ?case by (rule classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule classify_refuted)
next
  case BotState show ?case by (rule bot_state_empty)
next
  case (InitSound p) show ?case by (rule init_sound)
qed

subsection \<open>Program globals keyed by name\<close>

text \<open>
  The placement that keeps each program global at its own unknown
  \<open>global_of x\<close>. The specification is the component wrapped by the keyed lifter,
  and a point's state is its local half recombined with the solved environment
  over the program's declared globals. The root publishes each declared
  global's initial value at its key, and the node-owned buffer stays empty.

  Beyond the component's own soundness, the carrier owes monotone operations,
  that a name outside a read set is cut below \<open>free\<close> of that set, and two facts
  about concretization: the frame law \<open>mix\<close> of @{thm [source] keyed_split_contract},
  and that a state is described by its local half recombined with its own cuts.
\<close>

theorem dg_analysis_keyedI:
  fixes comp :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> 's::semilattice_sup lifted local_spec"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and global_of :: "vname \<Rightarrow> 'k"
    and cmb :: "'s lifted \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
    and rg :: "vname \<Rightarrow> 's lifted \<Rightarrow> 's lifted"
  assumes solver: "certified_solver solve solve_dom solve_c"
    and comp_sound:
      "\<And>p. sound_local_spec (declared_global p)
               (\<lambda>d. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) d))
               (comp (declared_global p) p)"
    and enter_single:
      "\<And>p ci d. ls_enter (comp (declared_global p) p) (ls_channel (comp (declared_global p) p) d)
                    ci (d, d)
                  = [(d, dg_pipeline.comp_entry comp (declared_global p) p ci d)]"
    and cmb_mono: "\<And>d d' g g'. d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> cmb d g \<le> cmb d' g'"
    and cmb_rl: "\<And>x g. cmb (rl x) g = cmb x g"
    and rl_cmb: "\<And>d g. rl (cmb d g) = rl d"
    and cmb_bot: "\<And>g. cmb Bot g = Bot"
    and rg_mono: "\<And>x v v'. v \<le> v' \<Longrightarrow> rg x v \<le> rg x v'"
    and rg_free: "\<And>x R v. x \<notin> set R \<Longrightarrow> rg x v \<le> free R"
    and mix: "\<And>p l0 e r s s' W.
        s \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
               (cmb l0 (full_view rg (declared_global_vars p) e)))
        \<Longrightarrow> s' \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) r)
        \<Longrightarrow> (\<forall>x. declared_global p x \<longrightarrow> x \<notin> set W \<longrightarrow> s' x = s x)
        \<Longrightarrow> s' \<in> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
               (cmb (rl r) (full_view rg (declared_global_vars p)
                  (\<lambda>x. if x \<in> set W then rg x r else e x))))"
    and init_view: "\<And>p. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) (Lifted init_st))
        \<subseteq> gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p))
             (cmb (Lifted init_st) (full_view rg (declared_global_vars p)
                (\<lambda>x. rg x (Lifted init_st)))))"
    and empty_rd: "\<And>p s. emp p s \<longleftrightarrow> empty\<^sub>V (rd (declared_global p) s)"
    and empty\<^sub>V_sound: "sound_emptiness empty\<^sub>V \<gamma>\<^sub>V"
    and seed_ne: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and seed_ne_global: "\<And>v ctx n. seed v ctx \<noteq> global_of n"
    and classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<gamma>\<^sub>V d \<Longrightarrow> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<gamma>\<^sub>V d
         \<Longrightarrow> \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and bot_state_empty: "\<gamma>\<^sub>V bot_state = {}"
    and init_sound:
      "\<And>p. cinit_stores (declared_global p) \<subseteq> \<gamma>\<^sub>V (rd (declared_global p) init_st)"
  shows "dg_analysis comp emp rd init_st buffer_key global_of seed
           solve solve_dom bot_state classify \<gamma>\<^sub>V empty\<^sub>V solve_c
           (\<lambda>p c. keyed_split_spec (declared_global p) cmb rl rg free c)
           (\<lambda>p d e. cmb d (full_view rg (declared_global_vars p) e)) (\<lambda>\<G>. rl) (\<lambda>\<G> d. Bot)
           (\<lambda>\<G> p. map (\<lambda>x. (x, rg x (Lifted init_st))) (declared_global_vars p))
           (\<lambda>p ci d e. cmb d (view_of rg (call_global_reads (declared_global p) (ci_args ci)) e
              (free (call_global_reads (declared_global p) (ci_args ci)))))"
proof -
  let ?gm = "\<lambda>p d. gamma_lift \<gamma>\<^sub>V (map_lift (rd (declared_global p)) d)"
  have gm_mono: "\<And>p x y. x \<le> y \<Longrightarrow> ?gm p x \<subseteq> ?gm p y"
    using comp_sound unfolding sound_local_spec_def by metis
  show ?thesis
  proof (rule dg_analysis.intro[OF solver dg_analysis_axioms.intro], goal_cases CompSound
      EnterSingle Contract Runs Deps EntrySound CmbBot Init EmptyRd EmptyV SeedNe SeedNeGlobal
      ClProved ClRefuted BotState InitSound)
    case (CompSound p) show ?case by (rule comp_sound)
  next
    case (EnterSingle p ci d) show ?case by (rule enter_single)
  next
    case (Contract p) show ?case
      unfolding dg_pipeline.analysis_spec_def
      using comp_sound[where p = p] cmb_mono rg_mono rg_free mix[where p = p]
      by (rule keyed_split_contract)
  next
    case (Runs p ci d \<sigma>) show ?case
      using enter_runs_keyed_enter_transfer[of cmb rl rg free
          "call_global_reads (declared_global p) (ci_args ci)"
          "global_names_in (declared_global p) (ci_formals ci)"
          "\<lambda>d. ls_enter (comp (declared_global p) p) (ls_channel (comp (declared_global p) p) d)
             ci (d, d)" d global_of \<sigma>]
      by (auto simp: dg_pipeline.analysis_spec_def dg_pipeline.entry_alt_def enter_single Let_def)
  next
    case (Deps p ci d \<sigma>) show ?case
      using enter_deps_keyed_enter_transfer[of cmb rl rg free
          "call_global_reads (declared_global p) (ci_args ci)"
          "global_names_in (declared_global p) (ci_formals ci)"
          "\<lambda>d. ls_enter (comp (declared_global p) p) (ls_channel (comp (declared_global p) p) d)
             ci (d, d)" d global_of \<sigma>]
      by (auto simp: dg_pipeline.analysis_spec_def dg_pipeline.entry_alt_def enter_single Let_def)
  next
    case (EntrySound p ci d \<sigma> pub s)
    let ?\<G> = "declared_global p" and ?xs = "declared_global_vars p"
    let ?c = "comp ?\<G> p"
    let ?e = "genv global_of \<sigma>"
    let ?R = "call_global_reads ?\<G> (ci_args ci)"
    let ?v = "view_of rg ?R ?e (free ?R)"
    let ?w = "cmb d ?v"
    let ?E = "dg_pipeline.comp_entry comp ?\<G> p ci ?w"
    let ?W = "global_names_in ?\<G> (ci_formals ci)"
    let ?ce = "call_enter ?\<G> (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci))"
    have alt: "dg_pipeline.entry_alt comp (\<lambda>\<G>. rl)
        (\<lambda>p ci d e. cmb d (view_of rg (call_global_reads (declared_global p) (ci_args ci)) e
           (free (call_global_reads (declared_global p) (ci_args ci)))))
        ?\<G> p ci d ?e = (rl ?w, rl ?E)"
      by (simp add: dg_pipeline.entry_alt_def Let_def)
    have R0: "enter_runs (enter\<^sup># (dg_pipeline.analysis_spec comp
          (\<lambda>p. keyed_split_spec (declared_global p) cmb rl rg free) ?\<G> p) ci)
        (mk_dg_man d global_of) \<sigma> [(rl ?w, rl ?E)] (pub_sides global_of rg ?W (?E \<squnion> bot))"
      using enter_runs_keyed_enter_transfer[of cmb rl rg free ?R ?W
          "\<lambda>d. ls_enter ?c (ls_channel ?c d) ci (d, d)" d global_of \<sigma>]
      by (simp add: dg_pipeline.analysis_spec_def enter_single)
    have pub: "pub = pub_sides global_of rg ?W (?E \<squnion> bot)"
      using enter_runsD_sides[OF EntrySound(1)[unfolded alt], of "\<lambda>_. Answer bot"]
        enter_runsD_sides[OF R0, of "\<lambda>_. Answer bot"]
      by (simp add: bot_fun_def[symmetric])
    have E_Bot: "?E \<squnion> Bot = ?E" by (cases ?E) simp_all
    have le: "rg x ?E \<le> ?e x" if "x \<in> set ?W" for x
    proof -
      have "DG bot (rg x ?E) \<le> pub (Inr (global_of x))"
        using pub_sides_ge[OF that, of rg "?E \<squnion> bot" global_of] by (simp add: pub E_Bot)
      then have "rg x ?E \<le> genv global_of pub x" by (simp add: less_eq_dg_state_def)
      also have "\<dots> \<le> ?e x" using EntrySound(2) by (simp add: le_fun_def)
      finally show ?thesis .
    qed
    have view_ge: "full_view rg ?xs ?e \<le> ?v"
      unfolding full_view_def
    proof (rule view_of_le)
      fix x assume "x \<in> set ?xs"
      show "rg x (?e x) \<le> ?v"
      proof (cases "x \<in> set ?R")
        case True then show ?thesis by (rule view_of_ge_mem)
      next
        case False
        then show ?thesis using rg_free view_of_ge_acc by (blast intro: order_trans)
      qed
    qed simp
    have s0: "s \<in> ?gm p (cmb d (full_view rg ?xs ?e))" using EntrySound(3) by simp
    have sw: "s \<in> ?gm p ?w"
      using s0 gm_mono[OF cmb_mono[OF order_refl view_ge]] by blast
    have sE: "?ce s \<in> ?gm p ?E"
    proof -
      obtain q where "q \<in> set (ls_enter ?c (ls_channel ?c ?w) ci (?w, ?w))" "?ce s \<in> ?gm p (snd q)"
        using comp_sound[where p = p] sw ls_channel_sound[OF comp_sound[where p = p] sw]
        unfolding sound_local_spec_def by (metis fst_conv)
      then show ?thesis by (simp add: enter_single)
    qed
    have fr: "\<forall>x. ?\<G> x \<longrightarrow> x \<notin> set ?W \<longrightarrow> ?ce s x = s x"
      by (auto intro: call_enter_frame)
    have "?ce s \<in> ?gm p (cmb (rl ?E) (full_view rg ?xs (\<lambda>x. if x \<in> set ?W then rg x ?E else ?e x)))"
      by (rule mix[OF s0 sE fr])
    moreover have "cmb (rl ?E) (full_view rg ?xs (\<lambda>x. if x \<in> set ?W then rg x ?E else ?e x))
        \<le> cmb (rl ?E) (full_view rg ?xs ?e)"
    proof (intro cmb_mono order_refl full_view_mono[OF rg_mono])
      fix x
      show "(if x \<in> set ?W then rg x ?E else ?e x) \<le> ?e x"
        using le[of x] by (cases "x \<in> set ?W") simp_all
    qed
    ultimately have "?ce s \<in> ?gm p (cmb (rl ?E) (full_view rg ?xs ?e))"
      using gm_mono by blast
    moreover have "s \<in> ?gm p (cmb (rl ?w) (full_view rg ?xs ?e))"
      using s0 by (simp add: rl_cmb cmb_rl)
    ultimately show ?case by (simp add: alt)
  next
    case (CmbBot p g) show ?case by (simp add: cmb_bot)
  next
    case (Init p)
    let ?xs = "declared_global_vars p"
    let ?ie = "dg_pipeline.init_env init_st buffer_key global_of (\<lambda>\<G> d. Bot)
      (\<lambda>\<G> p. map (\<lambda>x. (x, rg x (Lifted init_st))) (declared_global_vars p)) (declared_global p) p"
    have ie: "rg x (Lifted init_st) \<le> ?ie x" if x: "x \<in> set ?xs" for x
    proof -
      have "rg x (Lifted init_st)
          \<le> (\<Squnion>(m, d)\<leftarrow>filter (\<lambda>(m, d). m = x) (map (\<lambda>y. (y, rg y (Lifted init_st))) ys). d)"
        if "x \<in> set ys" for ys
        using that by (induction ys) (auto intro: le_supI1 le_supI2)
      then show ?thesis using x by (simp add: dg_pipeline.init_env_def le_supI2)
    qed
    have "full_view rg ?xs (\<lambda>x. rg x (Lifted init_st)) \<le> full_view rg ?xs ?ie"
      unfolding full_view_def
    proof (rule view_of_le)
      fix x assume x: "x \<in> set ?xs"
      show "rg x (rg x (Lifted init_st)) \<le> view_of rg ?xs ?ie bot"
        using rg_mono[OF ie[OF x], of x] view_of_ge_mem[OF x, of rg ?ie bot] by (rule order_trans)
    qed simp
    then show ?case
      using init_view[where p = p] gm_mono[OF cmb_mono[OF order_refl], where p = p] by blast
  next
    case (EmptyRd p s) show ?case by (rule empty_rd)
  next
    case EmptyV show ?case by (rule empty\<^sub>V_sound)
  next
    case (SeedNe v ctx) show ?case by (rule seed_ne)
  next
    case (SeedNeGlobal v ctx n) show ?case by (rule seed_ne_global)
  next
    case (ClProved c d s) then show ?case by (rule classify_proved)
  next
    case (ClRefuted c d s) then show ?case by (rule classify_refuted)
  next
    case BotState show ?case by (rule bot_state_empty)
  next
    case (InitSound p) show ?case by (rule init_sound)
  qed
qed

subsection \<open>An executable analysis as the pipeline's component\<close>

text \<open>
  What an executable non-relational analysis owes, stated over its own
  transfers: the abstract transfer it implements is sound, its executable
  mirror represents that transfer, and its routing, solver, classifier and
  entry state satisfy the pipeline's contracts on the represented abstract store.
  Its component is \<^const>\<open>exec_local_spec\<close>, so the generic pipeline runs
  exactly its local specification, and every theorem above holds of it.

  \<open>route_abs\<close> is the same routing decision taken on the abstract carrier, kept
  for the analyses that state it; the pipeline's soundness does not use it.
\<close>

locale dg_analysis_exec = certified_solver solve solve_dom solve_c
  for tf_st :: "(vname \<Rightarrow> bool) \<Rightarrow> edge_action
                  \<Rightarrow> 'a::numeric_domain default_st \<Rightarrow> 'a default_st"
    and enter_st :: "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st"
    and init_st :: "'a default_st"
    and buffer_key :: 'k
    and global_of :: "unit \<Rightarrow> 'k"
    and seed :: "pp \<Rightarrow> 'c \<Rightarrow> 'k"
    and route :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a default_st lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and root_ctx :: 'c
    and solve :: "(pp \<times> 'c, 'k, ('a default_st lifted, 'a default_st lifted) dg_state) eqsT
                  \<Rightarrow> pp \<times> 'c
                  \<Rightarrow> (pp \<times> 'c) set
                       \<times> (pp \<times> 'c + 'k \<Rightarrow> ('a default_st lifted, 'a default_st lifted) dg_state)"
    and solve_dom :: "(pp \<times> 'c, 'k, ('a default_st lifted, 'a default_st lifted) dg_state) eqsT
                      \<Rightarrow> pp \<times> 'c \<Rightarrow> bool"
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
    and route_abs :: "(vname \<Rightarrow> bool) \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> 'a abs_state lifted \<Rightarrow> call_action \<Rightarrow> 'c"
    and solve_c :: "(pp \<times> 'c, 'k,
                       ('a default_st lifted, 'a default_st lifted) dg_state) eqsT
                    \<Rightarrow> pp \<times> 'c
                    \<Rightarrow> ((pp \<times> 'c) set
                          \<times> (pp \<times> 'c + 'k
                               \<Rightarrow> ('a default_st lifted, 'a default_st lifted) dg_state)) option" +
  assumes tf_sound: "\<And>\<G>. sound_nonrelational_transfer \<G> sk asn spc br bd rt (en \<G>) ev"
    and tf_commute:
      "\<And>\<G> a s. live_default_st \<G> s
         \<Longrightarrow> \<rho>\<^bsub>\<G>\<^esub> (tf_st \<G> a s)
               = local_spec_step sk asn spc br bd rt ev a (\<rho>\<^bsub>\<G>\<^esub> s)"
    and enter_commute:
      "\<And>\<G> ci s. \<rho>\<^bsub>\<G>\<^esub> (enter_st \<G> ci s)
                    = en \<G> ci (\<rho>\<^bsub>\<G>\<^esub> s)"
    and route_agree:
      "\<And>\<G> u ctx d ca. route \<G> u ctx d ca
         = route_abs \<G> u ctx (\<rho>\<^bsub>\<G>\<^esub> d) ca"
    and exec_seed_ne_buffer_key: "\<And>v ctx. seed v ctx \<noteq> buffer_key"
    and exec_classify_proved:
      "\<And>c d s. classify c d = Check_Proved \<Longrightarrow> s \<in> \<gamma> d \<Longrightarrow> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and exec_classify_refuted:
      "\<And>c d s. classify c d = Check_Refuted \<Longrightarrow> s \<in> \<gamma> d
         \<Longrightarrow> \<not> truthy (\<lbrakk>c\<rbrakk>\<^sub>e s)"
    and bot_state_eq: "bot_state = bot"
    and exec_init_sound: "\<And>\<G>. cinit_stores \<G> \<subseteq> default_st_gamma \<G> init_st"
    and exec_own_key: "\<And>n. global_of n = buffer_key"

sublocale dg_analysis_exec \<subseteq> dg_analysis
    "\<lambda>\<G> p. exec_local_spec \<G> (default_st_is_bot_for (declared_global_vars p))
             (tf_st \<G>) (enter_st \<G>)"
    "\<lambda>p. default_st_is_bot_for (declared_global_vars p)"
    default_st_to_fun init_st buffer_key global_of seed route root_ctx
      solve solve_dom bot_state classify
    gamma_state is_empty_state solve_c "\<lambda>\<G> c. dg_spec_of c" "\<lambda>\<G> d e. d" "\<lambda>\<G> d. d"
      "\<lambda>\<G> d. Bot" "\<lambda>\<G> p. []" "\<lambda>p ci d e. d"
proof (rule dg_analysis_whole_stateI[OF certified_solver_axioms],
    goal_cases CompSound EnterSingle EmptyExact EmptyVExact SeedNe ClProved ClRefuted BotState
    Init SeedNeGlobal)
  case (CompSound p)
  interpret dom: dg_domain_exec "declared_global p"
      "default_st_is_bot_for (declared_global_vars p)" "tf_st (declared_global p)"
      "enter_st (declared_global p)" sk asn spc br bd rt "en (declared_global p)" ev
    by unfold_locales
       (rule tf_commute, assumption,
        rule enter_commute,
        rule default_st_is_bot_for_iff[OF declared_global_iff])
  show ?case
    by (rule dom.exec_local_spec_sound[OF tf_sound, unfolded gamma_lift_default_st_gamma_to_fun])
next
  case (EnterSingle p ci d)
  then show ?case by (simp add: dg_pipeline.comp_entry_def)
next
  case (EmptyExact p s)
  then show ?case by (rule default_st_is_bot_for_iff[OF declared_global_iff])
next
  case EmptyVExact show ?case
    by (rule sound_emptinessI) (erule is_empty_state_gamma_state_empty)
next
  case (SeedNe v ctx) then show ?case by (rule exec_seed_ne_buffer_key)
next
  case (ClProved c d s) then show ?case by (rule exec_classify_proved)
next
  case (ClRefuted c d s) then show ?case by (rule exec_classify_refuted)
next
  case BotState then show ?case
    by (simp add: bot_state_eq is_empty_state_iff_gamma_state_empty[symmetric])
next
  case (Init p) then show ?case
    using exec_init_sound[of "declared_global p"] by (simp add: default_st_gamma_def)
next
  case (SeedNeGlobal v ctx n) show ?case
    unfolding exec_own_key by (rule exec_seed_ne_buffer_key)
qed

text \<open>
  The component's soundness at the carrier's own concretization, which is
  what a caller composing components on the carrier needs.
\<close>

lemma (in dg_analysis_exec) exec_comp_sound:
  "sound_local_spec (declared_global p) (gamma_lift (default_st_gamma (declared_global p)))
     (exec_local_spec (declared_global p) (default_st_is_bot_for (declared_global_vars p))
        (tf_st (declared_global p)) (enter_st (declared_global p)))"
  unfolding gamma_lift_default_st_gamma_to_fun by (rule comp_sound)

text \<open>
  The state a call enters its callee with, at the executable component: the entry
  transfer, lifted over reachability.
\<close>

lemma (in dg_analysis_exec) comp_entry_exec:
  "dg_pipeline.comp_entry
     (\<lambda>\<G> p. exec_local_spec \<G> (default_st_is_bot_for (declared_global_vars p))
        (tf_st \<G>) (enter_st \<G>))
     \<G> p ci d
   = transfer_lift (default_st_is_bot_for (declared_global_vars p)) (enter_st \<G> ci) d"
  by (simp add: dg_pipeline.comp_entry_def)

text \<open>
  The same against the solved global, the shape \<^const>\<open>dg_pipeline.ctx_succ\<close>
  reads, so a caller can fold an executable entry back into it.
\<close>

lemma (in dg_analysis_exec) entry_of_exec:
  "entry_of \<G> p ci d (sol_global \<G> p)
   = transfer_lift (default_st_is_bot_for (declared_global_vars p)) (enter_st \<G> ci) d"
  by (simp add: dg_pipeline.entry_of_def dg_pipeline.entry_alt_def comp_entry_exec)

end
