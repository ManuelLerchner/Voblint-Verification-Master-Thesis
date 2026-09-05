theory Run_Analysis_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Exec.Routed_Domain_Exec"
    "Voblint_Framework.Routed_Context_Unit"
    "Voblint_Framework.Routed_Analysis_Sound"
    "Voblint_Solver.TD_Solver_Bridge"
    Source_Activation_Sound
begin

section \<open>Bundled end-to-end source soundness for D/G analyses\<close>

text \<open>
  One reusable theorem replaces the per-example chain
  \<open>solve_c success -> solve_dom -> partial_post_solution -> executable-to-abstract
  transport -> collecting soundness -> source-level soundness\<close>.

  \<^bold>\<open>This theorem bundles partial correctness and source-level soundness.  It does
  not establish that \<open>solve_c\<close> returns.\<close>  The caller supplies \<open>solve_c ... \<noteq> None\<close>
  (typically a code-generated \<^theory_text>\<open>by eval\<close> fact), and the bundle turns that single
  success into a source-level guarantee.  Termination of the vendored solver is not
  a theorem of this development.

  The result is \<^emph>\<open>query-parametric\<close>: the reached program point \<open>v\<close> is existential and
  matched to where the run actually is, and the D/G collecting endpoint
  \<open>collect_sound\<close> below holds at every covered point, so no premature
  specialisation to \<open>cfg_exit\<close> is needed.

  \<^bold>\<open>Why the solver step stays a one-line adapter.\<close>  The step \<open>solve_c success ->
  part_post_solution\<close> lives in the vendored locale \<^locale>\<open>TD_side_upd_rule\<close> as
  \<^verbatim>\<open>part_post_solution_of_solve_c\<close>, whose unknown type is rigid inside that locale
  and cannot be tied to the D/G unknown type \<open>pp \<times> unit\<close>.  So the executable-to-abstract
  transport lives in the \<^emph>\<open>global\<close> theorem below, and the caller feeds it the executable
  \<^const>\<open>part_post_solution\<close> obtained from a single \<^verbatim>\<open>by eval\<close> success via that adapter.
\<close>


section \<open>Registered executable D/G analyses\<close>

subsection \<open>The context-insensitive equation system\<close>

text \<open>
  A context-insensitive analysis is the routed protocol at the unit context:
  every call routes to \<^const>\<open>route_unit\<close>, the seed key is \<^const>\<open>Activation_Seed\<close>,
  the analysis global is \<^const>\<open>Analysis_Global\<close>, and targets resolve statically.
  \<^const>\<open>unit_routed_eqs\<close> (\<^theory>\<open>Voblint_Exec.Exec_DG_Generator\<close>) is that generator
  at an arbitrary specification. There is no second call protocol; both registration
  locales below name this one constant at their own specification and the compiled
  graph, and an executable run names it through its interpretation.
\<close>



subsection \<open>Registration locale for diagonal executable D/G analyses\<close>

text \<open>
  A registered diagonal analysis supplies only \<^emph>\<open>essential mathematics\<close> --- a sound
  abstract transfer \<^term>\<open>tf\<close> and its executable mirror \<^term>\<open>tf_st\<close> with the primitive
  commutation --- plus the vendored solver's \<^theory_text>\<open>part_post_solution_of_solve_c\<close> adapter
  for its chosen update rule (\<^term>\<open>solve\<close> / \<^term>\<open>solve_c\<close>).  It obtains a reusable
  executable source-soundness theorem \<^theory_text>\<open>run_source_sound\<close> and a semantic concretization
  accessor \<^theory_text>\<open>gamma\<close>, with no \<^const>\<open>dg_spec_step\<close> trees, \<open>fun_of_dg_st_for\<close>,
  \<^const>\<open>part_post_solution\<close>, or transport lemmas exposed to callers.
\<close>

locale ownership_split_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and sk :: "'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and solve :: "(pp \<times> unit, (unit, unit) routed_gk,
                    ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)"
    and solve_c :: "(pp \<times> unit, (unit, unit) routed_gk,
                      ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)) option"
  assumes tf_sound:
      "sound_transfer_for gs sk asn sp br bd rt en ev"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        live_resolved_st_q gs s \<Longrightarrow>
        fun_of_exec_dg_st_for gs (tf_st a s) =
        local_spec_step sk asn sp br bd rt ev a (fun_of_exec_dg_st_for gs s)"
    and enter_commute[simp]:
      "\<And>ci s.
        fun_of_exec_dg_st_for gs (enter_st ci s) =
        en ci (fun_of_exec_dg_st_for gs s)"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

text \<open>
  \<open>gamma\<close> is the caller-facing concretization at \<open>v\<close>: convert the executable
  post-solution \<open>sigma_st\<close> to its semantic function via \<open>fun_of_dg_st_for\<close>, then
  read off the set of stores the DG framework's own hook concretization assigns it,
  instantiated at this locale's context-insensitive \<open>gamma_ownership_split\<close>. This is the
  accessor \<open>run_source_sound\<close> states its soundness guarantee in terms of, so
  no \<open>dg_spec_step\<close>/\<open>fun_of_dg_st_for\<close>/\<open>part_post_solution\<close> plumbing reaches the
  caller.
\<close>
text \<open>
  \<open>gamma_ownership_split_exec\<close> is the executable-carrier sibling of \<open>gamma_ownership_split gs\<close>, reading
  its two arguments back through \<open>fun_of_exec_dg_st_for\<close> first --- the diagonal
  analogue of \<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>'s \<open>gamma_exec\<close>.
  \<open>run_source_sound\<close>/\<open>collect_sound\<close> read the solved system at this carrier
  directly, so no solved system is ever transported to the abstract one.
\<close>

definition gamma_ownership_split_exec :: "'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> store set" where
  "gamma_ownership_split_exec d g = gamma_ownership_split gs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"

text \<open>
  Each obligation is the abstract one under the readback: the observation
  lemmas expose what the executable tree computes, the readback commutations
  turn each ownership operation into its function-valued counterpart, and the
  locale's two commute assumptions replace \<open>tf_st\<close>/\<open>enter_st\<close> by \<open>tf\<close>. What
  remains is exactly the transfer contract.
\<close>

theorem sound_dg_spec_core_st: "sound_dg_spec_core (ownership_split_dg_spec_st_for gs tf_st enter_st) gamma_ownership_split_exec gs"
proof -
  interpret tfs: sound_transfer_for gs sk asn sp br bd rt en ev by (rule tf_sound)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d' g g')
    show ?case
      unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
      by (rule gamma_ownership_split_mono)
         (rule fun_of_resolved_st_q_for_mono[OF 1(1)],
          rule fun_of_resolved_st_q_for_mono[OF 1(2)])
  next
    case (2 a \<tau> src gk)
    show ?case
      unfolding dg_spec_step_ownership_split_st_for ownership_split_transfer_st_def gamma_ownership_split_exec_def
        dg_spec_edge_tree_def fun_of_exec_dg_st_for_def gamma_ownership_split_def
      apply (simp add: fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for)
      apply (cases "live_resolved_st_q gs (combine_resolved_st_q (locals (\<tau> src)) (globs (\<tau> (Inr gk))))")
       apply (simp add: tf_commute[unfolded fun_of_exec_dg_st_for_def]
              tfs.step_sound_for)
      apply (simp add: live_resolved_st_q_def is_empty_state_gamma_state_empty edge_collect_empty_set)
      done
  next
    case (3 s dc \<tau> gk t de ci)
    then show ?case
      unfolding dg_spec_combine_transfer_ownership_split_dg_spec_st_for
        ownership_split_combine_transfer_st_def gamma_ownership_split_exec_def combine_collect_def
        fun_of_exec_dg_st_for_def gamma_ownership_split_def
      by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
            mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc
            fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for
            fun_of_resolved_st_q_for_def[symmetric]
            reserved[unfolded reserved_ret_var_def]
            gamma_ownership_split_combine_assign[OF reserved, unfolded gamma_ownership_split_def])
  qed
qed

text \<open>
  A context-insensitive ownership-split analysis is the routed protocol at the
  unit context, exactly as the Base-style registration below is: same call
  operation, single context. \<open>routed_eqs\<close> is that generator at this
  specification.
\<close>

abbreviation routed_eqs ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT"
where
  "routed_eqs Pi ps \<equiv> unit_routed_eqs (ownership_split_dg_spec_st_for gs tf_st enter_st)
                        (compile_prog Pi ps)"

definition gamma ::
  "(pp \<times> unit) set
     \<Rightarrow> (pp \<times> unit + (unit, unit) routed_gk
          \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state)
     \<Rightarrow> pp \<Rightarrow> store set"
where
  "gamma vars sigma_st v =
     gamma_ownership_split_exec (solved_local_reader vars sigma_st (Inl (v, ())))
       (globs (sigma_st (Inr (Analysis_Global ()))))"

text \<open>
  The carrier's bottom really is empty here, and \<^const>\<open>reserved_ret_var\<close> is
  what makes it so: \<^const>\<open>ret_var\<close> is local, so a merged state whose local half
  is \<^const>\<open>bot\<close> assigns it \<^const>\<open>bot\<close> whatever the global half holds.
\<close>

lemma gamma_ownership_split_exec_bot [simp]:
  "gamma_ownership_split_exec bot g = {}"
  using reserved
  unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
    gamma_ownership_split_def reserved_ret_var_def
  by (auto simp: gamma_state_def combine_env_def)

text \<open>
  Where an ownership-split analysis differs from a Base-style one: its
  concretization reads the global channel, so covering the entered store against
  the \<^emph>\<open>solved\<close> global needs the entry's own publication to be inside that
  solution. It is, and the argument is one chain of directional bounds: the
  entry program's publications survive the fold over alternatives
  (\<open>routed_callee_call_tree_sides_ge_prefix\<close>), one resolved target survives the fold over
  targets (\<open>routed_call_tree_sides_ge_at\<close>), one call site survives the
  node's own equation (\<open>sides_comb_le_routed_node_rhs\<close>), and a
  post-solution contains every equation's publications. The continuation node is
  the one carrying that equation, which is why \<^const>\<open>vars_cover\<close>'s combine
  component is what makes it a covered unknown.
\<close>

lemma entry_publication_le_solution:
  fixes Pi :: proc_table and ps and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and ce: "(u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls (compile_prog Pi ps)"
    and runs: "enter_runs (enter\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st)
                   (call_info_of (CallEdge dst pars args) p))
                 (mk_dg_man (locals (snd (solve eqs x) (Inl (u, ())))) (\<lambda>_. Analysis_Global ()))
                 (snd (solve eqs x)) pairs pub"
  shows "pub (Inr (Analysis_Global ()))
           \<le> snd (solve eqs x) (Inr (Analysis_Global ()))"
proof -
  let ?g = "compile_prog Pi ps"
  let ?sigma = "snd (solve eqs x)"
  let ?ca = "CallEdge dst pars args"
  let ?S = "ownership_split_dg_spec_st_for gs tf_st enter_st"
  have finC: "finite (calls ?g)" by (simp add: compile_prog_finite)
  have res: "p \<in> set (static_resolve ?g cont u ?ca (locals (?sigma (Inl (u, ())))))"
    using ce by (simp add: static_resolve_iff finC)
  have site: "(u, ?ca) \<in> set (call_site_list ?g cont)"
    using ce by (auto simp: set_call_site_list[OF finC])
  have covcont: "(cont, ()) \<in> fst (solve eqs x)"
    using vars_cover_combineD[OF cover ce] .
  have pp: "part_post_solution eqs x ?sigma (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  have sides_sol: "sides_of_rhs (eqs (cont, ())) ?sigma \<le> ?sigma"
    using pp covcont
    unfolding part_post_solution_iff_tree_covered_at by (blast dest: tree_covered_at_sides)
  have "pub (Inr (Analysis_Global ()))
          \<le> sides_of_rhs (routed_callee_call_tree ?S (Analysis_Global ()) Activation_Seed
                route_unit (\<lambda>d. d = bot) () ?ca u
                (locals (?sigma (Inl (u, ())))) p) ?sigma (Inr (Analysis_Global ()))"
    using routed_callee_call_tree_sides_ge_prefix[OF runs] by (simp add: le_fun_def)
  also have "\<dots> \<le> sides_of_rhs (routed_call_tree ?S (Analysis_Global ()) Activation_Seed
                     (static_resolve ?g) (\<lambda>d. d = bot) route_unit () ?ca u cont)
                    ?sigma (Inr (Analysis_Global ()))"
    by (rule routed_call_tree_sides_ge_at
          [where resolve = "static_resolve ?g" and v = cont and cc = u
             and ctx = "()" and \<sigma> = "?sigma" and ca = ?ca, OF res])
  also have "\<dots> \<le> sides_of_rhs (eqs (cont, ())) ?sigma (Inr (Analysis_Global ()))"
    unfolding eqs_def unit_routed_eqs_def
    by (rule sides_comb_le_routed_node_rhs[OF site,
          where gkey = "\<lambda>_. Analysis_Global ()"])
  also have "\<dots> \<le> ?sigma (Inr (Analysis_Global ()))"
    using sides_sol by (simp add: le_fun_def)
  finally show ?thesis .
qed

text \<open>
  What a solved \<open>routed_eqs\<close> run is, as a routed context. The wrapper runs the
  pure entry against the reconstructed whole state, so the call has exactly one
  alternative; both of its halves are described by what the wrapper published at
  the shared slot, and \<open>entry_publication_le_solution\<close> places that publication
  inside the solved global the cover is taken against.
\<close>

lemma unit_routed_context_of_solve:
  fixes Pi :: proc_table and ps and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
  shows "unit_routed_context (ownership_split_dg_spec_st_for gs tf_st enter_st)
           gamma_ownership_split_exec gs (compile_prog Pi ps)
           (Analysis_Global ()) bot0 s0d s0g (snd (solve eqs x)) (fst (solve eqs x)) x
           (solved_local_reader (fst (solve eqs x)) (snd (solve eqs x)))
           Activation_Seed (\<lambda>d. d = bot)
           (\<lambda>d. gamma_ownership_split_exec d
                  (globs (snd (solve eqs x) (Inr (Analysis_Global ())))))"
proof -
  interpret base: sound_dg_spec_core "ownership_split_dg_spec_st_for gs tf_st enter_st"
      gamma_ownership_split_exec gs
    by (rule sound_dg_spec_core_st)
  interpret tfs: sound_transfer_for gs sk asn sp br bd rt en ev by (rule tf_sound)
  note mono = sound_dg_spec_core.gammaDG_mono[OF sound_dg_spec_core_st]
  show ?thesis
proof (unfold_locales, goal_cases Mono Step Comb FinE PP SgCov SgUncov Fwd FinC SeedKey
    IsBotBot IsBotSound EnterComplete CallFwd CombFwd EnterAgree)
  case (Mono d d' g g') then show ?case by (rule base.gammaDG_mono)
next
  case (Step a \<tau> src gk) show ?case by (rule base.step_sound)
next
  case (Comb s dc \<tau> gk t de ci) then show ?case by (rule base.combine_sound)
next
  case FinE show ?case by (rule finI)
next
  case PP show ?case using solver_pps[OF SOLVE] unfolding eqs_def unit_routed_eqs_def .
next
  case (SgCov v c) then show ?case by simp
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c) then show ?case using cover by (cases c) auto
next
  case FinC show ?case by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by simp
next
  case (EnterComplete u ctx dst pars args p cont s)
  let ?sigma = "snd (solve eqs x)"
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (?sigma (Inl (u, ctx)))"
  let ?dw = "combine_resolved_st_q ?d (globs (?sigma (Inr (Analysis_Global ()))))"
    let ?inner = "[(?dw, enter_st ?ci ?dw)]"
    let ?pairs = "map (\<lambda>(cont, entry). (restrict_local_resolved_q cont,
                                        restrict_local_resolved_q entry)) ?inner"
    let ?pub = "(bot :: pp \<times> unit + (unit, unit) routed_gk
                          \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state)
                  (Inr (Analysis_Global ())
                     := DG bot (ownership_split_enter_sides restrict_global_resolved_q ?inner))"
    have runs: "enter_runs
        (enter\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st) ?ci)
        (mk_dg_man ?d (\<lambda>_. Analysis_Global ())) ?sigma ?pairs (bot \<squnion> ?pub)"
      unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
      by (rule enter_runs_ownership_split_enter_transfer_gen)
         (rule enter_runs_local_enter_transfer_mk_dg_man)
    have deps: "enter_deps
        (enter\<^sup># (ownership_split_dg_spec_st_for gs tf_st enter_st) ?ci)
        (mk_dg_man ?d (\<lambda>_. Analysis_Global ())) ?sigma ?pairs
        ({Inr (Analysis_Global ())} \<union> {})"
      unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
      by (rule enter_deps_ownership_split_enter_transfer_gen)
         (rule enter_deps_local_enter_transfer_mk_dg_man)
    have whole: "s \<in> \<lbrakk>combine_env gs (fun_of_resolved_st_q_for gs ?d)
                        (fun_of_resolved_st_q_for gs
                           (globs (?sigma (Inr (Analysis_Global ())))))\<rbrakk>"
      using EnterComplete(3) unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
        gamma_ownership_split_def .
    have caller: "s \<in> gamma_ownership_split_exec (restrict_local_resolved_q ?dw)
        (globs (?sigma (Inr (Analysis_Global ()))))"
      using whole
      unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
        gamma_ownership_split_def
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
          combine_env_for_eq_restrictions)
    have entered: "call_enter gs (CallEdge dst pars args) s \<in> gamma_ownership_split_exec
        (restrict_local_resolved_q (enter_st ?ci ?dw))
        (restrict_global_resolved_q (enter_st ?ci ?dw))"
      unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
        gamma_ownership_split_def
      using tfs.tf_sound_enter_entry_for[OF whole, where ci = ?ci]
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
          fun_of_resolved_st_q_for_restrict_global_for call_enter_def
          enter_binding_concrete
          enter_commute[unfolded fun_of_exec_dg_st_for_def])
    have cov: "entry_pairs_cover
        (\<lambda>e. gamma_ownership_split_exec e
               (globs (?sigma (Inr (Analysis_Global ()))))) s
        (call_enter gs (CallEdge dst pars args) s) ?pairs"
    proof (rule entry_pairs_coverI)
      show "(restrict_local_resolved_q ?dw, restrict_local_resolved_q (enter_st ?ci ?dw))
              \<in> set ?pairs" by simp
      show "s \<in> gamma_ownership_split_exec (restrict_local_resolved_q ?dw)
              (globs (?sigma (Inr (Analysis_Global ()))))"
        by (rule caller)
      have ctx0: "ctx = ()" by simp
      have esides: "restrict_global_resolved_q (enter_st ?ci ?dw)
              \<le> globs (?sigma (Inr (Analysis_Global ())))"
        using entry_publication_le_solution
                [OF SOLVE[unfolded eqs_def] cover[unfolded eqs_def]
                    EnterComplete(2) runs[unfolded ctx0 eqs_def]]
              ownership_split_enter_sides_entry_le
                [where entry = "enter_st ?ci ?dw" and pairs = ?inner
                   and rg = restrict_global_resolved_q]
        by (simp add: eqs_def less_eq_dg_state_def)
      show "call_enter gs (CallEdge dst pars args) s
              \<in> gamma_ownership_split_exec (restrict_local_resolved_q (enter_st ?ci ?dw))
                  (globs (?sigma (Inr (Analysis_Global ()))))"
        using entered mono[OF order_refl esides] by auto
    qed
    show ?case using runs deps cov by blast
  next
  case (CallFwd u ctx dst pars args p cont)
  then show ?case using cover by (cases "route_unit u ctx
      (locals (snd (solve eqs x) (Inl (u, ctx)))) (CallEdge dst pars args)") auto
next
  case (CombFwd cl c1 dst pars args p cont)
  then show ?case using cover by (cases c1) auto
next
  case (EnterAgree cl s es dst pars args p cont)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using EnterAgree(1) unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' EnterAgree(2)] by simp
  then show ?case using es_eq by simp
qed
qed

text \<open>
  The per-node collecting endpoint. \<^const>\<open>ltr_collect\<close> is the union over
  contexts of \<^const>\<open>activation_collect\<close> (\<open>ltr_collect_eq_Union_activation\<close>),
  and at the unit context that union has one member, so the routed cap
  \<open>activation_collect_dg_sound\<close> bounds it directly.
\<close>

theorem collect_sound:
  fixes Pi :: proc_table and ps and v :: pp and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_ownership_split_exec s0d s0g"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v
           \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
proof -
  interpret R: unit_routed_context "ownership_split_dg_spec_st_for gs tf_st enter_st"
      gamma_ownership_split_exec gs "compile_prog Pi ps"
      "Analysis_Global ()" bot0 s0d s0g "snd (solve eqs x)" "fst (solve eqs x)" x
      "solved_local_reader (fst (solve eqs x)) (snd (solve eqs x))"
      Activation_Seed "\<lambda>d. d = bot"
      "\<lambda>d. gamma_ownership_split_exec d (globs (snd (solve eqs x) (Inr (Analysis_Global ()))))"
    unfolding eqs_def
    by (rule unit_routed_context_of_solve[OF SOLVE[unfolded eqs_def]
          cover[unfolded eqs_def] finI])
  have "ltr_collect gs (compile_prog Pi ps) S0 v
          = (\<Union>c. activation_collect gs enterc_unit () (compile_prog Pi ps) S0 v c)"
    by (rule ltr_collect_eq_Union_activation)
  also have "\<dots> \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
  proof (rule UN_least)
    fix c :: unit
    show "activation_collect gs enterc_unit () (compile_prog Pi ps) S0 v c
            \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
      unfolding gamma_def
      using R.routed.activation_collect_dg_sound[OF vars_cover_entryD[OF cover] sound0]
      by (cases c) simp
  qed
  finally show ?thesis .
qed

text \<open>
  The source-level endpoint: one concrete run of the source program lands at a
  simulated program point whose solved value describes the store it reached.
  \<open>collect_sound\<close> supplies the bound; \<open>source_reaches_ltr_collect\<close> supplies the
  point.
\<close>

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_ownership_split_exec s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
proof -
  from source_reaches_ltr_collect[OF wf s0mem run]
  obtain v stk where m: "csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect gs (compile_prog Pi ps) S0 v" by blast
  have "ltr_collect gs (compile_prog Pi ps) S0 v
          \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
    unfolding eqs_def
    by (rule collect_sound[OF SOLVE[unfolded eqs_def] cover[unfolded eqs_def] finI sound0])
  then show ?thesis using m coll by blast
qed

end


section \<open>Registered executable D/G analyses, lifted Base-style local carrier\<close>


subsection \<open>Registration locale for the lifted Base-style diagonal analysis\<close>

text \<open>
  The canonical executable Base analysis: whole-state \<open>D\<close> lifted for reachability,
  \<open>G\<close> the same type as \<open>D\<close> -- the only shape either registered instance
  (Sign, Parity) actually needs, and the shape \<^locale>\<open>routed_dg_domain_exec\<close>
  (\<^theory>\<open>Voblint_Exec.DG_Local_State_Exec\<close>) already proves sound at the executable
  carrier. A registered domain supplies only its eight transfer operations,
  \<open>tf_st\<close>, \<open>enter_st\<close> and \<open>empty_pred\<close>
  and their three primitive commute facts; this locale's \<open>sublocale\<close> discharges
  \<^locale>\<open>routed_dg_domain_exec\<close>'s three assumptions from exactly those facts,
  and its own \<open>sound_dg_spec_core_st\<close> theorem does the rest: no solved system is ever
  transported from the executable carrier to the abstract one, so this
  registration locale needs no separate post-solution transport theorem.
\<close>

locale local_state_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and sk :: "'a::sound_domain abs_state \<Rightarrow> 'a abs_state"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bd :: "pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and en :: "call_info \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and ev :: "analysis_event \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and empty_pred :: "'a exec_dg_st \<Rightarrow> bool"
    and solve :: "(pp \<times> unit, (unit, unit) routed_gk,
                    ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow>
                         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)"
    and solve_c :: "(pp \<times> unit, (unit, unit) routed_gk,
                      ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow>
                         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)) option"
  assumes tf_sound:
      "sound_transfer_for gs sk asn sp br bd rt en ev"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        live_resolved_st_q gs s \<Longrightarrow>
        fun_of_exec_dg_st_for gs (tf_st a s) =
        local_spec_step sk asn sp br bd rt ev a (fun_of_exec_dg_st_for gs s)"
    and enter_commute[simp]:
      "\<And>ci s.
        fun_of_exec_dg_st_for gs (enter_st ci s) =
        en ci (fun_of_exec_dg_st_for gs s)"
    and is_bot_exact[simp]:
      "\<And>s. empty_pred s = is_empty_state (fun_of_exec_dg_st_for gs s)"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

text \<open>
  The packaging correspondence and its executable-carrier soundness pullback
  are \<open>routed_dg_domain_exec\<close>'s own content (\<open>Voblint_Exec.DG_Local_State_Exec\<close>):
  discharging its three assumptions from this locale's own commute facts gets
  \<open>sound_dg_spec_core_st\<close> for free, so no transport of a solved system between
  carriers is needed here at all -- the solver's own executable post-solution
  already satisfies \<^locale>\<open>unit_routed_context\<close>'s \<open>pp\<close> premise directly.
\<close>

sublocale routed_dg_domain_exec gs empty_pred tf_st enter_st sk asn sp br bd rt en ev
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def], assumption,
      rule enter_commute[unfolded fun_of_exec_dg_st_for_def],
      rule is_bot_exact[unfolded fun_of_exec_dg_st_for_def])

text \<open>
  The unit context needs no per-instance routing or resolution argument:
  \<^const>\<open>route_unit\<close> ignores the local value it is handed, and \<^const>\<open>static_resolve\<close>
  ignores which carrier it reads that value at, so both agreement obligations
  \<^locale>\<open>routed_domain_exec\<close> asks for are free on the same function used on both
  sides. This sublocale is what lets \<open>routed_eqs\<close> below solve the buffered
  generator while still satisfying \<^locale>\<open>dg_ctx_activation_base\<close>'s premise,
  stated over the unbuffered one.\<close>

sublocale unit_buf: routed_domain_exec gs empty_pred tf_st enter_st sk asn sp br bd rt en ev
    "Analysis_Global ()" Activation_Seed route_unit route_unit static_resolve static_resolve
  by unfold_locales (simp_all add: route_unit_def static_resolve_def)

text \<open>
  A context-insensitive analysis is the routed protocol at the unit context: the
  same call operation every other context policy runs, with the single context
  \<^const>\<open>route_unit\<close> always chooses. \<open>routed_eqs\<close> is that generator at this
  specification --- the buffered generator, so a node with several intra
  predecessors or several returning calls publishes its analysis-global
  contribution once per evaluation rather than once per contribution;
  \<open>unit_buf.pp_st\<close> is what lets its computed post-solution still satisfy
  \<^locale>\<open>dg_ctx_activation_base\<close>'s premise below. \<open>gamma\<close> reads the solved table
  back through \<^locale>\<open>routed_dg_domain_exec\<close>'s own executable-carrier
  concretization --- at a covered unknown the table's local half, elsewhere
  \<^const>\<open>bot\<close>.
\<close>

abbreviation routed_eqs ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> 'a exec_dg_st lifted \<Rightarrow> 'a exec_dg_st lifted
     \<Rightarrow> 'a exec_dg_st lifted
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT"
where
  "routed_eqs Pi ps \<equiv> unit_routed_eqs_buffered spec_st (compile_prog Pi ps)"

definition gamma ::
  "(pp \<times> unit) set
     \<Rightarrow> (pp \<times> unit + (unit, unit) routed_gk
          \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)
     \<Rightarrow> pp \<Rightarrow> store set"
where
  "gamma vars sigma_st v =
     gamma_exec (solved_local_reader vars sigma_st (Inl (v, ()))) bot"

text \<open>
  What a solved \<open>routed_eqs\<close> run is, as a routed context: the solver's own
  post-solution is \<^locale>\<open>unit_routed_context\<close>'s \<open>pp\<close> premise verbatim, the
  reader is \<^const>\<open>solved_local_reader\<close>, and the three closure obligations
  (\<open>fwd\<close>, \<open>call_fwd\<close>, \<open>comb_fwd\<close>) are the corresponding components of
  \<^const>\<open>vars_cover\<close>. The specification's own entry contributes the covering
  alternative through \<open>entry_pairs_cover_st\<close>, and its bottom test is
  \<^const>\<open>Bot\<close> --- the one bottom this carrier has.
\<close>

lemma unit_routed_context_of_solve:
  fixes Pi :: proc_table and ps and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
  shows "unit_routed_context spec_st gamma_exec gs (compile_prog Pi ps)
           (Analysis_Global ()) bot0 s0d s0g (snd (solve eqs x)) (fst (solve eqs x)) x
           (solved_local_reader (fst (solve eqs x)) (snd (solve eqs x)))
           Activation_Seed (\<lambda>d. d = bot) (\<lambda>d. gamma_exec d bot)"
proof -
  interpret base: sound_dg_spec_core spec_st gamma_exec gs by (rule sound_dg_spec_core_st[OF tf_sound])
  show ?thesis
proof (unfold_locales, goal_cases Mono Step Comb FinE PP SgCov SgUncov Fwd FinC SeedKey
    IsBotBot IsBotSound EnterComplete CallFwd CombFwd EnterAgree)
  case (Mono d d' g g') then show ?case by (rule base.gammaDG_mono)
next
  case (Step a \<tau> src gk) show ?case by (rule base.step_sound)
next
  case (Comb s dc \<tau> gk t de ci) then show ?case by (rule base.combine_sound)
next
  case FinE show ?case by (rule finI)
next
  case PP
  have pp_buf:
      "part_post_solution
        (routed_node_rhs_buffered intra_predecessor_addr_list
          (\<lambda>_. Analysis_Global ()) route_unit unit_buf.intra_st
          (unit_buf.cmb_st (compile_prog Pi ps))
          (routed_entry_seed_tree Activation_Seed)
          (compile_prog Pi ps) bot0 s0d s0g)
        x (snd (solve eqs x)) (fst (solve eqs x))"
    using solver_pps[OF SOLVE] unfolding eqs_def
    by (simp add: unit_routed_eqs_buffered_def)
  have pp_old:
      "part_post_solution
        (routed_node_rhs intra_predecessor_addr_list
          (\<lambda>_. Analysis_Global ()) route_unit unit_buf.intra_st
          (unit_buf.cmb_st (compile_prog Pi ps))
          (routed_entry_seed_tree Activation_Seed)
          (compile_prog Pi ps) bot0 s0d s0g)
        x (snd (solve eqs x)) (fst (solve eqs x))"
    using unit_buf.pp_st[OF pp_buf] .
  have cmb_eq:
      "unit_buf.cmb_st (compile_prog Pi ps) =
        routed_call_tree spec_st (Analysis_Global ()) Activation_Seed
          (static_resolve (compile_prog Pi ps)) (\<lambda>d. d = bot)"
    by (simp add: route_unit_def static_resolve_def)
  then show ?case using pp_old by simp
next
  case (SgCov v c) then show ?case by (simp add: gamma_exec_def)
next
  case (SgUncov v c) then show ?case by (simp add: gamma_exec_def)
next
  case (Fwd u a v c) then show ?case using cover by (cases c) auto
next
  case FinC show ?case by (simp add: compile_prog_finite)
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by simp
next
  case (EnterComplete u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?caller = "locals (snd (solve eqs x) (Inl (u, ctx)))"
  have cov: "entry_pairs_cover (\<lambda>d. gamma_exec d (globs (snd (solve eqs x)
                 (Inr (Analysis_Global ()))))) s
      (call_enter gs (CallEdge dst pars args) s)
      [(?caller, transfer_lift empty_pred (enter_st ?ci) ?caller)]"
    using entry_pairs_cover_st[OF tf_sound, where ci = ?ci and d = ?caller]
      EnterComplete(3) by (simp add: gamma_exec_def)
  show ?case
    unfolding dgs_enter_local_state_st_for_lifted
    using enter_runs_local_enter_transfer enter_deps_local_enter_transfer cov
    by fastforce
next
  case (CallFwd u ctx dst pars args p cont)
  then show ?case using cover by (cases "route_unit u ctx (locals (snd (solve eqs x)
      (Inl (u, ctx)))) (CallEdge dst pars args)") auto
next
  case (CombFwd cl c1 dst pars args p cont)
  then show ?case using cover by (cases c1) auto
next
  case (EnterAgree cl s es dst pars args p cont)
  obtain dst' pars' args' p' cont' where
      ce': "(cl, CallEdge dst' pars' args', FunctionEntry p', cont')
              \<in> calls (compile_prog Pi ps)"
    and es_eq: "es = call_enter gs (CallEdge dst' pars' args') s"
    using EnterAgree(1) unfolding call_enter_store_def by blast
  have "CallEdge dst' pars' args' = CallEdge dst pars args"
    using compile_prog_calls_source_unique[OF ce' EnterAgree(2)] by simp
  then show ?case using es_eq by simp
qed
qed

text \<open>
  The per-node collecting endpoint. \<^const>\<open>ltr_collect\<close> is the union over
  contexts of \<^const>\<open>activation_collect\<close> (\<open>ltr_collect_eq_Union_activation\<close>),
  and at the unit context that union has one member, so the routed cap
  \<open>activation_collect_dg_sound\<close> bounds it directly.
\<close>

theorem collect_sound:
  fixes Pi :: proc_table and ps and v :: pp
    and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_exec s0d s0g"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v
           \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
proof -
  interpret R: unit_routed_context spec_st gamma_exec gs "compile_prog Pi ps"
      "Analysis_Global ()" bot0 s0d s0g "snd (solve eqs x)" "fst (solve eqs x)" x
      "solved_local_reader (fst (solve eqs x)) (snd (solve eqs x))"
      Activation_Seed "\<lambda>d. d = bot" "\<lambda>d. gamma_exec d bot"
    unfolding eqs_def
    by (rule unit_routed_context_of_solve[OF SOLVE[unfolded eqs_def]
          cover[unfolded eqs_def] finI])
  have "ltr_collect gs (compile_prog Pi ps) S0 v
          = (\<Union>c. activation_collect gs enterc_unit () (compile_prog Pi ps) S0 v c)"
    by (rule ltr_collect_eq_Union_activation)
  also have "\<dots> \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
  proof (rule UN_least)
    fix c :: unit
    show "activation_collect gs enterc_unit () (compile_prog Pi ps) S0 v c
            \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
      unfolding gamma_def
      using R.routed.activation_collect_dg_sound[OF vars_cover_entryD[OF cover] sound0]
      by (cases c) simp
  qed
  finally show ?thesis .
qed

text \<open>
  The source-level endpoint: one concrete run of the source program lands at a
  simulated program point whose solved value describes the store it reached.
  \<open>collect_sound\<close> supplies the cap \<open>source_sound_from_collecting_cap\<close> consumes,
  so this is the same bound read along an actual run.
\<close>

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store
    and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> routed_eqs Pi ps bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_exec s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
proof -
  from source_reaches_ltr_collect[OF wf s0mem run]
  obtain v stk where m: "csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect gs (compile_prog Pi ps) S0 v" by blast
  have "ltr_collect gs (compile_prog Pi ps) S0 v
          \<subseteq> gamma (fst (solve eqs x)) (snd (solve eqs x)) v"
    unfolding eqs_def
    by (rule collect_sound[OF SOLVE[unfolded eqs_def] cover[unfolded eqs_def] finI sound0])
  then show ?thesis using m coll by blast
qed

end


end




