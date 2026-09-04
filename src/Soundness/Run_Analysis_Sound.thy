theory Run_Analysis_Sound
  imports
    "Voblint_Exec.DG_Local_State_Exec"
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Framework.DG_LTR_Sound"
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
  \<^verbatim>\<open>dg_post_solution_collect_sound_ltr_for\<close> holds at every covered
  point, so no premature specialisation to \<open>cfg_exit\<close> is needed.

  \<^bold>\<open>Why the solver step stays a one-line adapter.\<close>  The step \<open>solve_c success ->
  part_post_solution\<close> lives in the vendored locale \<^locale>\<open>TD_side_upd_rule\<close> as
  \<^verbatim>\<open>part_post_solution_of_solve_c\<close>, whose unknown type is rigid inside that locale
  and cannot be tied to the D/G unknown type \<open>pp \<times> unit\<close>.  So the executable-to-abstract
  transport lives in the \<^emph>\<open>global\<close> theorem below, and the caller feeds it the executable
  \<^const>\<open>part_post_solution\<close> obtained from a single \<^verbatim>\<open>by eval\<close> success via that adapter.
\<close>


text \<open>The semantic core, generic in the storage classifier this locale fixes as \<open>gs\<close>:
  \<open>source_reaches_ltr_collect\<close> is already classifier-parametric, and
  \<open>dg_post_solution_collect_sound_ltr_for\<close> is this locale's own endpoint.\<close>

context sound_dg_spec_ltr_for
begin

theorem dg_run_source_sound_abs_for:
  fixes Pi :: proc_table and s0 t :: store
  assumes wf: "wf_compile_input gs Pi ps"
    and pp: "part_post_solution (hooks.hook_gen (compile_prog Pi ps) bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> dg_hook_gamma gammaDG sigma v"
proof -
  from source_reaches_ltr_collect[OF wf s0mem run]
  obtain v stk where m: "csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect gs (compile_prog Pi ps) S0 v" by blast
  have "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> dg_hook_gamma gammaDG sigma v"
    by (rule dg_post_solution_collect_sound_ltr_for[OF pp cover finI finC sound0])
  then show ?thesis using m coll by blast
qed

end


section \<open>Registered executable D/G analyses\<close>

subsection \<open>Executable-to-abstract transport for diagonal unit specifications\<close>

text \<open>
  A registered analysis states its transfer soundness about function-valued
  states, but runs on the solver's association lists. The two are related by
  one readback, and the ownership operations the diagonal specification uses
  commute with it, so the executable specification is sound for the readback
  of the concretization without any transport of a solved system.
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
    and solve :: "(pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)"
    and solve_c :: "(pp \<times> unit, unit, ('a exec_dg_st, 'a exec_dg_st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st, 'a exec_dg_st) dg_state)) option"
  assumes tf_sound:
      "sound_transfer_for gs sk asn sp br bd rt en ev"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        live_resolved_st_q gs s \<Longrightarrow>
        fun_of_exec_dg_st_for gs (tf_st a s) =
        local_spec_step sk asn sp br rt ev a (fun_of_exec_dg_st_for gs s)"
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
  \<open>run_source_sound\<close>/\<open>collect_sound\<close> interpret \<open>sound_dg_spec_ltr_for\<close> directly at
  this carrier, so no solved system is ever transported to the abstract one.
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

theorem sound_dg_spec_st: "sound_dg_spec (ownership_split_dg_spec_st_for gs tf_st enter_st) gamma_ownership_split_exec gs"
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
            man_with_local_def mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc
            fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for
            fun_of_resolved_st_q_for_def[symmetric]
            reserved[unfolded reserved_ret_var_def]
            gamma_ownership_split_combine_assign[OF reserved, unfolded gamma_ownership_split_def])
  qed
qed

text \<open>
  The monovariant generator's own entry obligation. The wrapper runs the pure
  entry against the reconstructed whole state, so the call has exactly one
  alternative; both of its halves are described by what the wrapper published at
  the shared slot, which is why the cover is taken against that publication.
\<close>

lemma sound_dg_spec_ltr_for_st:
  "sound_dg_spec_ltr_for (ownership_split_dg_spec_st_for gs tf_st enter_st)
     gamma_ownership_split_exec gs"
proof (rule sound_dg_spec_ltr_for.intro)
  show "sound_dg_spec (ownership_split_dg_spec_st_for gs tf_st enter_st)
          gamma_ownership_split_exec gs"
    by (rule sound_dg_spec_st)
next
  interpret tfs: sound_transfer_for gs sk asn sp br bd rt en ev by (rule tf_sound)
  note mono = sound_dg_spec.gammaDG_mono[OF sound_dg_spec_st]
  show "sound_dg_spec_ltr_for_axioms (ownership_split_dg_spec_st_for gs tf_st enter_st)
          gamma_ownership_split_exec gs"
    unfolding sound_dg_spec_ltr_for_axioms_def
  proof (intro allI impI)
    fix s and sigma :: "pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state"
      and u dst fs args callee
    assume sin: "s \<in> gamma_ownership_split_exec
                       (locals (sigma (Inl (u, ())))) (globs (sigma (Inr ())))"
    let ?ci = "call_info_of (CallEdge dst fs args) callee"
    let ?d = "locals (sigma (Inl (u, ())))"
    let ?dw = "combine_resolved_st_q ?d (globs (sigma (Inr ())))"
    let ?inner = "[(?dw, enter_st ?ci ?dw)]"
    let ?pairs = "map (\<lambda>(cont, entry). (restrict_local_resolved_q cont,
                                        restrict_local_resolved_q entry)) ?inner"
    let ?pub = "(bot :: pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state)
                  (Inr () := DG bot (ownership_split_enter_sides restrict_global_resolved_q ?inner))"
    have runs: "enter_runs
        (dgs_enter (ownership_split_dg_spec_st_for gs tf_st enter_st) ?ci)
        (mk_dg_man ?d (\<lambda>_. ())) sigma ?pairs (bot \<squnion> ?pub)"
      unfolding dgs_enter_ownership_split_dg_spec_st_for ownership_split_enter_transfer_st_def
      by (rule enter_runs_ownership_split_enter_transfer_gen)
         (use enter_runs_local_enter_transfer
                [of "\<lambda>d. [(d, enter_st ?ci d)]"
                    "man_with_local (mk_dg_man ?d (\<lambda>_. ())) ?dw" sigma]
          in simp)
    have whole: "s \<in> \<lbrakk>combine_env gs (fun_of_resolved_st_q_for gs ?d)
                        (fun_of_resolved_st_q_for gs (globs (sigma (Inr ()))))\<rbrakk>"
      using sin unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
        gamma_ownership_split_def .
    have caller: "s \<in> gamma_ownership_split_exec
        (restrict_local_resolved_q ?dw) (restrict_global_resolved_q ?dw)"
      using whole
      unfolding gamma_ownership_split_exec_def fun_of_exec_dg_st_for_def
        gamma_ownership_split_def
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
          fun_of_resolved_st_q_for_restrict_global_for combine_env_for_eq_restrictions)
    have entered: "call_enter gs (CallEdge dst fs args) s \<in> gamma_ownership_split_exec
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
        (\<lambda>e. gamma_ownership_split_exec e (globs ((bot \<squnion> ?pub) (Inr ())))) s
        (call_enter gs (CallEdge dst fs args) s) ?pairs"
    proof (rule entry_pairs_coverI)
      show "(restrict_local_resolved_q ?dw, restrict_local_resolved_q (enter_st ?ci ?dw))
              \<in> set ?pairs" by simp
      show "s \<in> gamma_ownership_split_exec
              (restrict_local_resolved_q ?dw) (globs ((bot \<squnion> ?pub) (Inr ())))"
        using caller
              mono[OF order_refl
                ownership_split_enter_sides_cont_le[where cont = ?dw and pairs = ?inner
                  and rg = restrict_global_resolved_q]]
        by auto
      show "call_enter gs (CallEdge dst fs args) s \<in> gamma_ownership_split_exec
              (restrict_local_resolved_q (enter_st ?ci ?dw))
              (globs ((bot \<squnion> ?pub) (Inr ())))"
        using entered
              mono[OF order_refl
                ownership_split_enter_sides_entry_le[where entry = "enter_st ?ci ?dw"
                  and pairs = ?inner and rg = restrict_global_resolved_q]]
        by auto
    qed
    show "call_enter gs (CallEdge dst fs args) s
            \<in> gamma_ownership_split_exec
                (locals (traverse_rhs (ltr_enter_tree_of
                    (ownership_split_dg_spec_st_for gs tf_st enter_st) u
                    (CallEdge dst fs args) (FunctionEntry callee)) sigma))
                (globs (sides_of_rhs (ltr_enter_tree_of
                    (ownership_split_dg_spec_st_for gs tf_st enter_st) u
                    (CallEdge dst fs args) (FunctionEntry callee)) sigma (Inr ())))"
      by (rule enter_sound_ltr_of_enter_runs
            [where gammaDG = gamma_ownership_split_exec, OF mono runs cov]) auto
  qed
qed

interpretation sds: sound_dg_spec_ltr_for
  "ownership_split_dg_spec_st_for gs tf_st enter_st" gamma_ownership_split_exec gs
  by (rule sound_dg_spec_ltr_for_st)

definition gamma :: "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = dg_hook_gamma gamma_ownership_split_exec sigma_st v"

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (ownership_split_dg_spec_st_for gs tf_st enter_st) (compile_prog Pi ps) bot0 s0d s0g"  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_ownership_split_exec s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  have pp_hook: "part_post_solution
      (sds.hooks.hook_gen (compile_prog Pi ps) bot0 s0d s0g) x
      (snd (solve eqs x)) (fst (solve eqs x))"
    using pp_st unfolding eqs_def
      sds.part_post_solution_dg_gen_of_iff[OF compile_prog_wf finC] .
  show ?thesis
    unfolding gamma_def
    by (rule sds.dg_run_source_sound_abs_for
          [OF wf pp_hook cover finI finC sound0 s0mem run])
qed

text \<open>
  The per-node collecting analogue of \<open>run_source_sound\<close>, dropping \<open>s0mem\<close>/
  \<open>run\<close>: reusable by any consumer that wants collecting soundness at an
  arbitrary program point for a computed D/G post-solution, without going
  through a concrete source run --- a check-report layer, for instance.
\<close>

theorem collect_sound:
  fixes Pi :: proc_table and ps and v :: pp and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (ownership_split_dg_spec_st_for gs tf_st enter_st) (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_ownership_split_exec s0d s0g"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  have pp_hook: "part_post_solution
      (sds.hooks.hook_gen (compile_prog Pi ps) bot0 s0d s0g) x
      (snd (solve eqs x)) (fst (solve eqs x))"
    using pp_st unfolding eqs_def
      sds.part_post_solution_dg_gen_of_iff[OF compile_prog_wf finC] .
  show ?thesis
    unfolding gamma_def
    by (rule sds.dg_post_solution_collect_sound_ltr_for
          [OF pp_hook cover finI finC sound0])
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
  and its own \<open>sound_dg_spec_st\<close> theorem does the rest: no solved system is ever
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
    and solve :: "(pp \<times> unit, unit,
                    ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)"
    and solve_c :: "(pp \<times> unit, unit, ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)) option"
  assumes tf_sound:
      "sound_transfer_for gs sk asn sp br bd rt en ev"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        live_resolved_st_q gs s \<Longrightarrow>
        fun_of_exec_dg_st_for gs (tf_st a s) =
        local_spec_step sk asn sp br rt ev a (fun_of_exec_dg_st_for gs s)"
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
  \<open>sound_dg_spec_st\<close> for free, so no transport of a solved system between
  carriers is needed here at all -- the solver's own executable post-solution
  already satisfies \<open>sound_dg_spec_ltr_for\<close>'s \<open>pp\<close> premise directly, once
  \<open>sds\<close> below interprets that locale at the executable carrier.
\<close>

sublocale routed_dg_domain_exec gs empty_pred tf_st enter_st sk asn sp br bd rt en ev
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def], assumption,
      rule enter_commute[unfolded fun_of_exec_dg_st_for_def],
      rule is_bot_exact[unfolded fun_of_exec_dg_st_for_def])

text \<open>
  \<open>gamma\<close> reads the executable post-solution back through \<open>gamma_exec\<close> ---
  \<^locale>\<open>routed_dg_domain_exec\<close>'s own executable-carrier concretization ---
  directly, with no transport to the abstract carrier first.
\<close>
definition gamma ::
  "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = dg_hook_gamma gamma_exec sigma_st v"

text \<open>
  The monovariant generator's own entry obligation. The specification's entry is
  pure, so its one alternative is the run, and \<open>entry_pairs_cover_st\<close> is the
  coverage that alternative already carries; the tree publishes nothing, which is
  why \<^const>\<open>bot\<close> is the global the cover is taken against.
\<close>

lemma sound_dg_spec_ltr_for_st:
  "sound_dg_spec_ltr_for (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
     gamma_exec gs"
proof (rule sound_dg_spec_ltr_for.intro)
  show "sound_dg_spec (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
          gamma_exec gs"
    by (rule sound_dg_spec_st[OF tf_sound])
next
  note mono = sound_dg_spec.gammaDG_mono[OF sound_dg_spec_st[OF tf_sound]]
  show "sound_dg_spec_ltr_for_axioms
          (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) gamma_exec gs"
    unfolding sound_dg_spec_ltr_for_axioms_def
  proof (intro allI impI)
    fix s and sigma :: "pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state"
      and u dst fs args callee
    assume sin: "s \<in> gamma_exec (locals (sigma (Inl (u, ())))) (globs (sigma (Inr ())))"
    let ?ci = "call_info_of (CallEdge dst fs args) callee"
    let ?d = "locals (sigma (Inl (u, ())))"
    have runs: "enter_runs
        (dgs_enter (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) ?ci)
        (mk_dg_man ?d (\<lambda>_. ())) sigma [(?d, transfer_lift empty_pred (enter_st ?ci) ?d)] bot"
      unfolding dgs_enter_local_state_st_for_lifted
      using enter_runs_local_enter_transfer
              [of "\<lambda>d. [(d, transfer_lift empty_pred (enter_st ?ci) d)]"
                  "mk_dg_man ?d (\<lambda>_. ())" sigma]
      by simp
    have cov: "entry_pairs_cover (\<lambda>e. gamma_exec e bot) s
        (call_enter gs (CallEdge dst fs args) s)
        [(?d, transfer_lift empty_pred (enter_st ?ci) ?d)]"
      using entry_pairs_cover_st[OF tf_sound, where ci = ?ci and d = ?d]
        sin by (simp add: gamma_exec_def)
    show "call_enter gs (CallEdge dst fs args) s
            \<in> gamma_exec
                (locals (traverse_rhs (ltr_enter_tree_of
                    (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) u
                    (CallEdge dst fs args) (FunctionEntry callee)) sigma))
                (globs (sides_of_rhs (ltr_enter_tree_of
                    (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st) u
                    (CallEdge dst fs args) (FunctionEntry callee)) sigma (Inr ())))"
      by (rule enter_sound_ltr_of_enter_runs
            [where gammaDG = gamma_exec, OF mono runs cov]) (auto simp: bot_fun_def)
  qed
qed

interpretation sds: sound_dg_spec_ltr_for
  "local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st" gamma_exec gs
  by (rule sound_dg_spec_ltr_for_st)

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store
    and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> dg_gen_of (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
                   (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_exec s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  have pp_hook: "part_post_solution
      (sds.hooks.hook_gen (compile_prog Pi ps) bot0 s0d s0g) x
      (snd (solve eqs x)) (fst (solve eqs x))"
    using pp_st unfolding eqs_def
      sds.part_post_solution_dg_gen_of_iff[OF compile_prog_wf finC] .
  show ?thesis
    unfolding gamma_def
    by (rule sds.dg_run_source_sound_abs_for
          [OF wf pp_hook cover finI finC sound0 s0mem run])
qed

text \<open>
  The per-node collecting analogue of \<open>run_source_sound\<close>, dropping \<open>s0mem\<close>/\<open>run\<close>:
  reusable by any consumer that wants collecting soundness at an arbitrary program
  point for a computed lifted D/G post-solution, without going through a concrete
  source run.
\<close>

theorem collect_sound:
  fixes Pi :: proc_table and ps and v :: pp
    and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> dg_gen_of (local_state_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
                   (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_exec s0d s0g"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  have pp_hook: "part_post_solution
      (sds.hooks.hook_gen (compile_prog Pi ps) bot0 s0d s0g) x
      (snd (solve eqs x)) (fst (solve eqs x))"
    using pp_st unfolding eqs_def
      sds.part_post_solution_dg_gen_of_iff[OF compile_prog_wf finC] .
  show ?thesis
    unfolding gamma_def
    by (rule sds.dg_post_solution_collect_sound_ltr_for
          [OF pp_hook cover finI finC sound0])
qed

end


end




