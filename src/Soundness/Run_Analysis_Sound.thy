theory Run_Analysis_Sound
  imports
    "Voblint_Exec.DG_Base_Exec"
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Solver.TD_Solver_Menu"
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

locale unit_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and tf :: "'a::sound_domain domain_transfer"
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
      "sound_transfer_for gs tf"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        fun_of_exec_dg_st_for gs (tf_st a s) =
        apply_tf tf a (fun_of_exec_dg_st_for gs s)"
    and enter_commute[simp]:
      "\<And>ci s.
        fun_of_exec_dg_st_for gs (enter_st ci s) =
        snd (enter\<^sup># tf ci (fun_of_exec_dg_st_for gs s))"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

text \<open>
  \<open>gamma\<close> is the caller-facing concretization at \<open>v\<close>: convert the executable
  post-solution \<open>sigma_st\<close> to its semantic function via \<open>fun_of_dg_st_for\<close>, then
  read off the set of stores the DG framework's own hook concretization assigns it,
  instantiated at this locale's context-insensitive \<open>gamma_unit\<close>. This is the
  accessor \<open>run_source_sound\<close> states its soundness guarantee in terms of, so
  no \<open>dg_spec_step\<close>/\<open>fun_of_dg_st_for\<close>/\<open>part_post_solution\<close> plumbing reaches the
  caller.
\<close>
text \<open>
  \<open>gamma_unit_exec\<close> is the executable-carrier sibling of \<open>gamma_unit gs\<close>, reading
  its two arguments back through \<open>fun_of_exec_dg_st_for\<close> first --- the diagonal
  analogue of \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>'s \<open>gamma_exec\<close>.
  \<open>run_source_sound\<close>/\<open>collect_sound\<close> interpret \<open>sound_dg_spec_ltr_for\<close> directly at
  this carrier, so no solved system is ever transported to the abstract one.
\<close>

definition gamma_unit_exec :: "'a exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> store set" where
  "gamma_unit_exec d g = gamma_unit gs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"

text \<open>
  Each obligation is the abstract one under the readback: the observation
  lemmas expose what the executable tree computes, the readback commutations
  turn each ownership operation into its function-valued counterpart, and the
  locale's two commute assumptions replace \<open>tf_st\<close>/\<open>enter_st\<close> by \<open>tf\<close>. What
  remains is exactly the transfer contract.
\<close>

theorem sound_dg_spec_st: "sound_dg_spec (unit_dg_spec_st_for gs tf_st enter_st) gamma_unit_exec gs"
proof -
  interpret tfs: sound_transfer_for gs tf by (rule tf_sound)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d' g g')
    show ?case
      unfolding gamma_unit_exec_def fun_of_exec_dg_st_for_def
      by (rule gamma_unit_mono)
         (rule fun_of_resolved_st_q_for_mono[OF 1(1)],
          rule fun_of_resolved_st_q_for_mono[OF 1(2)])
  next
    case (2 a \<tau> src gk)
    show ?case
      unfolding dg_spec_step_unit_st_for unit_transfer_st_def gamma_unit_exec_def
        dg_spec_edge_tree_def fun_of_exec_dg_st_for_def gamma_unit_def
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for
            tf_commute[unfolded fun_of_exec_dg_st_for_def]
            tfs.edge_collect_apply_tf_sound_for)
  next
    case (3 s \<tau> src gk ci)
    then show ?case
      unfolding dgs_enter_unit_dg_spec_st_for unit_transfer_st_def gamma_unit_exec_def
        fun_of_exec_dg_st_for_def gamma_unit_def
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for call_enter_def
            enter_commute[unfolded fun_of_exec_dg_st_for_def]
            tfs.tf_sound_enter_entry_for)
  next
    case (4 s \<tau> src_cc gk t src_ex ci)
    then show ?case
      unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_unit_dg_spec_st_for
        unit_combine_transfer_st_def gamma_unit_exec_def combine_collect_def
        fun_of_exec_dg_st_for_def gamma_unit_def
      by (simp add: fun_of_resolved_st_q_for_restrict_local_for
            fun_of_resolved_st_q_for_restrict_global_for
            fun_of_resolved_st_q_for_def[symmetric]
            gamma_unit_combine_assign[OF reserved, unfolded gamma_unit_def])
  qed
qed

interpretation sds: sound_dg_spec_ltr_for
  "unit_dg_spec_st_for gs tf_st enter_st" gamma_unit_exec gs
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_st)

definition gamma :: "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = dg_hook_gamma gamma_unit_exec sigma_st v"

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_st_for gs tf_st enter_st) (compile_prog Pi ps) bot0 s0d s0g"  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_unit_exec s0d s0g"
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
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_st_for gs tf_st enter_st) (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_unit_exec s0d s0g"
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
  (\<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>) already proves sound at the executable
  carrier. A registered domain supplies only \<open>tf\<close>/\<open>tf_st\<close>/\<open>enter_st\<close>/\<open>empty_pred\<close>
  and their three primitive commute facts; this locale's \<open>sublocale\<close> discharges
  \<^locale>\<open>routed_dg_domain_exec\<close>'s three assumptions from exactly those facts,
  and its own \<open>sound_dg_spec_st\<close> theorem does the rest: no solved system is ever
  transported from the executable carrier to the abstract one, so this
  registration locale needs no separate post-solution transport theorem.
\<close>

locale base_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and tf :: "'a::sound_domain domain_transfer"
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
      "sound_transfer_for gs tf"
    and reserved:
      "reserved_ret_var gs"
    and tf_commute[simp]:
      "\<And>a s.
        fun_of_exec_dg_st_for gs (tf_st a s) =
        apply_tf tf a (fun_of_exec_dg_st_for gs s)"
    and enter_commute[simp]:
      "\<And>ci s.
        fun_of_exec_dg_st_for gs (enter_st ci s) =
        snd (enter\<^sup># tf ci (fun_of_exec_dg_st_for gs s))"
    and is_bot_exact[simp]:
      "\<And>s. empty_pred s = is_empty_state (fun_of_exec_dg_st_for gs s)"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

text \<open>
  The packaging correspondence and its executable-carrier soundness pullback
  are \<open>routed_dg_domain_exec\<close>'s own content (\<open>Voblint_Exec.DG_Base_Exec\<close>):
  discharging its three assumptions from this locale's own commute facts gets
  \<open>sound_dg_spec_st\<close> for free, so no transport of a solved system between
  carriers is needed here at all -- the solver's own executable post-solution
  already satisfies \<open>sound_dg_spec_ltr_for\<close>'s \<open>pp\<close> premise directly, once
  \<open>sds\<close> below interprets that locale at the executable carrier.
\<close>

sublocale routed_dg_domain_exec gs empty_pred tf_st enter_st tf
  by unfold_locales
     (rule tf_commute[unfolded fun_of_exec_dg_st_for_def],
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

interpretation sds: sound_dg_spec_ltr_for
  "base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st" gamma_exec gs
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_st[OF tf_sound])

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store
    and bot0 s0d s0g :: "'a exec_dg_st lifted"
  defines "eqs \<equiv> dg_gen_of (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
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
  defines "eqs \<equiv> dg_gen_of (base_dg_spec_st_for_lifted gs empty_pred tf_st enter_st)
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




