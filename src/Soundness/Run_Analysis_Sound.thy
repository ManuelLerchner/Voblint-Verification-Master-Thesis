theory Run_Analysis_Sound
  imports
    "Voblint_Exec.Exec_DG_Bridge"
    "Voblint_Exec.DG_Base_Exec"
    "Voblint_Core.DG_LTR_Sound"
    "Voblint_Exec.Solver_Menu"
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

lemma dg_cmb_at_of_eq_for: "dg_cmb_at_of S = dg_cmb_at"
  by (rule ext)+ (simp add: dg_cmb_at_of_def dg_cmb_at_def)

lemma dg_cmb_of_eq_for: "dg_cmb_of S g = dg_cmb g"
  by (rule ext)+ (simp add: dg_cmb_of_def dg_cmb_def dg_cmb_at_of_eq_for)

lemma dg_extra_of_eq_for: "dg_extra_of S g = dg_extra g"
  by (rule ext)+ (simp add: dg_extra_of_def dg_extra_def dg_enter_def)

lemma dg_gen_of_eq_for:
  "dg_gen_of S g bot0 s0d s0g = dg_gen g bot0 s0d s0g"
  by (simp add: dg_gen_of_def dg_gen_def dg_cmb_of_eq_for dg_extra_of_eq_for)

theorem dg_run_source_sound_abs_for:
  fixes Pi :: proc_table and s0 t :: store
  assumes wf: "wf_compile_input gs Pi ps"
    and pp: "part_post_solution (dg_gen (compile_prog Pi ps) bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> dg_gamma sigma v"
proof -
  from source_reaches_ltr_collect[OF wf s0mem run]
  obtain v stk where m: "csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect gs (compile_prog Pi ps) S0 v" by blast
  have "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> dg_gamma sigma v"
    by (rule dg_post_solution_collect_sound_ltr_for[OF pp cover finI finC sound0])
  then show ?thesis using m coll by blast
qed

end

subsection \<open>Executable bundle: from a computed post-solution to source soundness\<close>

text \<open>
  The caller obtains \<open>pp_st\<close> from a single \<open>solve_c ... \<noteq> None\<close> success by the vendored
  adapter \<^verbatim>\<open>TD_side_<rule>_Interp.part_post_solution_of_solve_c\<close>.  This global theorem
  then hides executable-to-abstract transport, the D/G collecting endpoint, and the
  source bridge behind one application.  It is classifier-parametric in \<open>gs\<close>
  throughout: the executable-to-abstract transport uses
  \<open>part_post_solution_dg_st_to_abs_for\<close>, and the semantic core uses
  \<open>sound_dg_spec_ltr_for\<close>'s own \<open>dg_run_source_sound_abs_for\<close>.
\<close>

theorem dg_exec_run_source_sound_for:
  fixes Pi :: proc_table and s0 t :: store
    and S_st :: "('d1::bounded_semilattice_sup_bot exec_dg_st, 'g1::bounded_semilattice_sup_bot exec_dg_st) dg_spec"
    and S_abs :: "('d1 abs_state, 'g1 abs_state) dg_spec"
    and gammaDG :: "'d1 abs_state \<Rightarrow> 'g1 abs_state \<Rightarrow> store set"
    and bot0 s0d :: "'d1 exec_dg_st" and s0g :: "'g1 exec_dg_st"
    and gs :: "vname \<Rightarrow> bool"
  assumes sds: "sound_dg_spec_ltr_for S_abs gammaDG gs"
    and Hstep: "\<And>a d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g)
                        = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Henter: "\<And>ci d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st ci d g)
                        = dgs_enter S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Hcomb: "\<And>ci dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st ci dc de g)
                        = dgs_combine S_abs ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
    and Hcont: "\<And>ci d g. fun_of_exec_dg_st_for gs (caller_cont S_st ci d g)
                        = caller_cont S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and pp_st: "part_post_solution
                  (dg_gen_of S_st (compile_prog Pi ps) bot0 s0d s0g) x sigma_st vars"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sound_dg_spec.dg_gamma gammaDG (fun_of_dg_st_for gs \<circ> sigma_st) v"
proof -
  interpret sds: sound_dg_spec_ltr_for S_abs gammaDG gs by (rule sds)
  have pp_abs: "part_post_solution
      (dg_gen_of S_abs (compile_prog Pi ps)
         (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
      x (fun_of_dg_st_for gs \<circ> sigma_st) vars"
    by (rule part_post_solution_dg_st_to_abs_for[OF Hstep Henter Hcomb Hcont pp_st])
  have pp_gen: "part_post_solution
      (sds.dg_gen (compile_prog Pi ps)
         (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
      x (fun_of_dg_st_for gs \<circ> sigma_st) vars"
    using pp_abs unfolding sds.dg_gen_of_eq_for .
  show ?thesis
    by (rule sds.dg_run_source_sound_abs_for[OF wf pp_gen cover finI finC sound0 s0mem run])
qed

text \<open>
  The same executable-to-abstract transport as \<open>dg_exec_run_source_sound_for\<close>,
  stopping at the collecting endpoint instead of continuing through a
  concrete source run: no \<open>s0mem\<close>/\<open>run\<close> premise, and the conclusion holds at
  every \<open>v\<close>, not just the one point a run happens to reach. Reusable by any
  consumer (a check-report layer, for instance) that wants per-node collecting
  soundness for a computed D/G post-solution without going through
  \<open>csim\<close>/\<open>pstep\<close>.
\<close>

theorem dg_exec_collect_sound_for:
  fixes Pi :: proc_table and v :: pp
    and S_st :: "('d1::bounded_semilattice_sup_bot exec_dg_st, 'g1::bounded_semilattice_sup_bot exec_dg_st) dg_spec"
    and S_abs :: "('d1 abs_state, 'g1 abs_state) dg_spec"
    and gammaDG :: "'d1 abs_state \<Rightarrow> 'g1 abs_state \<Rightarrow> store set"
    and bot0 s0d :: "'d1 exec_dg_st" and s0g :: "'g1 exec_dg_st"
    and gs :: "vname \<Rightarrow> bool"
  assumes sds: "sound_dg_spec_ltr_for S_abs gammaDG gs"
    and Hstep: "\<And>a d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dg_spec_step S_st a d g)
                        = dg_spec_step S_abs a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Henter: "\<And>ci d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_enter S_st ci d g)
                        = dgs_enter S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and Hcomb: "\<And>ci dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (dgs_combine S_st ci dc de g)
                        = dgs_combine S_abs ci (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
    and Hcont: "\<And>ci d g. fun_of_exec_dg_st_for gs (caller_cont S_st ci d g)
                        = caller_cont S_abs ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
    and pp_st: "part_post_solution
                  (dg_gen_of S_st (compile_prog Pi ps) bot0 s0d s0g) x sigma_st vars"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v
           \<subseteq> sound_dg_spec.dg_gamma gammaDG (fun_of_dg_st_for gs \<circ> sigma_st) v"
proof -
  interpret sds: sound_dg_spec_ltr_for S_abs gammaDG gs by (rule sds)
  have pp_abs: "part_post_solution
      (dg_gen_of S_abs (compile_prog Pi ps)
         (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
      x (fun_of_dg_st_for gs \<circ> sigma_st) vars"
    by (rule part_post_solution_dg_st_to_abs_for[OF Hstep Henter Hcomb Hcont pp_st])
  have pp_gen: "part_post_solution
      (sds.dg_gen (compile_prog Pi ps)
         (fun_of_exec_dg_st_for gs bot0) (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g))
      x (fun_of_dg_st_for gs \<circ> sigma_st) vars"
    using pp_abs unfolding sds.dg_gen_of_eq_for .
  show ?thesis
    by (rule sds.dg_post_solution_collect_sound_ltr_for[OF pp_gen cover finI finC sound0])
qed

section \<open>Registered executable D/G analyses\<close>

subsection \<open>Executable-to-abstract transport for diagonal unit specifications\<close>

text \<open>
  For a diagonal (unit) D/G analysis the two transport-commutation hypotheses of
  \<^theory_text>\<open>dg_exec_run_source_sound_for\<close> are \<^emph>\<open>derivable\<close>: the combine side holds
  unconditionally, and the step side reduces to the single primitive per-action
  commutation of the executable transfer \<^term>\<open>tf_st\<close> with its abstract image
  \<^term>\<open>apply_tf tf\<close>.  The generic lemmas keep this transport argument in the
  registration interface rather than in individual analyses.
\<close>

text \<open>Classifier-parametric transport, generic in \<open>gs\<close> throughout: the entry
                  point for any consumer generic in the classifier.\<close>

lemma unit_dg_Hstep_for:
  assumes commute: "\<And>a s. fun_of_exec_dg_st_for gs (tf_st a s) = apply_tf tf a (fun_of_exec_dg_st_for gs s)"
  shows "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
             (dg_spec_step (unit_dg_spec_st_for gs tf_st enter_st) a d g)
           = dg_spec_step (unit_dg_spec_for gs tf) a (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  unfolding dg_spec_step_unit_st_for dg_spec_step_unit_for
  by (rule unit_step_st_commute_for
        [where f_st = "tf_st a" and f_abs = "apply_tf tf a", OF commute])

lemma unit_dg_Henter_for:
  assumes enter_commute: "\<And>ci s. fun_of_exec_dg_st_for gs (enter_st ci s) = snd (enter\<^sup># tf ci (fun_of_exec_dg_st_for gs s))"
  shows "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
             (dgs_enter (unit_dg_spec_st_for gs tf_st enter_st) ci d g)
           = dgs_enter (unit_dg_spec_for gs tf) ci (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  by (simp add: unit_dg_spec_st_for_def dgs_enter_unit_dg_spec_for unit_step_st_commute_for enter_commute comp_def)

lemma unit_dg_Hcomb_for:
  "map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs)
       (dgs_combine (unit_dg_spec_st_for gs tf_st enter_st) ci dc de g)
     = dgs_combine (unit_dg_spec_for gs tf) ci
         (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  by (rule unit_combine_step_st_commute_for)

text \<open>The caller half of \<open>enter\<close> is the identity on both sides of the diagonal
  correspondence, so its commute obligation holds by unfolding the two records ---
  but it is discharged here rather than assumed, so a future executable spec with
  a nontrivial continuation has to supply its own.\<close>

lemma unit_dg_Hcont_for:
  "fun_of_exec_dg_st_for gs (caller_cont (unit_dg_spec_st_for gs tf_st enter_st) ci d g)
     = caller_cont (unit_dg_spec_for gs tf) ci
         (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  by (simp add: unit_dg_spec_st_for_def unit_dg_spec_for_def)

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
  read off the set of stores the DG framework's own \<open>dg_gamma\<close> assigns it,
  instantiated at this locale's context-insensitive \<open>gamma_unit\<close>. This is the
  accessor \<open>run_source_sound\<close> states its soundness guarantee in terms of, so
  no \<open>dg_spec_step\<close>/\<open>fun_of_dg_st_for\<close>/\<open>part_post_solution\<close> plumbing reaches the
  caller.
\<close>
definition gamma :: "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st, 'a exec_dg_st) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = sound_dg_spec.dg_gamma (gamma_unit gs) (fun_of_dg_st_for gs \<circ> sigma_st) v"

lemma sds: "sound_dg_spec_ltr_for (unit_dg_spec_for gs tf) (gamma_unit gs) gs"
  unfolding sound_dg_spec_ltr_for_def
  by (rule sound_dg_spec_unit_for[OF tf_sound reserved])

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store and bot0 s0d s0g :: "'a exec_dg_st"
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_st_for gs tf_st enter_st) (compile_prog Pi ps) bot0 s0d s0g"  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_unit gs (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def
    by (rule dg_exec_run_source_sound_for
          [OF sds unit_dg_Hstep_for[OF tf_commute]
              unit_dg_Henter_for[OF enter_commute] unit_dg_Hcomb_for unit_dg_Hcont_for
              pp_st[unfolded eqs_def] wf cover[unfolded eqs_def]
              finI finC sound0 s0mem run])
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
    and sound0: "S0 \<subseteq> gamma_unit gs (fun_of_exec_dg_st_for gs s0d) (fun_of_exec_dg_st_for gs s0g)"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def
    by (rule dg_exec_collect_sound_for
          [OF sds unit_dg_Hstep_for[OF tf_commute]
              unit_dg_Henter_for[OF enter_commute] unit_dg_Hcomb_for unit_dg_Hcont_for
              pp_st[unfolded eqs_def] wf cover[unfolded eqs_def]
              finI finC sound0])
qed

end

section \<open>Registered executable D/G analyses, lifted Base-style local carrier\<close>

subsection \<open>Executable-to-abstract transport for the lifted diagonal carrier\<close>

text \<open>
  Lifted siblings of \<open>dg_exec_run_source_sound_for\<close>/\<open>dg_exec_collect_sound_for\<close>,
  reachability-lifted at the local carrier so a Base-style analysis (whole abstract
  state as \<open>D\<close>, no VIMP-global split into a solver-global unknown) can supply its own
  D and G types independently -- only their common \<open>exec_dg_st lifted\<close> wrapper shape,
  read back through the same classifier \<open>gs\<close>, is fixed here.  Every step is a direct
  citation of the already-proved generic transport
  \<open>part_post_solution_dg_st_to_abs_lifted_for\<close> and the classifier-parametric semantic
  core \<open>sound_dg_spec_ltr_for.dg_run_source_sound_abs_for\<close>; no trace or DG semantic
  argument is re-derived.
\<close>

theorem dg_exec_run_source_sound_lifted_for:
  fixes Pi :: proc_table and s0 t :: store
    and S_st :: "('d1::bounded_semilattice_sup_bot exec_dg_st lifted,
                   'g1::bounded_semilattice_sup_bot exec_dg_st lifted) dg_spec"
    and S_abs :: "('d1 abs_state lifted, 'g1 abs_state lifted) dg_spec"
    and gammaDG :: "'d1 abs_state lifted \<Rightarrow> 'g1 abs_state lifted \<Rightarrow> store set"
    and bot0 s0d :: "'d1 exec_dg_st lifted" and s0g :: "'g1 exec_dg_st lifted"
    and gs :: "vname \<Rightarrow> bool"
  assumes sds: "sound_dg_spec_ltr_for S_abs gammaDG gs"
    and Hstep: "\<And>a d g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dg_spec_step S_st a d g)
                      = dg_spec_step S_abs a (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Henter: "\<And>ci d g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dgs_enter S_st ci d g)
                      = dgs_enter S_abs ci (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Hcomb: "\<And>ci dc de g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dgs_combine S_st ci dc de g)
                      = dgs_combine S_abs ci (map_lift (fun_of_exec_dg_st_for gs) dc)
                          (map_lift (fun_of_exec_dg_st_for gs) de) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Hcont: "\<And>ci d g. map_lift (fun_of_exec_dg_st_for gs) (caller_cont S_st ci d g)
                      = caller_cont S_abs ci (map_lift (fun_of_exec_dg_st_for gs) d)
                          (map_lift (fun_of_exec_dg_st_for gs) g)"
    and pp_st: "part_post_solution
                  (dg_gen_of S_st (compile_prog Pi ps) bot0 s0d s0g) x sigma_st vars"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG (map_lift (fun_of_exec_dg_st_for gs) s0d) (map_lift (fun_of_exec_dg_st_for gs) s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sound_dg_spec.dg_gamma gammaDG
                     (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) v"
proof -
  interpret sds: sound_dg_spec_ltr_for S_abs gammaDG gs by (rule sds)
  have pp_abs: "part_post_solution
      (dg_gen_of S_abs (compile_prog Pi ps)
         (map_lift (fun_of_exec_dg_st_for gs) bot0) (map_lift (fun_of_exec_dg_st_for gs) s0d)
         (map_lift (fun_of_exec_dg_st_for gs) s0g))
      x (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) vars"
    by (rule part_post_solution_dg_st_to_abs_lifted_for[folded fun_of_exec_dg_st_for_def, OF Hstep Henter Hcomb Hcont pp_st])
  have pp_gen: "part_post_solution
      (sds.dg_gen (compile_prog Pi ps)
         (map_lift (fun_of_exec_dg_st_for gs) bot0) (map_lift (fun_of_exec_dg_st_for gs) s0d)
         (map_lift (fun_of_exec_dg_st_for gs) s0g))
      x (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) vars"
    using pp_abs unfolding sds.dg_gen_of_eq_for .
  show ?thesis
    by (rule sds.dg_run_source_sound_abs_for[OF wf pp_gen cover finI finC sound0 s0mem run])
qed

theorem dg_exec_collect_sound_lifted_for:
  fixes Pi :: proc_table and v :: pp
    and S_st :: "('d1::bounded_semilattice_sup_bot exec_dg_st lifted,
                   'g1::bounded_semilattice_sup_bot exec_dg_st lifted) dg_spec"
    and S_abs :: "('d1 abs_state lifted, 'g1 abs_state lifted) dg_spec"
    and gammaDG :: "'d1 abs_state lifted \<Rightarrow> 'g1 abs_state lifted \<Rightarrow> store set"
    and bot0 s0d :: "'d1 exec_dg_st lifted" and s0g :: "'g1 exec_dg_st lifted"
    and gs :: "vname \<Rightarrow> bool"
  assumes sds: "sound_dg_spec_ltr_for S_abs gammaDG gs"
    and Hstep: "\<And>a d g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dg_spec_step S_st a d g)
                      = dg_spec_step S_abs a (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Henter: "\<And>ci d g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dgs_enter S_st ci d g)
                      = dgs_enter S_abs ci (map_lift (fun_of_exec_dg_st_for gs) d) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Hcomb: "\<And>ci dc de g. map_prod (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs))
                        (dgs_combine S_st ci dc de g)
                      = dgs_combine S_abs ci (map_lift (fun_of_exec_dg_st_for gs) dc)
                          (map_lift (fun_of_exec_dg_st_for gs) de) (map_lift (fun_of_exec_dg_st_for gs) g)"
    and Hcont: "\<And>ci d g. map_lift (fun_of_exec_dg_st_for gs) (caller_cont S_st ci d g)
                      = caller_cont S_abs ci (map_lift (fun_of_exec_dg_st_for gs) d)
                          (map_lift (fun_of_exec_dg_st_for gs) g)"
    and pp_st: "part_post_solution
                  (dg_gen_of S_st (compile_prog Pi ps) bot0 s0d s0g) x sigma_st vars"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) vars"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gammaDG (map_lift (fun_of_exec_dg_st_for gs) s0d) (map_lift (fun_of_exec_dg_st_for gs) s0g)"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v
           \<subseteq> sound_dg_spec.dg_gamma gammaDG
               (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) v"
proof -
  interpret sds: sound_dg_spec_ltr_for S_abs gammaDG gs by (rule sds)
  have pp_abs: "part_post_solution
      (dg_gen_of S_abs (compile_prog Pi ps)
         (map_lift (fun_of_exec_dg_st_for gs) bot0) (map_lift (fun_of_exec_dg_st_for gs) s0d)
         (map_lift (fun_of_exec_dg_st_for gs) s0g))
      x (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) vars"
    by (rule part_post_solution_dg_st_to_abs_lifted_for[folded fun_of_exec_dg_st_for_def, OF Hstep Henter Hcomb Hcont pp_st])
  have pp_gen: "part_post_solution
      (sds.dg_gen (compile_prog Pi ps)
         (map_lift (fun_of_exec_dg_st_for gs) bot0) (map_lift (fun_of_exec_dg_st_for gs) s0d)
         (map_lift (fun_of_exec_dg_st_for gs) s0g))
      x (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) vars"
    using pp_abs unfolding sds.dg_gen_of_eq_for .
  show ?thesis
    by (rule sds.dg_post_solution_collect_sound_ltr_for[OF pp_gen cover finI finC sound0])
qed

subsection \<open>Registration locale for the lifted Base-style diagonal analysis\<close>

text \<open>
  The canonical executable Base analysis: whole-state \<open>D\<close> lifted for reachability,
  \<open>G\<close> left an independent, otherwise-unconstrained \<open>bounded_semilattice_sup_bot\<close> type
  (never forced to equal \<open>D\<close>'s content type or to \<open>unit\<close>) so this locale does not
  itself claim any particular \<open>G\<close> shape is fundamental -- only that the executable
  solver route \<open>dg_gen_of\<close> needs a common \<open>exec_dg_st lifted\<close> wrapper for both sides,
  the same plumbing constraint \<open>unit_dg_exec_analysis\<close> already carries.  A registered
  domain supplies only \<open>tf\<close>/\<open>tf_st\<close>/\<open>enter_st\<close>/\<open>is_bot_pred\<close> and their three primitive
  commute facts; the packaging-correspondence proof itself is \<^theory>\<open>Voblint_Exec.DG_Base_Exec\<close>'s
  \<open>base_dg_spec_st_for_lifted_dg_spec_step_commute\<close>/\<open>_dgs_enter_commute\<close>/\<open>_dgs_combine_commute\<close>,
  cited directly -- unlike \<open>unit_dg_exec_analysis\<close>, no intermediate \<open>unit_dg_H*_for\<close>
  layer is needed because the Base packaging proof already has exactly this shape.
\<close>

locale base_dg_exec_analysis =
  fixes gs :: "vname \<Rightarrow> bool"
    and tf :: "'a::sound_domain domain_transfer"
    and tf_st :: "edge_action \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and enter_st :: "call_info \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st"
    and is_bot_pred :: "'a exec_dg_st \<Rightarrow> bool"
    and solve :: "(pp \<times> unit, unit,
                    ('a exec_dg_st lifted, 'g::bounded_semilattice_sup_bot exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st lifted, 'g exec_dg_st lifted) dg_state)"
    and solve_c :: "(pp \<times> unit, unit, ('a exec_dg_st lifted, 'g exec_dg_st lifted) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times>
                       (pp \<times> unit + unit \<Rightarrow>
                         ('a exec_dg_st lifted, 'g exec_dg_st lifted) dg_state)) option"
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
      "\<And>s. is_bot_pred s = is_bot_state (fun_of_exec_dg_st_for gs s)"
    and solver_pps:
      "\<And>eqs x. solve_c eqs x \<noteq> None \<Longrightarrow>
        part_post_solution eqs x
          (snd (solve eqs x)) (fst (solve eqs x))"
begin

text \<open>
  \<open>gamma\<close> mirrors \<open>unit_dg_exec_analysis.gamma\<close> exactly, reading the lifted executable
  post-solution back through \<open>fun_of_dg_st_gen\<close> at the diagonal lifted reader and
  concretizing via \<open>gamma_dg_base\<close> -- the reachability stays lifted end-to-end from the
  solver's raw \<open>exec_dg_st lifted\<close> value through to this concretization call; nothing
  here converts a \<open>Bot\<close> solver value back to a plain \<open>abs_state\<close> bottom first.
\<close>
definition gamma ::
  "(pp \<times> unit + unit \<Rightarrow> ('a exec_dg_st lifted, 'g exec_dg_st lifted) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = sound_dg_spec.dg_gamma gamma_dg_base
           (fun_of_dg_st_gen (map_lift (fun_of_exec_dg_st_for gs)) (map_lift (fun_of_exec_dg_st_for gs)) \<circ> sigma_st) v"

lemma sds: "sound_dg_spec_ltr_for (base_dg_spec_for_lifted gs is_bot_state tf) gamma_dg_base gs"
  unfolding sound_dg_spec_ltr_for_def
  by (rule base_dg_spec_sound[OF tf_sound is_bot_state_gamma_state_empty])

theorem run_source_sound:
  fixes Pi :: proc_table and ps and s0 t :: store
    and bot0 s0d :: "'a exec_dg_st lifted" and s0g :: "'g exec_dg_st lifted"
  defines "eqs \<equiv> dg_gen_of (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st)
                   (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for gs) s0d) (map_lift (fun_of_exec_dg_st_for gs) s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep gs Pi) (main_body Pi, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. csim Pi (compile_prog Pi ps) (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def
    by (rule dg_exec_run_source_sound_lifted_for
          [OF sds base_dg_spec_st_for_lifted_dg_spec_step_commute[OF tf_commute is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_enter_commute[OF enter_commute is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_combine_commute[OF is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_caller_cont_commute
              pp_st[unfolded eqs_def] wf cover[unfolded eqs_def]
              finI finC sound0 s0mem run])
qed

text \<open>
  The per-node collecting analogue of \<open>run_source_sound\<close>, dropping \<open>s0mem\<close>/\<open>run\<close>:
  reusable by any consumer that wants collecting soundness at an arbitrary program
  point for a computed lifted D/G post-solution, without going through a concrete
  source run.
\<close>

theorem collect_sound:
  fixes Pi :: proc_table and ps and v :: pp
    and bot0 s0d :: "'a exec_dg_st lifted" and s0g :: "'g exec_dg_st lifted"
  defines "eqs \<equiv> dg_gen_of (base_dg_spec_st_for_lifted gs is_bot_pred tf_st enter_st)
                   (compile_prog Pi ps) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input gs Pi ps"
    and cover: "vars_cover (compile_prog Pi ps) (fst (solve eqs x))"
    and finI: "finite (intra (compile_prog Pi ps))"
    and finC: "finite (calls (compile_prog Pi ps))"
    and sound0: "S0 \<subseteq> gamma_dg_base (map_lift (fun_of_exec_dg_st_for gs) s0d) (map_lift (fun_of_exec_dg_st_for gs) s0g)"
  shows "ltr_collect gs (compile_prog Pi ps) S0 v \<subseteq> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def
    by (rule dg_exec_collect_sound_lifted_for
          [OF sds base_dg_spec_st_for_lifted_dg_spec_step_commute[OF tf_commute is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_enter_commute[OF enter_commute is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_combine_commute[OF is_bot_exact]
              base_dg_spec_st_for_lifted_dgs_caller_cont_commute
              pp_st[unfolded eqs_def] wf cover[unfolded eqs_def]
              finI finC sound0])
qed

end


end




