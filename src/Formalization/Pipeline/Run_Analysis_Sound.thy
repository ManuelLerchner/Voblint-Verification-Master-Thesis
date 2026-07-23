theory Run_Analysis_Sound
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.DG_LTR_Sound"
    "Voblint_Analysis.Solver_Menu"
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
  \<^verbatim>\<open>dg_post_solution_collect_sound_ltr\<close> holds at every covered
  point, so no premature specialisation to \<^const>\<open>cfg_exit\<close> is needed.

  \<^bold>\<open>Why the solver step stays a one-line adapter.\<close>  The step \<open>solve_c success ->
  part_post_solution\<close> lives in the vendored locale \<^locale>\<open>TD_side_upd_rule\<close> as
  \<^verbatim>\<open>part_post_solution_of_solve_c\<close>, whose unknown type is rigid inside that locale
  and cannot be tied to the D/G unknown type \<open>pp \<times> unit\<close>.  So the executable-to-abstract
  transport lives in the \<^emph>\<open>global\<close> theorem below, and the caller feeds it the executable
  \<^const>\<open>part_post_solution\<close> obtained from a single \<^verbatim>\<open>by eval\<close> success via that adapter.
\<close>

subsection \<open>The executable generator is the locale generator\<close>

context sound_dg_spec
begin

lemma dg_cmb_of_eq: "dg_cmb_of S = dg_cmb"
  by (rule ext)+ (simp add: dg_cmb_of_def dg_cmb_def)

lemma dg_gen_of_eq:
  "dg_gen_of S g bot0 s0d s0g = dg_gen g bot0 s0d s0g"
  by (simp add: dg_gen_of_def dg_gen_def dg_cmb_of_eq)

subsection \<open>Semantic core: abstract post-solution to source bound\<close>

theorem dg_run_source_sound_abs:
  fixes Pi :: proc_table and mnm :: pname and s0 t :: store
  assumes wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and pp: "part_post_solution (dg_gen (compile_prog Pi ps mnm main) bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges (compile_prog Pi ps mnm main))"
    and finC: "finite (combines (compile_prog Pi ps mnm main))"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep Pi) (main, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. concrete_program_match Pi ps main (residual, t, frs) (v, t, stk)
                 \<and> t \<in> dg_gamma sigma v"
proof -
  from source_reaches_ltr_collect[OF wf src s0mem run]
  obtain v stk where m: "concrete_program_match Pi ps main (residual, t, frs) (v, t, stk)"
    and coll: "t \<in> ltr_collect (compile_prog Pi ps mnm main) S0 v" by blast
  have "ltr_collect (compile_prog Pi ps mnm main) S0 v \<subseteq> dg_gamma sigma v"
    by (rule dg_post_solution_collect_sound_ltr
          [OF pp cover_entry cover_edge cover_combine finE finC sound0])
  then show ?thesis using m coll by blast
qed

end

subsection \<open>Executable bundle: from a computed post-solution to source soundness\<close>

text \<open>
  The caller obtains \<open>pp_st\<close> from a single \<open>solve_c ... \<noteq> None\<close> success by the vendored
  adapter \<^verbatim>\<open>TD_side_<rule>_Interp.part_post_solution_of_solve_c\<close>.  This global theorem
  then hides executable-to-abstract transport, the D/G collecting endpoint, and the
  source bridge behind one application.
\<close>

theorem dg_exec_run_source_sound:
  fixes Pi :: proc_table and mnm :: pname and s0 t :: store
    and S_st :: "('d1::bounded_semilattice_sup_bot st, 'g1::bounded_semilattice_sup_bot st) dg_spec"
    and S_abs :: "('d1 abs_state, 'g1 abs_state) dg_spec"
    and gammaDG :: "'d1 abs_state \<Rightarrow> 'g1 abs_state \<Rightarrow> store set"
    and bot0 s0d :: "'d1 st" and s0g :: "'g1 st"
  assumes sds: "sound_dg_spec S_abs gammaDG"
    and Hstep: "\<And>a d g. map_prod fun_of_st fun_of_st (dg_spec_step S_st a d g)
                        = dg_spec_step S_abs a (fun_of_st d) (fun_of_st g)"
    and Hcomb: "\<And>dst dc de g. map_prod fun_of_st fun_of_st (dgs_combine S_st dst dc de g)
                        = dgs_combine S_abs dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
    and pp_st: "part_post_solution
                  (dg_gen_of S_st (compile_prog Pi ps mnm main) bot0 s0d s0g) x sigma_st vars"
    and wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and cover_entry: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges (compile_prog Pi ps mnm main))"
    and finC: "finite (combines (compile_prog Pi ps mnm main))"
    and sound0: "S0 \<subseteq> gammaDG (fun_of_st s0d) (fun_of_st s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep Pi) (main, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. concrete_program_match Pi ps main (residual, t, frs) (v, t, stk)
                 \<and> t \<in> sound_dg_spec.dg_gamma gammaDG (fun_of_dg_st \<circ> sigma_st) v"
proof -
  interpret sds: sound_dg_spec S_abs gammaDG by (rule sds)
  have pp_abs: "part_post_solution
      (dg_gen_of S_abs (compile_prog Pi ps mnm main)
         (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g))
      x (fun_of_dg_st \<circ> sigma_st) vars"
    by (rule part_post_solution_dg_st_to_abs[OF Hstep Hcomb pp_st])
  have pp_gen: "part_post_solution
      (sds.dg_gen (compile_prog Pi ps mnm main)
         (fun_of_st bot0) (fun_of_st s0d) (fun_of_st s0g))
      x (fun_of_dg_st \<circ> sigma_st) vars"
    using pp_abs unfolding sds.dg_gen_of_eq .
  show ?thesis
    by (rule sds.dg_run_source_sound_abs
          [OF wf src pp_gen cover_entry cover_edge cover_combine finE finC sound0 s0mem run])
qed

section \<open>Domain-registration layer (A2)\<close>

subsection \<open>Generic executable-to-abstract transport for diagonal unit specs\<close>

text \<open>
  For a diagonal (unit) D/G analysis the two transport-commutation hypotheses of
  \<^theory_text>\<open>dg_exec_run_source_sound\<close> are \<^emph>\<open>derivable\<close>: the combine side holds
  unconditionally, and the step side reduces to the single primitive per-action
  commutation of the executable transfer \<^term>\<open>tf_st\<close> with its abstract image
  \<^term>\<open>apply_tf tf\<close>.  These two lemmas replace the per-instance \<open>_Hstep\<close> / \<open>_Hcomb\<close>
  boilerplate.
\<close>

lemma unit_dg_Hstep:
  assumes "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
  shows "map_prod fun_of_st fun_of_st (dg_spec_step (unit_dg_spec_st tf_st) a d g)
           = dg_spec_step (unit_dg_spec tf) a (fun_of_st d) (fun_of_st g)"
  by (simp add: dg_spec_step_unit_st dg_spec_step_unit unit_step_st_commute assms)

lemma unit_dg_Hcomb:
  "map_prod fun_of_st fun_of_st (dgs_combine (unit_dg_spec_st tf_st) dst dc de g)
     = dgs_combine (unit_dg_spec tf) dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  by (simp add: unit_dg_spec_st_def unit_dg_spec_def unit_combine_step_st_commute)

subsection \<open>Registration locale for diagonal executable D/G analyses\<close>

text \<open>
  A registered diagonal analysis supplies only \<^emph>\<open>essential mathematics\<close> --- a sound
  abstract transfer \<^term>\<open>tf\<close> and its executable mirror \<^term>\<open>tf_st\<close> with the primitive
  commutation --- plus the vendored solver's \<^theory_text>\<open>part_post_solution_of_solve_c\<close> adapter
  for its chosen update rule (\<^term>\<open>solve\<close> / \<^term>\<open>solve_c\<close>).  It obtains a reusable
  executable source-soundness theorem \<^theory_text>\<open>run_source_sound\<close> and a semantic concretization
  accessor \<^theory_text>\<open>gamma\<close>, with no \<^const>\<open>dg_spec_step\<close> trees, \<^const>\<open>fun_of_dg_st\<close>,
  \<^const>\<open>part_post_solution\<close>, or transport lemmas exposed to callers.
\<close>

locale unit_dg_exec_analysis =
  fixes tf :: "'a::sound_domain domain_transfer"
    and tf_st :: "edge_action \<Rightarrow> 'a st \<Rightarrow> 'a st"
    and solve :: "(pp \<times> unit, unit, ('a st, 'a st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> (pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> ('a st, 'a st) dg_state)"
    and solve_c :: "(pp \<times> unit, unit, ('a st, 'a st) dg_state) eqsT
                   \<Rightarrow> pp \<times> unit
                   \<Rightarrow> ((pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> ('a st, 'a st) dg_state)) option"
  assumes tf_sound: "sound_transfer tf"
    and tf_commute: "\<And>a s. fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)"
    and solver_pps: "\<And>eqs x. solve_c eqs x \<noteq> None
                      \<Longrightarrow> part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
begin

definition gamma :: "(pp \<times> unit + unit \<Rightarrow> ('a st, 'a st) dg_state) \<Rightarrow> pp \<Rightarrow> store set"
  where "gamma sigma_st v = sound_dg_spec.dg_gamma gamma_unit (fun_of_dg_st \<circ> sigma_st) v"

lemma sds: "sound_dg_spec (unit_dg_spec tf) gamma_unit"
  by (rule sound_dg_spec_unit[OF tf_sound])

theorem run_source_sound:
  fixes Pi :: proc_table and ps mnm main and s0 t :: store and bot0 s0d s0g :: "'a st"
  defines "eqs \<equiv> dg_gen_of (unit_dg_spec_st tf_st) (compile_prog Pi ps mnm main) bot0 s0d s0g"
  assumes SOLVE: "solve_c eqs x \<noteq> None"
    and wf: "wf_compile_input Pi ps main"
    and src: "source_com main"
    and cover_entry: "(cfg_entry (compile_prog Pi ps mnm main), ()) \<in> fst (solve eqs x)"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> fst (solve eqs x)"
    and cover_combine:
      "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines (compile_prog Pi ps mnm main) \<Longrightarrow> (w, ()) \<in> fst (solve eqs x)"
    and finE: "finite (edges (compile_prog Pi ps mnm main))"
    and finC: "finite (combines (compile_prog Pi ps mnm main))"
    and sound0: "S0 \<subseteq> gamma_unit (fun_of_st s0d) (fun_of_st s0g)"
    and s0mem: "s0 \<in> S0"
    and run: "star (pstep Pi) (main, s0, []) (residual, t, frs)"
  shows "\<exists>v stk. concrete_program_match Pi ps main (residual, t, frs) (v, t, stk)
                 \<and> t \<in> gamma (snd (solve eqs x)) v"
proof -
  have pp_st: "part_post_solution eqs x (snd (solve eqs x)) (fst (solve eqs x))"
    by (rule solver_pps[OF SOLVE])
  show ?thesis
    unfolding gamma_def eqs_def
    by (rule dg_exec_run_source_sound
          [OF sds unit_dg_Hstep[OF tf_commute] unit_dg_Hcomb
              pp_st[unfolded eqs_def] wf src
              cover_entry[unfolded eqs_def] cover_edge[unfolded eqs_def]
              cover_combine[unfolded eqs_def] finE finC sound0 s0mem run])
qed

end

end


