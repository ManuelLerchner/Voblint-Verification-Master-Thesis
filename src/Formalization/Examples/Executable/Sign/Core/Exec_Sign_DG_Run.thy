section \<open>Running the verified solver on the native D/G spine (Sign)\<close>

text \<open>
  The first end-to-end certified run on the carrier-opaque D/G equation system.
  A concrete call-free Sign program is compiled to a CFG; the executable D/G
  generator (\<open>dg_gen_of (unit_dg_spec_st sign_tf_st)\<close>, values in
  \<open>(sign st, sign st) dg_state\<close>) is handed to the vendored always-join TD-side
  solver; the solver \<^emph>\<open>computes\<close> a partial post-solution; that computed solution is
  transported value-wise through \<open>fun_of_dg_st\<close> to an abstract post-solution of
  \<open>sign_dg.dg_gen\<close>; and the native \<open>sound_dg_spec\<close> collecting-soundness endpoint
  turns it into an over-approximation of the interprocedural collecting semantics.

  The final theorem \<open>dgEx_collect_sound\<close> depends on the \<^emph>\<open>computed\<close> solver result
  \<open>snd dgEx_sol\<close>, not on any hand-written candidate solution.
\<close>

theory Exec_Sign_DG_Run
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_DG"
begin

subsection \<open>Sign as an executable D/G analysis\<close>

text \<open>
  The diagonal Sign spec (\<open>D = G = sign abs_state\<close>) has an executable mirror at
  \<open>sign st\<close>: \<open>unit_dg_spec_st sign_tf_st\<close>.  Its step and combine commute with the
  abstract \<open>unit_dg_spec sign_tf\<close> through \<open>fun_of_st\<close>, discharging the two
  hypotheses of \<open>part_post_solution_dg_st_to_abs\<close>.
\<close>

lemma sign_Hstep:
  "map_prod fun_of_st fun_of_st (dg_spec_step (unit_dg_spec_st sign_tf_st) a d g)
     = dg_spec_step (unit_dg_spec sign_tf) a (fun_of_st d) (fun_of_st g)"
  by (simp add: dg_spec_step_unit_st dg_spec_step_unit unit_step_st_commute sign_tf_st_commute)

lemma sign_Hcomb:
  "map_prod fun_of_st fun_of_st (dgs_combine (unit_dg_spec_st sign_tf_st) dst dc de g)
     = dgs_combine (unit_dg_spec sign_tf) dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  by (simp add: unit_dg_spec_st_def unit_dg_spec_def unit_combine_step_st_commute)

text \<open>The executable generator's abstract image is exactly the native \<open>sign_dg.dg_gen\<close>.\<close>

lemma dg_gen_of_eq_sign_dg_gen:
  "dg_gen_of (unit_dg_spec sign_tf) g bot0 s0d s0g = sign_dg.dg_gen g bot0 s0d s0g"
proof -
  have "dg_cmb_of (unit_dg_spec sign_tf) = sign_dg.dg_cmb"
    by (rule ext)+ (simp add: dg_cmb_of_def sign_dg.dg_cmb_def)
  thus ?thesis by (simp add: dg_gen_of_def sign_dg.dg_gen_def)
qed

subsection \<open>The concrete program and its computed solution\<close>

text \<open>
  A minimal call-free program \<^verbatim>\<open>x := 1; y := x\<close>: entry \<open>0\<close>, exit \<open>2\<close>, no combines.
\<close>

definition gEx :: cfg where
  "gEx = mk_cfg 0 2
     {(0, EA_Assign ''x'' (BaseN (AExp.N 1)), 1),
      (1, EA_Assign ''y'' (BaseN (AExp.V ''x'')), 2)} {}"

lemma gEx_edges: "edges gEx = {(0, EA_Assign ''x'' (BaseN (AExp.N 1)), 1), (1, EA_Assign ''y'' (BaseN (AExp.V ''x'')), 2)}"
  by (simp add: gEx_def mk_cfg_def)
lemma gEx_combines: "combines gEx = {}"
  by (simp add: gEx_def mk_cfg_def)
lemma gEx_entry: "cfg_entry gEx = 0"
  by (simp add: gEx_def mk_cfg_def)
lemma gEx_finE: "finite (edges gEx)" by (simp add: gEx_edges)
lemma gEx_finC: "finite (combines gEx)" by (simp add: gEx_combines)
lemma gEx_no_enter: "\<And>u a w. (u, a, w) \<in> edges gEx \<Longrightarrow> \<not> is_enter_action a"
  by (auto simp: gEx_edges is_enter_action_def split: edge_action.splits)

definition dgEx_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign st, sign st) dg_state) strategy_tree" where
  "dgEx_eqs = dg_gen_of (unit_dg_spec_st sign_tf_st) gEx bot cinit_sign_st cinit_sign_st"

definition dgEx_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign st, sign st) dg_state)" where
  "dgEx_sol = TD_side_always_join_Interp_solve dgEx_eqs (cfg_exit gEx, ())"

subsection \<open>The solver computes a partial post-solution\<close>

text \<open>
  The executable option-valued solver terminates on the D/G equation system --- a
  code-generated \<open>by eval\<close> fact --- so the solver-domain predicate holds and the
  vendored partial-post-solution theorem applies to the computed result.
\<close>

lemma dgEx_terminates_c: "TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ()) \<noteq> None"
  by eval

lemma dgEx_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(unit) TYPE((sign st, sign st) dg_state) dgEx_eqs (cfg_exit gEx, ())"
  using dgEx_terminates_c
  unfolding TD_side_always_join_Interp.term_equivalence TD_side_always_join_Interp.solve_c_dom_def
  by simp

lemma dgEx_pp_st:
  "part_post_solution dgEx_eqs (cfg_exit gEx, ()) (snd dgEx_sol) (fst dgEx_sol)"
  using TD_side_always_join_Interp.partial_post_solution[OF dgEx_solve_dom, of "fst dgEx_sol" "snd dgEx_sol"]
  unfolding dgEx_sol_def by simp

subsection \<open>Transport to the abstract post-solution\<close>

text \<open>
  The computed \<open>sign st\<close>-valued post-solution, mapped through \<open>fun_of_dg_st\<close>, is a
  post-solution of the abstract \<open>sign_dg.dg_gen\<close> --- unknown identities, \<open>vars\<close>, and
  dependencies unchanged.
\<close>

lemma dgEx_pp_abs:
  "part_post_solution (sign_dg.dg_gen gEx (fun_of_st (bot::sign st)) (fun_of_st cinit_sign_st) (fun_of_st cinit_sign_st))
     (cfg_exit gEx, ()) (fun_of_dg_st \<circ> snd dgEx_sol) (fst dgEx_sol)"
  using part_post_solution_dg_st_to_abs[OF sign_Hstep sign_Hcomb dgEx_pp_st[unfolded dgEx_eqs_def]]
  unfolding dg_gen_of_eq_sign_dg_gen .

subsection \<open>Collecting-semantics over-approximation from the computed result\<close>

lemma dgEx_cover_entry: "(cfg_entry gEx, ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def gEx_entry by eval
lemma dgEx_cover_1: "((1::pp), ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def by eval
lemma dgEx_cover_2: "((2::pp), ()) \<in> fst dgEx_sol"
  unfolding dgEx_sol_def by eval
lemma dgEx_cover_edge: "\<And>u a w. (u, a, w) \<in> edges gEx \<Longrightarrow> (w, ()) \<in> fst dgEx_sol"
  using dgEx_cover_1 dgEx_cover_2 by (auto simp: gEx_edges)
lemma dgEx_cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines gEx \<Longrightarrow> (w, ()) \<in> fst dgEx_sol"
  by (simp add: gEx_combines)
lemma dgEx_sound0: "cinit_stores \<subseteq> \<lbrakk>fun_of_st cinit_sign_st \<squnion> fun_of_st cinit_sign_st\<rbrakk>"
  by (simp add: fun_of_st_cinit_sign_st cinit_stores_def gamma_state_def sup.idem)

text \<open>
  \<^bold>\<open>The end-to-end theorem.\<close> Every concrete store reaching \<open>v\<close> in the
  interprocedural collecting semantics of the program is over-approximated by the
  native D/G concretization of the \<^emph>\<open>solver-computed\<close> solution.
\<close>

theorem dgEx_collect_sound:
  "cfg_collect gEx cinit_stores v \<subseteq> sign_dg_gamma (fun_of_dg_st \<circ> snd dgEx_sol) v"
  by (rule sign_dg_post_solution_collect_sound
        [OF dgEx_pp_abs[folded sign_dg_generator_def]
            dgEx_cover_entry dgEx_cover_edge dgEx_cover_combine gEx_finE gEx_no_enter gEx_finC dgEx_sound0])

subsection \<open>Inspecting the computed result\<close>

text \<open>
  The computed local and global slots at the exit, read back executably.  The naive
  diagonal Sign analysis merges the local and global halves at each edge, so it over-
  approximates to \<open>STop\<close> here --- sound, if imprecise; the retain / digest analyses
  recover per-slot precision.
\<close>

lemma dgEx_inspect:
  "map_option (\<lambda>sol. (lookup_st (locals (snd sol (Inl (2::pp, ())))) ''x'',
                       lookup_st (globs (snd sol (Inr ()))) ''x''))
     (TD_side_always_join_Interp_solve_c dgEx_eqs (cfg_exit gEx, ())) = Some (STop, STop)"
  by eval

end
