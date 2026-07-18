section \<open>Flagship: interval analysis of a counting loop, executed and certified on the D/G spine\<close>

text \<open>
  \<^bold>\<open>The complete story in one self-contained theory.\<close>  An IMP2 program (given inline
  below) is compiled to a CFG; the generic D/G framework generates an equation
  system; the \<^emph>\<open>verified\<close> top-down solver \<^emph>\<open>computes\<close> an interval solution inside
  Isabelle (with interval widening for termination); the computed solution is
  certified a partial post-solution by the solver's own correctness theorem; it is
  transported value-wise to the abstract D/G semantics; and the generic
  collecting-soundness theorem concludes that the computed abstraction
  over-approximates the concrete collecting semantics at every program point.

  \<^verbatim>\<open>
       IMP2 source
            |  compile_prog                          (section 2)
            v
          CFG
            |  dg_gen_of                              (section 4)
            v
    D/G equation system
            |  verified solver, by eval               (section 5)
            v
   computed interval solution  sigma
            |  solver correctness theorem             (section 6)
            v
    part_post_solution sigma
            |  part_post_solution_dg_st_to_abs        (section 7)
            v
   abstract post-solution
            |  ivl_dg_post_solution_collect_sound     (section 8)
            v
    cfg_collect subset gamma(sigma)   --- x in [0,20]  (section 9)
            |  compiler-correctness simulation        (section 10)
            v
   every IMP2 source run is bounded by sigma
  \<close>

  \<^bold>\<open>Every step is machine-checked, and the result is informative:\<close> the analysis
  discovers the loop invariant \<open>x in [0,20]\<close>, the body bound \<open>x in [0,19]\<close>, and the
  exact exit value \<open>x in [20,20]\<close> --- not \<open>top\<close>.  Section 10 lifts soundness from the
  collecting semantics to \<^emph>\<open>actual IMP2 source runs\<close> via the compiler-correctness
  simulation; section 11 exhibits an explicit reachable state so the guarantee is
  visibly \<^emph>\<open>not vacuous\<close>; section 12 emits an analysis-annotated GraphViz rendering.

  It reuses, without duplicating: the executable interval transfer \<open>ivl_tf_st\<close>
  (\<open>Ivl_Exec\<close>), the executable D/G bridge (\<open>Exec_DG_Bridge\<close>), the native interval
  D/G soundness endpoint (\<open>Interval_DG\<close>), the compiler-correctness simulation
  (\<open>Compiler_Correctness\<close>), and the vendored warrowing solver.
\<close>

theory Example_Interval_DG_Flagship
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Ivl_Exec"
    "Voblint_Analysis.Solver_Menu"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_IMP2.IMP2_Bridge"
    "Voblint_Formalization.Compiler_Correctness"
begin

no_notation Syntax.Assign (\<open>_ ::= _\<close> [1000, 61] 61)
hide_const (open) Syntax.N Syntax.V

subsection \<open>1. The program (inline IMP2 source)\<close>

text \<open>
  A bounded counting loop: initialise \<open>x\<close> to \<open>0\<close>, increment while \<open>x < 20\<close>.  On
  exit \<open>x = 20\<close>.  No procedures, no globals; \<open>x\<close> is a single flow-sensitive local.
  The analysis must \<^emph>\<open>discover\<close> the bound, not assume it.
\<close>

definition flagship_prog :: "IMP2_Proc.com" where
  "flagship_prog = imp \<lbrakk> x := 0; while (x < 20) { x := x + 1 } \<rbrakk>"

subsection \<open>2. CFG construction\<close>

text \<open>
  The source compiles to an interprocedural CFG by \<open>compile_prog\<close>.  Nodes:
  entry \<open>0\<close>, \<open>x := 0\<close> to \<open>1\<close>, loop head \<open>2\<close>, the guard \<open>x < 20\<close> to body \<open>3\<close> / exit
  \<open>5\<close>, increment \<open>x := x + 1\<close> to \<open>4\<close>, back-edge to \<open>2\<close>.  \<open>flagship_cfg_eq\<close> proves the
  compilation equals the explicit graph; the annotated rendering is in section 10.
\<close>

definition flagship_cfg :: cfg where
  "flagship_cfg = compile_prog Map.empty [] flagship_prog"

lemma flagship_cfg_eq:
  "flagship_cfg = mk_cfg 0 5
     {(0, EA_Assign ''x'' (BaseN (AExp.N 0)), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 3),
      (2, EA_AssumeNot (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 5),
      (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), 4),
      (4, EA_Nop, 2)}
     {}"
  unfolding flagship_cfg_def flagship_prog_def
  by (simp add: compile_eval_simps; blast)

lemma flagship_entry: "cfg_entry flagship_cfg = 0" by (simp add: flagship_cfg_eq mk_cfg_def)
lemma flagship_exit: "cfg_exit flagship_cfg = 5" by (simp add: flagship_cfg_eq mk_cfg_def)
lemma flagship_edges: "edges flagship_cfg =
     {(0, EA_Assign ''x'' (BaseN (AExp.N 0)), 1),
      (1, EA_Nop, 2),
      (2, EA_Assume (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 3),
      (2, EA_AssumeNot (Less (BaseN (AExp.V ''x'')) (BaseN (AExp.N 20))), 5),
      (3, EA_Assign ''x'' (Plus (BaseN (AExp.V ''x'')) (BaseN (AExp.N 1))), 4),
      (4, EA_Nop, 2)}"
  by (simp add: flagship_cfg_eq mk_cfg_def)
lemma flagship_combines: "combines flagship_cfg = {}" by (simp add: flagship_cfg_eq mk_cfg_def)

lemma flagship_finE: "finite (edges flagship_cfg)" by (simp add: flagship_edges)
lemma flagship_finC: "finite (combines flagship_cfg)" by (simp add: flagship_combines)

subsection \<open>3. The analysis specification (interval, as an executable D/G analysis)\<close>

text \<open>
  Intervals form the diagonal D/G analysis \<open>D = G = ivl abs_state\<close>.  Its executable
  mirror at \<open>ivl st\<close> is \<open>unit_dg_spec_st ivl_tf_st\<close> --- built generically by the
  bridge from the executable interval transfer \<open>ivl_tf_st\<close>.  The two transport
  obligations (step and combine commute with the abstract spec through
  \<open>fun_of_st\<close>) follow from the bridge's generic lemmas; only \<open>ivl_tf_st_commute\<close> is
  interval-specific --- the combine lemma is domain-agnostic.
\<close>

lemma ivl_Hstep:
  "map_prod fun_of_st fun_of_st (dg_spec_step (unit_dg_spec_st ivl_tf_st) a d g)
     = dg_spec_step (unit_dg_spec ivl_tf) a (fun_of_st d) (fun_of_st g)"
  by (simp add: dg_spec_step_unit_st dg_spec_step_unit unit_step_st_commute ivl_tf_st_commute)

lemma ivl_Hcomb:
  "map_prod fun_of_st fun_of_st (dgs_combine (unit_dg_spec_st ivl_tf_st) dst dc de g)
     = dgs_combine (unit_dg_spec ivl_tf) dst (fun_of_st dc) (fun_of_st de) (fun_of_st g)"
  by (simp add: unit_dg_spec_st_def unit_dg_spec_def unit_combine_step_st_commute)

text \<open>The executable generator's abstract image is exactly the native \<open>ivl_dg.dg_gen\<close>.\<close>

lemma dg_gen_of_eq_ivl_dg_gen:
  "dg_gen_of (unit_dg_spec ivl_tf) g bot0 s0d s0g = ivl_dg.dg_gen g bot0 s0d s0g"
proof -
  have "dg_cmb_of (unit_dg_spec ivl_tf) = ivl_dg.dg_cmb"
    by (rule ext)+ (simp add: dg_cmb_of_def ivl_dg.dg_cmb_def)
  thus ?thesis by (simp add: dg_gen_of_def ivl_dg.dg_gen_def)
qed

subsection \<open>4. Equation generation\<close>

text \<open>
  The generic D/G generator \<open>dg_gen_of\<close> turns the CFG into an equation system over
  unknowns \<open>(pp x unit) + unit\<close>, values in \<open>(ivl st, ivl st) dg_state\<close>.  Locals
  seed at \<open>cinit_ivl_st\<close> (globals \<open>[0,0]\<close>, locals \<open>top\<close>); the flow-insensitive
  global slot seeds at \<open>restrict_global_st cinit_ivl_st\<close> (bottom on locals, so it
  never pollutes the local \<open>x\<close> through the diagonal read).
\<close>

definition flagship_eqs :: "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (ivl st, ivl st) dg_state) strategy_tree" where
  "flagship_eqs = dg_gen_of (unit_dg_spec_st ivl_tf_st) flagship_cfg bot cinit_ivl_st (restrict_global_st cinit_ivl_st)"

subsection \<open>5. Executable solve\<close>

text \<open>
  The vendored \<open>TD_side_warrowing_apinis_Interp_solve_c\<close> --- pointwise interval
  widening on \<open>(ivl st, ivl st) dg_state\<close> for solver termination --- \<^emph>\<open>computes\<close> a
  solution.  Termination is a code-generated \<^verbatim>\<open>by eval\<close> fact; the solution is not
  written by hand.
\<close>

lemma flagship_terminates_c:
  "TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()) \<noteq> None"
  by eval

definition flagship_sol :: "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (ivl st, ivl st) dg_state)" where
  "flagship_sol = TD_side_warrowing_apinis_Interp_solve flagship_eqs (cfg_exit flagship_cfg, ())"

text \<open>The computed local interval for \<open>x\<close> at every node --- \<^emph>\<open>evaluated\<close>.\<close>

value "map_option
   (\<lambda>sol. map (\<lambda>p. (p, string_of_ivl (lookup_st (locals (snd sol (Inl (p, ())))) ''x''))) [0,1,2,3,4,5])
   (TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()))"

subsection \<open>6. Certified solution (reusing solver correctness)\<close>

text \<open>
  Termination gives the solver-domain predicate, and the vendored solver's
  \<^emph>\<open>correctness theorem\<close> \<open>TD_side_warrowing_apinis_Interp.partial_post_solution\<close>
  turns the computed result into a partial post-solution.  \<^bold>\<open>The equations are not
  re-checked\<close> --- solver correctness is reused.
\<close>

lemma flagship_solve_dom:
  "TD_side_warrowing_apinis_Interp.solve_dom TYPE(unit) TYPE((ivl st, ivl st) dg_state)
     flagship_eqs (cfg_exit flagship_cfg, ())"
  using flagship_terminates_c
  unfolding TD_side_warrowing_apinis_Interp.term_equivalence
            TD_side_warrowing_apinis_Interp.solve_c_dom_def
  by simp

lemma flagship_pp_st:
  "part_post_solution flagship_eqs (cfg_exit flagship_cfg, ()) (snd flagship_sol) (fst flagship_sol)"
  using TD_side_warrowing_apinis_Interp.partial_post_solution
          [OF flagship_solve_dom, of "fst flagship_sol" "snd flagship_sol"]
  unfolding flagship_sol_def by simp

subsection \<open>7. Transport to the abstract D/G semantics\<close>

text \<open>
  The bridge theorem \<open>part_post_solution_dg_st_to_abs\<close> maps the computed \<open>ivl st\<close>-valued
  post-solution through \<open>fun_of_dg_st\<close> to a post-solution of the abstract
  \<open>ivl_dg.dg_gen\<close> --- unknowns, \<open>vars\<close>, and dependencies unchanged, only values
  transported.
\<close>

lemma flagship_pp_abs:
  "part_post_solution
     (ivl_dg.dg_gen flagship_cfg (fun_of_st (bot::ivl st)) (fun_of_st cinit_ivl_st)
        (fun_of_st (restrict_global_st cinit_ivl_st)))
     (cfg_exit flagship_cfg, ()) (fun_of_dg_st \<circ> snd flagship_sol) (fst flagship_sol)"
  using part_post_solution_dg_st_to_abs[OF ivl_Hstep ivl_Hcomb flagship_pp_st[unfolded flagship_eqs_def]]
  unfolding dg_gen_of_eq_ivl_dg_gen .

subsection \<open>8. Soundness: the computed analysis over-approximates the collecting semantics\<close>

text \<open>
  The premises of the generic native endpoint \<open>ivl_dg_post_solution_collect_sound\<close>:
  every program point is covered by the solved variable set (\<^verbatim>\<open>by eval\<close>), the graph
  is finite and enter-free, and the concrete initial stores are covered by the seed.
\<close>

lemma flagship_cover_all: "\<forall>v \<in> {0,1,2,3,4,5}. ((v::pp), ()) \<in> fst flagship_sol"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_cover_entry: "(cfg_entry flagship_cfg, ()) \<in> fst flagship_sol"
  using flagship_cover_all flagship_entry by simp
lemma flagship_cover_edge: "\<And>u a w. (u, a, w) \<in> edges flagship_cfg \<Longrightarrow> (w, ()) \<in> fst flagship_sol"
  using flagship_cover_all by (auto simp: flagship_edges)
lemma flagship_cover_combine: "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines flagship_cfg \<Longrightarrow> (w, ()) \<in> fst flagship_sol"
  by (simp add: flagship_combines)

lemma flagship_sound0:
  "cinit_stores \<subseteq> \<lbrakk>fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st)\<rbrakk>"
proof -
  have "fun_of_st cinit_ivl_st \<squnion> fun_of_st (restrict_global_st cinit_ivl_st) = fun_of_st cinit_ivl_st"
    by (simp add: fun_of_st_cinit_ivl_st fun_of_st_restrict_global_st restrict_global_def sup_fun_def fun_eq_iff)
  thus ?thesis
    by (auto simp: cinit_stores_def gamma_state_def fun_of_st_cinit_ivl_st)
qed

text \<open>
  \<^bold>\<open>The end-to-end theorem.\<close>  Every concrete store reaching any program point \<open>v\<close> in
  the collecting semantics of \<open>flagship_cfg\<close> is contained in the native D/G
  concretization of the \<^emph>\<open>solver-computed\<close> solution \<open>snd flagship_sol\<close>.
\<close>

theorem flagship_collect_sound:
  "cfg_collect flagship_cfg cinit_stores v \<subseteq> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
  by (rule ivl_dg_post_solution_collect_sound
        [OF flagship_pp_abs[folded ivl_dg_generator_def]
            flagship_cover_entry flagship_cover_edge flagship_cover_combine
            flagship_finE flagship_finC flagship_sound0])

subsection \<open>9. Inspecting the certified result\<close>

text \<open>
  The computed local interval for \<open>x\<close> at the interesting points, on the \<^emph>\<open>same\<close>
  solution the soundness theorem certifies:

    \<^item> loop head (node \<open>2\<close>): \<open>x in [0,20]\<close> --- the loop invariant.
    \<^item> body entry (node \<open>3\<close>): \<open>x in [0,19]\<close> --- the guard \<open>x < 20\<close> refines the upper bound.
    \<^item> exit (node \<open>5\<close>): \<open>x in [20,20]\<close> --- the negated guard fixes \<open>x = 20\<close> exactly.

  With \<open>flagship_collect_sound\<close>, these are sound bounds on every reaching concrete
  store, computed by the verified solver.
\<close>

lemma flagship_head_computed:
  "lookup_st (locals (snd flagship_sol (Inl (2::pp, ())))) ''x'' = Ivl (Fin 0) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_body_computed:
  "lookup_st (locals (snd flagship_sol (Inl (3::pp, ())))) ''x'' = Ivl (Fin 0) (Fin 19)"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma flagship_exit_computed:
  "lookup_st (locals (snd flagship_sol (Inl (5::pp, ())))) ''x'' = Ivl (Fin 20) (Fin 20)"
  unfolding flagship_sol_def flagship_eqs_def by eval

subsection \<open>10. Lifting soundness to IMP2 source runs (compiler correctness)\<close>

text \<open>
  Sections 1--9 bound the \<^emph>\<open>collecting semantics\<close> of the compiled CFG.  The
  compiler-correctness simulation (\<open>Compiler_Correctness\<close>) closes the
  last gap to the source: every terminating-or-partial IMP2 small-step run
  (\<open>psteps\<close>) of the program is reproduced on the compiled CFG, so the concrete
  state it reaches lands in \<open>cfg_collect\<close> --- and therefore, by
  \<open>flagship_collect_sound\<close>, inside the solver-computed interval solution.

  The program is well-formed compiler input, and the simulation locale
  \<open>compiled_source_simulation\<close> interprets for it directly.
\<close>

lemma flagship_wf: "wf_compile_input Map.empty [] flagship_prog"
  unfolding wf_compile_input_def flagship_prog_def
  by (simp add: compile_eval_simps source_pi_def)

interpretation flagship_sim: compiled_source_simulation
    "Map.empty" "[]" flagship_prog flagship_cfg
    "concrete_program_match Map.empty [] flagship_prog"
proof
  show "flagship_cfg = compile_prog Map.empty [] flagship_prog"
    by (simp add: flagship_cfg_def)
  show "wf_compile_input Map.empty [] flagship_prog" by (rule flagship_wf)
  fix s
  show "concrete_program_match Map.empty [] flagship_prog (flagship_prog, s, []) (cfg_entry flagship_cfg, s, [])"
    using flagship_wf unfolding wf_compile_input_def
    by (simp add: flagship_cfg_def concrete_program_initial_match)
next
  fix src src' cf
  assume m: "concrete_program_match Map.empty [] flagship_prog src cf"
     and st: "pstep Map.empty src src'"
  show "\<exists>cf'. star (cstep flagship_cfg) cf cf' \<and> concrete_program_match Map.empty [] flagship_prog src' cf'"
    using concrete_program_step_match[OF flagship_wf m st] by (simp add: flagship_cfg_def)
qed

text \<open>
  \<^bold>\<open>The source-level capstone.\<close>  For any IMP2 run of \<open>flagship_prog\<close> from a
  C-faithful initial store (globals zero), whatever configuration \<open>src'\<close> it
  reaches matches a CFG point \<open>(v, t, stk)\<close> at which the concrete store \<open>t\<close> is
  contained in the concretization of the \<^emph>\<open>solver-computed\<close> interval solution.
  This is soundness against the real source semantics, not merely the CFG.
\<close>

theorem flagship_source_run_sound:
  assumes run: "psteps Map.empty (flagship_prog, s, []) src'"
      and init: "s \<in> cinit_stores"
  shows "\<exists>v t stk. concrete_program_match Map.empty [] flagship_prog src' (v, t, stk)
                   \<and> t \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
proof -
  obtain v t stk where m: "concrete_program_match Map.empty [] flagship_prog src' (v, t, stk)"
      and coll: "t \<in> cfg_collect flagship_cfg {s} v"
    using flagship_sim.source_reaches_cfg_collect[OF run] by blast
  have "cfg_collect flagship_cfg {s} v \<subseteq> cfg_collect flagship_cfg cinit_stores v"
    using init by (intro le_funD[OF cfg_collect_mono_S]) auto
  also have "\<dots> \<subseteq> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) v"
    by (rule flagship_collect_sound)
  finally show ?thesis using m coll by blast
qed

subsection \<open>11. Non-vacuity: an explicit reachable witness\<close>

text \<open>
  Sections 8--10 are inclusions and implications --- worth checking they are not
  vacuous.  We exhibit a concrete store that genuinely reaches the loop head, so
  the collecting set there is inhabited and the soundness conclusion applies to a
  real reachable state; and we show the computed bound is a \<^emph>\<open>proper\<close> constraint
  (it rejects \<open>x = 100\<close>), so soundness is not trivially \<open>top\<close>.

  The all-zero store is C-faithful, and an explicit two-edge trace
  (\<open>x := 0\<close> then the loop-head \<open>nop\<close>) carries it from the entry to the loop head
  inside \<open>cfg_collect\<close>.
\<close>

definition wit_store :: store where "wit_store = (\<lambda>_. 0)"

lemma wit_cinit: "wit_store \<in> cinit_stores"
  by (simp add: wit_store_def cinit_stores_def)

lemma wit_entry: "wit_store \<in> cfg_collect flagship_cfg cinit_stores (cfg_entry flagship_cfg)"
  using cfg_collect_entry wit_cinit by blast

lemma wit_ec:
  "wit_store \<in> edge_collect (EA_Assign ''x'' (BaseN (AExp.N 0))) (cfg_collect flagship_cfg cinit_stores 0)"
proof (subst edge_collect.simps(2), rule CollectI, rule exI[of _ wit_store], intro conjI)
  show "wit_store = wit_store(''x'' := IMP2_Expr.aval (BaseN (AExp.N 0)) wit_store)"
    by (simp add: wit_store_def fun_upd_idem)
  show "wit_store \<in> cfg_collect flagship_cfg cinit_stores 0"
    using wit_entry unfolding flagship_entry .
qed

lemma wit_at_1: "wit_store \<in> cfg_collect flagship_cfg cinit_stores 1"
proof -
  have e: "(0, EA_Assign ''x'' (BaseN (AExp.N 0)), 1) \<in> edges flagship_cfg" by (simp add: flagship_edges)
  have "wit_store \<in> collect_pp flagship_cfg (cfg_collect flagship_cfg cinit_stores) 1"
    unfolding collect_pp_def using wit_ec e by blast
  hence "wit_store \<in> cfg_collect_F flagship_cfg cinit_stores (cfg_collect flagship_cfg cinit_stores) 1"
    unfolding cfg_collect_F_def by blast
  thus ?thesis using cfg_collect_post by blast
qed

lemma wit_at_2: "wit_store \<in> cfg_collect flagship_cfg cinit_stores 2"
proof -
  have e: "(1, EA_Nop, 2) \<in> edges flagship_cfg" by (simp add: flagship_edges)
  have ec: "wit_store \<in> edge_collect EA_Nop (cfg_collect flagship_cfg cinit_stores 1)"
    using wit_at_1 by simp
  have "wit_store \<in> collect_pp flagship_cfg (cfg_collect flagship_cfg cinit_stores) 2"
    unfolding collect_pp_def using ec e by blast
  hence "wit_store \<in> cfg_collect_F flagship_cfg cinit_stores (cfg_collect flagship_cfg cinit_stores) 2"
    unfolding cfg_collect_F_def by blast
  thus ?thesis using cfg_collect_post by blast
qed

text \<open>
  \<^bold>\<open>The witness is reachable and satisfies the computed bound.\<close>  The all-zero store
  reaches the loop head, lands in the concretization of the computed interval
  solution there, and indeed has \<open>x = 0 in [0,20]\<close> --- so
  \<open>flagship_collect_sound\<close> is a statement about a genuinely inhabited set.
\<close>

theorem flagship_witness_reachable_and_bounded:
  "wit_store \<in> cfg_collect flagship_cfg cinit_stores 2
   \<and> wit_store \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) 2
   \<and> wit_store ''x'' = 0"
proof (intro conjI)
  show "wit_store \<in> cfg_collect flagship_cfg cinit_stores 2" by (rule wit_at_2)
  show "wit_store \<in> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) 2"
    using flagship_collect_sound wit_at_2 by blast
  show "wit_store ''x'' = 0" by (simp add: wit_store_def)
qed

text \<open>
  \<^bold>\<open>The bound is proper.\<close>  The global slot carries no local information
  (\<open>glob_x_at_2\<close>), so the loop-head concretization constrains \<open>x\<close> to exactly
  \<open>[0,20]\<close> and rejects, e.g., a store with \<open>x = 100\<close>.  The guarantee therefore says
  something --- it is not the trivial \<open>gamma top = UNIV\<close>.
\<close>

lemma glob_x_at_2: "lookup_st (globs (snd flagship_sol (Inr ()))) ''x'' = bot"
  unfolding flagship_sol_def flagship_eqs_def by eval

lemma head_x_bound:
  "(locals ((fun_of_dg_st \<circ> snd flagship_sol) (Inl (2, ())))
    \<squnion> globs ((fun_of_dg_st \<circ> snd flagship_sol) (Inr ()))) ''x'' = Ivl (Fin 0) (Fin 20)"
proof -
  have L: "fun_of_st (locals (snd flagship_sol (Inl (2, ())))) ''x'' = Ivl (Fin 0) (Fin 20)"
    using flagship_head_computed by simp
  have G: "fun_of_st (globs (snd flagship_sol (Inr ()))) ''x'' = bot" by (rule glob_x_at_2)
  show ?thesis by (simp add: fun_of_dg_st_simps sup_fun_def L G)
qed

theorem flagship_head_bound_proper:
  "(\<lambda>_. 100) \<notin> ivl_dg_gamma (fun_of_dg_st \<circ> snd flagship_sol) 2"
  unfolding ivl_dg_gamma_def ivl_dg.dg_gamma_def gamma_unit_def gamma_state_def
            ivl_dg.dg_D_def ivl_dg.dg_G_def
  apply (simp only: mem_Collect_eq not_all)
  apply (rule exI[of _ "''x''"])
  using head_x_bound apply (simp add: fun_of_dg_st_simps sup_fun_def)
  done

subsection \<open>12. Annotated GraphViz of the computed result\<close>

text \<open>
  A DOT rendering of \<open>flagship_cfg\<close> with each node annotated by the computed
  interval for \<open>x\<close>.  The \<^verbatim>\<open>ML_val\<close> below prints the DOT as a plain string; paste
  it into any GraphViz renderer (\<^verbatim>\<open>dot -Tpng\<close>) to view the analysed loop, each
  node labelled with the loop-invariant interval the verified solver computed.
\<close>

definition flagship_graph_config ::
  "(unit, unit, (ivl st, ivl st) dg_state, ivl st) analysis_graph_config" where
  "flagship_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        scope_locals (compiled_procedure_scope Map.empty [] flagship_prog
          flagship_cfg p)),
      return_slot_for_pp = (\<lambda>p.
        scope_return_slot (compiled_procedure_scope Map.empty [] flagship_prog
          flagship_cfg p)),
      globals_to_show = [],
      show_local = (\<lambda>_ _ vars d. map (\<lambda>x.
        x @ ''='' @ string_of_ivl (lookup_st d x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ _ _. [''(none)'']),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''main / root context''),
      source_text = Some (string_of_program Map.empty [] flagship_prog)
    \<rparr>"

definition flagship_graph_domain :: "(pp \<times> unit + unit) list" where
  "flagship_graph_domain =
    contextual_graph_domain flagship_cfg (\<lambda>_. [()])"

definition flagship_dot :: String.literal where
  "flagship_dot =
     String.implode
       (case TD_side_warrowing_apinis_Interp_solve_c flagship_eqs (cfg_exit flagship_cfg, ()) of
          None \<Rightarrow> ''solver did not terminate''
        | Some sol \<Rightarrow> contextual_analysis_dot flagship_graph_config flagship_cfg
            flagship_graph_domain (snd sol))"

ML_val \<open>writeln (@{code flagship_dot})\<close>


end
