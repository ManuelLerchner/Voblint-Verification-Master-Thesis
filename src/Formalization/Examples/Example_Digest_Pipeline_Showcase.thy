theory Example_Digest_Pipeline_Showcase
  imports "Voblint_Analysis.Exec_Sign_Mode_Compiled_Run"
begin

section \<open>The context-sensitive digest analysis, end to end\<close>

text \<open>
  One small program carried through the whole executable pipeline:

  \<^verbatim>\<open>source -> CFG -> equation system -> strategy tree -> solver -> solution
         -> digest projection -> annotated CFG -> GraphViz -> soundness\<close>

  Every box below is an executable \<^theory_text>\<open>value\<close> on the real artifacts, or a theorem
  discharged against the solver's own output.  Nothing is hand-computed.  The generic
  digest kernel (\<^theory>\<open>Voblint_Analysis.Digest_Global_Read\<close>), the digest writer, the
  vendored side-effecting TD solver, and the transport theorem are all reused unchanged;
  this theory only instantiates them on a program and reads the results back.
\<close>


subsection \<open>1. Source program\<close>

text \<open>
  \<open>main\<close> runs a two-way configuration: it sets a ghost local \<open>mode\<close> and the global \<open>Gval\<close>,
  calls the same procedure \<open>step\<close> once per mode, and in each case branches on the mode and
  computes a result.  \<open>mode\<close>, \<open>r1\<close>, \<open>r2\<close>, \<open>t\<close> are locals; \<open>G\<close>-prefixed \<open>Gval\<close> is the one
  global (Goblint's naming: a name is global iff it starts with \<open>G\<close>).
\<close>

definition demo_prog :: imp_prog where
  "demo_prog = \<lbrakk>
     int Gval;

     void step() {
       t := Gval
     }
     void main() {
       mode := 0;  Gval := 0;  step();
       if (0 < mode) { r1 := mode + mode } else { r1 := mode - 1 };
       mode := 1;  Gval := 1;  step();
       if (0 < mode) { r2 := mode + mode } else { r2 := mode - 1 }
     }
   \<rbrakk>"

value "prog_procs demo_prog"
value "prog_main demo_prog"


subsection \<open>2. Compilation\<close>

text \<open>The pipeline compiles the program to an interprocedural CFG.  \<open>step\<close> is compiled
  first (program points \<open>0\<close>, \<open>1\<close>); \<open>main\<close> is the rest.  An \<^const>\<open>EA_Enter\<close> edge is a
  call; each \<^emph>\<open>combine\<close> triple \<open>(call, exit, return)\<close> is the matching return.\<close>

definition demo_cfg :: cfg where
  "demo_cfg = compile_prog (prog_table demo_prog) (prog_procs demo_prog) (prog_main demo_prog)"

value "cfg_entry demo_cfg"
value "cfg_exit demo_cfg"
value "sorted_list_of_set (nodes demo_cfg)"
value "cfg_edges_list demo_cfg"
value "cfg_combines_list demo_cfg"


subsection \<open>3. Equation system\<close>

text \<open>
  The context is not chosen by hand: \<^const>\<open>mode_ec\<close> reads the caller's ghost \<open>''mode''\<close>
  and decodes it to a finite \<^typ>\<open>mode\<close> --- Goblint's \<open>context : D.t \<rightarrow> C.t\<close>.  The digest
  writer \<^const>\<open>side_cfg_T_eff_digest_st\<close> keys each global write by \<^const>\<open>mode_dg\<close> of its
  write-point state (Goblint's \<open>sideg (G, Digest.compute d)\<close>).  Together they turn the CFG
  into one equation per unknown \<open>(program point, context)\<close>; the right-hand side of each
  equation is a TD-side \<^emph>\<open>strategy tree\<close> of global/local reads ending in an answer.
\<close>

definition demo_eqs :: "(pp \<times> mode, mode, sign st) eqsT" where
  "demo_eqs = side_cfg_T_eff_digest_st mode_dg
                (\<lambda>c cc ex. switching_combine_digest_st mode_dg mode_prep cc ex c)
                demo_cfg sign_etf_st bot bot cinit_sign_st"


subsection \<open>4. Solver\<close>

text \<open>The reusable vendored side-effecting TD solver runs the equation system to a
  post-fixpoint.  \<^const>\<open>fst\<close> is the set of solved unknowns; \<^const>\<open>snd\<close> the assignment.
  \<open>step\<close>'s body \<open>(0, 1)\<close> is solved under \<^emph>\<open>both\<close> contexts \<^term>\<open>MZero\<close> and \<^term>\<open>MOne\<close>:
  the projection context generated one activation per mode automatically.\<close>

definition demo_solution ::
  "(pp \<times> mode) set \<times> ((pp \<times> mode) + mode \<Rightarrow> sign st)" where
  "demo_solution = TD_side_always_join_Interp_solve demo_eqs (cfg_exit demo_cfg, MZero)"

value "fst demo_solution"

text \<open>The equation at \<open>pp7\<close>, evaluated against the solution, is satisfied --- the solver
  output is a genuine fixpoint of the compiled system, not a hand-written table.\<close>
value "traverse_rhs (demo_eqs (7, MZero)) (snd demo_solution)"


subsection \<open>5. Queries\<close>

text \<open>What the analysis discovered.  The global \<open>Gval\<close> is split into two finite digest
  partitions --- \<^term>\<open>Inr MZero\<close> holds the mode-0 write, \<^term>\<open>Inr MOne\<close> the mode-1 write
  --- where a context-blind analysis would join them to \<^const>\<open>SNonNeg\<close>.\<close>

value "lookup_st (snd demo_solution (Inr MZero)) ''Gval''"          \<comment> \<open>SZero\<close>
value "lookup_st (snd demo_solution (Inr MOne)) ''Gval''"           \<comment> \<open>SPos\<close>
value "lookup_st (snd demo_solution (Inr MZero) \<squnion> snd demo_solution (Inr MOne)) ''Gval''"
                                                                    \<comment> \<open>SNonNeg (the loss avoided)\<close>

text \<open>The mode-dependent branch resolves per context: with \<open>mode = 0\<close> the guard \<open>0 < mode\<close>
  fails and the result is \<^const>\<open>SNeg\<close>; with \<open>mode = 1\<close> it holds and the result is
  \<^const>\<open>SPos\<close>.  The final results are read off the solved exit node.\<close>

value "lookup_st (snd demo_solution (Inl (7, MZero))) ''mode''"      \<comment> \<open>SZero at the first branch\<close>
value "lookup_st (snd demo_solution (Inl (cfg_exit demo_cfg, MZero))) ''r1''"  \<comment> \<open>SNeg\<close>
value "lookup_st (snd demo_solution (Inl (cfg_exit demo_cfg, MZero))) ''r2''"  \<comment> \<open>SPos\<close>

theorem demo_results_are_mode_separated:
  "lookup_st (snd demo_solution (Inl (cfg_exit demo_cfg, MZero))) ''r1'' = SNeg
   \<and> lookup_st (snd demo_solution (Inl (cfg_exit demo_cfg, MZero))) ''r2'' = SPos
   \<and> lookup_st (snd demo_solution (Inr MZero)) ''Gval'' = SZero
   \<and> lookup_st (snd demo_solution (Inr MOne)) ''Gval'' = SPos"
  unfolding demo_solution_def demo_eqs_def demo_cfg_def mode_prep_def mode_dg_def by eval


subsection \<open>6. Automatic digest projection\<close>

text \<open>
  The digest is not a second analysis and not a second fixpoint: it is \<^const>\<open>mode_dg\<close>,
  a projection of the abstract value state the solver already computed --- decode the
  ghost \<open>''mode''\<close> to a finite key.  Read off the solved states, it tracks the flow-sensitive
  mode: \<^term>\<open>MZero\<close> in the first half, \<^term>\<open>MOne\<close> after \<open>mode := 1\<close>.
\<close>

value "mode_dg (snd demo_solution (Inl (7, MZero)))"    \<comment> \<open>MZero\<close>
value "mode_dg (snd demo_solution (Inl (18, MZero)))"   \<comment> \<open>MOne\<close>


subsection \<open>7. Annotated CFG and GraphViz\<close>

text \<open>
  The solved run rendered as a CFG with three activation clusters --- \<open>main\<close> once,
  \<open>step @ MZero\<close>, \<open>step @ MOne\<close>.  Each node carries its solved abstract state; each cluster
  its own global partition box.  The two calls are routed by the digest \<^emph>\<open>computed from the
  solution\<close> via \<open>d_call_ctx\<close>: the mode-0 call enters \<open>step @ MZero\<close>, the mode-1 call
  enters \<open>step @ MOne\<close>, both returning into \<open>main\<close>.  Nothing here is annotated by hand.
\<close>

datatype dctx = DMain | DstepZero | DstepOne

definition dctx_mode :: "dctx \<Rightarrow> mode" where
  "dctx_mode r = (case r of DMain \<Rightarrow> MZero | DstepZero \<Rightarrow> MZero | DstepOne \<Rightarrow> MOne)"

definition dctx_key :: "dctx \<Rightarrow> string" where
  "dctx_key r = (case r of DMain \<Rightarrow> ''main'' | DstepZero \<Rightarrow> ''stepMZero'' | DstepOne \<Rightarrow> ''stepMOne'')"

definition dctx_label :: "dctx \<Rightarrow> string" where
  "dctx_label r = (case r of DMain \<Rightarrow> ''main'' | DstepZero \<Rightarrow> ''step @ MZero'' | DstepOne \<Rightarrow> ''step @ MOne'')"

definition step_pps :: "pp list" where "step_pps = [0, 1]"

definition d_call_ctx :: "pp \<Rightarrow> mode" where
  "d_call_ctx cc = mode_dg (snd demo_solution (Inl (cc, MZero)))"

definition d_rctx_of :: "pp \<Rightarrow> dctx" where
  "d_rctx_of cc = (if d_call_ctx cc = MZero then DstepZero else DstepOne)"

text \<open>Each \<open>step\<close> node's read \<open>t := Gval\<close> is shown context-served (the value of the
  cluster's own \<open>Gval\<close> partition): the callee's ghost is reset on entry, so the digest rides
  the context, not the reset local.\<close>
definition d_node_label :: "pp \<times> dctx \<Rightarrow> string" where
  "d_node_label pk =
     (case pk of (p, r) \<Rightarrow>
        let s = snd demo_solution (Inl (p, dctx_mode r)) in
        (case r of
           DMain \<Rightarrow>
             ''pp'' @ string_of_nat p @ gv_nl @
             ''mode='' @ show_val (lookup_st s ''mode'') @
             ''  r1='' @ show_val (lookup_st s ''r1'') @
             ''  r2='' @ show_val (lookup_st s ''r2'')
         | _ \<Rightarrow>
             ''pp'' @ string_of_nat p @ gv_nl @
             ''t='' @ show_val (lookup_st (snd demo_solution (Inr (dctx_mode r))) ''Gval'')))"

definition d_globals :: "dctx \<Rightarrow> string" where
  "d_globals r =
     (case r of
        DMain \<Rightarrow> ''Gval@MZero='' @ show_val (lookup_st (snd demo_solution (Inr MZero)) ''Gval'')
                 @ ''  Gval@MOne='' @ show_val (lookup_st (snd demo_solution (Inr MOne)) ''Gval'')
      | _ \<Rightarrow> ''Gval = '' @ show_val (lookup_st (snd demo_solution (Inr (dctx_mode r))) ''Gval''))"

definition d_nodes :: "(pp \<times> dctx) list" where
  "d_nodes =
     map (\<lambda>p. (p, DMain)) (filter (\<lambda>p. p \<notin> set step_pps) (sorted_list_of_set (nodes demo_cfg)))
   @ map (\<lambda>p. (p, DstepZero)) step_pps
   @ map (\<lambda>p. (p, DstepOne)) step_pps"

definition d_intra :: "((pp \<times> dctx) \<times> edge_action \<times> (pp \<times> dctx)) list" where
  "d_intra =
     [((u, DMain), a, (v, DMain)). (u, a, v) \<leftarrow> cfg_edges_list demo_cfg,
        a \<noteq> EA_Enter, u \<notin> set step_pps, v \<notin> set step_pps]
   @ [((u, r), a, (v, r)). (u, a, v) \<leftarrow> cfg_edges_list demo_cfg,
        u \<in> set step_pps, v \<in> set step_pps, r \<leftarrow> [DstepZero, DstepOne]]"

definition d_calls :: "((pp \<times> dctx) \<times> (pp \<times> dctx)) list" where
  "d_calls =
     [((u, DMain), (v, d_rctx_of u)). (u, a, v) \<leftarrow> cfg_edges_list demo_cfg, a = EA_Enter]"

definition d_returns :: "((pp \<times> dctx) \<times> (pp \<times> pp \<times> pp) \<times> (pp \<times> dctx)) list" where
  "d_returns =
     [((ex, d_rctx_of cc), (cc, ex, ret), (ret, DMain)). (cc, ex, ret) \<leftarrow> cfg_combines_list demo_cfg]"

definition demo_dot :: string where
  "demo_dot =
     ctx_debug_graphviz_with_globals
       dctx_key dctx_label d_globals d_node_label (\<lambda>_. ''shape=box'')
       [DMain, DstepZero, DstepOne]
       d_nodes d_intra d_calls d_returns"

definition demo_dot_lit :: String.literal where
  "demo_dot_lit = String.implode demo_dot"

text \<open>Paste the emitted DOT into any Graphviz renderer.\<close>
ML_val \<open>writeln (@{code demo_dot_lit})\<close>


subsection \<open>8. Soundness\<close>

text \<open>
  The essential theorem.  The executable solver output is a genuine
  \<^const>\<open>part_post_solution\<close> of the digest equation system, and it \<^emph>\<open>transports\<close> --- through
  the reused generic bridge, without touching the kernel --- to a post-solution of the
  \<^emph>\<open>abstract\<close> digest generator \<^const>\<open>side_cfg_T_eff_digest\<close> that the collecting-soundness
  theorem quantifies over.  So the run the solver computes is a certified over-approximation
  target, not a hand-built witness.
\<close>

lemma demo_solve_c_some:
  "TD_side_always_join_Interp_solve_c demo_eqs (cfg_exit demo_cfg, MZero) \<noteq> None"
  unfolding demo_eqs_def demo_cfg_def mode_prep_def mode_dg_def by eval

lemma demo_solve_dom:
  "TD_side_always_join_Interp.solve_dom TYPE(mode) TYPE(sign st)
     demo_eqs (cfg_exit demo_cfg, MZero)"
  unfolding TD_side_always_join_Interp.term_equivalence
            TD_side_always_join_Interp.solve_c_dom_def
  using demo_solve_c_some by simp

lemma demo_part_post_solution_st:
  "part_post_solution demo_eqs (cfg_exit demo_cfg, MZero)
     (snd demo_solution) (fst demo_solution)"
  using TD_side_always_join_Interp.partial_post_solution
      [OF demo_solve_dom, of "fst demo_solution" "snd demo_solution"]
  unfolding demo_solution_def by simp

theorem demo_abstracts:
  "part_post_solution
     (side_cfg_T_eff_digest mode_dg_abs
        (\<lambda>ctx cc ex. abs_switching_combine_digest mode_dg_abs mode_prep_abs cc ex ctx)
        demo_cfg sign_etf_unit (fun_of_st bot) (fun_of_st bot) (fun_of_st cinit_sign_st))
     (cfg_exit demo_cfg, MZero)
     (\<lambda>k. fun_of_st (snd demo_solution k)) (fst demo_solution)"
proof -
  have pp_st: "part_post_solution
       (side_cfg_T_eff_digest_st mode_dg
          (\<lambda>ctx cc ex. switching_combine_digest_st mode_dg mode_prep cc ex ctx)
          demo_cfg sign_etf_st bot bot cinit_sign_st) (cfg_exit demo_cfg, MZero)
       (snd demo_solution) (fst demo_solution)"
    using demo_part_post_solution_st unfolding demo_eqs_def by simp
  show ?thesis
    by (rule part_post_solution_digest_switching_st_to_abs_eff_unit_transfer
          [OF sign_etf_unit_edge_tree sign_etf_unit_combine_tree
              sign_etf_st_edge_tree sign_etf_st_combine_tree sign_tf_st_commute
              mode_prep_commute mode_dg_compat pp_st])
qed

text \<open>
  The read side and its boundary are the same as for the underlying digest run: the
  projection reader \<^const>\<open>mode_obs\<close> is certified against the context read exactly where the
  ghost is set (the mode-setting frame), and its single kernel premise \<open>MODE_AGREE\<close> is
  machine-checked \<^emph>\<open>false\<close> at callee interiors --- Goblint's frame-locality, a proven boundary
  rather than a gap.  See \<^theory>\<open>Voblint_Analysis.Exec_Sign_Mode_Compiled_Run\<close> and
  \<open>docs/DIGEST_TWO_FAMILIES.md\<close>.
\<close>

end

