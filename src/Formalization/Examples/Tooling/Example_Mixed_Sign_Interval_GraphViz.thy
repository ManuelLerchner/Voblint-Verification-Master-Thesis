section \<open>Example: flow-sensitive Sign answers and a shared Interval invariant\<close>

theory Example_Mixed_Sign_Interval_GraphViz
  imports
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Analysis.Analysis_GraphViz"
begin

text \<open>
  The program compiles through the ordinary IMP2-to-CFG pipeline.  The variable
  @{text "''x''"} is local according to @{const is_global}.  Per-point answer
  unknowns carry Sign stores, while the single side unknown carries an Interval
  store chosen by this analysis.  The side slot is called @{const globs} by the
  generic routing layer, but it is not an IMP2 global-variable store.

  Starting from @{text "x = 0"}, execution visits @{text "x = -1"} and finishes
  at @{text "x = 2"}.  The exit Sign answer is therefore positive.  The shared
  Interval invariant joins all three values and is @{text "[-1, 2]"}.  The DOT
  rendering displays the flow-sensitive Sign answers at CFG nodes and the
  flow-insensitive Interval invariant in a separate cluster.
\<close>

definition mixed_graphviz_prog :: com where
  "mixed_graphviz_prog = \<lbrakk> x := -1; x := 2 \<rbrakk>"

definition mixed_graphviz_cfg :: cfg where
  "mixed_graphviz_cfg =
     compile_prog (\<lambda>_. None) [] mixed_graphviz_prog"

definition mixed_graphviz_eqs ::
  "(pp \<times> unit, unit, (sign st, ivl st) dg_state) eqsT"
where
  "mixed_graphviz_eqs =
     mixed_si_generator_st mixed_graphviz_cfg bot
       mixed_si_example_sign_seed mixed_si_example_ivl_seed"

definition mixed_graphviz_result ::
  "(pp \<times> unit) set \<times>
   (pp \<times> unit + unit \<Rightarrow> (sign st, ivl st) dg_state)"
where
  "mixed_graphviz_result =
     TD_side_always_join_Interp_solve mixed_graphviz_eqs
       (cfg_exit mixed_graphviz_cfg, ())"

definition mixed_graphviz_solution ::
  "pp \<times> unit + unit \<Rightarrow> (sign st, ivl st) dg_state"
where
  "mixed_graphviz_solution = snd mixed_graphviz_result"

lemma mixed_graphviz_terminates:
  "TD_side_always_join_Interp_solve_c mixed_graphviz_eqs
     (cfg_exit mixed_graphviz_cfg, ()) \<noteq> None"
  by eval

lemma mixed_graphviz_part_post_solution:
  "part_post_solution mixed_graphviz_eqs
     (cfg_exit mixed_graphviz_cfg, ())
     (snd mixed_graphviz_result) (fst mixed_graphviz_result)"
  unfolding mixed_graphviz_result_def
  by (rule TD_side_always_join_Interp.part_post_solution_of_solve_c)
    (rule mixed_graphviz_terminates)

lemma mixed_graphviz_x_is_local:
  "\<not> is_global ''x''"
  by (rule mixed_si_example_x_is_local)

lemma mixed_graphviz_expected:
  "lookup_st
      (locals (mixed_graphviz_solution
        (Inl (cfg_exit mixed_graphviz_cfg, ())))) ''x'' = SPos
   \<and> lookup_st (globs (mixed_graphviz_solution (Inr ()))) ''x''
      = Ivl (Fin (-1)) (Fin 2)"
  by eval

definition mixed_graphviz_dot :: String.literal where
  "mixed_graphviz_dot =
     String.implode
       (ctx_debug_graphviz_same_ctx_cfg_with_globals
         (\<lambda>_. ''unit'')
         (\<lambda>_. ''mixed Sign answers'')
         (\<lambda>_. ''flow-insensitive Interval invariant'' @ gv_nl
           @ label_of_st show_val (cfg_local_vars mixed_graphviz_cfg)
               (globs (mixed_graphviz_solution (Inr ()))))
         (ctx_debug_state_node_label_auto mixed_graphviz_cfg
           (\<lambda>pc. locals (mixed_graphviz_solution (Inl pc))))
         (ctx_debug_default_node_attrs mixed_graphviz_cfg)
         [()] mixed_graphviz_cfg)"

ML_val \<open>writeln (@{code mixed_graphviz_dot})\<close>

end
