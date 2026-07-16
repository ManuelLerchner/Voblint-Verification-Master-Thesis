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
  "mixed_graphviz_prog = imp \<lbrakk> x := -1; x := 2 \<rbrakk>"

definition mixed_graphviz_cfg :: cfg where
  "mixed_graphviz_cfg =
     compile_prog (\<lambda>_. None) [] mixed_graphviz_prog"

definition mixed_graphviz_eqs ::
  "(pp \<times> unit, unit, (sign abs_state, ivl abs_state) dg_state) eqsT"
where
  "mixed_graphviz_eqs =
     mixed_si_generator mixed_graphviz_cfg bot
       (fun_of_st top_sign_st) (fun_of_st top_ivl_st)"

definition mixed_graphviz_local_value :: "pp \<Rightarrow> sign abs_state" where
  "mixed_graphviz_local_value p =
     (\<lambda>v. if v = ''x''
       then (if p = 0 then SZero else if p = 1 then SNeg else if p = 2 then SPos else STop)
       else STop)"

definition mixed_graphviz_global_value :: "unit \<Rightarrow> ivl abs_state" where
  "mixed_graphviz_global_value _ =
     (\<lambda>v. if v = ''x'' then Ivl (Fin (-1)) (Fin 2) else Ivl MinInf PlusInf)"

definition mixed_graphviz_solution ::
  "pp \<times> unit + unit \<Rightarrow> (sign abs_state, ivl abs_state) dg_state"
where
  "mixed_graphviz_solution z =
     (case z of
        Inl (p, ()) \<Rightarrow> DG (mixed_graphviz_local_value p) (mixed_graphviz_global_value ())
      | Inr () \<Rightarrow> DG (mixed_graphviz_local_value (cfg_exit mixed_graphviz_cfg))
                    (mixed_graphviz_global_value ()))"

lemma mixed_graphviz_x_is_local:
  "\<not> is_global ''x''"
  by (simp add: is_global_def)

definition mixed_graphviz_label_of_abs_state ::
  "('a::bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow> 'a abs_state \<Rightarrow> string"
where
  "mixed_graphviz_label_of_abs_state pr vars st =
     join_gv_nl (map (\<lambda>x. x @ ''='' @ pr (st x)) vars)"

definition mixed_graphviz_node_label :: "pp \<times> unit \<Rightarrow> string" where
  "mixed_graphviz_node_label pc =
     (case pc of (p, ctx) \<Rightarrow>
        ''pp'' @ string_of_nat p
        @ (let l = mixed_graphviz_label_of_abs_state show_val
                   (cfg_local_vars mixed_graphviz_cfg)
                   (locals (mixed_graphviz_solution (Inl pc))) in
           if l = [] then [] else gv_nl @ l))"

definition mixed_graphviz_globals_label :: "unit \<Rightarrow> string" where
  "mixed_graphviz_globals_label _ =
     ''flow-insensitive Interval invariant'' @ gv_nl @
      mixed_graphviz_label_of_abs_state show_val (cfg_local_vars mixed_graphviz_cfg)
        (globs (mixed_graphviz_solution (Inr ())))"

definition mixed_graphviz_dot :: String.literal where
  "mixed_graphviz_dot =
     String.implode
       (ctx_debug_graphviz_same_ctx_cfg_with_globals
         (\<lambda>_. ''unit'')
         (\<lambda>_. ''mixed Sign answers'')
         mixed_graphviz_globals_label
         mixed_graphviz_node_label
         (ctx_debug_default_node_attrs mixed_graphviz_cfg)
         [()] mixed_graphviz_cfg)"

ML_val \<open>writeln (@{code mixed_graphviz_dot})\<close>

end
