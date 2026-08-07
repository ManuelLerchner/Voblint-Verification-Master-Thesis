section \<open>Example: flow-sensitive Sign answers and a shared Interval invariant\<close>

theory Example_Mixed_Sign_Interval_GraphViz
  imports
    "Voblint_VIMP.VIMP_Notation"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Analysis.Analysis_GraphViz"
begin

text \<open>
  The program compiles through the ordinary VIMP-to-CFG pipeline.  The variable
  @{text "''x''"} is local: this program declares no \<open>global\<close> variables, so
  its classifier is trivially false everywhere.  Per-point answer unknowns
  carry Sign stores, while the single side unknown carries an Interval
  store chosen by this analysis.  The side slot is called @{const globs} by the
  generic routing layer, but it is not an VIMP global-variable store.

  Starting from @{text "x = 0"}, execution visits @{text "x = -1"} and finishes
  at @{text "x = 2"}.  The exit Sign answer is therefore positive.  The shared
  Interval invariant joins all three values and is @{text "[-1, 2]"}.  The DOT
  rendering displays the flow-sensitive Sign answers at CFG nodes and the
  flow-insensitive Interval invariant in a separate cluster.
\<close>

definition mixed_graphviz_prog :: imp_prog where
  "mixed_graphviz_prog = program { void main() { x := -1; x := 2 } }"

text \<open>No \<open>global\<close> declarations, and this file compiles directly through a bare
  proc table rather than \<^const>\<open>mixed_graphviz_prog\<close> itself, so the classifier
  is fixed trivially false rather than derived via \<^const>\<open>declared_global\<close>.\<close>
abbreviation mixed_graphviz_gs :: "vname \<Rightarrow> bool" where
  "mixed_graphviz_gs \<equiv> (\<lambda>_. False)"

definition mixed_graphviz_cfg :: cfg where
  "mixed_graphviz_cfg =
     compile_prog (\<lambda>_. None) [] prog_main_name (prog_main mixed_graphviz_prog)"

definition mixed_graphviz_local_value :: "pp \<Rightarrow> sign abs_state" where
  "mixed_graphviz_local_value p =
     (\<lambda>v. if v = ''x''
       then (case p of
         FunctionEntry _ \<Rightarrow> SZero
       | Statement n \<Rightarrow>
           (if n = 0 then SZero else if n = 1 then SNeg else SPos)
       | FunctionResult _ \<Rightarrow> SPos)
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
      | Inr () \<Rightarrow> DG (mixed_graphviz_local_value (FunctionResult ''main''))
                    (mixed_graphviz_global_value ()))"

lemma mixed_graphviz_x_is_local:
  "\<not> mixed_graphviz_gs ''x''"
  by simp



definition mixed_graphviz_graph_config ::
  "(unit, unit, (sign abs_state, ivl abs_state) dg_state, sign abs_state)
    analysis_graph_config" where
  "mixed_graphviz_graph_config =
    \<lparr> local_of = locals,
      route = (\<lambda>_ _ _ _. ()),
      show_context = (\<lambda>_. ''unit''),
      locals_for_pp = (\<lambda>p.
        let sc = compiled_procedure_scope mixed_graphviz_gs (\<lambda>_. None) [] prog_main_name (prog_main mixed_graphviz_prog)
          mixed_graphviz_cfg p
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>_. None),
      globals_to_show =
        scope_locals (compiled_procedure_scope mixed_graphviz_gs (\<lambda>_. None) [] prog_main_name (prog_main mixed_graphviz_prog)
          mixed_graphviz_cfg (cfg_entry mixed_graphviz_cfg)),
      show_local = (\<lambda>_ _ vars st.
        map (\<lambda>x. x @ ''='' @ show_val (st x)) vars),
      format_return = (\<lambda>_ _ _ _. []),
      show_global = (\<lambda>_ vars s.
        ''flow-insensitive Interval invariant'' #
          map (\<lambda>x. x @ ''='' @ show_val (globs s x)) vars),
      show_global_key = (\<lambda>_. ''Global''),
      is_shared_global = (\<lambda>_. True),
      show_internal_globals = False,
      owner_of = (\<lambda>_. ''main''),
      cluster_label = (\<lambda>_ _. ''mixed Sign answers''),
      source_text = Some (pretty_string_of_program (\<lambda>_. None) [] (prog_main mixed_graphviz_prog)),
      node_annotation = (\<lambda>_. None)
    \<rparr>"

definition mixed_graphviz_graph_domain :: "(pp \<times> unit + unit) list" where
  "mixed_graphviz_graph_domain =
    contextual_graph_domain mixed_graphviz_cfg (\<lambda>_. [()]) @ [Inr ()]"


definition mixed_graphviz_dot :: String.literal where
  "mixed_graphviz_dot =
     String.implode (contextual_analysis_dot mixed_graphviz_graph_config
       mixed_graphviz_cfg mixed_graphviz_graph_domain mixed_graphviz_solution)"

ML_val \<open>writeln (@{code mixed_graphviz_dot})\<close>

end
