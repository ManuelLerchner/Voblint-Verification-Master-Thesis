theory Analysis_GraphViz
  imports
    "Voblint_CFG.CFG_GraphViz"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_CFG.Exec_CFG"
    TD_Side_CFG
    Exec_St
    Abstract_Domain
begin

section \<open>Generic analysis-annotated CFG rendering\<close>

text \<open>
  Bridges the executable abstract state (@{text "'a st"}) with the
  @{const to_graphviz_labeled} entry point in
  @{theory Voblint_CFG.CFG_GraphViz}.

  The @{class show_val} instance for the domain type is resolved
  automatically; call sites supply only the variable list and the raw
  solver result.

  The @{text "_lit"} variants return @{type String.literal}, which the
  code generator maps to native ML @{text "string"}, so example files
  need no @{text "char list"} decoder -- a single @{command ML_val}
  with @{text "writeln"} suffices.
\<close>

subsection \<open>Node-label builder\<close>

text \<open>
  The side TD solver stores @{text "sol (Inl pp)"} (frame-local, flow-sensitive)
  and @{text "sol (Inr ())"} (single global unknown, flow-insensitive) separately.
  Node labels show flow-sensitive @{text "Inl"} locals scoped to each procedure
  region.  Globals are not repeated on nodes (the solver keeps one flow-insensitive
  @{text "Inr"} unknown); they appear once in @{text "cluster_globals"}.
\<close>

definition gv_nl :: string where "gv_nl = [CHR 0x5C, CHR 0x6E]"

fun join_gv_nl :: "string list \<Rightarrow> string" where
  "join_gv_nl [] = []"
| "join_gv_nl [s] = s"
| "join_gv_nl (s # ss) = s @ gv_nl @ join_gv_nl ss"

definition label_of_st ::
    "('a::bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow> 'a st \<Rightarrow> string" where
  "label_of_st pr vars st =
     join_gv_nl (map (\<lambda>x. x @ ''='' @ pr (lookup_st st x)) vars)"

definition side_env_st ::
    "(pp + unit \<Rightarrow> 'a::bounded_semilattice_sup_bot st) \<Rightarrow> pp \<Rightarrow> 'a st" where
  "side_env_st sol p = sol (Inl p) \<squnion> sol (Inr ())"

definition collect_vars_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list" where
  "collect_vars_prog \<Pi> ps main =
     remdups (concat (map (\<lambda>(_, a, _). vars_of_action a) (prog_cfg_edges \<Pi> ps main)))"

definition collect_region_vars ::
    "(pp \<times> edge_action \<times> pp) list \<Rightarrow> pp list \<Rightarrow> vname list" where
  "collect_region_vars Es pps =
     remdups (concat (map (\<lambda>e. case e of (u, a, v) \<Rightarrow>
            if mem_pp u pps then vars_of_action a else []) Es))"

definition collect_local_vars_region ::
    "(pp \<times> edge_action \<times> pp) list \<Rightarrow> pp list \<Rightarrow> vname list" where
  "collect_local_vars_region Es pps =
     filter (\<lambda>x. \<not> is_global x) (collect_region_vars Es pps)"

fun region_pps_of :: "graphviz_region list \<Rightarrow> pp \<Rightarrow> pp list" where
  "region_pps_of [] p = []"
| "region_pps_of ((owner, vs) # regs) p =
     (if mem_pp p vs then vs else region_pps_of regs p)"

definition collect_global_vars_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> vname list" where
  "collect_global_vars_prog \<Pi> ps main =
     filter is_global (collect_vars_prog \<Pi> ps main)"

subsection \<open>Per-pp and global-side labelers\<close>

definition analysis_local_node_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_local_node_label pr lvars sol p =
     (let base = string_of_nat p @ [CHR 0x5C, CHR 0x6E] @ label_of_st pr lvars (sol (Inl p))
      in  if lvars = [] then string_of_nat p else base)"

definition analysis_region_node_label_prog ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_region_node_label_prog pr \<Pi> ps main sol p =
     analysis_local_node_label pr
       (collect_local_vars_region (prog_cfg_edges \<Pi> ps main)
          (region_pps_of (compile_prog_regions \<Pi> ps main) p))
       sol p"

definition globals_side_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> string" where
  "globals_side_label pr gvars sol = label_of_st pr gvars (sol (Inr ()))"

definition globals_cluster_dot :: "string \<Rightarrow> string" where
  "globals_cluster_dot lab =
     (if lab = [] then []
      else ''  subgraph cluster_globals {'' @ nl
        @ ''    label='' @ dq @ ''globals (flow-insensitive)'' @ dq @ '';'' @ nl
        @ ''    style=filled; color=lightyellow;'' @ nl
        @ ''    globals_side [shape=note,label='' @ dq @ lab @ dq @ ''];'' @ nl
        @ ''  }'' @ nl)"

(* Legacy combined label (Inl join Inr); kept for cfg-level call sites. *)

definition analysis_node_label ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow>
     (pp + unit \<Rightarrow> 'a st) \<Rightarrow> pp \<Rightarrow> string" where
  "analysis_node_label pr vars sol p =
     string_of_nat p @ [CHR 0x5C, CHR 0x6E] @ label_of_st pr vars (side_env_st sol p)"

subsection \<open>Annotated DOT generators\<close>

definition graphviz_of_analysis ::
    "('a::bounded_semilattice_sup_bot \<Rightarrow> string) \<Rightarrow> vname list \<Rightarrow> (pp + unit \<Rightarrow> 'a st) \<Rightarrow>
     cfg \<Rightarrow> graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "graphviz_of_analysis pr vars sol g regs ents exts =
     to_graphviz_labeled (analysis_node_label pr vars sol) g regs ents exts"

text \<open>
  Auto variant: the @{class show_val} instance supplies the printer.
\<close>

definition graphviz_of_analysis_auto ::
    "vname list \<Rightarrow> (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow>
     cfg \<Rightarrow> graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "graphviz_of_analysis_auto vars sol g regs ents exts =
     graphviz_of_analysis show_val vars sol g regs ents exts"

definition edges_to_dot_list :: "(pp \<times> edge_action \<times> pp) list \<Rightarrow> string" where
  "edges_to_dot_list Es = concat (map edge_to_dot Es)"

definition combines_to_dot_list :: "(pp \<times> pp \<times> pp) list \<Rightarrow> string" where
  "combines_to_dot_list Cs = concat (map combine_to_dot Cs)"

definition proc_entry_pps_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp list" where
  "proc_entry_pps_prog \<Pi> ps main = enter_targets (prog_cfg_edges \<Pi> ps main)"

definition proc_exit_pps_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> pp list" where
  "proc_exit_pps_prog \<Pi> ps main = combine_exits (prog_cfg_combines \<Pi> ps main)"

definition to_graphviz_labeled_prog ::
    "(pp \<Rightarrow> string) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "to_graphviz_labeled_prog lbl \<Pi> ps main regs proc_entries proc_exits =
     (let g = compile_prog \<Pi> ps main
      in  ''digraph CFG {'' @ nl
       @ ''  rankdir=TB;'' @ nl
       @ concat (map (region_to_dot_labeled lbl g proc_entries proc_exits) regs)
       @ edges_to_dot_list (prog_cfg_edges \<Pi> ps main)
       @ combines_to_dot_list (prog_cfg_combines \<Pi> ps main)
       @ ''}'' @ nl)"

definition to_graphviz_side_analysis_prog ::
    "(pp \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     graphviz_region list \<Rightarrow> pp list \<Rightarrow> pp list \<Rightarrow> string" where
  "to_graphviz_side_analysis_prog lbl globals_lab \<Pi> ps main regs proc_entries proc_exits =
     (let g = compile_prog \<Pi> ps main
      in  ''digraph CFG {'' @ nl
       @ ''  rankdir=TB;'' @ nl
       @ concat (map (region_to_dot_labeled lbl g proc_entries proc_exits) regs)
       @ edges_to_dot_list (prog_cfg_edges \<Pi> ps main)
       @ combines_to_dot_list (prog_cfg_combines \<Pi> ps main)
       @ globals_cluster_dot globals_lab
       @ ''}'' @ nl)"

definition graphviz_of_analysis_prog ::
    "(pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow>
     proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> string" where
  "graphviz_of_analysis_prog sol \<Pi> ps main =
     to_graphviz_side_analysis_prog
       (analysis_region_node_label_prog show_val \<Pi> ps main sol)
       (globals_side_label show_val (collect_global_vars_prog \<Pi> ps main) sol)
       \<Pi> ps main
       (compile_prog_regions \<Pi> ps main)
       (proc_entry_pps_prog \<Pi> ps main)
       (proc_exit_pps_prog \<Pi> ps main)"

subsection \<open>Whole-program convenience wrappers\<close>

text \<open>
  The @{text "annotated_dot_of_prog"} family bundles
  @{const compile_prog}, @{const compile_prog_regions},
  @{const collect_vars_cfg}, and @{const graphviz_of_analysis_auto}
  into a single call.  The @{text "_lit"} suffix means
  @{const String.implode} is applied so the code generator returns a
  native ML @{text "string"} -- no @{text "char list"} decoder needed.
\<close>

definition annotated_dot_of_prog ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow> string" where
  "annotated_dot_of_prog \<Pi> ps main sol =
     graphviz_of_analysis_prog sol \<Pi> ps main"

definition annotated_dot_of_prog_lit ::
    "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow>
     (pp + unit \<Rightarrow> 'a::{show_val, bounded_semilattice_sup_bot} st) \<Rightarrow> String.literal" where
  "annotated_dot_of_prog_lit \<Pi> ps main sol =
     String.implode (annotated_dot_of_prog \<Pi> ps main sol)"

definition plain_dot_of_prog_lit :: "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> String.literal" where
  "plain_dot_of_prog_lit \<Pi> ps main =
     String.implode
       (to_graphviz_labeled_prog pp_plain_label \<Pi> ps main
          (compile_prog_regions \<Pi> ps main)
          (proc_entry_pps_prog \<Pi> ps main)
          (proc_exit_pps_prog \<Pi> ps main))"

end

