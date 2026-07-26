section \<open>Presentation-only pruning of the rendered CFG\<close>

theory Example_Pruned_GraphViz
  imports
    Example_Compile_Baseline
    "Voblint_Analysis.Analysis_GraphViz"
begin

text \<open>
  Rendering filter, not a compiler change: the compiled graph is kept exactly as the analysis
  sees it, and only the rendered projection drops nodes that no execution can reach.  Roots
  are all \<^term>\<open>FunctionEntry\<close> nodes, so a procedure that \<open>main\<close> never calls still renders
  instead of being mistaken for compiler debris.

  A call edge survives when its call site does; its callee entry and its continuation are then
  reachable by construction of \<open>succ_list\<close>, so no dangling endpoint can appear.

  Intended final home once the compiler stack is editable: \<open>prune_cfg\<close> beside
  \<^const>\<open>cfg_reaches\<close> in \<open>CFG_Prune\<close>, the renderer wrapper beside
  \<^const>\<open>raw_cfg_dot\<close> in \<open>Analysis_GraphViz\<close>.
\<close>

subsection \<open>The pruned graph\<close>

definition prune_cfg :: "cfg \<Rightarrow> cfg" where
  "prune_cfg g =
     (let keep = set (reach_list g)
      in \<lparr> intra = set (filter (\<lambda>(u, a, v). u \<in> keep \<and> v \<in> keep) (cfg_intra_list g)),
           calls = set (filter (\<lambda>(c, ca, ce, k). c \<in> keep) (cfg_calls_list g)),
           cfg_entry = cfg_entry g \<rparr>)"

text \<open>Pruning only removes: both relations are subsets of the originals, so every fact
  quantified over \<^const>\<open>intra\<close> or \<^const>\<open>calls\<close> transfers to the pruned graph.\<close>

lemma prune_cfg_intra_subset: "intra (prune_cfg g) \<subseteq> intra g"
  unfolding prune_cfg_def
  by (cases "finite (intra g)") (auto simp: Let_def cfg_intra_list_def)

lemma prune_cfg_calls_subset: "calls (prune_cfg g) \<subseteq> calls g"
  unfolding prune_cfg_def
  by (cases "finite (calls g)") (auto simp: Let_def cfg_calls_list_def)

lemma prune_cfg_entry [simp]: "cfg_entry (prune_cfg g) = cfg_entry g"
  unfolding prune_cfg_def by (simp add: Let_def)

text \<open>Structural well-formedness is inherited, because \<^const>\<open>wf_cfg\<close> is a set of universally
  quantified edge conditions and pruning only deletes edges.\<close>

lemma prune_cfg_wf:
  assumes "wf_cfg g"
  shows "wf_cfg (prune_cfg g)"
  using assms prune_cfg_intra_subset prune_cfg_calls_subset
  unfolding wf_cfg_def by blast

lemma prune_cfg_wf_compile_prog: "wf_cfg (prune_cfg (compile_prog \<Pi> ps mnm main))"
  by (rule prune_cfg_wf[OF compile_prog_wf])

subsection \<open>Rendering the pruned graph\<close>

definition pruned_cfg_dot ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> string" where
  "pruned_cfg_dot \<Pi> ps mnm main =
    (let g = prune_cfg (compile_prog \<Pi> ps mnm main);
         cfg = raw_cfg_graph_config \<Pi> ps mnm main;
         domain = contextual_graph_domain g (\<lambda>_. [()])
     in contextual_analysis_dot cfg g domain (\<lambda>_. ()))"

definition pruned_cfg_dot_lit ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> String.literal" where
  "pruned_cfg_dot_lit \<Pi> ps mnm main =
    String.implode (pruned_cfg_dot \<Pi> ps mnm main)"

subsection \<open>Effect on the factorial example\<close>

value "all_nodes_list (prune_cfg factorial_cfg)"

value "dead_list (prune_cfg factorial_cfg)"

value "nop_edge_list (prune_cfg factorial_cfg)"

text \<open>The renderer still code-generates through the pruned graph: the DOT source is produced
  without touching the compiler or the analysis.\<close>

value "length
  (pruned_cfg_dot
     (prog_table factorial_program) (prog_procs factorial_program)
     ''main'' (prog_main factorial_program))
   < length
      (raw_cfg_dot
         (prog_table factorial_program) (prog_procs factorial_program)
         ''main'' (prog_main factorial_program))"

end
