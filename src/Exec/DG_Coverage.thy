theory DG_Coverage
  imports Exec_DG_Generator "Voblint_CFG.CFG_Prune"
begin

section \<open>Solved-key coverage from graph reachability\<close>

text \<open>
  \<^const>\<open>vars_cover\<close> is the premise the D/G node-soundness bridge turns on: the solved
  key set must contain the entry, every intra edge's target, and every call edge's
  callee entry and continuation.

  It need not be evaluated. \<^const>\<open>part_post_solution\<close> already closes the solved key
  set downwards along its dependencies, and the executable generator's local reads at a
  node are exactly that node's \<^const>\<open>cfg_succ_rel\<close> predecessors: an intra
  predecessor, a call site whose callee entry or continuation this node is, and the
  \<^const>\<open>FunctionResult\<close> of a callee returning here. So a node the graph reaches
  \<^const>\<open>cfg_exit\<close> from is solved as soon as the exit is, and coverage of the whole
  graph becomes a statement about the \<^emph>\<open>graph\<close> --- that no node is cut off from the
  exit --- rather than about the solver run.
\<close>

subsection \<open>Local reads of one generated equation\<close>

text \<open>The call site and the callee exit are read before the specification's combine
  transfer runs, so they are dependencies whatever that transfer does. The analysis
  global is deliberately not claimed here: a local-only specification never reads it,
  and coverage does not need it.\<close>

lemma dep_aux_dg_cmb_at_of:
  "{Inl (cc, ctx), Inl (FunctionResult p, ctx)}
     \<subseteq> dep_aux \<sigma> (dg_cmb_at_of S ctx ca cc p)"
  unfolding dg_cmb_at_of_def
  by (rule dep_aux_dg_spec_combine_tree_sources)

text \<open>One generated equation's dependency set is the union over the three tree groups
  the generator folds: the node's intra predecessors, the call sites returning here,
  and --- at a \<^const>\<open>FunctionEntry\<close> --- the call sites entering here.\<close>

lemma dep_aux_side_cfg_T_eff_keyed_seed_dg_char:
  "dep_aux \<sigma> (side_cfg_T_eff_keyed_seed_dg pred_sel gkey route it cmb extra g bot0 s0d s0g
       (v, ctx))
     = (\<Union>t \<in> set (map (\<lambda>(src, a). it ctx src a) (pred_sel g v ctx)
          @ map (\<lambda>(cc, ca). cmb route ctx ca cc v) (call_site_list g v)
          @ extra route ctx v). dep_aux \<sigma> t)"
  unfolding side_cfg_T_eff_keyed_seed_dg_def
  by (simp add: Let_def dep_aux_Side dep_aux_side_rhs_fold_dg_char)

lemma dep_aux_dg_gen_of_char:
  "dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (v, ()))
     = (\<Union>t \<in> set (map (\<lambda>(src, a). dg_spec_edge_tree S a src (\<lambda>_. ()))
            (intra_predecessor_addr_list g v ())
          @ map (\<lambda>(cc, ca). dg_cmb_of S g (\<lambda>_ _ _ _. ()) () ca cc v) (call_site_list g v)
          @ dg_extra_of S g (\<lambda>_ _ _ _. ()) () v). dep_aux \<sigma> t)"
  unfolding dg_gen_of_def
  by (rule dep_aux_side_cfg_T_eff_keyed_seed_dg_char)
text \<open>Each of the three groups contributes its trees' dependencies to the whole.\<close>

lemma dep_aux_dg_gen_of_pred_mem:
  assumes "(u, a) \<in> set (intra_predecessor_list g v)"
  shows "dep_aux \<sigma> (dg_spec_edge_tree S a (Inl (u, ())) (\<lambda>_. ()))
           \<subseteq> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (v, ()))"
  unfolding dep_aux_dg_gen_of_char intra_predecessor_addr_list_def using assms by force

lemma dep_aux_dg_gen_of_site_mem:
  assumes "(cc, ca) \<in> set (call_site_list g v)"
  shows "dep_aux \<sigma> (dg_cmb_of S g (\<lambda>_ _ _ _. ()) () ca cc v)
           \<subseteq> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (v, ()))"
  unfolding dep_aux_dg_gen_of_char using assms by force

lemma dep_aux_dg_gen_of_extra_mem:
  assumes "t \<in> set (dg_extra_of S g (\<lambda>_ _ _ _. ()) () v)"
  shows "dep_aux \<sigma> t \<subseteq> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (v, ()))"
  unfolding dep_aux_dg_gen_of_char using assms by force

subsection \<open>Each structural successor step is a local dependency\<close>

lemma dep_dg_gen_of_intra:
  assumes fin: "finite (intra g)" and e: "(u, a, v) \<in> intra g"
  shows "Inl (u, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (v, ()))"
proof -
  have pred: "(u, a) \<in> set (intra_predecessor_list g v)"
    using fin e by (simp add: intra_predecessors_def)
  have "Inl (u, ()) \<in> dep_aux \<sigma> (dg_spec_edge_tree S a (Inl (u, ())) (\<lambda>_. ()))"
    by (rule dep_aux_dg_spec_edge_tree_source)
  with dep_aux_dg_gen_of_pred_mem[OF pred] show ?thesis by blast
qed

lemma dep_dg_gen_of_comb:
  assumes fin: "finite (calls g)" and e: "(cs, ca, FunctionEntry p, k) \<in> calls g"
  shows "Inl (cs, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (k, ()))"
    and "Inl (FunctionResult p, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (k, ()))"
proof -
  have site: "(cs, ca) \<in> set (call_site_list g k)" using fin e by auto
  have p_res: "p \<in> set (static_targets g k cs ca)"
    using static_targets_iff[OF fin] e by simp
  have tree: "dg_cmb_at_of S () ca cs p
                \<in> set (map (dg_cmb_at_of S () ca cs) (static_targets g k cs ca))"
    using p_res by simp
  have inner: "{Inl (cs, ()), Inl (FunctionResult p, ())}
                 \<subseteq> dep_aux \<sigma> (dg_cmb_of S g (\<lambda>_ _ _ _. ()) () ca cs k)"
  proof -
    have "dep_aux \<sigma> (dg_cmb_at_of S () ca cs p)
            \<subseteq> dep_aux \<sigma> (dg_cmb_of S g (\<lambda>_ _ _ _. ()) () ca cs k)"
      unfolding dg_cmb_of_def dep_aux_side_rhs_fold_dg_char using tree by blast
    then show ?thesis using dep_aux_dg_cmb_at_of by blast
  qed
  note outer = dep_aux_dg_gen_of_site_mem[OF site, of \<sigma> S bot0 s0d s0g]
  show "Inl (cs, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (k, ()))"
    using inner outer by blast
  show "Inl (FunctionResult p, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (k, ()))"
    using inner outer by blast
qed

lemma dep_dg_gen_of_entry:
  assumes fin: "finite (calls g)" and e: "(cs, ca, ce, k) \<in> calls g"
  shows "Inl (cs, ()) \<in> dep_aux \<sigma> (dg_gen_of S g bot0 s0d s0g (ce, ()))"
proof -
  have site: "(cs, ca) \<in> set (entry_call_list g ce)"
    using fin e by (auto simp: entry_calls_def)
  obtain dst fs as where ca_eq: "ca = CallEdge dst fs as" by (cases ca) auto
  let ?p = "case ce of FunctionEntry p \<Rightarrow> p | _ \<Rightarrow> undefined"
  have mem: "transfer_tree (dgs_enter S (call_info_of ca ?p)) (Inl (cs, ())) (\<lambda>_. ())
             \<in> set (dg_extra_of S g (\<lambda>_ _ _ _. ()) () ce)"
    unfolding dg_extra_of_def using site by force
  have "Inl (cs, ()) \<in> dep_aux \<sigma>
       (transfer_tree (dgs_enter S (call_info_of ca ?p)) (Inl (cs, ())) (\<lambda>_. ()))"
    by (rule dep_aux_transfer_tree_source)
  with dep_aux_dg_gen_of_extra_mem[OF mem] show ?thesis by blast
qed

text \<open>\<^const>\<open>wf_cfg\<close> supplies the one shape fact the combine group needs: a call edge's
  callee is a \<^const>\<open>FunctionEntry\<close>, so the continuation really does read a
  \<^const>\<open>FunctionResult\<close>.\<close>

lemma dep_dg_gen_of_succ:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and wf: "wf_cfg g"
      and step: "(u, w) \<in> cfg_succ_rel g"
  shows "(u, ()) \<in> dep\<^sub>L (dg_gen_of S g bot0 s0d s0g) \<sigma> (w, ())"
  using step
proof (cases rule: cfg_succ_rel_cases)
  case (INTRA a)
  then show ?thesis
    using dep_dg_gen_of_intra[OF fin(1) INTRA] by (simp add: dep\<^sub>L_def dep_def)
next
  case (ENTRY ca k)
  then show ?thesis
    using dep_dg_gen_of_entry[OF fin(2) ENTRY] by (simp add: dep\<^sub>L_def dep_def)
next
  case (COMB_CALLER ca ce)
  obtain p where "ce = FunctionEntry p"
    using wf COMB_CALLER unfolding wf_cfg_def by blast
  then show ?thesis
    using COMB_CALLER dep_dg_gen_of_comb(1)[OF fin(2)] by (simp add: dep\<^sub>L_def dep_def)
next
  case (COMB_RESULT cs ca p k)
  then show ?thesis
    using dep_dg_gen_of_comb(2)[OF fin(2) COMB_RESULT(1)] by (simp add: dep\<^sub>L_def dep_def)
qed

subsection \<open>Everything that reaches the exit is solved\<close>

lemma dg_gen_of_solved_of_reaches:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and wf: "wf_cfg g"
      and pp: "part_post_solution (dg_gen_of S g bot0 s0d s0g) (v0, ()) \<sigma> vars"
      and reach: "cfg_reaches g v v0"
  shows "(v, ()) \<in> vars"
proof -
  have base0: "(v0, ()) \<in> vars" using pp by simp
  have closed: "\<And>x y. x \<in> vars \<Longrightarrow> y \<in> dep\<^sub>L (dg_gen_of S g bot0 s0d s0g) \<sigma> x \<Longrightarrow> y \<in> vars"
    using pp by blast
  from reach have "(v, v0) \<in> (cfg_succ_rel g)\<^sup>*" by (simp add: cfg_reaches_def)
  then show ?thesis
  proof (induction rule: converse_rtrancl_induct)
    case base
    then show ?case using base0 by simp
  next
    case (step y z)
    have "(y, ()) \<in> dep\<^sub>L (dg_gen_of S g bot0 s0d s0g) \<sigma> (z, ())"
      by (rule dep_dg_gen_of_succ[OF fin wf step.hyps(1)])
    then show ?case using closed step.IH by blast
  qed
qed

theorem vars_cover_of_dg_gen_of:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and wf: "wf_cfg g"
      and covered: "\<And>v. v \<in> cfg_nodes g \<Longrightarrow> cfg_reaches g v (cfg_exit g)"
      and pp: "part_post_solution (dg_gen_of S g bot0 s0d s0g) (cfg_exit g, ()) \<sigma> vars"
  shows "vars_cover g vars"
proof -
  have solved: "\<And>v. v \<in> cfg_nodes g \<Longrightarrow> (v, ()) \<in> vars"
    by (rule dg_gen_of_solved_of_reaches[OF fin wf pp covered])
  show ?thesis
  proof (rule vars_coverI)
    show "(cfg_entry g, ()) \<in> vars" by (rule solved) (simp add: cfg_nodes_def)
  next
    fix u a w assume "(u, a, w) \<in> intra g"
    then show "(w, ()) \<in> vars" by (rule solved[OF intra_endpoints_in_nodes(2)])
  next
    fix cs dst fs as q k assume "(cs, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g"
    then show "(FunctionEntry q, ()) \<in> vars"
      by (rule solved[OF call_endpoints_in_nodes(2)])
  next
    fix cs dst fs as q k assume "(cs, CallEdge dst fs as, FunctionEntry q, k) \<in> calls g"
    then show "(k, ()) \<in> vars" by (rule solved[OF call_endpoints_in_nodes(3)])
  qed
qed

subsection \<open>Deciding exit coverage by backward closure\<close>

text \<open>
  The remaining premise --- every node reaches the exit --- is a finite structural
  question about the graph, with no solver in it. \<open>dep_pred_list\<close> enumerates one
  node's \<^const>\<open>cfg_succ_rel\<close> predecessors, \<open>bwd_closure\<close> iterates that
  enumeration from \<^const>\<open>cfg_exit\<close>, and \<open>cfg_exit_covers\<close> asks whether the
  closure has swallowed every node after as many rounds as there are nodes. Only
  soundness is proved: a positive answer really does exhibit a path, which is the
  direction a coverage premise needs.
\<close>

definition dep_pred_list :: "cfg \<Rightarrow> cfg_node \<Rightarrow> cfg_node list" where
  "dep_pred_list g v =
     map fst (intra_predecessor_list g v)
     @ map fst (call_site_list g v)
     @ map (\<lambda>(cc, ca, p). FunctionResult p) (call_target_list g v)
     @ map fst (entry_call_list g v)"

fun bwd_closure :: "cfg \<Rightarrow> nat \<Rightarrow> cfg_node list" where
  "bwd_closure g 0 = [cfg_exit g]"
| "bwd_closure g (Suc i) =
     remdups (bwd_closure g i @ concat (map (dep_pred_list g) (bwd_closure g i)))"

definition cfg_exit_covers :: "cfg \<Rightarrow> bool" where
  "cfg_exit_covers g =
     list_all (\<lambda>v. v \<in> set (bwd_closure g (length (cfg_node_list g)))) (cfg_node_list g)"

lemma dep_pred_list_succ:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and mem: "u \<in> set (dep_pred_list g v)"
  shows "(u, v) \<in> cfg_succ_rel g"
proof -
  from mem consider
      (INTRA) a where "(u, a, v) \<in> intra g"
    | (CALLER) ca p where "(u, ca, FunctionEntry p, v) \<in> calls g"
    | (RESULT) cc ca p where "(cc, ca, FunctionEntry p, v) \<in> calls g" "u = FunctionResult p"
    | (ENTRY) ca k where "(u, ca, v, k) \<in> calls g"
    unfolding dep_pred_list_def
    using fin
    by (auto simp: intra_predecessors_def entry_calls_def call_target_list_iff)
  then show ?thesis
    by cases (blast intro: cfg_succ_rel_intra cfg_succ_rel_comb_caller
                           cfg_succ_rel_comb_result cfg_succ_rel_entry)+
qed

lemma bwd_closure_reaches:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and mem: "v \<in> set (bwd_closure g i)"
  shows "cfg_reaches g v (cfg_exit g)"
  using mem
proof (induction i arbitrary: v)
  case 0
  then show ?case by (simp add: cfg_reaches_refl)
next
  case (Suc i)
  from Suc.prems consider (old) "v \<in> set (bwd_closure g i)"
    | (new) w where "w \<in> set (bwd_closure g i)" "v \<in> set (dep_pred_list g w)"
    by auto
  then show ?case
  proof cases
    case old
    then show ?thesis by (rule Suc.IH)
  next
    case (new w)
    have "cfg_succ g v w"
      using dep_pred_list_succ[OF fin new(2)] by (simp add: cfg_succ_def)
    then show ?thesis using Suc.IH[OF new(1)] by (rule cfg_succ_reaches)
  qed
qed

theorem cfg_exit_covers_reaches:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and covers: "cfg_exit_covers g"
      and node: "v \<in> cfg_nodes g"
  shows "cfg_reaches g v (cfg_exit g)"
proof -
  have "v \<in> set (cfg_node_list g)" using node fin by simp
  then have "v \<in> set (bwd_closure g (length (cfg_node_list g)))"
    using covers unfolding cfg_exit_covers_def by (simp add: list_all_iff)
  then show ?thesis by (rule bwd_closure_reaches[OF fin])
qed

text \<open>The packaged form an instance cites: finiteness, well-formedness, one structural
  coverage check on the graph, and the solver's own post-solution.\<close>

theorem vars_cover_of_dg_gen_of_covers:
  assumes fin: "finite (intra g)" "finite (calls g)"
      and wf: "wf_cfg g"
      and covers: "cfg_exit_covers g"
      and pp: "part_post_solution (dg_gen_of S g bot0 s0d s0g) (cfg_exit g, ()) \<sigma> vars"
  shows "vars_cover g vars"
  by (rule vars_cover_of_dg_gen_of[OF fin wf _ pp])
     (rule cfg_exit_covers_reaches[OF fin covers])

end
