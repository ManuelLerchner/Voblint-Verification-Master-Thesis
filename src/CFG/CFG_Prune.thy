theory CFG_Prune
  imports CFG_Collect IMP2_Proc_to_CFG
begin

section \<open>Dead-procedure pruning for interprocedural CFGs\<close>

text \<open>
  `compile_prog` unions every procedure's edges/combines into the graph,
  whether or not the procedure is ever called.  A defined-but-uncalled
  procedure leaves body nodes that are edge-targets yet cannot reach the
  program exit -- breaking the ''every program point reaches the exit''
  well-formedness condition.

  We prune the graph to the backward cone of the exit (the live, reachable
  nodes), keeping the solver on the full graph.  The collecting value at the
  exit is unchanged (a witness from entry to exit stays inside the cone), so
  soundness transports back to the unpruned analysis with no well-formedness
  hypothesis.
\<close>

subsection \<open>Interprocedural reachability\<close>

(* One dependency step: u's abstract value feeds w's right-hand side, either
   via an edge (u -> w) or a combine predecessor relation. *)
definition cfg_succ_rel :: "cfg \<Rightarrow> (pp \<times> pp) set" where
  "cfg_succ_rel g =
     {(u, w). \<exists>a. (u, a, w) \<in> edges g} \<union>
     {(u, w). \<exists>ct \<in> combines g. combine_call_node ct = u \<and> combine_return_node ct = w} \<union>
     {(u, w). \<exists>ct \<in> combines g. combine_exit_node ct = u \<and> combine_return_node ct = w}"

definition cfg_succ :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> bool" where
  "cfg_succ g u w \<longleftrightarrow> (u, w) \<in> cfg_succ_rel g"

definition cfg_reaches :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> bool" where
  "cfg_reaches g v v0 \<longleftrightarrow> (v, v0) \<in> (cfg_succ_rel g)^*"

definition cone :: "cfg \<Rightarrow> pp \<Rightarrow> pp set" where
  "cone g v0 = {v. cfg_reaches g v v0}"

definition prune_to :: "cfg \<Rightarrow> pp \<Rightarrow> cfg" where
  "prune_to g v0 =
     mk_cfg (cfg_entry g) (cfg_exit g)
       {e \<in> edges g. snd (snd e) \<in> cone g v0}
       {ct \<in> combines g. combine_return_node ct \<in> cone g v0}"

definition prune_cfg :: "cfg \<Rightarrow> cfg" where
  "prune_cfg g = prune_to g (cfg_exit g)"

subsection \<open>reaches basics\<close>

lemma cfg_reaches_refl: "cfg_reaches g v v"
  by (simp add: cfg_reaches_def)

lemma cfg_succ_reaches:
  "cfg_succ g u w \<Longrightarrow> cfg_reaches g w v0 \<Longrightarrow> cfg_reaches g u v0"
  by (auto simp: cfg_succ_def cfg_reaches_def intro: converse_rtrancl_into_rtrancl)

lemma cfg_succ_mono:
  assumes "edges g1 \<subseteq> edges g2" "combines g1 \<subseteq> combines g2" "cfg_succ g1 u w"
  shows "cfg_succ g2 u w"
  using assms unfolding cfg_succ_def cfg_succ_rel_def by blast
lemma cfg_reaches_mono:
  assumes "edges g1 \<subseteq> edges g2" "combines g1 \<subseteq> combines g2" "cfg_reaches g1 v w"
  shows "cfg_reaches g2 v w"
proof -
  have sub: "cfg_succ_rel g1 \<subseteq> cfg_succ_rel g2"
    using assms unfolding cfg_succ_rel_def by blast
  have "(cfg_succ_rel g1)^* \<subseteq> (cfg_succ_rel g2)^*"
    using sub by (rule rtrancl_mono)
  thus ?thesis using assms(3) unfolding cfg_reaches_def by blast
qed

subsection \<open>prune_to selectors\<close>

lemma edges_prune_to[simp]:
  "edges (prune_to g v0) = {e \<in> edges g. snd (snd e) \<in> cone g v0}"
  by (simp add: prune_to_def)

lemma combines_prune_to[simp]:
  "combines (prune_to g v0) = {ct \<in> combines g. combine_return_node ct \<in> cone g v0}"
  by (simp add: prune_to_def)

lemma cfg_entry_prune_to[simp]: "cfg_entry (prune_to g v0) = cfg_entry g"
  by (simp add: prune_to_def)

lemma cfg_exit_prune_to[simp]: "cfg_exit (prune_to g v0) = cfg_exit g"
  by (simp add: prune_to_def)

(* Reachability is discharged by the side solver via dep_side_rhs_tree_* and
   cfg_reaches_imp_trans_dep_or_eq_side_eff (TD_Side_Eff_Soundness).
   The graph-level pruning frame below is solver-agnostic. *)

subsection \<open>Collect frame: witness transport\<close>

lemma cfg_witness_prune_to:
  assumes "cfg_witness g S v t"
  shows "cfg_reaches g v v0 \<longrightarrow> cfg_witness (prune_to g v0) S v t"
  using assms
proof (induction rule: cfg_witness.induct)
  case (entry v s Sa)
  then show ?case by (auto intro: cfg_witness.entry)
next
  case (edge u a v Sa s t)
  show ?case
  proof (rule impI)
    assume rv: "cfg_reaches g v v0"
    have usucc: "cfg_succ g u v"
      using edge.hyps(1) unfolding cfg_succ_def cfg_succ_rel_def by blast
    have ruv: "cfg_reaches g u v0"
      using cfg_succ_reaches[OF usucc rv] .
    have wu: "cfg_witness (prune_to g v0) Sa u s"
      using edge.IH ruv by blast
    have ev: "(u, a, v) \<in> edges (prune_to g v0)"
      using edge.hyps(1) rv by (simp add: cone_def)
    show "cfg_witness (prune_to g v0) Sa v t"
      by (rule cfg_witness.edge[OF ev wu edge.hyps(3)])
  qed
next
  case (combine c ex v dst Sa sto t u)
  show ?case
  proof (rule impI)
    assume rv: "cfg_reaches g v v0"
    have call_pred: "\<exists>ct\<in>combines g. combine_call_node ct = c \<and> combine_return_node ct = v"
      using combine.hyps(1) by (intro bexI[of _ "(c, ex, v, dst)"]) (auto simp: combine_call_node_def combine_return_node_def)
    have csucc: "cfg_succ g c v"
      unfolding cfg_succ_def cfg_succ_rel_def using call_pred by blast
    have exit_pred: "\<exists>ct\<in>combines g. combine_exit_node ct = ex \<and> combine_return_node ct = v"
      using combine.hyps(1) by (intro bexI[of _ "(c, ex, v, dst)"]) (auto simp: combine_exit_node_def combine_return_node_def)
    have exsucc: "cfg_succ g ex v"
      unfolding cfg_succ_def cfg_succ_rel_def using exit_pred by blast
    have rc: "cfg_reaches g c v0"
      using cfg_succ_reaches[OF csucc rv] .
    have rex': "cfg_reaches g ex v0"
      using cfg_succ_reaches[OF exsucc rv] .
    have wc: "cfg_witness (prune_to g v0) Sa c sto"
      using combine.IH(1) rc by blast
    have wex: "cfg_witness (prune_to g v0) Sa ex t"
      using combine.IH(2) rex' by blast
    have rv': "cfg_reaches g (combine_return_node (c, ex, v, dst)) v0"
      using combine.hyps(1) rv by (simp add: combine_return_node_def)
    have cv: "(c, ex, v, dst) \<in> combines (prune_to g v0)"
      using combine.hyps(1) rv' by (simp add: cone_def)
    show "cfg_witness (prune_to g v0) Sa v u"
      by (rule cfg_witness.combine[OF cv wc wex combine.hyps(4)])
  qed
qed

lemma cfg_collect_prune_exit:
  "cfg_collect g S (cfg_exit g) \<subseteq> cfg_collect (prune_cfg g) S (cfg_exit g)"
proof
  fix t assume "t \<in> cfg_collect g S (cfg_exit g)"
  then have wg: "cfg_witness g S (cfg_exit g) t"
    by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
  have wp: "cfg_witness (prune_to g (cfg_exit g)) S (cfg_exit g) t"
    using cfg_witness_prune_to[OF wg] cfg_reaches_refl by blast
  show "t \<in> cfg_collect (prune_cfg g) S (cfg_exit g)"
    using wp by (simp add: prune_cfg_def cfg_collect_eq_paths cfg_collect_paths_def)
qed

subsection \<open>Entry reaches exit for compile_prog\<close>

lemma cfg_succ_imp_reaches: "cfg_succ g u w \<Longrightarrow> cfg_reaches g u w"
  using cfg_succ_reaches cfg_reaches_refl by blast

lemma cfg_reaches_trans:
  "cfg_reaches g a b \<Longrightarrow> cfg_reaches g b c \<Longrightarrow> cfg_reaches g a c"
  by (auto simp: cfg_reaches_def)

lemma cfg_reaches_edge:
  "(u, a, w) \<in> edges g \<Longrightarrow> cfg_reaches g u w"
  by (rule cfg_succ_imp_reaches) (auto simp: cfg_succ_def cfg_succ_rel_def)

lemma cfg_reaches_combine_call:
  "ct \<in> combines g \<Longrightarrow> cfg_reaches g (combine_call_node ct) (combine_return_node ct)"
  by (rule cfg_succ_imp_reaches) (auto simp: cfg_succ_def cfg_succ_rel_def)

lemma cfg_reaches_combine_exit:
  "ct \<in> combines g \<Longrightarrow> cfg_reaches g (combine_exit_node ct) (combine_return_node ct)"
  by (rule cfg_succ_imp_reaches) (auto simp: cfg_succ_def cfg_succ_rel_def)

lemma cfg_reaches_mk_mono:
  assumes "E1 \<subseteq> E2" "C1 \<subseteq> C2"
  assumes "cfg_reaches (mk_cfg a b E1 C1) v w"
  shows "cfg_reaches (mk_cfg a' b' E2 C2) v w"
  by (rule cfg_reaches_mono[OF _ _ assms(3)]) (use assms in auto)

lemma compile_entry_cfg_reaches_exit:
  "compile \<Pi> lay c n = (n', en, ex, E, C) \<Longrightarrow>
   cfg_reaches (mk_cfg en ex E C) en ex"
proof (induction c arbitrary: n n' en ex E C rule: com.induct)
  case SKIP
  then show ?case by (auto intro: cfg_reaches_edge)
next
  case (Assign x a)
  then show ?case by (auto intro: cfg_reaches_edge)
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
      c1': "compile \<Pi> lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2': "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and res: "en = en1" "ex = ex2"
             "E = E1 \<union> (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}) \<union> E2" "C = C1 \<union> C2"
    using Seq.prems by (auto split: prod.splits)
  have r1: "cfg_reaches (mk_cfg en ex E C) en1 ex1"
    by (rule cfg_reaches_mk_mono[OF _ _ Seq.IH(1)[OF c1']]) (use res in auto)
  have r2: "cfg_reaches (mk_cfg en ex E C) en2 ex2"
    by (rule cfg_reaches_mk_mono[OF _ _ Seq.IH(2)[OF c2']]) (use res in auto)
  have re: "cfg_reaches (mk_cfg en ex E C) ex1 en2"
    using res by (auto intro: cfg_reaches_edge cfg_reaches_refl)
  show ?case using r1 r2 re res cfg_reaches_trans by blast
next
  case (If b c1 c2)
  obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
      c1': "compile \<Pi> lay c1 (Suc n) = (n1, en1, ex1, E1, C1)"
    and c2': "compile \<Pi> lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and res: "en = n" "ex = n2"
             "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2 \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
             "C = C1 \<union> C2"
    using If.prems by (auto split: prod.splits)
  have e_en1: "cfg_reaches (mk_cfg en ex E C) n en1"
    using res by (auto intro: cfg_reaches_edge)
  have r1: "cfg_reaches (mk_cfg en ex E C) en1 ex1"
    by (rule cfg_reaches_mk_mono[OF _ _ If.IH(1)[OF c1']]) (use res in auto)
  have ex1_xn: "cfg_reaches (mk_cfg en ex E C) ex1 n2"
    using res by (auto intro: cfg_reaches_edge)
  show ?case using e_en1 r1 ex1_xn res cfg_reaches_trans by blast
next
  case (While b c)
  obtain n1 en1 ex1 E1 C1 where
      cc: "compile \<Pi> lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and res: "en = n" "ex = n1"
             "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, n)}"
             "C = C1"
    using While.prems by (auto split: prod.splits)
  show ?case using res by (auto intro: cfg_reaches_edge)
next
  case (Scope c)
  obtain m ein exin Ein Cin where
      cc: "compile \<Pi> lay c (Suc n) = (m, ein, exin, Ein, Cin)"
    and res: "en = n" "ex = m"
             "E = Ein \<union> {(n, EA_Enter [] [], ein)}"
             "C = Cin \<union> {(n, exin, m, None)}"
    using Scope.prems by (auto split: prod.splits)
  have comb: "(n, exin, m, None) \<in> C"
    using res by auto
  have comb_cfg: "(n, exin, m, None) \<in> combines (mk_cfg en ex E C)"
    using comb res by simp
  have r: "cfg_reaches (mk_cfg en ex E C) (combine_call_node (n, exin, m, None)) (combine_return_node (n, exin, m, None))"
    using comb_cfg by (rule cfg_reaches_combine_call)
  show ?case using r res by (simp add: combine_call_node_def combine_return_node_def)
next
  case (Call dst p actuals)
  show ?case
  proof (cases "\<Pi> p")
    case None
    then show ?thesis using Call.prems by (auto split: option.splits prod.splits intro: cfg_reaches_refl)
  next
    case (Some decl)
    have PIp[simp]: "\<Pi> p = Some decl"
      using Some by simp
    show ?thesis
    proof (cases "lay p")
      case None
      then show ?thesis using Call.prems Some by (auto split: prod.splits intro: cfg_reaches_refl)
    next
      case (Some info)
      then obtain en_p ex_p Ns_p E_p C_p where info'[simp]: "info = (en_p, ex_p, Ns_p, E_p, C_p)"
        by (cases info) simp
      have layp[simp]: "lay p = Some (en_p, ex_p, Ns_p, E_p, C_p)"
        using Some by simp
      have eq:
        "(n + 2, n, n + 1,
          {(n, EA_Enter (formals decl) actuals, en_p)},
          {(n, ex_p, n + 1, dst)}) = (n', en, ex, E, C)"
        using Call.prems by auto
      have en_n[simp]: "en = n" and ex_n[simp]: "ex = n + 1"
        using eq by simp_all
      have E_n[simp]: "E = {(n, EA_Enter (formals decl) actuals, en_p)}"
        and C_n[simp]: "C = {(n, ex_p, n + 1, dst)}"
        using eq by simp_all
      have comb: "(n, ex_p, n + 1, dst) \<in> C"
        by simp
      have comb_cfg: "(n, ex_p, n + 1, dst) \<in> combines (mk_cfg en ex E C)"
        using comb by simp
      have r: "cfg_reaches (mk_cfg en ex E C) (combine_call_node (n, ex_p, n + 1, dst)) (combine_return_node (n, ex_p, n + 1, dst))"
        using comb_cfg by (rule cfg_reaches_combine_call)
      have r': "cfg_reaches (mk_cfg en ex E C) n (n + 1)"
        using r by (simp add: combine_call_node_def combine_return_node_def)
      show ?thesis using r' by simp
    qed
  qed
next
  case Restore
  then have [simp]: "n' = n" "en = n" "ex = n" "E = {}" "C = {}"
    by simp_all
  show ?case
    by (simp add: cfg_reaches_refl)
qed

lemma compile_prog_entry_cfg_reaches_exit:
  "cfg_reaches (compile_prog \<Pi> ps main)
     (cfg_entry (compile_prog \<Pi> ps main)) (cfg_exit (compile_prog \<Pi> ps main))"
proof -
  obtain n1 lay E_proc C_proc where
    procs: "compile_procs_list \<Pi> ps (\<lambda>_. None) 0 = (n1, lay, E_proc, C_proc)"
    by (cases "compile_procs_list \<Pi> ps (\<lambda>_. None) 0") auto
  obtain n2 en ex E_main C_main where
    cmain: "compile \<Pi> lay main n1 = (n2, en, ex, E_main, C_main)"
    by (cases "compile \<Pi> lay main n1") auto
  have g_eq: "compile_prog \<Pi> ps main = mk_cfg en ex (E_proc \<union> E_main) (C_proc \<union> C_main)"
    using procs cmain
    by (simp add: compile_prog_def compile_prog_with_regions_def Let_def)
  have rm: "cfg_reaches (mk_cfg en ex E_main C_main) en ex"
    by (rule compile_entry_cfg_reaches_exit[OF cmain])
  have lift: "cfg_reaches (mk_cfg en ex (E_proc \<union> E_main) (C_proc \<union> C_main)) en ex"
  proof (rule cfg_reaches_mk_mono)
    show "E_main \<subseteq> E_proc \<union> E_main" by auto
    show "C_main \<subseteq> C_proc \<union> C_main" by auto
    show "cfg_reaches (mk_cfg en ex E_main C_main) en ex" by (rule rm)
  qed
  show ?thesis using lift unfolding g_eq by simp
qed

end
