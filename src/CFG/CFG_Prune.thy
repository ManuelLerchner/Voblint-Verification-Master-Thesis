theory CFG_Prune
  imports CFG_Collect_IP IMP2_Proc_to_CFG
begin

(*
  Dead-procedure pruning for interprocedural CFGs.

  `compile_prog` unions every procedure's edges/combines into the graph,
  whether or not the procedure is ever called.  A defined-but-uncalled
  procedure leaves body nodes that are edge-targets yet cannot reach the
  program exit -- breaking the "every program point reaches the exit"
  well-formedness condition.

  We prune the graph to the backward cone of the exit (the live, reachable
  nodes), keeping the solver on the full graph.  The collecting value at the
  exit is unchanged (a witness from entry to exit stays inside the cone), so
  soundness transports back to the unpruned analysis with no well-formedness
  hypothesis.
*)

(* -- Interprocedural reachability ---------------------------------------- *)

(* One dependency step: u's abstract value feeds w's right-hand side, either
   via an edge (u -> w) or a combine (call site or callee exit of w). *)
definition ip_succ :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> bool" where
  "ip_succ g u w \<longleftrightarrow>
     (\<exists>a. (u, a, w) \<in> edges g)
   \<or> (\<exists>e. (u, e, w) \<in> combines g)
   \<or> (\<exists>c. (c, u, w) \<in> combines g)"

definition ip_reaches :: "cfg \<Rightarrow> pp \<Rightarrow> pp \<Rightarrow> bool" where
  "ip_reaches g v v0 \<longleftrightarrow> (v, v0) \<in> {(u, w). ip_succ g u w}\<^sup>*"

definition cone :: "cfg \<Rightarrow> pp \<Rightarrow> pp set" where
  "cone g v0 = {v. ip_reaches g v v0}"

definition prune_to :: "cfg \<Rightarrow> pp \<Rightarrow> cfg" where
  "prune_to g v0 =
     mk_ip_cfg (cfg_entry g) (cfg_exit g)
       {e \<in> edges g. snd (snd e) \<in> cone g v0}
       {ct \<in> combines g. snd (snd ct) \<in> cone g v0}"

definition prune_cfg :: "cfg \<Rightarrow> cfg" where
  "prune_cfg g = prune_to g (cfg_exit g)"

(* -- reaches basics ------------------------------------------------------ *)

lemma ip_reaches_refl: "ip_reaches g v v"
  by (simp add: ip_reaches_def)

lemma ip_succ_reaches:
  "ip_succ g u w \<Longrightarrow> ip_reaches g w v0 \<Longrightarrow> ip_reaches g u v0"
  by (auto simp: ip_reaches_def intro: converse_rtrancl_into_rtrancl)

lemma ip_succ_mono:
  assumes "edges g1 \<subseteq> edges g2" "combines g1 \<subseteq> combines g2" "ip_succ g1 u w"
  shows "ip_succ g2 u w"
  using assms unfolding ip_succ_def by blast

lemma ip_reaches_mono:
  assumes "edges g1 \<subseteq> edges g2" "combines g1 \<subseteq> combines g2" "ip_reaches g1 v w"
  shows "ip_reaches g2 v w"
proof -
  have "{(u, w). ip_succ g1 u w} \<subseteq> {(u, w). ip_succ g2 u w}"
    using ip_succ_mono[OF assms(1,2)] by auto
  then have "{(u, w). ip_succ g1 u w}\<^sup>* \<subseteq> {(u, w). ip_succ g2 u w}\<^sup>*"
    by (rule rtrancl_mono)
  thus ?thesis using assms(3) unfolding ip_reaches_def by blast
qed

(* -- prune_to selectors -------------------------------------------------- *)

lemma edges_prune_to[simp]:
  "edges (prune_to g v0) = {e \<in> edges g. snd (snd e) \<in> cone g v0}"
  by (simp add: prune_to_def)

lemma combines_prune_to[simp]:
  "combines (prune_to g v0) = {ct \<in> combines g. snd (snd ct) \<in> cone g v0}"
  by (simp add: prune_to_def)

lemma cfg_entry_prune_to[simp]: "cfg_entry (prune_to g v0) = cfg_entry g"
  by (simp add: prune_to_def)

lemma cfg_exit_prune_to[simp]: "cfg_exit (prune_to g v0) = cfg_exit g"
  by (simp add: prune_to_def)

lemma edges_prune_to_sub: "edges (prune_to g v0) \<subseteq> edges g"
  by auto

lemma combines_prune_to_sub: "combines (prune_to g v0) \<subseteq> combines g"
  by auto

lemma finite_edges_prune_to:
  "finite (edges g) \<Longrightarrow> finite (edges (prune_to g v0))"
  using edges_prune_to_sub by (rule_tac finite_subset) auto

lemma finite_combines_prune_to:
  "finite (combines g) \<Longrightarrow> finite (combines (prune_to g v0))"
  using combines_prune_to_sub by (rule_tac finite_subset) auto

(* The reach discharge for the retired plain top-down solver used to live here.
   The side solver now discharges reachability via dep_side_rhs_tree_ip_* and
   ip_reaches_imp_trans_dep_or_eq_side (TD_Side_IP_CFG / TD_Side_IP_Soundness).
   The graph-level pruning frame below is solver-agnostic. *)

(* -- collect frame: witness transport ------------------------------------ *)

lemma ip_witness_prune_to:
  assumes "ip_witness g S v t"
  shows "ip_reaches g v v0 \<longrightarrow> ip_witness (prune_to g v0) S v t"
  using assms
proof (induction rule: ip_witness.induct)
  case (entry v s Sa)
  then show ?case
    by (auto intro: ip_witness.entry)
next
  case (edge u a v Sa s t)
  show ?case
  proof (rule impI)
    assume rv: "ip_reaches g v v0"
    have ruv: "ip_reaches g u v0"
      using edge.hyps(1) rv ip_succ_reaches unfolding ip_succ_def by blast
    have wu: "ip_witness (prune_to g v0) Sa u s" using edge.IH ruv by blast
    have ev: "(u, a, v) \<in> edges (prune_to g v0)"
      using edge.hyps(1) rv by (simp add: cone_def)
    show "ip_witness (prune_to g v0) Sa v t"
      by (rule ip_witness.edge[OF ev wu edge.hyps(3)])
  qed
next
  case (combine c ex v Sa s t)
  show ?case
  proof (rule impI)
    assume rv: "ip_reaches g v v0"
    have rc: "ip_reaches g c v0"
      using combine.hyps(1) rv ip_succ_reaches unfolding ip_succ_def by blast
    have rex: "ip_reaches g ex v0"
      using combine.hyps(1) rv ip_succ_reaches unfolding ip_succ_def by blast
    have wc: "ip_witness (prune_to g v0) Sa c s" using combine.IH(1) rc by blast
    have wex: "ip_witness (prune_to g v0) Sa ex t" using combine.IH(2) rex by blast
    have cv: "(c, ex, v) \<in> combines (prune_to g v0)"
      using combine.hyps(1) rv by (simp add: cone_def)
    show "ip_witness (prune_to g v0) Sa v (combine_states s t)"
      by (rule ip_witness.combine[OF cv wc wex])
  qed
qed

lemma cfg_collect_ip_prune_exit:
  "cfg_collect_ip g S (cfg_exit g) \<subseteq> cfg_collect_ip (prune_cfg g) S (cfg_exit g)"
proof
  fix t assume "t \<in> cfg_collect_ip g S (cfg_exit g)"
  then have wg: "ip_witness g S (cfg_exit g) t"
    by (simp add: cfg_collect_ip_eq_paths cfg_collect_ip_paths_def)
  have wp: "ip_witness (prune_to g (cfg_exit g)) S (cfg_exit g) t"
    using ip_witness_prune_to[OF wg] ip_reaches_refl by blast
  show "t \<in> cfg_collect_ip (prune_cfg g) S (cfg_exit g)"
    using wp by (simp add: prune_cfg_def cfg_collect_ip_eq_paths cfg_collect_ip_paths_def)
qed

(* -- entry reaches exit for compile_prog --------------------------------- *)

lemma ip_succ_imp_reaches: "ip_succ g u w \<Longrightarrow> ip_reaches g u w"
  using ip_succ_reaches ip_reaches_refl by blast

lemma ip_reaches_trans:
  "ip_reaches g a b \<Longrightarrow> ip_reaches g b c \<Longrightarrow> ip_reaches g a c"
  by (auto simp: ip_reaches_def)

lemma ip_reaches_edge:
  "(u, a, w) \<in> edges g \<Longrightarrow> ip_reaches g u w"
  by (rule ip_succ_imp_reaches) (auto simp: ip_succ_def)

lemma ip_reaches_combine_call:
  "(u, e, w) \<in> combines g \<Longrightarrow> ip_reaches g u w"
  by (rule ip_succ_imp_reaches) (auto simp: ip_succ_def)

lemma ip_reaches_combine_exit:
  "(c, u, w) \<in> combines g \<Longrightarrow> ip_reaches g u w"
  by (rule ip_succ_imp_reaches) (auto simp: ip_succ_def)

lemma ip_reaches_mk_mono:
  assumes "E1 \<subseteq> E2" "C1 \<subseteq> C2"
  assumes "ip_reaches (mk_ip_cfg a b E1 C1) v w"
  shows "ip_reaches (mk_ip_cfg a' b' E2 C2) v w"
  by (rule ip_reaches_mono[OF _ _ assms(3)]) (use assms in auto)

lemma compile_pcom_entry_ip_reaches_exit:
  "compile_pcom pi lay c n = (n', en, ex, E, C) \<Longrightarrow>
   ip_reaches (mk_ip_cfg en ex E C) en ex"
proof (induction c arbitrary: n n' en ex E C rule: pcom.induct)
  case PSKIP
  then show ?case by (auto intro: ip_reaches_edge)
next
  case (PAssign x a)
  then show ?case by (auto intro: ip_reaches_edge)
next
  case (PSeq c1 c2)
  obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
        c1: "compile_pcom pi lay c1 n = (n1, en1, ex1, E1, C1)"
    and c2: "compile_pcom pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and res: "en = en1" "ex = ex2"
             "E = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2" "C = C1 \<union> C2"
    using PSeq.prems by (auto split: prod.splits)
  have r1: "ip_reaches (mk_ip_cfg en ex E C) en1 ex1"
  proof (rule ip_reaches_mk_mono)
    show "E1 \<subseteq> E" using res by auto
    show "C1 \<subseteq> C" using res by auto
    show "ip_reaches (mk_ip_cfg en1 ex1 E1 C1) en1 ex1" using PSeq.IH(1)[OF c1] .
  qed
  have r2: "ip_reaches (mk_ip_cfg en ex E C) en2 ex2"
  proof (rule ip_reaches_mk_mono)
    show "E2 \<subseteq> E" using res by auto
    show "C2 \<subseteq> C" using res by auto
    show "ip_reaches (mk_ip_cfg en2 ex2 E2 C2) en2 ex2" using PSeq.IH(2)[OF c2] .
  qed
  have re: "ip_reaches (mk_ip_cfg en ex E C) ex1 en2"
    using res by (auto intro: ip_reaches_edge)
  show ?case
    using r1 re r2 res by (auto intro: ip_reaches_trans)
next
  case (PIf b c1 c2)
  obtain n1 en1 ex1 E1 C1 n2 en2 ex2 E2 C2 where
        c1: "compile_pcom pi lay c1 (Suc n) = (n1, en1, ex1, E1, C1)"
    and c2: "compile_pcom pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    and res: "en = n" "ex = n2"
             "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
                   \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
             "C = C1 \<union> C2"
    using PIf.prems by (auto split: prod.splits)
  have e_en1: "ip_reaches (mk_ip_cfg en ex E C) n en1"
    using res by (auto intro: ip_reaches_edge)
  have r1: "ip_reaches (mk_ip_cfg en ex E C) en1 ex1"
  proof (rule ip_reaches_mk_mono)
    show "E1 \<subseteq> E" using res by auto
    show "C1 \<subseteq> C" using res by auto
    show "ip_reaches (mk_ip_cfg en1 ex1 E1 C1) en1 ex1" using PIf.IH(1)[OF c1] .
  qed
  have ex1_xn: "ip_reaches (mk_ip_cfg en ex E C) ex1 n2"
    using res by (auto intro: ip_reaches_edge)
  show ?case
    using e_en1 r1 ex1_xn res by (auto intro: ip_reaches_trans)
next
  case (PWhile b c)
  obtain n1 en1 ex1 E1 C1 where
        cc: "compile_pcom pi lay c (Suc n) = (n1, en1, ex1, E1, C1)"
    and res: "en = n" "ex = n1"
             "E = {(n, EA_Assume b, en1), (n, EA_AssumeNot b, n1)} \<union> E1
                   \<union> {(ex1, EA_Nop, n)}"
             "C = C1"
    using PWhile.prems by (auto split: prod.splits)
  show ?case using res by (auto intro: ip_reaches_edge)
next
  case (PScope c)
  obtain m ein exin Ein Cin where
        cc: "compile_pcom pi lay c (Suc n) = (m, ein, exin, Ein, Cin)"
    and res: "en = n" "ex = m"
             "E = Ein \<union> {(n, EA_Nop, ein)}"
             "C = Cin \<union> {(n, exin, m)}"
    using PScope.prems by (auto split: prod.splits)
  show ?case using res by (auto intro: ip_reaches_combine_call)
next
  case (PCall p)
  show ?case
  proof (cases "lay p")
    case None
    then show ?thesis using PCall.prems by (auto intro: ip_reaches_refl)
  next
    case (Some info)
    obtain en_p ex_p E_p C_p where info: "info = (en_p, ex_p, E_p, C_p)"
      by (cases info)
    have res: "en = n" "ex = n + 1" "E = {(n, EA_Enter, en_p)}" "C = {(n, ex_p, n + 1)}"
      using PCall.prems Some info by auto
    show ?thesis using res by (auto intro: ip_reaches_combine_call)
  qed
next
  case PRestore
  then show ?case by (auto intro: ip_reaches_refl)
qed

lemma compile_prog_entry_ip_reaches_exit:
  "ip_reaches (compile_prog pi ps main)
     (cfg_entry (compile_prog pi ps main)) (cfg_exit (compile_prog pi ps main))"
proof -
  obtain n1 lay E_proc C_proc where
    procs: "compile_procs_list pi ps (\<lambda>_. None) 0 = (n1, lay, E_proc, C_proc)"
    by (cases "compile_procs_list pi ps (\<lambda>_. None) 0") auto
  obtain n2 en ex E_main C_main where
    cmain: "compile_pcom pi lay main n1 = (n2, en, ex, E_main, C_main)"
    by (cases "compile_pcom pi lay main n1") auto
  have g_eq: "compile_prog pi ps main = mk_ip_cfg en ex (E_proc \<union> E_main) (C_proc \<union> C_main)"
    using procs cmain
    by (simp add: compile_prog_def compile_prog_with_regions_def Let_def)
  have rm: "ip_reaches (mk_ip_cfg en ex E_main C_main) en ex"
    by (rule compile_pcom_entry_ip_reaches_exit[OF cmain])
  have lift: "ip_reaches (mk_ip_cfg en ex (E_proc \<union> E_main) (C_proc \<union> C_main)) en ex"
  proof (rule ip_reaches_mk_mono)
    show "E_main \<subseteq> E_proc \<union> E_main" by auto
    show "C_main \<subseteq> C_proc \<union> C_main" by auto
    show "ip_reaches (mk_ip_cfg en ex E_main C_main) en ex" by (rule rm)
  qed
  show ?thesis using lift unfolding g_eq by simp
qed

end
