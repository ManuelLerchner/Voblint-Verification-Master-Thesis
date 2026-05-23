theory CFG_Collecting
  imports IMP2_to_CFG IMP2_Collecting CFG_Path
begin

(*
  CFG -- Collecting Semantics.

  Defines the collecting semantics directly on the CFG as the canonical
  fixpoint of the transfer functions over edges, then proves it agrees
  with path-based collecting (cfg_edges_collect).  Used in
  Equations/Constraint_System_Sound.thy via runs_to.
*)

(* \<midarrow>\<midarrow> Per-Edge Transfer Function on State Sets \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop          S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s : S}"
  | "edge_collect (EA_Assume b)    S = Collect (\<lambda>s. s \<in> S \<and> bval b s)"
  | "edge_collect (EA_AssumeNot b) S = Collect (\<lambda>s. s \<in> S \<and> \<not> bval b s)"

lemma edge_collect_empty_set[simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms  apply (cases a)
  by(auto)

(* \<midarrow>\<midarrow> Per-Edge Transfer Function on State Sets \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

(*
  edges_collect aggregates the resulting state after walking along a list of edges
  and running edge_collect each time
*)
fun edges_collect :: "(edge_action * pp) list => store set => store set" where
  "edges_collect [] S = S"
| "edges_collect ((a, _) # es) S = edges_collect es (edge_collect a S)"


lemma edges_collect_empty_set[simp]: "edges_collect es {} = {}"
  apply (induction es)
  by(auto)

lemma edges_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> edges_collect es S \<subseteq> edges_collect es T"
  apply (induction es arbitrary: S T)
  apply(auto)
  by (meson edge_collect_mono in_mono)

lemma edges_collect_append:
  "edges_collect (es1 @ es2) S = edges_collect es2 (edges_collect es1 S)"
  apply (induction es1 arbitrary: S)
  by auto

(*
  edges_collect only inspects edge actions; the pp component of each
  step is discarded.  Hence shifting pp's via offset_path is invisible
  to edges_collect.
*)
lemma edges_collect_offset_path[simp]:
  "edges_collect (offset_path k es) S = edges_collect es S"
  apply (induction es arbitrary: S)
  by(auto)


(* \<midarrow>\<midarrow> CFG Collecting Environment \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  A collecting environment maps each program point to the set of states
  that can appear there during any execution starting from some fixed
  initial set.
*)

type_synonym cenv = "pp => store set"


(* \<midarrow>\<midarrow> Collecting Transformer for One Program Point \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  collect_pp g rho v = join of edge_collect(a)(rho u) over all (u,a,v) in g.
  This is the single-step "push" of states through each incoming edge.
*)

definition collect_pp :: "cfg => cenv => pp => store set" where
  "collect_pp g rho v =
     Union {edge_collect a (rho u) | u a. (u, a, v) : edges g}"

(* \<midarrow>\<midarrow> Least Fixpoint (Collecting Semantics over CFG) \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)
(*
  Given an initial store set S at the entry, the CFG collecting semantics
  is the least fixpoint of the monotone transformer collect_pp.
*)

definition cfg_collect_F :: "cfg => store set => cenv => cenv" where
  "cfg_collect_F g S rho v =
     (if v = cfg_entry g then S Un collect_pp g rho v
      else collect_pp g rho v)"

definition cfg_collect :: "cfg => store set => cenv" where
  "cfg_collect g S = lfp (cfg_collect_F g S)"

(* \<midarrow>\<midarrow> Monotonicity of collect_pp \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>
   Required for lfp to be well-defined. *)

lemma collect_pp_mono:
  "mono (\<lambda>rho. collect_pp g rho v)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  then have ru: "\<And>u. rho1 u \<subseteq> rho2 u"
    by (simp add: le_fun_def)
  have edge: "\<And>u a. (u, a, v) \<in> edges g \<Longrightarrow> edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    by (meson ru edge_collect_mono)
  then show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def by blast
qed

lemma cfg_collect_F_mono:
  "mono (cfg_collect_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "cfg_collect_F g S rho1 \<le> cfg_collect_F g S rho2"
    unfolding cfg_collect_F_def le_fun_def
    using collect_pp_mono le monotoneD by fastforce
qed

lemma cfg_collect_lfp_unfold:
  "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
  unfolding cfg_collect_def
  by (simp add: cfg_collect_F_mono def_lfp_unfold)

lemma cfg_collect_F_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_F g S rho \<le> cfg_collect_F g S' rho"
  unfolding cfg_collect_F_def le_fun_def by auto

lemma cfg_collect_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect g S \<le> cfg_collect g S'"
  unfolding cfg_collect_def
  by (rule lfp_mono) (rule cfg_collect_F_mono_S)

(* Path-based collecting environment. *)
definition cfg_edges_collect :: "cfg => store set => pp => store set" where
  "cfg_edges_collect g S v =
     (\<Union>es\<in>{es. cfg_path g (cfg_entry g) es v}. edges_collect es S)"

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
  apply(cases a)
  by(auto)


(* One CFG step extends path-based collecting. *)
lemma cfg_edges_collect_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_edges_collect g S u) \<subseteq> cfg_edges_collect g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_edges_collect g S u)"
  then obtain es where es: "cfg_path g (cfg_entry g) es u"
    and x: "x \<in> edge_collect a (edges_collect es S)"
    unfolding cfg_edges_collect_def
    by (smt (verit) UN_iff edge_collect_member mem_Collect_eq)
    
  then obtain s where s: "s \<in> edges_collect es S"
    and x: "x \<in> edge_collect a {s}"
    using edge_collect_member
    by meson 

  have p: "cfg_path g u [(a, v)] v"
    by (rule cfg_path.step[OF e cfg_path.empty])
  have es': "cfg_path g (cfg_entry g) (es @ [(a, v)]) v"
    by (rule cfg_path_append[OF es p])
  have "x \<in> edges_collect (es @ [(a, v)]) S"
    using x s unfolding edges_collect_append edges_collect.simps
    using edge_collect_member by blast 
 
  then show "x \<in> cfg_edges_collect g S v"
    unfolding cfg_edges_collect_def using es' by auto
qed

lemma cfg_edges_collect_entry:
  "S \<subseteq> cfg_edges_collect g S (cfg_entry g)"
  unfolding cfg_edges_collect_def by(auto)
 
(*
  Post-fixpoint: cfg_edges_collect satisfies cfg_collect_F.
  Proof via edges_collect_append + cfg_path_append; one line per edge action.
*)
lemma cfg_edges_collect_post:
  "cfg_collect_F g S (cfg_edges_collect g S) v \<subseteq> cfg_edges_collect g S v"
  unfolding cfg_collect_F_def
  apply(auto)
  using cfg_edges_collect_entry apply blast
  using cfg_edges_collect_step collect_pp_def apply fastforce
  using cfg_edges_collect_step collect_pp_def by fastforce


lemma cfg_collect_le_edges_collect:
  "cfg_collect g S v \<subseteq> cfg_edges_collect g S v"
proof -
  have pf: "cfg_collect_F g S (cfg_edges_collect g S) \<le> cfg_edges_collect g S"
    unfolding le_fun_def using cfg_edges_collect_post by simp
  have "lfp (cfg_collect_F g S) \<le> cfg_edges_collect g S"
    using pf cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def le_fun_def by simp
qed

(* \<midarrow>\<midarrow> to_cfg / compile alignment \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

lemma to_cfg_compile:
  obtains n' en ex E where
    "compile c 0 = (n', en, ex, E)"
    "cfg_entry (to_cfg c) = en"
    "cfg_exit (to_cfg c) = ex"
    "edges (to_cfg c) = E"
  unfolding to_cfg_def
  by (cases "compile c 0") (auto simp: Let_def)

lemma edges_collect_member:
  "x \<in> edges_collect es S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edges_collect es {s})"
proof (induction es arbitrary: S x)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    apply(auto)
    apply (metis edge_collect_member ep local.Cons edges_collect.simps(2))
    by (meson empty_subsetI insert_subset edges_collect_mono_strong subsetD)
qed

lemma edges_collect_nop_append:
  "edges_collect (es1 @ [(EA_Nop, w)] @ es2) S = edges_collect es2 (edges_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  show ?case by (simp add: edges_collect_append)
next
  case (Cons e es1)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep edges_collect.simps edges_collect_append Cons by simp
qed

lemma compile_Seq_0:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "compile (c1 ;; c2) 0 = (n2, en1, ex2, E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2)"
  using assms by (simp add: compile.simps Let_def)

lemma compile_While_0: 
  assumes "compile c 1 = (n1, en1, ex1, E1)"
  shows "compile (WHILE b DO c) 0 =
         (Suc n1, (0::pp), n1,
          {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)})"
  using assms by (simp add: compile.simps Let_def)

lemma compile_If_0:
  assumes c1: "compile c1 1 = (n1, en1, ex1, E1)"
    and   c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "compile (IF b THEN c1 ELSE c2) 0 =
         (n2 + 1, (0::pp), n2,
          {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
          \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)})"
  using assms by (simp add: compile.simps Let_def)

lemma cfg_edges_entry_exit_Seq:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    and "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
proof -
  define E12 where "E12 = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
  from c1 c2 have cmp: "compile (c1 ;; c2) 0 = (n2, en1, ex2, E12)"
    unfolding E12_def by (rule compile_Seq_0)
  show "edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    unfolding to_cfg_def E12_def[symmetric] cmp by simp
  show "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    unfolding to_cfg_def cmp by simp
  show "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
    unfolding to_cfg_def cmp by simp
qed

lemma cfg_edges_entry_exit_If:
  assumes c1: "compile c1 1 = (n1, en1, ex1, E1)"
    and   c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "edges (to_cfg (IF b THEN c1 ELSE c2)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
         \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    and "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n2"
proof -
  define EI where "EI = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
                       \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
  from c1 c2 have cmp: "compile (IF b THEN c1 ELSE c2) 0 = (n2 + 1, 0, n2, EI)"
    unfolding EI_def by (rule compile_If_0)
  show "edges (to_cfg (IF b THEN c1 ELSE c2)) =
        {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
        \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    unfolding to_cfg_def EI_def[symmetric] cmp by simp
  show "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    unfolding to_cfg_def cmp by simp
  show "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n2"
    unfolding to_cfg_def cmp by simp
qed

lemma cfg_edges_entry_exit_While:
  assumes c: "compile c 1 = (n1, en1, ex1, E1)"
  shows "edges (to_cfg (WHILE b DO c)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    and "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
proof -
  define EW where "EW = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
  from c have cmp: "compile (WHILE b DO c) 0 = (Suc n1, 0, n1, EW)"
    unfolding EW_def by (rule compile_While_0)
  show "edges (to_cfg (WHILE b DO c)) =
        {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    unfolding to_cfg_def EW_def[symmetric] cmp by simp
  show "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    unfolding to_cfg_def cmp by simp
  show "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
    unfolding to_cfg_def cmp by simp
qed

lemma cfg_path_mono_edges:
  assumes sub: "edges g \<subseteq> edges h"
    and p: "cfg_path g u es v"
  shows "cfg_path h u es v"
  using p sub by (induction rule: cfg_path.induct) (auto intro: cfg_path.intros subsetD)

lemma mem_edges_collect_from_set:
  "t \<in> edges_collect es M \<Longrightarrow> \<exists>m\<in>M. t \<in> edges_collect es {m}"
proof (induction es arbitrary: M t)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  obtain M' where M': "M' = edge_collect a M" by simp
  from Cons.prems ew obtain t': "t \<in> edges_collect es M'"
    using M' edges_collect.simps(2) by blast
  from Cons.IH[OF this] obtain m where m: "m \<in> M'" and tm: "t \<in> edges_collect es {m}"
    by blast
  from m have "m \<in> edge_collect a M"
    using M' by auto

  then obtain m0 where m0: "m0 \<in> M" and mm: "m \<in> edge_collect a {m0}"
    by (cases a) (auto simp: mem_Collect_eq)
  have "t \<in> edges_collect (e # es) {m0}"
    unfolding ew edges_collect.simps mm tm
    using mm edges_collect_member tm by blast
  with m0 show ?case by blast
qed

(*
  Edge classification in `to_cfg (c1 ;; c2)`.  By compile_fresh / compile_ge:
  - E1 edges have both endpoints < n1
  - the bridge (ex1, EA_Nop, en20+n1) has source ex1 < n1
  - offset_edges n1 E20 has all endpoints \<ge> n1
  So an edge's source decides which subset it belongs to.
*)

lemma compound_Seq_edge_src_ge_n1:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and u_ge: "n1 \<le> u"
  shows "(u, a, w) \<in> offset_edges n1 E20"
proof -
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have Eseq: "edges (to_cfg (c1 ;; c2)) =
              E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    using cfg_edges_entry_exit_Seq[OF c1 c2_n] by simp
  from compile_fresh[OF c1] have E1_src_lt: "\<forall>e \<in> E1. fst e < n1" by simp
  from compile_fresh[OF c1] have ex1_lt: "ex1 < n1" by simp
  show ?thesis
    using edge u_ge Eseq E1_src_lt ex1_lt by force
qed

lemma compound_Seq_edge_src_lt_n1:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and u_lt: "u < n1"
  shows "(u, a, w) \<in> E1 \<or> (u = ex1 \<and> a = EA_Nop \<and> w = en20 + n1)"
proof -
  have c2_n: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0, of n1] by simp
  have Eseq: "edges (to_cfg (c1 ;; c2)) =
              E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    using cfg_edges_entry_exit_Seq[OF c1 c2_n] by simp
  from compile_ge[OF c2_n] have E2_src_ge: "\<forall>e \<in> offset_edges n1 E20. n1 \<le> fst e" by simp
  show ?thesis
    using edge u_lt Eseq E2_src_ge by force
qed

(*
  A compound-Seq path starting at u \<ge> n1 stays in the c2 region; its
  step list is the offset_path of a path in to_cfg c2.
*)
lemma cfg_path_Seq_in_c2:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "cfg_path (to_cfg (c1 ;; c2)) u es v"
    and u_ge: "n1 \<le> u"
  shows "\<exists>es'. es = offset_path n1 es' \<and>
                cfg_path (to_cfg c2) (u - n1) es' (v - n1)"
  using p u_ge
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have "u = v" by (cases rule: cfg_path.cases) simp_all
  hence "cfg_path (to_cfg c2) (u - n1) [] (v - n1)" by (simp add: cfg_path.empty)
  thus ?case by (rule_tac x = "[]" in exI) simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and ps: "cfg_path (to_cfg (c1 ;; c2)) w tl v"
    by (cases rule: cfg_path.cases) auto
  have e_off: "(u, a, w) \<in> offset_edges n1 E20"
    using compound_Seq_edge_src_ge_n1[OF c1 c2_0 e_compound Cons.prems(2)] .
  from e_off obtain u0 w0 where
        decomp: "u = u0 + n1" "w = w0 + n1" "(u0, a, w0) \<in> E20"
    unfolding offset_edges_def by auto
  have kw: "n1 \<le> w" using decomp(2) by simp
  from Cons.IH[OF ps kw] obtain es' where
        es_eq: "tl = offset_path n1 es'"
    and pe2: "cfg_path (to_cfg c2) (w - n1) es' (v - n1)"
    by auto
  have toc2_edges: "edges (to_cfg c2) = E20"
    unfolding to_cfg_def using c2_0 by (simp add: Let_def)
  have edge_c2: "(u - n1, a, w - n1) \<in> edges (to_cfg c2)"
    using toc2_edges decomp by simp
  let ?es'_full = "(a, w - n1) # es'"
  have p_full: "cfg_path (to_cfg c2) (u - n1) ?es'_full (v - n1)"
    by (rule cfg_path.step[OF edge_c2 pe2])
  have list_eq: "(a, w) # tl = offset_path n1 ?es'_full"
    using es_eq decomp(2) by simp
  show ?case
    using p_full list_eq hd_eq by (rule_tac x = "?es'_full" in exI) simp
qed

(*
  Strong Seq path split.  A path in to_cfg (c1;;c2) starting at u < n1
  and ending at the compound exit factors uniquely through the bridge
  (ex1, EA_Nop, en20+n1) into a path in to_cfg c1 (u \<to> ex1) and a
  path in to_cfg c2 (en20 \<to> ex20), with the c2-part shifted via
  offset_path n1.
*)
lemma cfg_path_Seq_split:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "cfg_path (to_cfg (c1 ;; c2)) u es (ex20 + n1)"
    and u_lt: "u < n1"
  shows "\<exists>es1 es2.
           es = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2 \<and>
           cfg_path (to_cfg c1) u es1 ex1 \<and>
           cfg_path (to_cfg c2) en20 es2 ex20"
  using p u_lt
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have eq: "u = ex20 + n1" by (cases rule: cfg_path.cases) simp_all
  with Nil.prems(2) show ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (c1 ;; c2))"
    and ps: "cfg_path (to_cfg (c1 ;; c2)) w tl (ex20 + n1)"
    by (cases rule: cfg_path.cases) auto
  from compound_Seq_edge_src_lt_n1[OF c1 c2_0 e_compound Cons.prems(2)]
  consider (E1) "(u, a, w) \<in> E1" | (bridge) "u = ex1" "a = EA_Nop" "w = en20 + n1"
    by auto
  thus ?case
  proof cases
    case E1
    from compile_fresh[OF c1] E1 have w_lt: "w < n1" by auto
    from Cons.IH[OF ps w_lt] obtain es1 es2 where
          tl_eq: "tl = es1 @ (EA_Nop, en20 + n1) # offset_path n1 es2"
      and p1: "cfg_path (to_cfg c1) w es1 ex1"
      and p2: "cfg_path (to_cfg c2) en20 es2 ex20"
      by blast
    have toc1_edges: "edges (to_cfg c1) = E1"
      unfolding to_cfg_def using c1 by (simp add: Let_def)
    have edge_c1: "(u, a, w) \<in> edges (to_cfg c1)" using E1 toc1_edges by simp
    let ?es1_full = "(a, w) # es1"
    have p1_full: "cfg_path (to_cfg c1) u ?es1_full ex1"
      by (rule cfg_path.step[OF edge_c1 p1])
    have list_eq: "(a, w) # tl = ?es1_full @ (EA_Nop, en20 + n1) # offset_path n1 es2"
      using tl_eq by simp
    show ?thesis
      using list_eq p1_full p2 hd_eq by blast
  next
    case bridge
    have w_ge: "n1 \<le> w" using bridge(3) by simp
    from cfg_path_Seq_in_c2[OF c1 c2_0 ps w_ge] obtain es' where
          tl_eq: "tl = offset_path n1 es'"
      and pe2: "cfg_path (to_cfg c2) (w - n1) es' ((ex20 + n1) - n1)"
      by auto
    have wn: "w - n1 = en20" using bridge(3) by simp
    have exn: "(ex20 + n1) - n1 = ex20" by simp
    have p2: "cfg_path (to_cfg c2) en20 es' ex20" using pe2 wn exn by simp
    have p1: "cfg_path (to_cfg c1) u [] ex1"
      using bridge(1) by (simp add: cfg_path.empty)
    have list_eq: "(a, w) # tl = [] @ (EA_Nop, en20 + n1) # offset_path n1 es'"
      using bridge tl_eq by simp
    show ?thesis
      using list_eq p1 p2 hd_eq by blast
  qed
qed

(*
  Edge classification in `to_cfg (IF b THEN c1 ELSE c2)` by source pp.
  Compound layout (compile c1 at 1, compile c2 at n10+1):
    pp 0          : entry, source of two pre-edges (Assume / AssumeNot)
    [1, n10+1)    : c1 region (offset_edges 1 E10 + source of c1-post bridge)
    [n10+1, n2)   : c2 region (offset_edges (n10+1) E20 + source of c2-post bridge)
    pp n2 = n20+(n10+1) : exit, sink (no outgoing edges)
*)

lemma compound_If_edge_src_c1:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and u_in: "1 \<le> u" and u_lt: "u < n10 + 1"
  shows "(u, a, w) \<in> offset_edges 1 E10 \<or>
         (u = ex10 + 1 \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10
             \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by simp
  from compile_ge[OF c2_n] have E2_src_ge: "\<forall>e \<in> offset_edges (n10 + 1) E20. n10 + 1 \<le> fst e"
    by simp
  from compile_ge[OF c2_n] have ex2n_ge: "n10 + 1 \<le> ex20 + (n10 + 1)" by simp
  show ?thesis
    using edge u_in u_lt Eif E2_src_ge ex2n_ge by force
qed

lemma compound_If_edge_src_c2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and edge: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and u_in: "n10 + 1 \<le> u" and u_lt: "u < n20 + (n10 + 1)"
  shows "(u, a, w) \<in> offset_edges (n10 + 1) E20 \<or>
         (u = ex20 + (n10 + 1) \<and> a = EA_Nop \<and> w = n20 + (n10 + 1))"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10
             \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by simp
  from compile_fresh[OF c1_1] have E1_src_lt: "\<forall>e \<in> offset_edges 1 E10. fst e < n10 + 1"
    by simp
  from compile_fresh[OF c1_1] have ex1_lt: "ex10 + 1 < n10 + 1" by simp
  show ?thesis
    using edge u_in u_lt Eif E1_src_lt ex1_lt by force
qed

(* The compound If exit pp n2 has no outgoing edges (it is a sink). *)
lemma compound_If_no_source_n2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
  shows "\<not> (\<exists>a w. (n20 + (n10 + 1), a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2)))"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10
             \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by simp
  from compile_fresh[OF c1_1] have E1_lt: "\<forall>e \<in> offset_edges 1 E10. fst e < n10 + 1" by simp
  from compile_fresh[OF c2_n] have E2_lt: "\<forall>e \<in> offset_edges (n10 + 1) E20. fst e < n20 + (n10 + 1)"
    by simp
  from compile_fresh[OF c1_1] have ex1_lt: "ex10 + 1 < n10 + 1" by simp
  from compile_fresh[OF c2_n] have ex2_lt: "ex20 + (n10 + 1) < n20 + (n10 + 1)" by simp
  show ?thesis
    using Eif E1_lt E2_lt ex1_lt ex2_lt by force
qed


(*
  A compound-If path from u in c1's region to the compound exit n2 factors
  uniquely as (offset_path 1 of a c1 path u-1 \<to> ex10) followed by the
  c1-post Nop bridge to n2.  Variant: cfg_path_If_factor_c2 for c2 side.
*)
lemma cfg_path_If_factor_c1:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) u es (n20 + (n10 + 1))"
    and u_in: "1 \<le> u" and u_lt: "u < n10 + 1"
  shows "\<exists>es'. es = offset_path 1 es' @ [(EA_Nop, n20 + (n10 + 1))] \<and>
                cfg_path (to_cfg c1) (u - 1) es' ex10"
  using p u_in u_lt
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have "u = n20 + (n10 + 1)" by (cases rule: cfg_path.cases) simp_all
  with Nil.prems(3) show ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and ps: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) w tl (n20 + (n10 + 1))"
    by (cases rule: cfg_path.cases) auto
  from compound_If_edge_src_c1[OF c1 c2 e_compound Cons.prems(2) Cons.prems(3)]
  consider (E1) "(u, a, w) \<in> offset_edges 1 E10"
         | (bridge) "u = ex10 + 1" "a = EA_Nop" "w = n20 + (n10 + 1)"
    by auto
  thus ?case
  proof cases
    case E1
    from E1 obtain u0 w0 where decomp: "u = u0 + 1" "w = w0 + 1" "(u0, a, w0) \<in> E10"
      unfolding offset_edges_def by auto
    have w_in: "1 \<le> w" using decomp(2) by simp
    have w_lt: "w < n10 + 1"
      using compile_fresh[OF c1] decomp(2,3) by force
    from Cons.IH[OF ps w_in w_lt] obtain es' where
          tl_eq: "tl = offset_path 1 es' @ [(EA_Nop, n20 + (n10 + 1))]"
      and pe1: "cfg_path (to_cfg c1) (w - 1) es' ex10"
      by auto
    have toc1_edges: "edges (to_cfg c1) = E10"
      unfolding to_cfg_def using c1 by (simp add: Let_def)
    have edge_c1: "(u - 1, a, w - 1) \<in> edges (to_cfg c1)"
      using toc1_edges decomp by simp
    let ?es'_full = "(a, w - 1) # es'"
    have p_full: "cfg_path (to_cfg c1) (u - 1) ?es'_full ex10"
      by (rule cfg_path.step[OF edge_c1 pe1])
    have list_eq: "(a, w) # tl = offset_path 1 ?es'_full @ [(EA_Nop, n20 + (n10 + 1))]"
      using tl_eq decomp(2) by simp
    show ?thesis using p_full list_eq hd_eq by (rule_tac x = "?es'_full" in exI) simp
  next
    case bridge
    have w_n2: "w = n20 + (n10 + 1)" using bridge(3) .
    have tl_empty: "tl = []"
    proof (rule ccontr)
      assume "tl \<noteq> []"
      then obtain hd' tl' where tl_cons: "tl = hd' # tl'" by (cases tl) auto
      obtain a' w' where hd'_eq: "hd' = (a', w')" by (cases hd') auto
      from ps tl_cons hd'_eq obtain
            e_next: "(w, a', w') \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
        by (cases rule: cfg_path.cases) auto
      from e_next w_n2 compound_If_no_source_n2[OF c1 c2] show False by blast
    qed
    have empty_p: "cfg_path (to_cfg c1) (u - 1) [] ex10"
      using bridge(1) by (simp add: cfg_path.empty)
    have list_eq: "(a, w) # tl = offset_path 1 [] @ [(EA_Nop, n20 + (n10 + 1))]"
      using bridge tl_empty by simp
    show ?thesis using list_eq empty_p hd_eq by (rule_tac x = "[]" in exI) simp
  qed
qed

lemma cfg_path_If_factor_c2:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) u es (n20 + (n10 + 1))"
    and u_in: "n10 + 1 \<le> u" and u_lt: "u < n20 + (n10 + 1)"
  shows "\<exists>es'. es = offset_path (n10 + 1) es' @ [(EA_Nop, n20 + (n10 + 1))] \<and>
                cfg_path (to_cfg c2) (u - (n10 + 1)) es' ex20"
  using p u_in u_lt
proof (induction es arbitrary: u)
  case Nil
  from Nil(1) have "u = n20 + (n10 + 1)" by (cases rule: cfg_path.cases) simp_all
  with Nil.prems(3) show ?case by simp
next
  case (Cons hd tl)
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from Cons.prems(1) hd_eq obtain
        e_compound: "(u, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and ps: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) w tl (n20 + (n10 + 1))"
    by (cases rule: cfg_path.cases) auto
  from compound_If_edge_src_c2[OF c1 c2 e_compound Cons.prems(2) Cons.prems(3)]
  consider (E2) "(u, a, w) \<in> offset_edges (n10 + 1) E20"
         | (bridge) "u = ex20 + (n10 + 1)" "a = EA_Nop" "w = n20 + (n10 + 1)"
    by auto
  thus ?case
  proof cases
    case E2
    from E2 obtain u0 w0 where
          decomp: "u = u0 + (n10 + 1)" "w = w0 + (n10 + 1)" "(u0, a, w0) \<in> E20"
      unfolding offset_edges_def by auto
    have w_in: "n10 + 1 \<le> w" using decomp(2) by simp
    have w_lt: "w < n20 + (n10 + 1)"
      using compile_fresh[OF c2] decomp(2,3) by force
    from Cons.IH[OF ps w_in w_lt] obtain es' where
          tl_eq: "tl = offset_path (n10 + 1) es' @ [(EA_Nop, n20 + (n10 + 1))]"
      and pe2: "cfg_path (to_cfg c2) (w - (n10 + 1)) es' ex20"
      by auto
    have toc2_edges: "edges (to_cfg c2) = E20"
      unfolding to_cfg_def using c2 by (simp add: Let_def)
    have edge_c2: "(u - (n10 + 1), a, w - (n10 + 1)) \<in> edges (to_cfg c2)"
      using toc2_edges decomp by simp
    let ?es'_full = "(a, w - (n10 + 1)) # es'"
    have p_full: "cfg_path (to_cfg c2) (u - (n10 + 1)) ?es'_full ex20"
      by (rule cfg_path.step[OF edge_c2 pe2])
    have list_eq: "(a, w) # tl = offset_path (n10 + 1) ?es'_full @ [(EA_Nop, n20 + (n10 + 1))]"
      using tl_eq decomp(2) by simp
    show ?thesis using p_full list_eq hd_eq by (rule_tac x = "?es'_full" in exI) simp
  next
    case bridge
    have w_n2: "w = n20 + (n10 + 1)" using bridge(3) .
    have tl_empty: "tl = []"
    proof (rule ccontr)
      assume "tl \<noteq> []"
      then obtain hd' tl' where tl_cons: "tl = hd' # tl'" by (cases tl) auto
      obtain a' w' where hd'_eq: "hd' = (a', w')" by (cases hd') auto
      from ps tl_cons hd'_eq obtain
            e_next: "(w, a', w') \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
        by (cases rule: cfg_path.cases) auto
      from e_next w_n2 compound_If_no_source_n2[OF c1 c2] show False by blast
    qed
    have empty_p: "cfg_path (to_cfg c2) (u - (n10 + 1)) [] ex20"
      using bridge(1) by (simp add: cfg_path.empty)
    have list_eq: "(a, w) # tl = offset_path (n10 + 1) [] @ [(EA_Nop, n20 + (n10 + 1))]"
      using bridge tl_empty by simp
    show ?thesis using list_eq empty_p hd_eq by (rule_tac x = "[]" in exI) simp
  qed
qed

(*
  Strong If path split.  A path in to_cfg (IF b THEN c1 ELSE c2) from
  the compound entry 0 to the compound exit n2 begins with one of the
  two pre-edges (Assume b / AssumeNot b) and ends with the matching
  post-Nop bridge.
*)
lemma cfg_path_If_split:
  assumes c1: "compile c1 0 = (n10, en10, ex10, E10)"
    and c2: "compile c2 0 = (n20, en20, ex20, E20)"
    and p: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 es (n20 + (n10 + 1))"
  shows "(\<exists>es1. es = (EA_Assume b, en10 + 1)
                     # offset_path 1 es1
                     @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> cfg_path (to_cfg c1) en10 es1 ex10)
       \<or> (\<exists>es2. es = (EA_AssumeNot b, en20 + (n10 + 1))
                     # offset_path (n10 + 1) es2
                     @ [(EA_Nop, n20 + (n10 + 1))]
              \<and> cfg_path (to_cfg c2) en20 es2 ex20)"
proof -
  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2, of "n10 + 1"] by simp
  have Eif: "edges (to_cfg (IF b THEN c1 ELSE c2)) =
             {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
             \<union> offset_edges 1 E10
             \<union> offset_edges (n10 + 1) E20
             \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by simp

  have es_ne: "es \<noteq> []"
  proof (rule ccontr)
    assume "\<not> es \<noteq> []"
    hence "es = []" by simp
    with p have "0 = n20 + (n10 + 1)" by (cases rule: cfg_path.cases) simp_all
    thus False by simp
  qed
  then obtain hd tl where es_cons: "es = hd # tl" by (cases es) auto
  obtain a w where hd_eq: "hd = (a, w)" by (cases hd) auto
  from p es_cons hd_eq obtain
        e_first: "(0, a, w) \<in> edges (to_cfg (IF b THEN c1 ELSE c2))"
    and ps: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) w tl (n20 + (n10 + 1))"
    by (cases rule: cfg_path.cases) auto

  from compile_fresh[OF c1] have ex10_lt: "ex10 < n10" by simp
  from compile_fresh[OF c2_n] have ex2n_lt: "ex20 + (n10 + 1) < n20 + (n10 + 1)" by simp
  from compile_ge[OF c1_1] have en1_in_c1: "1 \<le> en10 + 1 \<and> en10 + 1 \<le> n10 + 1"
    using compile_fresh[OF c1_1] by simp
  from compile_ge[OF c2_n] have en2n_ge: "n10 + 1 \<le> en20 + (n10 + 1)" by simp

  (* By edge classification at source 0: only two pre-edges have source 0. *)
  have e_cases:
    "(a = EA_Assume b \<and> w = en10 + 1) \<or> (a = EA_AssumeNot b \<and> w = en20 + (n10 + 1))"
  proof -
    have b1: "\<And>x ay y. (x, ay, y) \<in> offset_edges 1 E10 \<Longrightarrow> 1 \<le> x"
      using compile_ge[OF c1_1] by force
    have b2: "\<And>x ay y. (x, ay, y) \<in> offset_edges (n10 + 1) E20 \<Longrightarrow> n10 + 1 \<le> x"
      using compile_ge[OF c2_n] by force
    show ?thesis
      using e_first Eif b1 b2 en2n_ge by force
  qed
  
  thus ?thesis
  proof
    assume A: "a = EA_Assume b \<and> w = en10 + 1"
    hence w_eq: "w = en10 + 1" and a_eq: "a = EA_Assume b" by auto
    from compile_fresh[OF c1_1] have w_in: "1 \<le> w" "w < n10 + 1" using w_eq by auto
    from cfg_path_If_factor_c1[OF c1 c2 ps w_in(1) w_in(2)] obtain es1 where
          tl_eq: "tl = offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc1: "cfg_path (to_cfg c1) (w - 1) es1 ex10"
      by blast
    have w_minus: "w - 1 = en10" using w_eq by simp
    from pc1 w_minus have pc1': "cfg_path (to_cfg c1) en10 es1 ex10" by simp
    have es_eq:
      "es = (EA_Assume b, en10 + 1) # offset_path 1 es1 @ [(EA_Nop, n20 + (n10 + 1))]"
      using es_cons hd_eq a_eq w_eq tl_eq by simp
    show ?thesis using es_eq pc1' by blast
  next
    assume A: "a = EA_AssumeNot b \<and> w = en20 + (n10 + 1)"
    hence w_eq: "w = en20 + (n10 + 1)" and a_eq: "a = EA_AssumeNot b" by auto
    from compile_ge[OF c2_n] compile_fresh[OF c2_n]
      have w_in: "n10 + 1 \<le> w" "w < n20 + (n10 + 1)" using w_eq by auto
    from cfg_path_If_factor_c2[OF c1 c2 ps w_in(1) w_in(2)] obtain es2 where
          tl_eq: "tl = offset_path (n10 + 1) es2 @ [(EA_Nop, n20 + (n10 + 1))]"
      and pc2: "cfg_path (to_cfg c2) (w - (n10 + 1)) es2 ex20"
      by blast
    have w_minus: "w - (n10 + 1) = en20" using w_eq by simp
    from pc2 w_minus have pc2': "cfg_path (to_cfg c2) en20 es2 ex20" by simp
    have es_eq:
      "es = (EA_AssumeNot b, en20 + (n10 + 1)) # offset_path (n10 + 1) es2
             @ [(EA_Nop, n20 + (n10 + 1))]"
      using es_cons hd_eq a_eq w_eq tl_eq by simp
    show ?thesis using es_eq pc2' by blast
  qed
qed

lemma cfg_collect_step:
  assumes e: "(u, a, v) : edges g"
  shows "edge_collect a (cfg_collect g S u) \<subseteq> cfg_collect g S v"
proof -
  have "collect_pp g (cfg_collect g S) v = cfg_collect_F g S (cfg_collect g S) v"
    if "v \<noteq> cfg_entry g"
    unfolding that cfg_collect_F_def 
    apply(auto)
    by (simp add: that)
  have "edge_collect a (cfg_collect g S u) \<subseteq> collect_pp g (cfg_collect g S) v"
    unfolding collect_pp_def using e by blast
  also have "collect_pp g (cfg_collect g S) v \<subseteq> cfg_collect g S v"
  proof (cases "v = cfg_entry g")
    case True
    have "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
      using cfg_collect_lfp_unfold by simp
    then show ?thesis unfolding True cfg_collect_F_def 
      apply(auto)
      by (metis UnCI)
  next
    case False
    have ne: "v \<noteq> cfg_entry g" using False by simp
    have "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
      using cfg_collect_lfp_unfold by simp
    then show ?thesis unfolding ne cfg_collect_F_def 
      apply(auto)

      by (metis ne)
  qed
  finally show ?thesis .
qed

lemma path_sound_cfg_collect_aux:
  assumes p: "cfg_path g u es v"
  shows "edges_collect es (cfg_collect g S u) \<subseteq> cfg_collect g S v"
proof (insert p, induction es arbitrary: u v)
  case Nil
  then have "u = v" by (cases rule: cfg_path.cases) simp_all
  then show ?case by simp
next
  case (Cons e es')
  assume p: "cfg_path g u (e # es') v"
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  from p ew obtain ed: "(u, a, w) \<in> edges g" and p2: "cfg_path g w es' v"
    by (cases rule: cfg_path.cases) auto
  have step_edge: "edge_collect a (cfg_collect g S u) \<subseteq> cfg_collect g S w"
    by (rule cfg_collect_step[OF ed])
  have IH: "edges_collect es' (cfg_collect g S w) \<subseteq> cfg_collect g S v"
    by (rule Cons.IH[OF p2])
  have "edges_collect es' (edge_collect a (cfg_collect g S u))
        \<subseteq> edges_collect es' (cfg_collect g S w)"
    by (rule edges_collect_mono_strong[OF step_edge])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule IH)
  finally show ?case unfolding ew edges_collect.simps .
qed  

lemma path_sound_cfg_collect:
  assumes es: "cfg_path g (cfg_entry g) es v"
  shows "edges_collect es S \<subseteq> cfg_collect g S v"
proof -
  have ent: "S \<subseteq> cfg_collect g S (cfg_entry g)"
  proof -
    have "cfg_collect g S (cfg_entry g) = cfg_collect_F g S (cfg_collect g S) (cfg_entry g)"
      using cfg_collect_lfp_unfold by simp
    then show ?thesis unfolding cfg_collect_F_def by auto
  qed
  have "edges_collect es S \<subseteq> edges_collect es (cfg_collect g S (cfg_entry g))"
    by (rule edges_collect_mono_strong[OF ent])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule path_sound_cfg_collect_aux[OF es])
  finally show ?thesis .
qed

(* Per-pp lfp <-> path-based equality.

   Both formulations of CFG collecting agree at every program point, not
   just the exit.  Used by the small-step pipeline soundness chain:
   `pipeline_invariant_sound` is stated in lfp form (`cfg_collect`); the
   small-step bridge talks about CFG paths (= `cfg_edges_collect`). *)
theorem cfg_collect_eq_cfg_edges_collect:
  "cfg_collect g S v = cfg_edges_collect g S v"
proof (rule order_antisym)
  show "cfg_collect g S v \<subseteq> cfg_edges_collect g S v"
    by (rule cfg_collect_le_edges_collect)
  show "cfg_edges_collect g S v \<subseteq> cfg_collect g S v"
  proof
    fix x assume "x \<in> cfg_edges_collect g S v"
    then obtain es where
      es: "cfg_path g (cfg_entry g) es v" and
      x:  "x \<in> edges_collect es S"
      unfolding cfg_edges_collect_def by blast
    from path_sound_cfg_collect[OF es] x
    show "x \<in> cfg_collect g S v" by blast
  qed
qed

(* ── Source-level run predicate ────────────────────────────────────────────────────────── *)

text \<open>
  \<open>runs_to c s t\<close> is the source-level surface for ``\<open>c\<close> can produce \<open>t\<close> from \<open>s\<close>''.
  Definitionally, this is exit-projected \<open>cfg_collect\<close> with singleton input \<open>{s}\<close>;
  consumers unfold \<open>runs_to_def\<close> to reach the analyzer-side fixpoint.

  Replaces the big-step predicate \<open>(c,s) \<Rightarrow> t\<close> in downstream soundness
  statements.  See \<open>docs/BIG_STEP_REMOVAL.md\<close>.
\<close>

definition runs_to :: "com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "runs_to c s t \<longleftrightarrow> t \<in> cfg_collect (to_cfg c) {s} (cfg_exit (to_cfg c))"

end
