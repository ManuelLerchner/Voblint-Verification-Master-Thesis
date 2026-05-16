theory CFG_Collecting
  imports IMP2_to_CFG IMP2_Collecting CFG_Path Goblint_Formalization.Attempt2_Step0
begin

(*
  CFG -- Collecting Semantics.

  Defines the collecting semantics directly on the CFG as the canonical
  fixpoint of the transfer functions over edges, then proves it agrees
  with the IMP2 collecting semantics.  This bridge is used in
  Equations/Constraint_System_Sound.thy.
*)

(* ── Per-Edge Transfer Function on State Sets ─────────────────── *)

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop          S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s : S}"
  | "edge_collect (EA_Assume b)    S = Collect (\<lambda>s. s \<in> S \<and> bval b s)"
  | "edge_collect (EA_AssumeNot b) S = Collect (\<lambda>s. s \<in> S \<and> \<not> bval b s)"

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
proof (cases a)
  case EA_Nop
  with assms show ?thesis by simp
next
  case (EA_Assign x1 a1)
  with assms show ?thesis by auto
next
  case (EA_Assume b)
  with assms show ?thesis by (auto simp add: subset_iff mem_Collect_eq)
next
  case (EA_AssumeNot b)
  with assms show ?thesis by (auto simp add: subset_iff mem_Collect_eq)
qed

(* Lived in CFG_Path.thy but must follow edge_collect (no import cycle). *)
fun path_collect :: "(edge_action * pp) list => store set => store set" where
  "path_collect [] S = S"
| "path_collect ((a, _) # es) S = path_collect es (edge_collect a S)"

lemma path_collect_empty[simp]: "path_collect [] S = S"
  by simp

lemma path_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> path_collect es S \<subseteq> path_collect es T"
proof (induction es arbitrary: S T)
  case Nil
  assume le: "S \<subseteq> T"
  show "path_collect [] S \<subseteq> path_collect [] T"
    unfolding path_collect.simps using le by blast
next
  case (Cons e es)
  assume le: "S \<subseteq> T"
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  have sub_edge: "edge_collect a S \<subseteq> edge_collect a T"
    by (rule edge_collect_mono[OF le])
  have step: "path_collect es (edge_collect a S) \<subseteq> path_collect es (edge_collect a T)"
    by (rule Cons.IH[OF sub_edge])
  show "path_collect (e # es) S \<subseteq> path_collect (e # es) T"
    unfolding path_collect.simps using ep step by simp
qed

lemma path_collect_mono:
  assumes subset: "S \<subseteq> T"
  shows "path_collect es S \<subseteq> path_collect es T"
  by (rule path_collect_mono_strong[OF subset])

(*
  path_collect only inspects edge actions; the pp component of each
  step is discarded.  Hence shifting pp's via offset_path is invisible
  to path_collect.  Used to glue an IH path (lifted via cfg_path_offset)
  back into the surrounding compound graph's collecting argument.
*)
lemma path_collect_offset_path[simp]:
  "path_collect (offset_path k es) S = path_collect es S"
proof (induction es arbitrary: S)
  case Nil
  show ?case by simp
next
  case (Cons e es)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep offset_path_Cons path_collect.simps using Cons by simp
qed

lemma path_collect_append:
  "path_collect (es1 @ es2) S = path_collect es2 (path_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  show ?case by simp
next
  case (Cons e es1)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep path_collect.simps using Cons.IH by simp
qed

(* ── CFG Collecting Environment ───────────────────────────────── *)
(*
  A collecting environment maps each program point to the set of states
  that can appear there during any execution starting from some fixed
  initial set.
*)

type_synonym cenv = "pp => store set"

definition cenv_join :: "pp => cenv set => store set" where
  "cenv_join v envs = Union {rho v | rho. rho : envs}"

(* ── Collecting Transformer for One Program Point ─────────────── *)
(*
  collect_pp g rho v = join of edge_collect(a)(rho u) over all (u,a,v) in g.
  This is the single-step "push" of states through each incoming edge.
*)

definition collect_pp :: "cfg => cenv => pp => store set" where
  "collect_pp g rho v =
     Union {edge_collect a (rho u) | u a. (u, a, v) : cfg_edges g}"

(* ── Least Fixpoint (Collecting Semantics over CFG) ───────────── *)
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

lemma cfg_collect_def':
  "cfg_collect g S = lfp (cfg_collect_F g S)"
  unfolding cfg_collect_def by simp

(* ── Monotonicity of collect_pp ──────────────────────────────────
   Required for lfp to be well-defined. *)

lemma collect_pp_mono:
  "mono (\<lambda>rho. collect_pp g rho v)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  have ru: "\<And>u. rho1 u \<subseteq> rho2 u"
    using le by (simp add: le_fun_def)
  have edge: "\<And>u a. (u, a, v) \<in> cfg_edges g \<Longrightarrow> edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    by (meson ru edge_collect_mono)
  show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def using edge by blast
qed

lemma cfg_collect_F_mono:
  "mono (cfg_collect_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "cfg_collect_F g S rho1 \<le> cfg_collect_F g S rho2"
    unfolding cfg_collect_F_def le_fun_def
  proof (intro allI)
    fix v
    show "(if v = cfg_entry g then S Un collect_pp g rho1 v else collect_pp g rho1 v)
          \<subseteq> (if v = cfg_entry g then S Un collect_pp g rho2 v else collect_pp g rho2 v)"
    proof (cases "v = cfg_entry g")
      case True
      have "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
        using le collect_pp_mono monoD by blast
      then show ?thesis
        using True by auto
    next
      case False
      have "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
        using le collect_pp_mono monoD by blast
      then show ?thesis
        using False by auto
    qed
  qed
qed

lemma cfg_collect_lfp_unfold:
  "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
  unfolding cfg_collect_def'
  using lfp_unfold[OF cfg_collect_F_mono, symmetric] by simp

(* Path-based collecting environment (for cfg_collect_exit_le_collect). *)
definition cfg_path_collect :: "cfg => store set => pp => store set" where
  "cfg_path_collect g S v =
     (\<Union>es\<in>{es. cfg_path g (cfg_entry g) es v}. path_collect es S)"

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
proof (cases a)
  case EA_Nop
  then show ?thesis by auto
next
  case (EA_Assign x1 a1)
  then show ?thesis by auto
next
  case (EA_Assume b)
  then show ?thesis by (auto simp: mem_Collect_eq)
next
  case (EA_AssumeNot b)
  then show ?thesis by (auto simp: mem_Collect_eq)
qed

(* One CFG step extends path-based collecting. *)
lemma cfg_path_collect_step:
  assumes e: "(u, a, v) : cfg_edges g"
  shows "edge_collect a (cfg_path_collect g S u) \<subseteq> cfg_path_collect g S v"
proof (rule subsetI)
  fix x
  assume x: "x \<in> edge_collect a (cfg_path_collect g S u)"
  then obtain es where es: "cfg_path g (cfg_entry g) es u"
    and x: "x \<in> edge_collect a (path_collect es S)"
    unfolding cfg_path_collect_def
    by (smt (verit) UN_iff edge_collect_member mem_Collect_eq)
    
  then obtain s where s: "s \<in> path_collect es S"
    and x: "x \<in> edge_collect a {s}"
    using edge_collect_member
    by meson 
  have p: "cfg_path g u [(a, v)] v"
    by (rule cfg_path.step[OF e cfg_path.empty])
  have es': "cfg_path g (cfg_entry g) (es @ [(a, v)]) v"
    by (rule cfg_path_append[OF es p])
  have "x \<in> path_collect (es @ [(a, v)]) S"
    using x s unfolding path_collect_append path_collect.simps
    using edge_collect_member by blast 
 
  then show "x \<in> cfg_path_collect g S v"
    unfolding cfg_path_collect_def using es' by auto
qed

lemma cfg_path_collect_entry:
  "S \<subseteq> cfg_path_collect g S (cfg_entry g)"
proof (rule subsetI)
  fix s
  assume s: "s \<in> S"
  have "cfg_path g (cfg_entry g) [] (cfg_entry g)"
    by (rule cfg_path.empty)
  then show "s \<in> cfg_path_collect g S (cfg_entry g)"
    unfolding cfg_path_collect_def using s by auto
qed

(*
  Post-fixpoint: cfg_path_collect satisfies cfg_collect_F.
  Proof via path_collect_append + cfg_path_append; one line per edge action.
*)
lemma cfg_path_collect_post:
  "cfg_collect_F g S (cfg_path_collect g S) v \<subseteq> cfg_path_collect g S v"
  unfolding cfg_collect_F_def
  apply(cases "v = cfg_entry g")
  apply(auto)
  using cfg_path_collect_entry apply blast
  using cfg_path_collect_step collect_pp_def apply fastforce
  using cfg_path_collect_step collect_pp_def by fastforce


lemma cfg_collect_le_path_collect:
  "cfg_collect g S v \<subseteq> cfg_path_collect g S v"
proof -
  have pf: "cfg_collect_F g S (cfg_path_collect g S) \<le> cfg_path_collect g S"
    unfolding le_fun_def using cfg_path_collect_post by simp
  have "lfp (cfg_collect_F g S) \<le> cfg_path_collect g S"
    using pf cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def' le_fun_def by simp
qed

(* ── to_cfg / compile alignment ───────────────────────────────── *)

lemma to_cfg_compile:
  obtains n' en ex E where
    "compile c 0 = (n', en, ex, E)"
    "cfg_entry (to_cfg c) = en"
    "cfg_exit (to_cfg c) = ex"
    "cfg_edges (to_cfg c) = E"
  unfolding to_cfg_def
  by (cases "compile c 0") (auto simp: Let_def)

lemma path_collect_member:
  "x \<in> path_collect es S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> path_collect es {s})"
proof (induction es arbitrary: S x)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    apply(auto)
    apply (metis edge_collect_member ep local.Cons path_collect.simps(2))
    by (meson empty_subsetI insert_subset path_collect_mono_strong subsetD)
qed

lemma path_collect_nop_append:
  "path_collect (es1 @ [(EA_Nop, w)] @ es2) S = path_collect es2 (path_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  show ?case by (simp add: path_collect_append)
next
  case (Cons e es1)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep path_collect.simps path_collect_append Cons by simp
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
  shows "cfg_edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    and "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
proof -
  define E12 where "E12 = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
  from c1 c2 have cmp: "compile (c1 ;; c2) 0 = (n2, en1, ex2, E12)"
    unfolding E12_def by (rule compile_Seq_0)
  show "cfg_edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    unfolding to_cfg_def E12_def[symmetric] cmp by simp
  show "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    unfolding to_cfg_def cmp by simp
  show "cfg_exit (to_cfg (c1 ;; c2)) = ex2"
    unfolding to_cfg_def cmp by simp
qed

lemma cfg_edges_entry_exit_If:
  assumes c1: "compile c1 1 = (n1, en1, ex1, E1)"
    and   c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "cfg_edges (to_cfg (IF b THEN c1 ELSE c2)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
         \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
    and "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n2"
proof -
  define EI where "EI = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, en2)} \<union> E1 \<union> E2
                       \<union> {(ex1, EA_Nop, n2), (ex2, EA_Nop, n2)}"
  from c1 c2 have cmp: "compile (IF b THEN c1 ELSE c2) 0 = (n2 + 1, 0, n2, EI)"
    unfolding EI_def by (rule compile_If_0)
  show "cfg_edges (to_cfg (IF b THEN c1 ELSE c2)) =
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
  shows "cfg_edges (to_cfg (WHILE b DO c)) =
         {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    and "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    and "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
proof -
  define EW where "EW = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
  from c have cmp: "compile (WHILE b DO c) 0 = (Suc n1, 0, n1, EW)"
    unfolding EW_def by (rule compile_While_0)
  show "cfg_edges (to_cfg (WHILE b DO c)) =
        {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    unfolding to_cfg_def EW_def[symmetric] cmp by simp
  show "cfg_entry (to_cfg (WHILE b DO c)) = 0"
    unfolding to_cfg_def cmp by simp
  show "cfg_exit  (to_cfg (WHILE b DO c)) = n1"
    unfolding to_cfg_def cmp by simp
qed

lemma cfg_path_mono_edges:
  assumes sub: "cfg_edges g \<subseteq> cfg_edges h"
    and p: "cfg_path g u es v"
  shows "cfg_path h u es v"
  using p sub by (induction rule: cfg_path.induct) (auto intro: cfg_path.intros subsetD)

lemma cfg_edges_compile_Seq_E1_subset:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "E1 \<subseteq> cfg_edges (to_cfg (c1 ;; c2))"
proof -
  have HG: "cfg_edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (fact cfg_edges_entry_exit_Seq(1)[OF c1 c2])
  then show ?thesis unfolding HG by blast
qed

lemma cfg_edges_compile_Seq_E2_subset:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "E2 \<subseteq> cfg_edges (to_cfg (c1 ;; c2))"
proof -
  have HG: "cfg_edges (to_cfg (c1 ;; c2)) = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    by (fact cfg_edges_entry_exit_Seq(1)[OF c1 c2])
  then show ?thesis unfolding HG by blast
qed

lemma seq_comp_entry_ne_exit:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "en1 \<noteq> ex2"
proof -
  define E12 where "E12 = E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
  from assms have "compile (c1 ;; c2) 0 = (n2, en1, ex2, E12)"
    unfolding E12_def by (rule compile_Seq_0)
  from compile_entry_ne_exit[OF this] show ?thesis by simp
qed

lemma Seq_edge_cross_bridge:
  fixes E1 E2 :: "(pp \<times> edge_action \<times> pp) set"
    and u v n1 ex1 en2 :: pp
    and a :: edge_action
  assumes bd1: "\<forall>e \<in> E1. fst e < n1 \<and> snd (snd e) < n1"
    and ge2: "\<forall>e \<in> E2. n1 \<le> fst e"
    and e: "(u, a, v) \<in> E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
    and lt_u: "u < n1" and ge_v: "n1 \<le> v"
  shows "(u, a, v) = (ex1, EA_Nop, en2)"
proof -
  have not_E1: "(u, a, v) \<notin> E1"
  proof
    assume H: "(u, a, v) \<in> E1"
    with bd1 have "snd (snd (u, a, v)) < n1" by blast
    hence "v < n1" by simp
    with ge_v show False by simp
  qed
  have not_E2: "(u, a, v) \<notin> E2"
 using ge2 lt_u by fastforce
  from e not_E1 not_E2 show ?thesis by simp
qed

lemma mem_path_collect_from_set:
  "t \<in> path_collect es M \<Longrightarrow> \<exists>m\<in>M. t \<in> path_collect es {m}"
proof (induction es arbitrary: M t)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  obtain M' where M': "M' = edge_collect a M" by simp
  from Cons.prems ew obtain t': "t \<in> path_collect es M'"
    using M' path_collect.simps(2) by blast
  from Cons.IH[OF this] obtain m where m: "m \<in> M'" and tm: "t \<in> path_collect es {m}"
    by blast
  from m have "m \<in> edge_collect a M"
    using M' by auto

  then obtain m0 where m0: "m0 \<in> M" and mm: "m \<in> edge_collect a {m0}"
    by (cases a) (auto simp: mem_Collect_eq)
  have "t \<in> path_collect (e # es) {m0}"
    unfolding ew path_collect.simps mm tm
    using mm path_collect_member tm by blast
  with m0 show ?case by blast
qed

lemma path_collect_via_append:
  assumes "t \<in> path_collect (es1 @ es2) {s}"
  shows "\<exists>mid. mid \<in> path_collect es1 {s} \<and> t \<in> path_collect es2 {mid}"
proof -
  have "t \<in> path_collect es2 (path_collect es1 {s})"
    using assms by (simp only: path_collect_append)
  from mem_path_collect_from_set[OF this] obtain mid where
    "mid \<in> path_collect es1 {s}" and TM: "t \<in> path_collect es2 {mid}" by blast
  then show ?thesis using TM by blast
qed

lemma Seq_en2_ge_n1:
  assumes c2: "compile c2 n1 = (n2, en2, ex2, E2)"
  shows "en2 \<ge> n1"
proof -
  from compile_ge[OF c2] show ?thesis by simp
qed

lemma cfg_path_Seq_split:
  assumes c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and c2: "compile c2 n1 = (n2, en2, ex2, E2)"
    and en_lt: "en < n1"
  defines "G \<equiv> to_cfg (c1 ;; c2)"
      and E12: "E12 \<equiv> E1 \<union> {(ex1, EA_Nop, en2)} \<union> E2"
  assumes p: "cfg_path G en es ex2"
  shows "\<exists>es1 es2. es = es1 @ ((EA_Nop, en2) # es2) \<and>
         cfg_path G en es1 ex1 \<and> cfg_path G en2 es2 ex2"
  (* TODO: Peel the unique NOP bridge using compile freshness (E1 < n1 \<le> fst E2) *)
  sorry

lemma cfg_collect_step:
  assumes e: "(u, a, v) : cfg_edges g"
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
  shows "path_collect es (cfg_collect g S u) \<subseteq> cfg_collect g S v"
proof (insert p, induction es arbitrary: u v)
  case Nil
  then have "u = v" by (cases rule: cfg_path.cases) simp_all
  then show ?case by simp
next
  case (Cons e es')
  assume p: "cfg_path g u (e # es') v"
  obtain a w where ew: "e = (a, w)" by (cases e) auto
  from p ew obtain ed: "(u, a, w) \<in> cfg_edges g" and p2: "cfg_path g w es' v"
    by (cases rule: cfg_path.cases) auto
  have step_edge: "edge_collect a (cfg_collect g S u) \<subseteq> cfg_collect g S w"
    by (rule cfg_collect_step[OF ed])
  have IH: "path_collect es' (cfg_collect g S w) \<subseteq> cfg_collect g S v"
    by (rule Cons.IH[OF p2])
  have "path_collect es' (edge_collect a (cfg_collect g S u))
        \<subseteq> path_collect es' (cfg_collect g S w)"
    by (rule path_collect_mono_strong[OF step_edge])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule IH)
  finally show ?case unfolding ew path_collect.simps .
qed  

lemma path_sound_cfg_collect:
  assumes es: "cfg_path g (cfg_entry g) es v"
  shows "path_collect es S \<subseteq> cfg_collect g S v"
proof -
  have ent: "S \<subseteq> cfg_collect g S (cfg_entry g)"
  proof -
    have "cfg_collect g S (cfg_entry g) = cfg_collect_F g S (cfg_collect g S) (cfg_entry g)"
      using cfg_collect_lfp_unfold by simp
    then show ?thesis unfolding cfg_collect_F_def by auto
  qed
  have "path_collect es S \<subseteq> path_collect es (cfg_collect g S (cfg_entry g))"
    by (rule path_collect_mono_strong[OF ent])
  also have "\<dots> \<subseteq> cfg_collect g S v"
    by (rule path_sound_cfg_collect_aux[OF es])
  finally show ?thesis .
qed

(* big-step execution yields a CFG path to exit (converse of compile_path_big_step). *)
lemma big_step_cfg_path:
  assumes "(c, s) \<Rightarrow> t" and  "s \<in> S" 
  shows "\<exists>es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))
            \<and> t \<in> path_collect es {s}"
using assms proof (induction "(c,s)" "t" arbitrary: c s S rule: big_step.induct)
  case Skip
  obtain n' en ex E where comp: "compile SKIP 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg SKIP) = en"
    and ex: "cfg_exit (to_cfg SKIP) = ex"
    and E: "cfg_edges (to_cfg SKIP) = E"
    by (rule to_cfg_compile)
  from comp have en0: "en = 0" and ex1: "ex = 1" and Eeq: "E = {(0, EA_Nop, 1)}"
    by auto
  show ?case
    by (metis E Eeq cfg_path.step edge_collect.simps(1) empty en en0 ex ex1 insertI1 path_collect.simps(2)
        path_collect_empty)
   
    

next
  case (Assign x a)
  obtain n' en ex E where comp: "compile (x ::= a) 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg (x ::= a)) = en"
    and ex: "cfg_exit (to_cfg (x ::= a)) = ex"
    and E: "cfg_edges (to_cfg (x ::= a)) = E"
    by (rule to_cfg_compile)
  from comp have en0: "en = 0" and ex1: "ex = 1" and Eeq: "E = {(0, EA_Assign x a, 1)}"
    by auto
  show ?case
    apply (rule exI[where x = "[(EA_Assign x a, 1)]"])
    using E Eeq en0 ex1 en ex assms(2)
    by (simp add: cfg_path.step empty)
   
  
  
next
  case (Seq c1 s1 t2 c2 t3)
  from Seq.hyps(2) obtain es1 where
        p1: "cfg_path (to_cfg c1) (cfg_entry (to_cfg c1)) es1 (cfg_exit (to_cfg c1))"
    and t2in: "t2 \<in> path_collect es1 {s1}"
    by blast
  from Seq.hyps(4) obtain es2 where
        p2: "cfg_path (to_cfg c2) (cfg_entry (to_cfg c2)) es2 (cfg_exit (to_cfg c2))"
    and t3in: "t3 \<in> path_collect es2 {t2}"
    by blast

  obtain n1 en1 ex1 E1 where
        c1: "compile c1 0 = (n1, en1, ex1, E1)"
    and en1_eq: "cfg_entry (to_cfg c1) = en1"
    and ex1_eq: "cfg_exit  (to_cfg c1) = ex1"
    and E1_eq:  "cfg_edges (to_cfg c1) = E1"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    and E20_eq:  "cfg_edges (to_cfg c2) = E20"
    by (rule to_cfg_compile)

  have c2_n1: "compile c2 n1 = (n20 + n1, en20 + n1, ex20 + n1, offset_edges n1 E20)"
    using compile_from_0_offsets[OF c2_0] by simp

  have Eseq:   "cfg_edges (to_cfg (c1 ;; c2)) =
                E1 \<union> {(ex1, EA_Nop, en20 + n1)} \<union> offset_edges n1 E20"
    and en_seq: "cfg_entry (to_cfg (c1 ;; c2)) = en1"
    and ex_seq: "cfg_exit  (to_cfg (c1 ;; c2)) = ex20 + n1"
    using cfg_edges_entry_exit_Seq[OF c1 c2_n1] by auto

  (* Lift c1 path into compound graph. *)
  from p1 en1_eq ex1_eq have p1': "cfg_path (to_cfg c1) en1 es1 ex1" by simp
  have sub1: "cfg_edges (to_cfg c1) \<subseteq> cfg_edges (to_cfg (c1 ;; c2))"
    unfolding E1_eq Eseq by blast
  have P1: "cfg_path (to_cfg (c1 ;; c2)) en1 es1 ex1"
    by (rule cfg_path_mono_edges[OF sub1 p1'])

  (* Lift c2 path via pp-shift by n1, then mono into compound. *)
  have toc2_eq: "to_cfg c2 = \<lparr>cfg_entry = en20, cfg_exit = ex20, cfg_edges = E20\<rparr>"
    unfolding to_cfg_def using c2_0 by (simp add: Let_def)
  from p2 en20_eq ex20_eq have p2': "cfg_path (to_cfg c2) en20 es2 ex20" by simp
  hence p2_rec: "cfg_path \<lparr>cfg_entry = en20, cfg_exit = ex20, cfg_edges = E20\<rparr>
                            en20 es2 ex20"
    using toc2_eq by simp
  let ?es2k = "offset_path n1 es2"
  have p2k: "cfg_path \<lparr>cfg_entry = en20 + n1, cfg_exit = ex20 + n1,
                       cfg_edges = offset_edges n1 E20\<rparr>
                      (en20 + n1) ?es2k (ex20 + n1)"
    by (rule cfg_path_offset[OF p2_rec])
  have sub2: "cfg_edges \<lparr>cfg_entry = en20 + n1, cfg_exit = ex20 + n1,
                         cfg_edges = offset_edges n1 E20\<rparr>
              \<subseteq> cfg_edges (to_cfg (c1 ;; c2))"
    unfolding Eseq by simp blast
  have P2: "cfg_path (to_cfg (c1 ;; c2)) (en20 + n1) ?es2k (ex20 + n1)"
    by (rule cfg_path_mono_edges[OF sub2 p2k])

  (* Glue edge ex1 -[Nop]-> en20+n1. *)
  have glue_edge: "(ex1, EA_Nop, en20 + n1) \<in> cfg_edges (to_cfg (c1 ;; c2))"
    unfolding Eseq by blast
  have glue: "cfg_path (to_cfg (c1 ;; c2)) ex1 [(EA_Nop, en20 + n1)] (en20 + n1)"
    by (rule cfg_path.step[OF glue_edge cfg_path.empty])

  (* Concatenate full path. *)
  have step1: "cfg_path (to_cfg (c1 ;; c2)) en1 (es1 @ [(EA_Nop, en20 + n1)]) (en20 + n1)"
    by (rule cfg_path_append[OF P1 glue])
  let ?es = "es1 @ [(EA_Nop, en20 + n1)] @ ?es2k"
  have path: "cfg_path (to_cfg (c1 ;; c2)) en1 ?es (ex20 + n1)"
    using cfg_path_append[OF step1 P2] by simp

  (* Collect side: t3 lands in path_collect of full path. *)
  have t3_in: "t3 \<in> path_collect ?es {s1}"
  proof -
    have a: "{t2} \<subseteq> path_collect es1 {s1}" using t2in by simp
    have b: "path_collect es2 {t2} \<subseteq> path_collect es2 (path_collect es1 {s1})"
      by (rule path_collect_mono[OF a])
    from t3in b have t3_step: "t3 \<in> path_collect es2 (path_collect es1 {s1})" by blast
    have eq: "path_collect ?es {s1} = path_collect es2 (path_collect es1 {s1})"
      using path_collect_nop_append[of es1 "en20 + n1" ?es2k "{s1}"] by simp
    show ?thesis using t3_step eq by simp
  qed

  show ?case
    using path t3_in en_seq ex_seq by metis
next
  case (IfTrue b s c1 t c2)
  from IfTrue.hyps(3) obtain es1 where
        p1: "cfg_path (to_cfg c1) (cfg_entry (to_cfg c1)) es1 (cfg_exit (to_cfg c1))"
    and tin: "t \<in> path_collect es1 {s}"
    by blast
  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and en10_eq: "cfg_entry (to_cfg c1) = en10"
    and ex10_eq: "cfg_exit  (to_cfg c1) = ex10"
    and E10_eq:  "cfg_edges (to_cfg c1) = E10"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    by (rule to_cfg_compile)

  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp

  have Eif:   "cfg_edges (to_cfg (IF b THEN c1 ELSE c2)) =
               {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
               \<union> offset_edges 1 E10
               \<union> offset_edges (n10 + 1) E20
               \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                  (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    and en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto

  (* Lift c1 path via offset 1, mono into compound *)
  have toc1_rec: "to_cfg c1 = \<lparr>cfg_entry = en10, cfg_exit = ex10, cfg_edges = E10\<rparr>"
    unfolding to_cfg_def using c1_0 by (simp add: Let_def)
  from p1 en10_eq ex10_eq have p1': "cfg_path (to_cfg c1) en10 es1 ex10" by simp
  hence p1_rec: "cfg_path \<lparr>cfg_entry = en10, cfg_exit = ex10, cfg_edges = E10\<rparr> en10 es1 ex10"
    using toc1_rec by simp
  let ?es1k = "offset_path 1 es1"
  have p1k: "cfg_path \<lparr>cfg_entry = en10 + 1, cfg_exit = ex10 + 1, cfg_edges = offset_edges 1 E10\<rparr>
                      (en10 + 1) ?es1k (ex10 + 1)"
    by (rule cfg_path_offset[OF p1_rec])
  have sub1: "cfg_edges \<lparr>cfg_entry = en10 + 1, cfg_exit = ex10 + 1, cfg_edges = offset_edges 1 E10\<rparr>
              \<subseteq> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by simp blast
  have P1: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (en10 + 1) ?es1k (ex10 + 1)"
    by (rule cfg_path_mono_edges[OF sub1 p1k])

  (* Pre/post glue edges *)
  have pre_edge: "(0, EA_Assume b, en10 + 1) \<in> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by blast
  have pre: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 [(EA_Assume b, en10 + 1)] (en10 + 1)"
    by (rule cfg_path.step[OF pre_edge cfg_path.empty])

  have post_edge: "(ex10 + 1, EA_Nop, n20 + (n10 + 1)) \<in> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by blast
  have post: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (ex10 + 1)
                       [(EA_Nop, n20 + (n10 + 1))] (n20 + (n10 + 1))"
    by (rule cfg_path.step[OF post_edge cfg_path.empty])

  let ?es = "[(EA_Assume b, en10 + 1)] @ ?es1k @ [(EA_Nop, n20 + (n10 + 1))]"
  have mid: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (en10 + 1)
                      (?es1k @ [(EA_Nop, n20 + (n10 + 1))]) (n20 + (n10 + 1))"
    by (rule cfg_path_append[OF P1 post])
  have path: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 ?es (n20 + (n10 + 1))"
    using cfg_path_append[OF pre mid] by simp

  (* Collect side *)
  have eq_head: "path_collect [(EA_Assume b, en10 + 1)] {s} = {s}"
    using IfTrue.hyps(1) by auto
  have eq_es: "path_collect ?es {s} = path_collect es1 {s}"
  proof -
    have "path_collect ?es {s}
          = path_collect (?es1k @ [(EA_Nop, n20 + (n10 + 1))])
                         (path_collect [(EA_Assume b, en10 + 1)] {s})"
      by (simp add: path_collect_append)
    also have "\<dots> = path_collect (?es1k @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
      using eq_head by simp
    also have "\<dots> = path_collect [(EA_Nop, n20 + (n10 + 1))] (path_collect ?es1k {s})"
      by (rule path_collect_append)
    also have "\<dots> = path_collect ?es1k {s}" by simp
    also have "\<dots> = path_collect es1 {s}" by simp
    finally show ?thesis .
  qed
  have t_in: "t \<in> path_collect ?es {s}"
    using tin eq_es by simp

  show ?case
    using path t_in en_if ex_if by metis
next
  case (IfFalse b s c2 t c1)
  from IfFalse.hyps(3) obtain es2 where
        p2: "cfg_path (to_cfg c2) (cfg_entry (to_cfg c2)) es2 (cfg_exit (to_cfg c2))"
    and tin: "t \<in> path_collect es2 {s}"
    by blast
  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    by (rule to_cfg_compile)
  obtain n20 en20 ex20 E20 where
        c2_0: "compile c2 0 = (n20, en20, ex20, E20)"
    and en20_eq: "cfg_entry (to_cfg c2) = en20"
    and ex20_eq: "cfg_exit  (to_cfg c2) = ex20"
    and E20_eq:  "cfg_edges (to_cfg c2) = E20"
    by (rule to_cfg_compile)

  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp
  have c2_n: "compile c2 (n10 + 1) =
              (n20 + (n10 + 1), en20 + (n10 + 1), ex20 + (n10 + 1), offset_edges (n10 + 1) E20)"
    using compile_from_0_offsets[OF c2_0, of "n10 + 1"] by simp

  have Eif:   "cfg_edges (to_cfg (IF b THEN c1 ELSE c2)) =
               {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, en20 + (n10 + 1))}
               \<union> offset_edges 1 E10
               \<union> offset_edges (n10 + 1) E20
               \<union> {(ex10 + 1, EA_Nop, n20 + (n10 + 1)),
                  (ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1))}"
    and en_if: "cfg_entry (to_cfg (IF b THEN c1 ELSE c2)) = 0"
    and ex_if: "cfg_exit  (to_cfg (IF b THEN c1 ELSE c2)) = n20 + (n10 + 1)"
    using cfg_edges_entry_exit_If[OF c1_1 c2_n] by auto

  (* Lift c2 path via offset n10+1, mono into compound *)
  have toc2_rec: "to_cfg c2 = \<lparr>cfg_entry = en20, cfg_exit = ex20, cfg_edges = E20\<rparr>"
    unfolding to_cfg_def using c2_0 by (simp add: Let_def)
  from p2 en20_eq ex20_eq have p2': "cfg_path (to_cfg c2) en20 es2 ex20" by simp
  hence p2_rec: "cfg_path \<lparr>cfg_entry = en20, cfg_exit = ex20, cfg_edges = E20\<rparr> en20 es2 ex20"
    using toc2_rec by simp
  let ?es2k = "offset_path (n10 + 1) es2"
  have p2k: "cfg_path \<lparr>cfg_entry = en20 + (n10 + 1), cfg_exit = ex20 + (n10 + 1),
                       cfg_edges = offset_edges (n10 + 1) E20\<rparr>
                      (en20 + (n10 + 1)) ?es2k (ex20 + (n10 + 1))"
    by (rule cfg_path_offset[OF p2_rec])
  have sub2: "cfg_edges \<lparr>cfg_entry = en20 + (n10 + 1), cfg_exit = ex20 + (n10 + 1),
                         cfg_edges = offset_edges (n10 + 1) E20\<rparr>
              \<subseteq> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by simp blast
  have P2: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (en20 + (n10 + 1)) ?es2k (ex20 + (n10 + 1))"
    by (rule cfg_path_mono_edges[OF sub2 p2k])

  (* Pre/post glue edges *)
  have pre_edge: "(0, EA_AssumeNot b, en20 + (n10 + 1)) \<in> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by blast
  have pre: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0
                      [(EA_AssumeNot b, en20 + (n10 + 1))] (en20 + (n10 + 1))"
    by (rule cfg_path.step[OF pre_edge cfg_path.empty])

  have post_edge: "(ex20 + (n10 + 1), EA_Nop, n20 + (n10 + 1)) \<in> cfg_edges (to_cfg (IF b THEN c1 ELSE c2))"
    unfolding Eif by blast
  have post: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (ex20 + (n10 + 1))
                       [(EA_Nop, n20 + (n10 + 1))] (n20 + (n10 + 1))"
    by (rule cfg_path.step[OF post_edge cfg_path.empty])

  let ?es = "[(EA_AssumeNot b, en20 + (n10 + 1))] @ ?es2k @ [(EA_Nop, n20 + (n10 + 1))]"
  have mid: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) (en20 + (n10 + 1))
                      (?es2k @ [(EA_Nop, n20 + (n10 + 1))]) (n20 + (n10 + 1))"
    by (rule cfg_path_append[OF P2 post])
  have path: "cfg_path (to_cfg (IF b THEN c1 ELSE c2)) 0 ?es (n20 + (n10 + 1))"
    using cfg_path_append[OF pre mid] by simp

  (* Collect side *)
  have eq_head: "path_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s} = {s}"
    using IfFalse.hyps(1) by auto
  have eq_es: "path_collect ?es {s} = path_collect es2 {s}"
  proof -
    have "path_collect ?es {s}
          = path_collect (?es2k @ [(EA_Nop, n20 + (n10 + 1))])
                         (path_collect [(EA_AssumeNot b, en20 + (n10 + 1))] {s})"
      by (simp add: path_collect_append)
    also have "\<dots> = path_collect (?es2k @ [(EA_Nop, n20 + (n10 + 1))]) {s}"
      using eq_head by simp
    also have "\<dots> = path_collect [(EA_Nop, n20 + (n10 + 1))] (path_collect ?es2k {s})"
      by (rule path_collect_append)
    also have "\<dots> = path_collect ?es2k {s}" by simp
    also have "\<dots> = path_collect es2 {s}" by simp
    finally show ?thesis .
  qed
  have t_in: "t \<in> path_collect ?es {s}"
    using tin eq_es by simp

  show ?case
    using path t_in en_if ex_if by metis
next
  case (WhileFalse b s c1)
  (* Avoid shadowing outer schematic command c from the lemma conclusion. *)
  obtain n' en ex E where comp: "compile (WHILE b DO c1) 0 = (n', en, ex, E)"
    and enG: "cfg_entry (to_cfg (WHILE b DO c1)) = en"
    and exG: "cfg_exit (to_cfg (WHILE b DO c1)) = ex"
    and EG: "cfg_edges (to_cfg (WHILE b DO c1)) = E"
    by (rule to_cfg_compile)
  obtain n1 en1 ex1 E1 where sub: "compile c1 1 = (n1, en1, ex1, E1)"
    by (cases "compile c1 1") auto
  from sub have comp_shape: "compile (WHILE b DO c1) 0 =
      (Suc n1, 0, n1, {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)})"
    by (rule compile_While_0)
  with comp have ens: "n' = Suc n1" "en = 0" "ex = n1"
    and Eeq: "E = {(0, EA_Assume b, en1), (0, EA_AssumeNot b, n1)} \<union> E1 \<union> {(ex1, EA_Nop, 0)}"
    by simp_all
  have edge: "(en, EA_AssumeNot b, ex) \<in> cfg_edges (to_cfg (WHILE b DO c1))"
    using ens Eeq EG by simp
  have path: "cfg_path (to_cfg (WHILE b DO c1)) en [(EA_AssumeNot b, ex)] ex"
    by (rule cfg_path.step[OF edge cfg_path.empty])
  have mem: "s \<in> path_collect [(EA_AssumeNot b, ex)] {s}"
    using WhileFalse.hyps(1) by (simp add: path_collect.simps)
  show ?case
    apply (rule exI[where x = "[(EA_AssumeNot b, ex)]"])
    using path mem enG exG
    by auto
   
next
  case (WhileTrue b s c1 s' s'')
  from WhileTrue.hyps(3) obtain es1 where
        p1: "cfg_path (to_cfg c1) (cfg_entry (to_cfg c1)) es1 (cfg_exit (to_cfg c1))"
    and s'_in: "s' \<in> path_collect es1 {s}"
    by blast
  from WhileTrue.hyps(5) obtain es2 where
        p2: "cfg_path (to_cfg (WHILE b DO c1))
                      (cfg_entry (to_cfg (WHILE b DO c1))) es2
                      (cfg_exit  (to_cfg (WHILE b DO c1)))"
    and s''_in: "s'' \<in> path_collect es2 {s'}"
    by blast

  obtain n10 en10 ex10 E10 where
        c1_0: "compile c1 0 = (n10, en10, ex10, E10)"
    and en10_eq: "cfg_entry (to_cfg c1) = en10"
    and ex10_eq: "cfg_exit  (to_cfg c1) = ex10"
    and E10_eq:  "cfg_edges (to_cfg c1) = E10"
    by (rule to_cfg_compile)

  have c1_1: "compile c1 1 = (n10 + 1, en10 + 1, ex10 + 1, offset_edges 1 E10)"
    using compile_from_0_offsets[OF c1_0, of 1] by simp

  have Ew:    "cfg_edges (to_cfg (WHILE b DO c1)) =
               {(0, EA_Assume b, en10 + 1), (0, EA_AssumeNot b, n10 + 1)}
               \<union> offset_edges 1 E10
               \<union> {(ex10 + 1, EA_Nop, 0)}"
    and en_w: "cfg_entry (to_cfg (WHILE b DO c1)) = 0"
    and ex_w: "cfg_exit  (to_cfg (WHILE b DO c1)) = n10 + 1"
    using cfg_edges_entry_exit_While[OF c1_1] by auto

  (* Lift body path via offset 1, mono into compound *)
  have toc1_rec: "to_cfg c1 = \<lparr>cfg_entry = en10, cfg_exit = ex10, cfg_edges = E10\<rparr>"
    unfolding to_cfg_def using c1_0 by (simp add: Let_def)
  from p1 en10_eq ex10_eq have p1': "cfg_path (to_cfg c1) en10 es1 ex10" by simp
  hence p1_rec: "cfg_path \<lparr>cfg_entry = en10, cfg_exit = ex10, cfg_edges = E10\<rparr> en10 es1 ex10"
    using toc1_rec by simp
  let ?es1k = "offset_path 1 es1"
  have p1k: "cfg_path \<lparr>cfg_entry = en10 + 1, cfg_exit = ex10 + 1, cfg_edges = offset_edges 1 E10\<rparr>
                      (en10 + 1) ?es1k (ex10 + 1)"
    by (rule cfg_path_offset[OF p1_rec])
  have sub1: "cfg_edges \<lparr>cfg_entry = en10 + 1, cfg_exit = ex10 + 1, cfg_edges = offset_edges 1 E10\<rparr>
              \<subseteq> cfg_edges (to_cfg (WHILE b DO c1))"
    unfolding Ew by simp blast
  have P1: "cfg_path (to_cfg (WHILE b DO c1)) (en10 + 1) ?es1k (ex10 + 1)"
    by (rule cfg_path_mono_edges[OF sub1 p1k])

  (* Glue edges: head -> body entry, body exit -> head *)
  have head_edge: "(0, EA_Assume b, en10 + 1) \<in> cfg_edges (to_cfg (WHILE b DO c1))"
    unfolding Ew by blast
  have head: "cfg_path (to_cfg (WHILE b DO c1)) 0 [(EA_Assume b, en10 + 1)] (en10 + 1)"
    by (rule cfg_path.step[OF head_edge cfg_path.empty])

  have back_e: "(ex10 + 1, EA_Nop, 0) \<in> cfg_edges (to_cfg (WHILE b DO c1))"
    unfolding Ew by blast
  have back_p: "cfg_path (to_cfg (WHILE b DO c1)) (ex10 + 1) [(EA_Nop, 0)] (0::pp)"
    by (rule cfg_path.step[OF back_e cfg_path.empty])

  (* Recursive WHILE path: rebind via en_w/ex_w *)
  from p2 en_w ex_w have p2': "cfg_path (to_cfg (WHILE b DO c1)) 0 es2 (n10 + 1)" by simp

  (* Concatenate: head; ?es1k; back; es2 *)
  let ?es = "[(EA_Assume b, en10 + 1)] @ ?es1k @ [(EA_Nop, 0)] @ es2"
  have stepA: "cfg_path (to_cfg (WHILE b DO c1)) (en10 + 1) (?es1k @ [(EA_Nop, 0)]) (0::pp)"
    by (rule cfg_path_append[OF P1 back_p])
  have stepB: "cfg_path (to_cfg (WHILE b DO c1)) (en10 + 1) (?es1k @ [(EA_Nop, 0)] @ es2) (n10 + 1)"
    using cfg_path_append[OF stepA p2'] by simp
  have path: "cfg_path (to_cfg (WHILE b DO c1)) 0 ?es (n10 + 1)"
    using cfg_path_append[OF head stepB] by simp

  (* Collect side *)
  have eq_head: "path_collect [(EA_Assume b, en10 + 1)] {s} = {s}"
    using WhileTrue.hyps(1) by auto
  have s''_in_chain: "s'' \<in> path_collect ?es {s}"
  proof -
    have eq_all: "path_collect ?es {s} = path_collect es2 (path_collect es1 {s})"
    proof -
      have "path_collect ?es {s}
            = path_collect (?es1k @ [(EA_Nop, 0)] @ es2)
                           (path_collect [(EA_Assume b, en10 + 1)] {s})"
        by (simp add: path_collect_append)
      also have "\<dots> = path_collect (?es1k @ [(EA_Nop, 0)] @ es2) {s}"
        using eq_head by simp
      also have "\<dots> = path_collect es2
                                  (path_collect [(EA_Nop, 0)] (path_collect ?es1k {s}))"
        by (simp add: path_collect_append)
      also have "\<dots> = path_collect es2 (path_collect ?es1k {s})" by simp
      also have "\<dots> = path_collect es2 (path_collect es1 {s})" by simp
      finally show ?thesis .
    qed
    have a: "{s'} \<subseteq> path_collect es1 {s}" using s'_in by simp
    have b: "path_collect es2 {s'} \<subseteq> path_collect es2 (path_collect es1 {s})"
      by (rule path_collect_mono[OF a])
    from s''_in b have "s'' \<in> path_collect es2 (path_collect es1 {s})" by blast
    thus ?thesis using eq_all by simp
  qed

  show ?case
    using path s''_in_chain en_w ex_w by metis
qed

(* CFG path from entry to exit implies big-step execution. *)
lemma compile_path_big_step:
  assumes es: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and s: "s \<in> S"
    and t: "t \<in> path_collect es {s}"
  shows "(c, s) \<Rightarrow> t"
  using assms
proof (induction c arbitrary: es s t S rule: com.induct)
  case SKIP
  obtain n' en ex E where comp: "compile SKIP 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg SKIP) = en"
    and ex: "cfg_exit (to_cfg SKIP) = ex"
    and E: "cfg_edges (to_cfg SKIP) = E"
    by (rule to_cfg_compile)
  from comp have en_ex: "en = 0" "ex = 1" "E = {(0, EA_Nop, 1)}"
    by(auto)
  from es en ex E en_ex have "es = [(EA_Nop, 1)]"
    apply(simp)
    by (metis SKIP.prems(1) cfg_path.cases[of "to_cfg SKIP" ex _ ex]
        cfg_path.cases[of "to_cfg SKIP" en es ex] n_not_Suc_n[of en]
        prod.inject[of ex "(_, _)" en "(EA_Nop, ex)"] prod.inject[of EA_Nop ex]
        prod.inject[of en "(_, _)" en "(EA_Nop, ex)"] singletonD[of "(ex, _, _)" "(en, EA_Nop, ex)"]
        singletonD[of "(en, _, _)" "(en, EA_Nop, ex)"])

 
  show ?case
    using SKIP.prems(3) `es = [(EA_Nop, 1)]` by auto
    
next
  case (Assign x a)
  obtain n' en ex E where comp: "compile (x ::= a) 0 = (n', en, ex, E)"
    and en: "cfg_entry (to_cfg (x ::= a)) = en"
    and ex: "cfg_exit (to_cfg (x ::= a)) = ex"
    and E: "cfg_edges (to_cfg (x ::= a)) = E"
    by (rule to_cfg_compile)
  from comp have en_ex: "en = 0" "ex = 1" "E = {(0, EA_Assign x a, 1)}"
      apply(auto)
    done 
   
  from es en ex E en_ex have "es = [(EA_Assign x a, 1)]"
    apply(simp)
    by (metis Assign.prems(1) Pair_inject cfg_path.cases n_not_Suc_n singletonD)
  
  from t s en_ex es have "t = s(x := aval a s)"
    apply(auto)
    using Assign.prems(3) `es = [(EA_Assign x a, 1)]` by auto
  show ?case using Assign `t = s(x := aval a s)` by blast
next
  case (Seq c1 c2)
    show ?case 
      sorry
next
  case (If b c1 c2)
  show ?case sorry
next
  case (While b c)
  show ?case sorry
qed

(* ── Correspondence Theorem ──────────────────────────────────────
   CFG collecting semantics at the exit node equals IMP2 collecting.
   Split into two directions so each can be proved independently. *)

lemma cfg_path_collect_exit_le_collect:
  "cfg_path_collect (to_cfg c) S (cfg_exit (to_cfg c)) <= collect c S"
proof (unfold cfg_path_collect_def collect_def, rule subsetI)
  fix t
  assume t: "t \<in> (\<Union>es\<in>{es. cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))}.
                  path_collect es S)"
  then obtain es where es: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and t: "t \<in> path_collect es S"
    by auto
  then obtain s where s: "s \<in> S" and t: "t \<in> path_collect es {s}"
    by (meson path_collect_member)
 
  show "t \<in> {t. \<exists>s\<in>S. (c, s) \<Rightarrow> t}"
    using compile_path_big_step[OF es s t] 
    using s by auto
qed

lemma cfg_collect_exit_le_collect:
  "cfg_collect (to_cfg c) S (cfg_exit (to_cfg c)) <= collect c S"
  using cfg_collect_le_path_collect cfg_path_collect_exit_le_collect
  by (rule order_trans)

(*
  ⊇ direction: every big_step output is captured by the CFG collecting semantics.

  Proof: induction on the big_step derivation.
  For each rule, unfold cfg_collect one step and show the output lands in the lfp.
  The WHILE case needs the IH for the body AND for the recursive WHILE call.
  Key lemma needed: lfp unfolding (lfp f = f (lfp f)) to push states through edges.
*)
lemma collect_le_cfg_collect_exit:
  "collect c S <= cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
proof (rule subsetI)
  fix t
  assume t: "t \<in> collect c S"
  then obtain s where s: "s \<in> S" and st: "(c, s) \<Rightarrow> t"
    unfolding collect_def by auto
  obtain es where es: "cfg_path (to_cfg c) (cfg_entry (to_cfg c)) es (cfg_exit (to_cfg c))"
    and pt: "t \<in> path_collect es {s}"
    using big_step_cfg_path st by blast
  show "t \<in> cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
    using path_sound_cfg_collect[OF es] pt
    by (meson empty_subsetI insert_subset path_collect_mono_strong s subsetD) 
qed

theorem cfg_collect_exit_eq_collect:
  "cfg_collect (to_cfg c) S (cfg_exit (to_cfg c)) = collect c S"
  by (rule antisym) (rule cfg_collect_exit_le_collect, rule collect_le_cfg_collect_exit)

(* ── Reachability on CFG ─────────────────────────────────────────
   Helper: a store s is reachable at program point v iff it appears
   in cfg_collect. Used in soundness proofs. *)

definition cfg_reach :: "cfg => store set => pp => store set" where
  "cfg_reach g S = cfg_collect g S"

lemma cfg_reach_entry:
  "S <= cfg_reach (to_cfg c) S (cfg_entry (to_cfg c))"
proof -
  let ?g = "to_cfg c"
  have eq: "cfg_collect ?g S (cfg_entry ?g) =
            cfg_collect_F ?g S (cfg_collect ?g S) (cfg_entry ?g)"
    using cfg_collect_lfp_unfold[of ?g S] by simp
  have sub: "S \<subseteq> cfg_collect_F ?g S (cfg_collect ?g S) (cfg_entry ?g)"
    unfolding cfg_collect_F_def by simp
  show ?thesis
    unfolding cfg_reach_def using eq sub by simp
qed

end
