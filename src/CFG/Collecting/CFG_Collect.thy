theory CFG_Collect
  imports "Voblint_IMP2.IMP2_Expr" CFG_Path "Voblint_IMP2.IMP2_Globals" IMP2_Proc_to_CFG
begin

section \<open>CFG collecting semantics\<close>

text \<open>
  Pointwise CFG collecting semantics over store sets. Normal edges use
  edge_collect and collect_pp. Interprocedural return flow uses combine triples:
  (call, proc_exit, return) contributes states built from the call state and
  the procedure-exit state at the return program point.

  Run-to-exit projection is defined in CFG_Collect_Runs.
\<close>

subsection \<open>Edge transfer\<close>

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s \<in> S}"
  | "edge_collect (EA_Assume b) S = {s. s \<in> S \<and> bval b s}"
  | "edge_collect (EA_AssumeNot b) S = {s. s \<in> S \<and> \<not> bval b s}"
  | "edge_collect (EA_Enter xs es) S =
       {bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s) | s. s \<in> S}"

lemma edge_collect_empty_set[simp]: "edge_collect a {} = {}"
  by (cases a) auto

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
  using assms by (cases a) auto

lemma edge_collect_member:
  "x \<in> edge_collect a S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edge_collect a {s})"
  by (cases a) auto

subsection \<open>Single-store step\<close>

text \<open>
  edge_step is the single-store version of edge_collect: it returns None
  exactly when an assume edge filters the store out, and Some of the updated
  store otherwise.
\<close>
fun edge_step :: "edge_action => store => store option" where
    "edge_step EA_Nop           s = Some s"
  | "edge_step (EA_Assign x a)  s = Some (s(x := aval a s))"
  | "edge_step (EA_Assume b)    s = (if bval b s then Some s else None)"
  | "edge_step (EA_AssumeNot b) s = (if bval b s then None else Some s)"
  | "edge_step (EA_Enter xs es) s = Some (bind_formals xs (map (\<lambda>e. aval e s) es) (enter_state s))"

(* edge_collect on a singleton agrees with edge_step, viewed as an option-set. *)
lemma edge_collect_single:
  "edge_collect a {s} = set_option (edge_step a s)"
  by (cases a) auto

subsection \<open>Path transfer\<close>

text \<open>
  edges_collect folds edge actions over a path. It ignores the target program
  point carried with each path step.
\<close>

fun edges_collect :: "(edge_action * pp) list => store set => store set" where
  "edges_collect [] S = S"
| "edges_collect ((a, _) # es) S = edges_collect es (edge_collect a S)"

lemma edges_collect_empty_set[simp]: "edges_collect es {} = {}"
  by (induction es) auto

lemma edges_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> edges_collect es S \<subseteq> edges_collect es T"
  apply (induction es S arbitrary: T rule:edges_collect.induct)
  by (auto simp add: edge_collect_mono)

lemma edges_collect_member:
  "x \<in> edges_collect es S \<longleftrightarrow> (\<exists>s\<in>S. x \<in> edges_collect es {s})"
proof (induction es arbitrary: S x)
  case Nil
  then show ?case by auto
next
  case (Cons e es)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case unfolding ep
    by (metis edge_collect_member edges_collect.simps(2) local.Cons)
qed

lemma edges_collect_memberE[elim]:
  assumes "x \<in> edges_collect es S"
  obtains s where "s \<in> S" and "x \<in> edges_collect es {s}"
  using assms edges_collect_member by blast

lemma edges_collect_append[simp]:
  "edges_collect (es1 @ es2) S = edges_collect es2 (edges_collect es1 S)"
  apply (induction es1 arbitrary: S)
  by auto

lemma edges_collect_nop_append:
  "edges_collect (es1 @ [(EA_Nop, w)] @ es2) S = edges_collect es2 (edges_collect es1 S)"
proof (induction es1 arbitrary: S)
  case Nil
  show ?case by simp
next
  case (Cons e es1)
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  show ?case
    unfolding ep edges_collect.simps edges_collect_append Cons by simp
qed

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
    by (cases a) auto
  have "t \<in> edges_collect (e # es) {m0}"
    unfolding ew edges_collect.simps mm tm
    using mm edges_collect_member tm by blast
  with m0 show ?case by blast
qed

lemma edges_collect_offset_path[simp]:
  "edges_collect (offset_path k es) S = edges_collect es S"
  by (induction es arbitrary: S) (auto simp: offset_path_def)

subsection \<open>Collecting environments\<close>

text \<open>
  A collecting environment maps each program point to the set of stores that can
  appear there during an execution from a fixed initial set.
\<close>

type_synonym cenv = "pp => store set"

definition collect_pp :: "cfg => cenv => pp => store set" where
  "collect_pp g \<rho> v =
     \<Union>{edge_collect a (\<rho> u) | u a. (u, a, v) : edges g}"

lemma collect_pp_mono:
  "mono (\<lambda>\<rho>. collect_pp g \<rho> v)"
proof
  fix rho1 rho2 :: cenv
  assume "rho1 \<le> rho2"
  then have "\<forall>u. rho1 u \<subseteq> rho2 u"
    by (simp add: le_fun_def)
  then have edge: "\<forall>a u. edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    using edge_collect_mono by auto
  then show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def by auto
qed

subsection \<open>Interprocedural combine transfer\<close>


(* Goblint's combine_env then combine_assign: restore the caller, then write the
   callee's ret_var into the destination.  Deterministic, hence a singleton. *)
definition combine_collect :: "vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)"

text \<open>The binary env-combine is the destination-free instance: with no
  destination the callee return slot is not written back.\<close>
lemma combine_collect_None: "combine_collect None s t = <s|t>"
  by (simp add: combine_collect_def)

definition collect_combine_pp :: "cfg \<Rightarrow> cenv \<Rightarrow> pp \<Rightarrow> store set" where
  "collect_combine_pp g \<rho> v =
     { combine_collect dst s t
        | c ex ret dst s t.
            (c, ex, ret, dst) \<in> combines g \<and> ret = v \<and> s \<in> \<rho> c \<and> t \<in> \<rho> ex }"

definition cfg_collect_F :: "cfg \<Rightarrow> store set \<Rightarrow> cenv \<Rightarrow> cenv" where
  "cfg_collect_F g S \<rho> v =
     (if v = cfg_entry g then S else {})
     \<union> collect_pp g \<rho> v
     \<union> collect_combine_pp g \<rho> v"

definition cfg_collect :: "cfg \<Rightarrow> store set \<Rightarrow> cenv" where
  "cfg_collect g S = lfp (cfg_collect_F g S)"

subsection \<open>Monotonicity\<close>

lemma combine_collect_mono:
  assumes "S \<subseteq> S'" and "T \<subseteq> T'"
  shows "{combine_collect dst s t | s t. s \<in> S \<and> t \<in> T}
         \<subseteq> {combine_collect dst s t | s t. s \<in> S' \<and> t \<in> T'}"
  using assms by blast

lemma collect_combine_pp_mono:
  "mono (\<lambda>\<rho>. collect_combine_pp g \<rho> v)"
proof
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  have sub: "\<And>u. rho1 u \<subseteq> rho2 u"
    using le unfolding le_fun_def by auto
  show "collect_combine_pp g rho1 v \<subseteq> collect_combine_pp g rho2 v"
    unfolding collect_combine_pp_def
    using sub by blast
qed

lemma cfg_collect_F_mono:
  "mono (cfg_collect_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "cfg_collect_F g S rho1 \<le> cfg_collect_F g S rho2"
  proof (rule le_funI)
    fix v
    show "cfg_collect_F g S rho1 v \<subseteq> cfg_collect_F g S rho2 v"
      unfolding cfg_collect_F_def
      using monoD[OF collect_pp_mono[of g v] le]
            monoD[OF collect_combine_pp_mono[of g v] le]
      by auto
  qed
qed

lemma cfg_collect_F_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_F g S \<rho> \<le> cfg_collect_F g S' \<rho>"
  unfolding cfg_collect_F_def le_fun_def by auto

lemma cfg_collect_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect g S \<le> cfg_collect g S'"
  unfolding cfg_collect_def
  by (rule lfp_mono) (rule cfg_collect_F_mono_S)

lemma cfg_collect_lfp_unfold:
  "cfg_collect g S = cfg_collect_F g S (cfg_collect g S)"
  unfolding cfg_collect_def
  by (simp add: cfg_collect_F_mono def_lfp_unfold)

lemma cfg_collect_post:
  "cfg_collect_F g S (cfg_collect g S) v \<subseteq> cfg_collect g S v"
proof -
  have eq: "cfg_collect_F g S (cfg_collect g S) v = cfg_collect g S v"
    using cfg_collect_lfp_unfold by (simp add: le_fun_def)
  show ?thesis by (simp add: eq)
qed

lemma cfg_collect_entry:
  "S \<subseteq> cfg_collect g S (cfg_entry g)"
proof -
  have "S \<subseteq> cfg_collect_F g S (cfg_collect g S) (cfg_entry g)"
    unfolding cfg_collect_F_def by auto
  thus ?thesis using cfg_collect_post by blast
qed

lemma collect_combine_pp_member:
  assumes "(c, ex, ret, dst) \<in> combines g" "ret = v"
      and "s \<in> \<rho> c" "t \<in> \<rho> ex"
      and "x = combine_collect dst s t"
  shows "x \<in> collect_combine_pp g \<rho> v"
  using assms unfolding collect_combine_pp_def by blast

lemma collect_combine_pp_in_cfg_collect:
  assumes le: "\<rho> \<le> cfg_collect g S"
  shows "collect_combine_pp g \<rho> v \<subseteq> cfg_collect g S v"
proof
  fix x
  assume xin: "x \<in> collect_combine_pp g \<rho> v"
  from xin obtain c ex ret dst s t where
        h: "(c, ex, ret, dst) \<in> combines g" "ret = v"
    and st: "s \<in> \<rho> c" "t \<in> \<rho> ex"
    and xmem: "x = combine_collect dst s t"
    unfolding collect_combine_pp_def by blast
  from le have sc: "s \<in> cfg_collect g S c" and tc: "t \<in> cfg_collect g S ex"
    unfolding le_fun_def using st by auto
  have mem: "x \<in> collect_combine_pp g (cfg_collect g S) v"
    using h sc tc xmem by (rule collect_combine_pp_member)
  have step: "x \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def using mem by auto
  show "x \<in> cfg_collect g S v"
    using step cfg_collect_post by blast
qed

subsection \<open>Witness-based paths (edge + combine)\<close>

inductive cfg_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" for g where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> cfg_witness g S v s"
  | edge: "(u, a, v) \<in> edges g \<Longrightarrow> cfg_witness g S u s \<Longrightarrow>
           t \<in> edge_collect a {s} \<Longrightarrow> cfg_witness g S v t"
  | combine: "(c, ex, v, dst) \<in> combines g \<Longrightarrow> cfg_witness g S c s \<Longrightarrow>
             cfg_witness g S ex t \<Longrightarrow> u = combine_collect dst s t \<Longrightarrow>
             cfg_witness g S v u"

definition cfg_collect_paths :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store set" where
  "cfg_collect_paths g S v = {s. cfg_witness g S v s}"

lemma cfg_collect_paths_entry:
  "S \<subseteq> cfg_collect_paths g S (cfg_entry g)"
  unfolding cfg_collect_paths_def using cfg_witness.entry by blast

lemma cfg_collect_paths_edge:
  assumes e: "(u, a, v) \<in> edges g"
  shows "edge_collect a (cfg_collect_paths g S u) \<subseteq> cfg_collect_paths g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_collect_paths g S u)"
  then obtain st where st: "st \<in> cfg_collect_paths g S u" and x: "x \<in> edge_collect a {st}"
    using edge_collect_member by blast
  have wit: "cfg_witness g S u st"
    using st unfolding cfg_collect_paths_def by simp
  show "x \<in> cfg_collect_paths g S v"
    unfolding cfg_collect_paths_def using cfg_witness.edge[OF e wit x] by auto
qed

lemma cfg_collect_paths_combine:
  assumes h: "(c, ex, v, dst) \<in> combines g"
  shows "{combine_collect dst s t | s t.
           s \<in> cfg_collect_paths g S c \<and> t \<in> cfg_collect_paths g S ex}
         \<subseteq> cfg_collect_paths g S v"
proof
  fix x
  assume x: "x \<in> {combine_collect dst s t | s t.
                    s \<in> cfg_collect_paths g S c \<and> t \<in> cfg_collect_paths g S ex}"
  then obtain s t where
        sc: "cfg_witness g S c s" and te: "cfg_witness g S ex t"
    and x: "x = combine_collect dst s t"
    unfolding cfg_collect_paths_def by blast
  show "x \<in> cfg_collect_paths g S v"
    unfolding cfg_collect_paths_def using cfg_witness.combine[OF h sc te x] by auto
qed

lemma cfg_collect_paths_post:
  "cfg_collect_F g S (cfg_collect_paths g S) v \<subseteq> cfg_collect_paths g S v"
proof -
  have entry: "(if v = cfg_entry g then S else {}) \<subseteq> cfg_collect_paths g S v"
    using cfg_collect_paths_entry by auto
  have step: "collect_pp g (cfg_collect_paths g S) v \<subseteq> cfg_collect_paths g S v"
    unfolding collect_pp_def using cfg_collect_paths_edge by blast
  have comb: "collect_combine_pp g (cfg_collect_paths g S) v \<subseteq> cfg_collect_paths g S v"
  proof
    fix x
    assume xin: "x \<in> collect_combine_pp g (cfg_collect_paths g S) v"
    from xin obtain c ex ret dst s t where h: "(c, ex, ret, dst) \<in> combines g"
      and rv: "ret = v"
      and st: "s \<in> cfg_collect_paths g S c" "t \<in> cfg_collect_paths g S ex"
      and x: "x = combine_collect dst s t"
      unfolding collect_combine_pp_def by auto
    from h rv have h': "(c, ex, v, dst) \<in> combines g" by simp
    have xin': "x \<in> {combine_collect dst s t | s t.
                        s \<in> cfg_collect_paths g S c \<and> t \<in> cfg_collect_paths g S ex}"
      using st x by blast
    show "x \<in> cfg_collect_paths g S v"
      using cfg_collect_paths_combine[OF h'] xin' by blast
  qed
  show ?thesis
    unfolding cfg_collect_F_def using entry step comb by auto
qed

lemma cfg_collect_le_paths:
  "cfg_collect g S v \<subseteq> cfg_collect_paths g S v"
proof -
  have pf: "cfg_collect_F g S (cfg_collect_paths g S) \<le> cfg_collect_paths g S"
    unfolding le_fun_def using cfg_collect_paths_post by simp
  have "lfp (cfg_collect_F g S) \<le> cfg_collect_paths g S"
    using pf cfg_collect_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_def le_fun_def by simp
qed

lemma cfg_witness_in_cfg_collect:
  assumes wit: "cfg_witness g S v s"
  shows "s \<in> cfg_collect g S v"
proof -
  from wit show ?thesis
  proof (induction rule: cfg_witness.induct)
    case (entry vp sto Sa)
    have "sto \<in> cfg_collect_F g Sa (cfg_collect g Sa) vp"
      unfolding cfg_collect_F_def using entry by auto
    then show ?case using cfg_collect_post by blast
  next
    case (edge u a v Sa sto t)
    have ih: "sto \<in> cfg_collect g Sa u" using edge.IH by simp
    have "t \<in> edge_collect a (cfg_collect g Sa u)"
    proof -
      have sub: "{sto} \<subseteq> cfg_collect g Sa u" using ih by simp
      have mono: "edge_collect a {sto} \<subseteq> edge_collect a (cfg_collect g Sa u)"
        using edge_collect_mono[OF sub] .
      show ?thesis using edge(3) mono by auto
    qed
    have "t \<in> collect_pp g (cfg_collect g Sa) v"
      unfolding collect_pp_def using edge(1) \<open>t \<in> edge_collect a (cfg_collect g Sa u)\<close> by auto
    have "t \<in> cfg_collect_F g Sa (cfg_collect g Sa) v"
      unfolding cfg_collect_F_def using \<open>t \<in> collect_pp g (cfg_collect g Sa) v\<close> by auto
    then show ?case using cfg_collect_post by blast
  next
    case (combine c ex v dst Sa sto t u)
    have "u \<in> collect_combine_pp g (cfg_collect g Sa) v"
      using collect_combine_pp_member[OF combine(1) refl combine.IH(1) combine.IH(2) combine(4)] .
    have "u \<in> cfg_collect_F g Sa (cfg_collect g Sa) v"
      unfolding cfg_collect_F_def using \<open>u \<in> collect_combine_pp g (cfg_collect g Sa) v\<close>
      by auto
    then show ?case using cfg_collect_post by blast
  qed
qed

lemma cfg_collect_paths_le:
  "cfg_collect_paths g S v \<subseteq> cfg_collect g S v"
  unfolding cfg_collect_paths_def using cfg_witness_in_cfg_collect by auto

lemma cfg_collect_eq_paths:
  "cfg_collect g S v = cfg_collect_paths g S v"
  using cfg_collect_le_paths cfg_collect_paths_le by (rule antisym)


end
