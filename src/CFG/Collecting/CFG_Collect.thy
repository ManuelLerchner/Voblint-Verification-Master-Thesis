theory CFG_Collect
  imports CFG_Collect_Edges IMP2_Proc_to_CFG
begin

section \<open>Interprocedural collecting semantics\<close>

text \<open>
  Interprocedural collecting semantics: extends the per-edge transformer
  with combine triples from combines g:
    (call, proc_exit, return) contributes
      { combine_states s t | s in C call, t in C proc_exit }
    at the return program point.

  Operational adequacy (pruns_to => cfg_collect) is proved in
  CFG_Collect_Adeq.
\<close>

definition collect_combine_pp :: "cfg \<Rightarrow> cenv \<Rightarrow> pp \<Rightarrow> store set" where
  "collect_combine_pp g \<rho> v =
     \<Union>{ {<s|t> | s t. s \<in> \<rho> c \<and> t \<in> \<rho> ex}
           | c ex ret. (c, ex, ret) \<in> combines g \<and> ret = v }"

definition cfg_collect_F :: "cfg \<Rightarrow> store set \<Rightarrow> cenv \<Rightarrow> cenv" where
  "cfg_collect_F g S \<rho> v =
     (if v = cfg_entry g then S else {})
     \<union> collect_pp g \<rho> v
     \<union> collect_combine_pp g \<rho> v"

definition cfg_collect :: "cfg \<Rightarrow> store set \<Rightarrow> cenv" where
  "cfg_collect g S = lfp (cfg_collect_F g S)"

subsection \<open>Monotonicity\<close>

lemma combine_states_image_mono:
  assumes "S \<subseteq> S'" and "T \<subseteq> T'"
  shows "{<s|t> | s t. s \<in> S \<and> t \<in> T}
         \<subseteq> {<s|t> | s t. s \<in> S' \<and> t \<in> T'}"
  using assms by blast

lemma collect_combine_pp_mono:
  "mono (\<lambda>\<rho>. collect_combine_pp g \<rho> v)"
proof
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  have sub: "\<And>u. rho1 u \<subseteq> rho2 u"
    using le unfolding le_fun_def by auto
  show "collect_combine_pp g rho1 v \<subseteq> collect_combine_pp g rho2 v"
  proof
    fix x
    assume xin: "x \<in> collect_combine_pp g rho1 v"
    from xin[unfolded collect_combine_pp_def]
    obtain c ex ret s t where
      h: "(c, ex, ret) \<in> combines g" "ret = v"
      and st: "s \<in> rho1 c" "t \<in> rho1 ex"
      and x: "x = <s|t>"
      by blast
    have "s \<in> rho2 c" "t \<in> rho2 ex" using st sub by auto
    thus "x \<in> collect_combine_pp g rho2 v"
      unfolding collect_combine_pp_def x using h by blast
  qed
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
      by (auto dest: subsetD)
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
  assumes "(c, ex, ret) \<in> combines g" "ret = v"
      and "s \<in> \<rho> c" "t \<in> \<rho> ex"
  shows "<s|t> \<in> collect_combine_pp g \<rho> v"
  using assms unfolding collect_combine_pp_def by blast

lemma collect_combine_pp_in_cfg_collect:
  assumes le: "\<rho> \<le> cfg_collect g S"
  shows "collect_combine_pp g \<rho> v \<subseteq> cfg_collect g S v"
proof
  fix x
  assume xin: "x \<in> collect_combine_pp g \<rho> v"
  from xin obtain c ex ret s t where
        h: "(c, ex, ret) \<in> combines g" "ret = v"
    and st: "s \<in> \<rho> c" "t \<in> \<rho> ex"
    and x: "x = <s|t>"
    unfolding collect_combine_pp_def by blast
  from le have sc: "s \<in> cfg_collect g S c" and tc: "t \<in> cfg_collect g S ex"
    unfolding le_fun_def using st by auto
  have mem: "<s|t> \<in> collect_combine_pp g (cfg_collect g S) v"
  proof (rule collect_combine_pp_member)
    show "(c, ex, ret) \<in> combines g" using h by simp
    show "ret = v" using h by simp
    show "s \<in> cfg_collect g S c" using sc .
    show "t \<in> cfg_collect g S ex" using tc .
  qed
  have step: "<s|t> \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def using mem by auto
  show "x \<in> cfg_collect g S v"
    using x step cfg_collect_post by blast
qed

subsection \<open>Witness-based paths (edge + combine)\<close>

inductive cfg_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" for g where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> cfg_witness g S v s"
  | edge: "(u, a, v) \<in> edges g \<Longrightarrow> cfg_witness g S u s \<Longrightarrow>
           t \<in> edge_collect a {s} \<Longrightarrow> cfg_witness g S v t"
  | combine: "(c, ex, v) \<in> combines g \<Longrightarrow> cfg_witness g S c s \<Longrightarrow>
             cfg_witness g S ex t \<Longrightarrow> cfg_witness g S v <s|t>"

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
  assumes h: "(c, ex, v) \<in> combines g"
  shows "{<s|t> | s t.
           s \<in> cfg_collect_paths g S c \<and> t \<in> cfg_collect_paths g S ex}
         \<subseteq> cfg_collect_paths g S v"
proof
  fix x
  assume x: "x \<in> {<s|t> | s t.
                    s \<in> cfg_collect_paths g S c \<and> t \<in> cfg_collect_paths g S ex}"
  then obtain s t where
        sc: "cfg_witness g S c s" and te: "cfg_witness g S ex t"
    and x: "x = <s|t>"
    unfolding cfg_collect_paths_def by blast
  show "x \<in> cfg_collect_paths g S v"
    unfolding cfg_collect_paths_def using cfg_witness.combine[OF h sc te] x by auto
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
    from xin obtain c ex s t where h: "(c, ex, v) \<in> combines g"
      and st: "s \<in> cfg_collect_paths g S c" "t \<in> cfg_collect_paths g S ex"
    and x: "x = <s|t>"
      unfolding collect_combine_pp_def by auto
    show "x \<in> cfg_collect_paths g S v"
      using cfg_collect_paths_combine[OF h] st x by (auto simp: cfg_collect_paths_def)
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
    case (combine c ex v Sa sto t)
    have "<sto|t> \<in> collect_combine_pp g (cfg_collect g Sa) v"
      using collect_combine_pp_member[OF combine(1) refl combine.IH(1) combine.IH(2)] .
    have "<sto|t> \<in> cfg_collect_F g Sa (cfg_collect g Sa) v"
      unfolding cfg_collect_F_def using \<open><sto|t> \<in> collect_combine_pp g (cfg_collect g Sa) v\<close>
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
