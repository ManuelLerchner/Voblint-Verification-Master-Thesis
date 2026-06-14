theory CFG_Collect_IP
  imports CFG_Collect_Edges IMP2_Proc_to_CFG
begin

section \<open>Interprocedural collecting semantics\<close>

text \<open>
  Extends cfg_collect with combine triples from combines g:
    (call, proc_exit, return) contributes
      { combine_states s t | s in C call, t in C proc_exit }
    at the return program point.

  When combines g = {}, agrees with cfg_collect.
  Operational adequacy (pruns_to => cfg_collect_ip) is proved in
  CFG_Collect_IP_Adeq.
\<close>

definition collect_combine_pp :: "cfg \<Rightarrow> cenv \<Rightarrow> pp \<Rightarrow> store set" where
  "collect_combine_pp g rho v =
     \<Union>{ {combine_states s t | s t. s \<in> rho c \<and> t \<in> rho ex}
           | c ex ret. (c, ex, ret) \<in> combines g \<and> ret = v }"

definition cfg_collect_ip_F :: "cfg \<Rightarrow> store set \<Rightarrow> cenv \<Rightarrow> cenv" where
  "cfg_collect_ip_F g S rho v =
     (if v = cfg_entry g then S else {})
     \<union> collect_pp g rho v
     \<union> collect_combine_pp g rho v"

definition cfg_collect_ip :: "cfg \<Rightarrow> store set \<Rightarrow> cenv" where
  "cfg_collect_ip g S = lfp (cfg_collect_ip_F g S)"

subsection \<open>Monotonicity\<close>

lemma combine_states_image_mono:
  assumes "S \<subseteq> S'" and "T \<subseteq> T'"
  shows "{combine_states s t | s t. s \<in> S \<and> t \<in> T}
         \<subseteq> {combine_states s t | s t. s \<in> S' \<and> t \<in> T'}"
  using assms by blast

lemma collect_combine_pp_mono:
  "mono (\<lambda>rho. collect_combine_pp g rho v)"
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
      and x: "x = combine_states s t"
      by blast
    have "s \<in> rho2 c" "t \<in> rho2 ex" using st sub by auto
    thus "x \<in> collect_combine_pp g rho2 v"
      unfolding collect_combine_pp_def x using h by blast
  qed
qed

lemma cfg_collect_ip_F_mono:
  "mono (cfg_collect_ip_F g S)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  show "cfg_collect_ip_F g S rho1 \<le> cfg_collect_ip_F g S rho2"
  proof (rule le_funI)
    fix v
    show "cfg_collect_ip_F g S rho1 v \<subseteq> cfg_collect_ip_F g S rho2 v"
      unfolding cfg_collect_ip_F_def
      using monoD[OF collect_pp_mono[of g v] le]
            monoD[OF collect_combine_pp_mono[of g v] le]
      by (auto dest: subsetD)
  qed
qed

lemma cfg_collect_ip_F_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_ip_F g S rho \<le> cfg_collect_ip_F g S' rho"
  unfolding cfg_collect_ip_F_def le_fun_def by auto

lemma cfg_collect_ip_mono_S:
  "S \<subseteq> S' \<Longrightarrow> cfg_collect_ip g S \<le> cfg_collect_ip g S'"
  unfolding cfg_collect_ip_def
  by (rule lfp_mono) (rule cfg_collect_ip_F_mono_S)

lemma cfg_collect_ip_lfp_unfold:
  "cfg_collect_ip g S = cfg_collect_ip_F g S (cfg_collect_ip g S)"
  unfolding cfg_collect_ip_def
  by (simp add: cfg_collect_ip_F_mono def_lfp_unfold)

subsection \<open>Relation to intra-procedural cfg_collect\<close>

lemma collect_combine_pp_empty[simp]:
  "combines g = {} \<Longrightarrow> collect_combine_pp g rho v = {}"
  unfolding collect_combine_pp_def by auto

lemma cfg_collect_ip_F_eq_cfg_collect_F:
  assumes "combines g = {}"
  shows "cfg_collect_ip_F g S rho v = cfg_collect_F g S rho v"
  unfolding cfg_collect_ip_F_def cfg_collect_F_def using assms by auto

lemma cfg_collect_ip_eq_cfg_collect:
  assumes "combines g = {}"
  shows "cfg_collect_ip g S = cfg_collect g S"
proof -
  have eq: "cfg_collect_ip_F g S = cfg_collect_F g S"
  proof
    fix rho
    show "cfg_collect_ip_F g S rho = cfg_collect_F g S rho"
    proof (rule ext)
      fix v
      show "cfg_collect_ip_F g S rho v = cfg_collect_F g S rho v"
        using cfg_collect_ip_F_eq_cfg_collect_F[OF assms] .
    qed
  qed
  show ?thesis unfolding cfg_collect_ip_def cfg_collect_def eq by simp
qed

lemma cfg_collect_ip_F_ge_cfg_collect_F:
  "cfg_collect_F g S rho v \<subseteq> cfg_collect_ip_F g S rho v"
  unfolding cfg_collect_F_def cfg_collect_ip_F_def by auto

lemma cfg_collect_le_cfg_collect_ip:
  "cfg_collect g S \<le> cfg_collect_ip g S"
  unfolding cfg_collect_def cfg_collect_ip_def
  by (simp add: cfg_collect_ip_F_ge_cfg_collect_F le_funI lfp_mono)
 

lemma cfg_collect_ip_entry:
  "S \<subseteq> cfg_collect_ip g S (cfg_entry g)"
  by (smt (verit, best) Un_upper1 cfg_collect_F_def cfg_collect_ip_F_ge_cfg_collect_F
      cfg_collect_ip_lfp_unfold order_trans)

lemma cfg_collect_ip_post:
  "cfg_collect_ip_F g S (cfg_collect_ip g S) v \<subseteq> cfg_collect_ip g S v"
proof -
  have eq: "cfg_collect_ip_F g S (cfg_collect_ip g S) v = cfg_collect_ip g S v"
    using cfg_collect_ip_lfp_unfold by (simp add: le_fun_def)
  show ?thesis by (simp add: eq)
qed

lemma collect_combine_pp_member:
  assumes "(c, ex, ret) \<in> combines g" "ret = v"
      and "s \<in> rho c" "t \<in> rho ex"
  shows "combine_states s t \<in> collect_combine_pp g rho v"
  using assms unfolding collect_combine_pp_def by blast

lemma collect_combine_pp_in_cfg_collect_ip:
  assumes le: "rho \<le> cfg_collect_ip g S"
  shows "collect_combine_pp g rho v \<subseteq> cfg_collect_ip g S v"
proof
  fix x
  assume xin: "x \<in> collect_combine_pp g rho v"
  from xin obtain c ex ret s t where
        h: "(c, ex, ret) \<in> combines g" "ret = v"
    and st: "s \<in> rho c" "t \<in> rho ex"
    and x: "x = combine_states s t"
    unfolding collect_combine_pp_def by blast
  from le have sc: "s \<in> cfg_collect_ip g S c" and tc: "t \<in> cfg_collect_ip g S ex"
    unfolding le_fun_def using st by auto
  have mem: "combine_states s t \<in> collect_combine_pp g (cfg_collect_ip g S) v"
  proof (rule collect_combine_pp_member)
    show "(c, ex, ret) \<in> combines g" using h by simp
    show "ret = v" using h by simp
    show "s \<in> cfg_collect_ip g S c" using sc .
    show "t \<in> cfg_collect_ip g S ex" using tc .
  qed
  have step: "combine_states s t \<in> cfg_collect_ip_F g S (cfg_collect_ip g S) v"
    unfolding cfg_collect_ip_F_def using mem by auto
  show "x \<in> cfg_collect_ip g S v"
    using x step cfg_collect_ip_post by blast
qed

subsection \<open>Witness-based paths (edge + combine)\<close>

inductive ip_witness :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store \<Rightarrow> bool" for g where
  entry: "v = cfg_entry g \<Longrightarrow> s \<in> S \<Longrightarrow> ip_witness g S v s"
  | edge: "(u, a, v) \<in> edges g \<Longrightarrow> ip_witness g S u s \<Longrightarrow>
           t \<in> edge_collect a {s} \<Longrightarrow> ip_witness g S v t"
  | combine: "(c, ex, v) \<in> combines g \<Longrightarrow> ip_witness g S c s \<Longrightarrow>
             ip_witness g S ex t \<Longrightarrow> ip_witness g S v (combine_states s t)"

definition cfg_collect_ip_paths :: "cfg \<Rightarrow> store set \<Rightarrow> pp \<Rightarrow> store set" where
  "cfg_collect_ip_paths g S v = {s. ip_witness g S v s}"

lemma cfg_collect_ip_paths_entry:
  "S \<subseteq> cfg_collect_ip_paths g S (cfg_entry g)"
  unfolding cfg_collect_ip_paths_def using ip_witness.entry by blast

lemma cfg_collect_ip_paths_edge:
  assumes e: "(u, a, v) \<in> edges g"
  shows "edge_collect a (cfg_collect_ip_paths g S u) \<subseteq> cfg_collect_ip_paths g S v"
proof
  fix x
  assume x: "x \<in> edge_collect a (cfg_collect_ip_paths g S u)"
  then obtain st where st: "st \<in> cfg_collect_ip_paths g S u" and x: "x \<in> edge_collect a {st}"
    using edge_collect_member by blast
  have wit: "ip_witness g S u st"
    using st unfolding cfg_collect_ip_paths_def by simp
  show "x \<in> cfg_collect_ip_paths g S v"
    unfolding cfg_collect_ip_paths_def using ip_witness.edge[OF e wit x] by auto
qed

lemma cfg_collect_ip_paths_combine:
  assumes h: "(c, ex, v) \<in> combines g"
  shows "{combine_states s t | s t.
           s \<in> cfg_collect_ip_paths g S c \<and> t \<in> cfg_collect_ip_paths g S ex}
         \<subseteq> cfg_collect_ip_paths g S v"
proof
  fix x
  assume x: "x \<in> {combine_states s t | s t.
                    s \<in> cfg_collect_ip_paths g S c \<and> t \<in> cfg_collect_ip_paths g S ex}"
  then obtain s t where
        sc: "ip_witness g S c s" and te: "ip_witness g S ex t"
    and x: "x = combine_states s t"
    unfolding cfg_collect_ip_paths_def by blast
  show "x \<in> cfg_collect_ip_paths g S v"
    unfolding cfg_collect_ip_paths_def using ip_witness.combine[OF h sc te] x by auto
qed

lemma cfg_collect_ip_paths_post:
  "cfg_collect_ip_F g S (cfg_collect_ip_paths g S) v \<subseteq> cfg_collect_ip_paths g S v"
proof -
  have entry: "(if v = cfg_entry g then S else {}) \<subseteq> cfg_collect_ip_paths g S v"
    using cfg_collect_ip_paths_entry by auto
  have step: "collect_pp g (cfg_collect_ip_paths g S) v \<subseteq> cfg_collect_ip_paths g S v"
    unfolding collect_pp_def using cfg_collect_ip_paths_edge by blast
  have comb: "collect_combine_pp g (cfg_collect_ip_paths g S) v \<subseteq> cfg_collect_ip_paths g S v"
  proof
    fix x
    assume xin: "x \<in> collect_combine_pp g (cfg_collect_ip_paths g S) v"
    from xin obtain c ex s t where h: "(c, ex, v) \<in> combines g"
      and st: "s \<in> cfg_collect_ip_paths g S c" "t \<in> cfg_collect_ip_paths g S ex"
      and x: "x = combine_states s t"
      unfolding collect_combine_pp_def by auto
    show "x \<in> cfg_collect_ip_paths g S v"
      using cfg_collect_ip_paths_combine[OF h] st x by (auto simp: cfg_collect_ip_paths_def)
  qed
  show ?thesis
    unfolding cfg_collect_ip_F_def using entry step comb by auto
qed

lemma cfg_collect_ip_le_paths:
  "cfg_collect_ip g S v \<subseteq> cfg_collect_ip_paths g S v"
proof -
  have pf: "cfg_collect_ip_F g S (cfg_collect_ip_paths g S) \<le> cfg_collect_ip_paths g S"
    unfolding le_fun_def using cfg_collect_ip_paths_post by simp
  have "lfp (cfg_collect_ip_F g S) \<le> cfg_collect_ip_paths g S"
    using pf cfg_collect_ip_F_mono lfp_lowerbound by blast
  then show ?thesis
    unfolding cfg_collect_ip_def le_fun_def by simp
qed

lemma ip_witness_in_cfg_collect_ip:
  assumes wit: "ip_witness g S v s"
  shows "s \<in> cfg_collect_ip g S v"
proof -
  from wit show ?thesis
  proof (induction rule: ip_witness.induct)
    case (entry vp sto Sa)
    have "sto \<in> cfg_collect_ip_F g Sa (cfg_collect_ip g Sa) vp"
      unfolding cfg_collect_ip_F_def using entry by auto
    then show ?case using cfg_collect_ip_post by blast
  next
    case (edge u a v Sa sto t)
    have ih: "sto \<in> cfg_collect_ip g Sa u" using edge.IH by simp
    have "t \<in> edge_collect a (cfg_collect_ip g Sa u)"
    proof -
      have sub: "{sto} \<subseteq> cfg_collect_ip g Sa u" using ih by simp
      have mono: "edge_collect a {sto} \<subseteq> edge_collect a (cfg_collect_ip g Sa u)"
        using edge_collect_mono[OF sub] .
      show ?thesis using edge(3) mono by auto
    qed
    have "t \<in> collect_pp g (cfg_collect_ip g Sa) v"
      unfolding collect_pp_def using edge(1) \<open>t \<in> edge_collect a (cfg_collect_ip g Sa u)\<close> by auto
    have "t \<in> cfg_collect_ip_F g Sa (cfg_collect_ip g Sa) v"
      unfolding cfg_collect_ip_F_def using \<open>t \<in> collect_pp g (cfg_collect_ip g Sa) v\<close> by auto
    then show ?case using cfg_collect_ip_post by blast
  next
    case (combine c ex v Sa sto t)
    have "combine_states sto t \<in> collect_combine_pp g (cfg_collect_ip g Sa) v"
      using collect_combine_pp_member[OF combine(1) refl combine.IH(1) combine.IH(2)] .
    have "combine_states sto t \<in> cfg_collect_ip_F g Sa (cfg_collect_ip g Sa) v"
      unfolding cfg_collect_ip_F_def using \<open>combine_states sto t \<in> collect_combine_pp g (cfg_collect_ip g Sa) v\<close>
      by auto
    then show ?case using cfg_collect_ip_post by blast
  qed
qed

lemma cfg_collect_ip_paths_le:
  "cfg_collect_ip_paths g S v \<subseteq> cfg_collect_ip g S v"
  unfolding cfg_collect_ip_paths_def using ip_witness_in_cfg_collect_ip by auto

lemma cfg_collect_ip_eq_paths:
  "cfg_collect_ip g S v = cfg_collect_ip_paths g S v"
  using cfg_collect_ip_le_paths cfg_collect_ip_paths_le by (rule antisym)


end
