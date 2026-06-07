theory CFG_Collect_IP
  imports CFG_Edges_Collect IMP2_Proc_to_CFG
begin

(*
  Interprocedural collecting semantics (M1 slice 2).

  Extends cfg_collect with combine triples from combines g:
    (call, proc_exit, return) contributes
      { combine_states s t | s in C call, t in C proc_exit }
    at the return program point.

  When combines g = {}, agrees with cfg_collect.
  Operational adequacy (pruns_to => cfg_collect_ip) is the next proof target.
*)

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

(* -- Monotonicity ------------------------------------------------ *)

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

(* -- Relation to intra-procedural cfg_collect ---------------------- *)

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


end
