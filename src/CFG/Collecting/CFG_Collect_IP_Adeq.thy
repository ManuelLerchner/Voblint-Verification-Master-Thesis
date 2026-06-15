theory CFG_Collect_IP_Adeq
  imports CFG_Collect_IP "Voblint_IMP2.IMP2_Proc"
begin

section \<open>Operational adequacy for cfg_collect_ip\<close>

text \<open>
  Exit projection for interprocedural programs, plus the first concrete
  witness: non-recursive call that increments a global (IMP2_Proc.pcall_global_increment).
\<close>

definition singleton_store :: "store \<Rightarrow> store set" where
  "singleton_store s = {s}"

definition pruns_to_ip ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pruns_to_ip \<Pi> ps c s t =
     (let g = compile_prog \<Pi> ps c in t \<in> cfg_collect_ip g (singleton_store s) (cfg_exit g))"

lemma pruns_to_ipD[elim]:
  "pruns_to_ip \<Pi> ps c s t
   \<Longrightarrow> t \<in> cfg_collect_ip (compile_prog \<Pi> ps c) (singleton_store s)
                  (cfg_exit (compile_prog \<Pi> ps c))"
  unfolding pruns_to_ip_def by (auto simp: Let_def)

lemma cfg_collect_ip_lfp_lowerbound:
  assumes le: "cfg_collect_ip_F g S env \<le> env"
  shows "cfg_collect_ip g S \<le> env"
  unfolding cfg_collect_ip_def
  using le lfp_lowerbound by blast

lemma cfg_collect_ip_collect_pp:
  "collect_pp g (cfg_collect_ip g S) v \<subseteq> cfg_collect_ip g S v"
proof
  fix x
  assume xin: "x \<in> collect_pp g (cfg_collect_ip g S) v"
  have step: "x \<in> cfg_collect_ip_F g S (cfg_collect_ip g S) v"
    unfolding cfg_collect_ip_F_def using xin by auto
  show "x \<in> cfg_collect_ip g S v" using step cfg_collect_ip_post by blast
qed

lemma cfg_collect_ip_edge:
  assumes e: "(u, a, v) \<in> edges g"
      and xin: "x \<in> edge_collect a (cfg_collect_ip g S u)"
  shows "x \<in> cfg_collect_ip g S v"
proof -
  have "x \<in> collect_pp g (cfg_collect_ip g S) v"
    unfolding collect_pp_def using e xin by blast
  thus ?thesis using cfg_collect_ip_collect_pp by blast
qed

lemma cfg_collect_ip_combine:
  assumes h: "(c, ex, ret) \<in> combines g" and ret: "ret = v"
      and sc: "s \<in> cfg_collect_ip g S c" and te: "t \<in> cfg_collect_ip g S ex"
  shows "combine_states s t \<in> cfg_collect_ip g S v"
proof -
  have mem: "combine_states s t \<in> collect_combine_pp g (cfg_collect_ip g S) v"
    using collect_combine_pp_member[OF h ret sc te] .
  have step: "combine_states s t \<in> cfg_collect_ip_F g S (cfg_collect_ip g S) v"
    unfolding cfg_collect_ip_F_def using mem by auto
  show ?thesis using step cfg_collect_ip_post by blast
qed

subsection \<open>compile_prog shape for the increment witness\<close>

definition inc_body :: com where
  "inc_body = Assign ''Gx'' (Plus (V ''Gx'') (N 1))"

definition inc_pi :: proc_table where
  "inc_pi = (\<lambda>_. None)(''p'' := Some inc_body)"

definition inc_g :: cfg where
  "inc_g = mk_ip_cfg 2 3
    {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
     (2, EA_Enter, 0)}
    {(2, 1, 3)}"

lemma inc_pi_body: "inc_pi ''p'' = Some inc_body"
  by (simp add: inc_pi_def inc_body_def)

lemma compile_procs_list_singleton_inc:
  "compile_procs_list inc_pi [''p''] (\<lambda>_. None) 0 =
     (2, ((\<lambda>_. None)(''p'' := Some (0, 1, {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {}))),
      {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {})"
  by (simp add: inc_pi_def inc_body_def compile_procs_list.simps compile.simps)

lemma compile_inc_call:
  "compile inc_pi
     ((\<lambda>_. None)(''p'' := Some (0, 1, { (0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {})))
     (Call ''p'') 2 =
   (3, 2, 3, {(2, EA_Enter, 0)}, {(2, 1, 3)})"
  by (simp add: compile.simps)

lemma compile_prog_inc_entry:
  "cfg_entry (compile_prog inc_pi [''p''] (Call ''p'')) = 2"
proof -
  obtain lay E_proc C_proc where
    procs: "compile_procs_list inc_pi [''p''] (\<lambda>_. None) 0 = (2, lay, E_proc, C_proc)"
    by (metis compile_procs_list_singleton_inc)
  have lay_eq: "lay = (\<lambda>_. None)(''p'' := Some (0, 1,
      {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {}))"
    using procs compile_procs_list_singleton_inc by simp
  have call: "compile inc_pi lay (Call ''p'') 2 = (3, 2, 3, {(2, EA_Enter, 0)}, {(2, 1, 3)})"
    using compile_inc_call unfolding lay_eq by simp
  show ?thesis
    unfolding compile_prog_def compile_prog_with_regions_def mk_ip_cfg_def
    using procs call by (simp add: Let_def split: prod.splits)
qed

lemma compile_prog_inc_exit:
  "cfg_exit (compile_prog inc_pi [''p''] (Call ''p'')) = 3"
proof -
  obtain lay E_proc C_proc where
    procs: "compile_procs_list inc_pi [''p''] (\<lambda>_. None) 0 = (2, lay, E_proc, C_proc)"
    by (metis compile_procs_list_singleton_inc)
  have lay_eq: "lay = (\<lambda>_. None)(''p'' := Some (0, 1,
      {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {}))"
    using procs compile_procs_list_singleton_inc by simp
  have call: "compile inc_pi lay (Call ''p'') 2 = (3, 2, 3, {(2, EA_Enter, 0)}, {(2, 1, 3)})"
    using compile_inc_call unfolding lay_eq by simp
  show ?thesis
    unfolding compile_prog_def compile_prog_with_regions_def mk_ip_cfg_def
    using procs call by (simp add: Let_def split: prod.splits)
qed

lemma compile_prog_inc_edges:
  "edges (compile_prog inc_pi [''p''] (Call ''p'')) =
     {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
      (2, EA_Enter, 0)}"
proof -
  obtain lay E_proc C_proc where
    procs: "compile_procs_list inc_pi [''p''] (\<lambda>_. None) 0 = (2, lay, E_proc, C_proc)"
    by (metis compile_procs_list_singleton_inc)
  have lay_eq: "lay = (\<lambda>_. None)(''p'' := Some (0, 1,
      {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {}))"
    using procs compile_procs_list_singleton_inc by simp
  have call: "compile inc_pi lay (Call ''p'') 2 = (3, 2, 3, {(2, EA_Enter, 0)}, {(2, 1, 3)})"
    using compile_inc_call unfolding lay_eq by simp
  show ?thesis
    unfolding compile_prog_def compile_prog_with_regions_def mk_ip_cfg_def
    using procs call lay_eq compile_procs_list_singleton_inc
    by (auto simp: Let_def split: prod.splits)
qed

lemma compile_prog_inc_combines:
  "combines (compile_prog inc_pi [''p''] (Call ''p'')) = {(2, 1, 3)}"
proof -
  obtain lay E_proc C_proc where
    procs: "compile_procs_list inc_pi [''p''] (\<lambda>_. None) 0 = (2, lay, E_proc, C_proc)"
    by (metis compile_procs_list_singleton_inc)
  have lay_eq: "lay = (\<lambda>_. None)(''p'' := Some (0, 1,
      {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1)}, {}))"
    using procs compile_procs_list_singleton_inc by simp
  have call: "compile inc_pi lay (Call ''p'') 2 = (3, 2, 3, {(2, EA_Enter, 0)}, {(2, 1, 3)})"
    using compile_inc_call unfolding lay_eq by simp
  show ?thesis
    unfolding compile_prog_def compile_prog_with_regions_def mk_ip_cfg_def
    using procs call lay_eq compile_procs_list_singleton_inc
    by (simp add: Let_def split: prod.splits)
qed

lemma compile_prog_inc_structure:
  shows "cfg_entry inc_g = 2"
    and "cfg_exit inc_g = 3"
    and "edges inc_g =
       {(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1),
        (2, EA_Enter, 0)}"
    and "combines inc_g = {(2, 1, 3)}"
  unfolding inc_g_def mk_ip_cfg_def by auto

lemma collect_pp_edges_cong:
  "edges g1 = edges g2 \<Longrightarrow> collect_pp g1 \<rho> v = collect_pp g2 \<rho> v"
  unfolding collect_pp_def by auto

lemma collect_combine_pp_combines_cong:
  "combines g1 = combines g2
   \<Longrightarrow> collect_combine_pp g1 \<rho> v = collect_combine_pp g2 \<rho> v"
  unfolding collect_combine_pp_def by auto

lemma cfg_collect_ip_cong:
  assumes entry: "cfg_entry g1 = cfg_entry g2"
  assumes edges: "edges g1 = edges g2"
  assumes combines: "combines g1 = combines g2"
  shows "cfg_collect_ip g1 S v = cfg_collect_ip g2 S v"
proof -
  have F: "cfg_collect_ip_F g1 S = cfg_collect_ip_F g2 S"
    using assms unfolding cfg_collect_ip_F_def
    using collect_combine_pp_def collect_pp_def by presburger
  show ?thesis
    unfolding cfg_collect_ip_def
    by (simp add: F)
qed

lemma edge_collect_assign_enter_state:
  fixes s :: store and x :: vname and a :: aexp
  assumes "enter_state s \<in> S"
  shows "(enter_state s)(x := aval a (enter_state s)) \<in> edge_collect (EA_Assign x a) S"
  using assms by (auto simp: edge_collect.simps)

lemma aval_plus_gx_on_enter:
  "aval (Plus (V ''Gx'') (N 1)) (enter_state s) = s ''Gx'' + 1"
  by (simp add: enter_state_def is_global_def)

lemma combine_after_enter_global_assign:
  assumes "is_global x"
  shows "<s | (enter_state s)(x := v)> = s(x := v)"
  using assms by (auto simp: combine_states_def enter_state_def)

subsection \<open>Witness: global increment survives a single call\<close>

lemma pcall_global_increment_cfg_collect_ip:
  fixes s :: store
  shows "s(''Gx'' := s ''Gx'' + 1) \<in> cfg_collect_ip inc_g (singleton_store s) (cfg_exit inc_g)"
proof -
  let ?g = inc_g and ?S = "singleton_store s"
    and ?t = "s(''Gx'' := s ''Gx'' + 1)"
  have entry: "singleton_store s \<subseteq> cfg_collect_ip ?g ?S (cfg_entry ?g)"
    using cfg_collect_ip_entry by simp
  have s_at_call: "s \<in> cfg_collect_ip ?g ?S 2"
    using entry compile_prog_inc_structure(1) singleton_store_def by auto
  have en: "(2, EA_Enter, 0) \<in> edges ?g"
    using compile_prog_inc_structure by simp
  have enter: "enter_state s \<in> cfg_collect_ip ?g ?S 0"
  proof (rule cfg_collect_ip_edge[OF en])
    show "enter_state s \<in> edge_collect EA_Enter (cfg_collect_ip ?g ?S 2)"
      using s_at_call by (simp add: edge_collect.simps)
  qed
  have asg: "(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)), 1) \<in> edges ?g"
    using compile_prog_inc_structure by simp
  let ?body_store = "(enter_state s)(''Gx'' := s ''Gx'' + 1)"
  have edge_asg: "?body_store \<in> edge_collect (EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)))
                  (cfg_collect_ip ?g ?S 0)"
  proof -
    have mem: "(enter_state s)(''Gx'' := aval (Plus (V ''Gx'') (N 1)) (enter_state s))
      \<in> edge_collect (EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1))) (cfg_collect_ip ?g ?S 0)"
      using enter edge_collect_assign_enter_state by blast
    show ?thesis using mem aval_plus_gx_on_enter by simp
  qed
  have body_store: "?body_store \<in> cfg_collect_ip ?g ?S 1"
    using cfg_collect_ip_edge[OF asg edge_asg] by simp
  have comb: "(2, 1, 3) \<in> combines ?g"
    using compile_prog_inc_structure by simp
  have g: "is_global ''Gx''"
    by (simp add: is_global_def)
  have "?t = combine_states s ?body_store"
    using combine_after_enter_global_assign[OF g] by (simp add: enter_state_def)
  show ?thesis
    using cfg_collect_ip_combine[OF comb refl s_at_call body_store]
      combine_after_enter_global_assign[OF g]
    by (simp add: compile_prog_inc_structure(2) enter_state_def)
qed

lemma pruns_to_ip_pcall_global_increment:
  fixes s :: store
  shows "pruns_to_ip inc_pi [''p''] (Call ''p'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?g = "compile_prog inc_pi [''p''] (Call ''p'')"
  have collect_inc: "s(''Gx'' := s ''Gx'' + 1)
    \<in> cfg_collect_ip inc_g (singleton_store s) (cfg_exit inc_g)"
    using pcall_global_increment_cfg_collect_ip by simp
  have exit_eq: "cfg_exit ?g = cfg_exit inc_g"
    by (simp add: compile_prog_inc_exit compile_prog_inc_structure(2))
  have cong_at_exit: "cfg_collect_ip inc_g (singleton_store s) (cfg_exit inc_g)
    = cfg_collect_ip ?g (singleton_store s) (cfg_exit inc_g)"
  proof (rule cfg_collect_ip_cong)
    show "cfg_entry inc_g = cfg_entry ?g"
      using compile_prog_inc_entry compile_prog_inc_structure(1) by simp
    show "edges inc_g = edges ?g"
      using compile_prog_inc_edges compile_prog_inc_structure by simp
    show "combines inc_g = combines ?g"
      using compile_prog_inc_combines compile_prog_inc_structure by simp
  qed
  show ?thesis unfolding pruns_to_ip_def
    using collect_inc cong_at_exit exit_eq by simp
qed

lemma pruns_to_inc_pcall:
  fixes s :: store
  shows "pruns_to inc_pi (Call ''p'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  have p: "inc_pi ''p'' = Some (Assign ''Gx'' (Plus (V ''Gx'') (N 1)))"
    by (simp add: inc_pi_body inc_body_def)
  show ?thesis
    by (simp add: inc_body_def inc_pi_body pcall_global_increment)
qed

end
