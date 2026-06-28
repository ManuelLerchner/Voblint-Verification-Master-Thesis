theory CFG_Collect_Runs
  imports CFG_Collect "Voblint_IMP2.IMP2_Proc"
begin

section \<open>Run-to-exit projection for cfg_collect\<close>

text \<open>
  Exit projection for interprocedural programs.  The predicate relates a
  source-level procedure table, procedure list, command, and initial store to
  the stores collected at the compiled CFG exit.
\<close>


definition singleton_store :: "store \<Rightarrow> store set" where
  "singleton_store s = {s}"

definition cfg_runs_to ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "cfg_runs_to \<Pi> ps c s t =
     (let g = compile_prog \<Pi> ps c in t \<in> cfg_collect g (singleton_store s) (cfg_exit g))"

lemma cfg_runs_toD[elim]:
  "cfg_runs_to \<Pi> ps c s t
   \<Longrightarrow> t \<in> cfg_collect (compile_prog \<Pi> ps c) (singleton_store s)
                  (cfg_exit (compile_prog \<Pi> ps c))"
  unfolding cfg_runs_to_def by (auto simp: Let_def)

lemma cfg_collect_lfp_lowerbound:
  assumes le: "cfg_collect_F g S env \<le> env"
  shows "cfg_collect g S \<le> env"
  unfolding cfg_collect_def
  using le lfp_lowerbound by blast

lemma cfg_collect_collect_pp:
  "collect_pp g (cfg_collect g S) v \<subseteq> cfg_collect g S v"
proof
  fix x
  assume xin: "x \<in> collect_pp g (cfg_collect g S) v"
  have step: "x \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def using xin by auto
  show "x \<in> cfg_collect g S v" using step cfg_collect_post by blast
qed

lemma cfg_collect_edge:
  assumes e: "(u, a, v) \<in> edges g"
      and xin: "x \<in> edge_collect a (cfg_collect g S u)"
  shows "x \<in> cfg_collect g S v"
proof -
  have "x \<in> collect_pp g (cfg_collect g S) v"
    unfolding collect_pp_def using e xin by blast
  thus ?thesis using cfg_collect_collect_pp by blast
qed

lemma cfg_collect_combine:
  assumes h: "(c, ex, ret) \<in> combines g" and ret: "ret = v"
      and sc: "s \<in> cfg_collect g S c" and te: "t \<in> cfg_collect g S ex"
  shows "<s|t> \<in> cfg_collect g S v"
proof -
  have mem: "<s|t> \<in> collect_combine_pp g (cfg_collect g S) v"
    using collect_combine_pp_member[OF h ret sc te] .
  have step: "<s|t> \<in> cfg_collect_F g S (cfg_collect g S) v"
    unfolding cfg_collect_F_def using mem by auto
  show ?thesis using step cfg_collect_post by blast
qed

end
