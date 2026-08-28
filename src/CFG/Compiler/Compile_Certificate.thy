theory Compile_Certificate
  imports Control_Simulation Control_Simulation_Forward Compile_Invariants
begin

section \<open>The static compiler certificate for a whole compiled program\<close>

text \<open>The static source contract establishes the runtime return guard for the root activation.\<close>
lemma wf_compile_input_source_wf:
  assumes "wf_compile_input source_global \<Pi> ps mnm main"
  shows "source_wf (main, s, [])"
  using wf_compile_inputD(8)[OF assms] wf_compile_inputD(4)[OF assms]
  by (rule source_com_no_return_source_wf)

text \<open>
  \<^const>\<open>procs_compiled\<close> is the static certificate \<^const>\<open>csim\<close> reads: every procedure declared
  in \<open>\<Pi>\<close> has its body fragment, entry \<open>EA_Nop\<close> wiring and \<open>EA_Ret None\<close> exit wiring in the
  target graph.  It covers the entry procedure \<open>mnm\<close> too, since
  \<open>\<Pi> mnm = Some \<lparr>formals = [], body = main\<rparr>\<close> makes \<open>FunctionEntry mnm\<close> an ordinary
  \<^const>\<open>proc_activation\<close>.
\<close>
theorem procs_compiled_compile_prog:
  assumes wf: "wf_compile_input source_global \<Pi> ps mnm main"
  shows "procs_compiled \<Pi> (compile_prog \<Pi> ps mnm main)"
  unfolding procs_compiled_def
proof (intro allI impI)
  fix p decl assume pd: "\<Pi> p = Some decl"
  let ?g = "compile_prog \<Pi> ps mnm main"
  obtain n1 Eprocs Kprocs n2 Emain Kmain where
      procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    and mainc: "compile_proc \<Pi> mnm \<lparr>formals = [], body = main\<rparr> n1 = (n2, Emain, Kmain)"
    and intra_g: "intra ?g = Eprocs \<union> Emain" and calls_g: "calls ?g = Kprocs \<union> Kmain"
    by (rule compile_prog_intra_split)
  have srccom: "source_com (body decl)"
    using wf_compile_inputD(7)[OF wf] pd unfolding source_pi_def by blast
  have "\<exists>m m' Ef Kf. compile_proc \<Pi> p decl m = (m', Ef, Kf)
          \<and> Ef \<subseteq> intra ?g \<and> Kf \<subseteq> calls ?g"
  proof (cases "p = mnm")
    case True
    with pd wf_compile_inputD(2)[OF wf] have "decl = \<lparr>formals = [], body = main\<rparr>" by simp
    then show ?thesis using mainc True intra_g calls_g by blast
  next
    case False
    with pd wf_compile_inputD(10)[OF wf] have "p \<in> set ps" by auto
    from compile_procs_member[OF procs this pd] show ?thesis using intra_g calls_g le_supI1 by metis
  qed
  then obtain m m' Ef Kf where cp: "compile_proc \<Pi> p decl m = (m', Ef, Kf)"
    and Esub: "Ef \<subseteq> intra ?g" and Ksub: "Kf \<subseteq> calls ?g" by blast
  from cp obtain Eb where
    cb: "compile \<Pi> p (body decl) (Statement (m + csize (body decl))) m
           = (m + csize (body decl), Statement m, Eb, Kf)"
    and Edef: "Ef = insert (FunctionEntry p, EA_Nop, Statement m)
                 (if falls_through (body decl)
                  then insert (Statement (m + csize (body decl)), EA_Ret None p, FunctionResult p)
                         Eb
                  else Eb)"
    by (rule compile_procE)
  have Ebsub: "Eb \<subseteq> intra ?g" using Edef Esub by (auto split: if_splits)
  have ent: "(FunctionEntry p, EA_Nop, Statement m) \<in> intra ?g" using Edef Esub by auto
  have ext: "falls_through (body decl) \<longrightarrow>
               (Statement (m + csize (body decl)), EA_Ret None p, FunctionResult p) \<in> intra ?g"
    using Edef Esub by auto
  show "\<exists>k n n' en E K. compile \<Pi> p (body decl) k n = (n', en, E, K)
          \<and> E \<subseteq> intra ?g \<and> K \<subseteq> calls ?g
          \<and> (FunctionEntry p, EA_Nop, en) \<in> intra ?g
          \<and> (falls_through (body decl) \<longrightarrow>
               (k, EA_Ret None p, FunctionResult p) \<in> intra ?g)
          \<and> source_com (body decl) \<and> special_table p = None"
    using cb Ebsub Ksub ent ext srccom wf_compile_inputD(6)[OF wf pd] by blast
qed

end
