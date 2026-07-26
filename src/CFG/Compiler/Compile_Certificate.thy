theory Compile_Certificate
  imports Control_Simulation Compile_Invariants
begin

section \<open>The static compiler certificate for a whole compiled program\<close>

text \<open>The static source contract establishes the runtime return guard for the root activation.\<close>
lemma wf_compile_input_source_wf:
  assumes "wf_compile_input \<Pi> ps mnm main"
  shows "source_wf (main, s, [])"
  using wf_compile_input_source_com[OF assms] wf_compile_input_no_return[OF assms]
  by (rule source_com_no_return_source_wf)

text \<open>
  \<^const>\<open>procs_compiled\<close> is the static compiler-correctness certificate \<^const>\<open>csim\<close> reads: every
  procedure declared in \<open>\<Pi>\<close> has its body-fragment, entry \<open>EA_Nop\<close> wiring and \<open>EA_Ret None\<close> exit
  wiring included in the target graph.  For a whole compiled program this holds by construction:
  the distinguished entry procedure \<open>mnm\<close> (declared in \<open>\<Pi>\<close> with body \<open>main\<close>) is compiled by the
  \<open>compile_proc\<close> arm of \<^const>\<open>compile_prog\<close>, and every callee in \<open>ps\<close> by \<^const>\<open>compile_procs\<close>;
  each fragment is a subset of the corresponding edge/call union.
\<close>

text \<open>Each declared member of a \<^const>\<open>compile_procs\<close> pass contributes its own \<^const>\<open>compile_proc\<close>
  fragment as a subset of the accumulated edge and call sets.\<close>
lemma compile_procs_member_incl:
  assumes "compile_procs \<Pi> ps n = (n', E, K)"
    and "p \<in> set ps" and "\<Pi> p = Some decl"
  shows "\<exists>m m' Ep Kp. compile_proc \<Pi> p decl m = (m', Ep, Kp) \<and> Ep \<subseteq> E \<and> Kp \<subseteq> K"
  using assms
proof (induction ps arbitrary: n n' E K)
  case Nil then show ?case by simp
next
  case (Cons q qs)
  show ?case
  proof (cases "\<Pi> q")
    case None
    with Cons.prems(2,3) have pqs: "p \<in> set qs" by auto
    from None Cons.prems(1) have "compile_procs \<Pi> qs n = (n', E, K)" by simp
    from Cons.IH[OF this pqs Cons.prems(3)] show ?thesis .
  next
    case (Some declq)
    obtain n1 Eq Kq where cq: "compile_proc \<Pi> q declq n = (n1, Eq, Kq)"
      by (metis prod_cases3)
    obtain n2 E' K' where crest: "compile_procs \<Pi> qs n1 = (n2, E', K')"
      by (metis prod_cases3)
    from Cons.prems(1) Some cq crest
    have EK: "E = Eq \<union> E'" "K = Kq \<union> K'" by (simp_all add: Let_def)
    show ?thesis
    proof (cases "p = q")
      case True
      with Cons.prems(3) Some have "decl = declq" by simp
      with cq True have "compile_proc \<Pi> p decl n = (n1, Eq, Kq)" by simp
      moreover have "Eq \<subseteq> E" "Kq \<subseteq> K" using EK by auto
      ultimately show ?thesis by blast
    next
      case False
      with Cons.prems(2) have "p \<in> set qs" by simp
      from Cons.IH[OF crest this Cons.prems(3)] obtain m m' Ep Kp
        where "compile_proc \<Pi> p decl m = (m', Ep, Kp)" "Ep \<subseteq> E'" "Kp \<subseteq> K'" by blast
      moreover have "E' \<subseteq> E" "K' \<subseteq> K" using EK by auto
      ultimately show ?thesis by blast
    qed
  qed
qed

text \<open>A well-formed compiled program satisfies the static \<^const>\<open>procs_compiled\<close> certificate,
  \<^emph>\<open>including\<close> the distinguished entry procedure \<open>mnm\<close>: because \<open>\<Pi> mnm = Some (proc_decl_of [] main)\<close>
  the entry node \<open>FunctionEntry mnm\<close> is an ordinary \<^const>\<open>proc_activation\<close>, so \<open>csim.Base\<close>
  applies to the initial main activation uniformly with every other procedure.\<close>
theorem procs_compiled_compile_prog:
  assumes wf: "wf_compile_input \<Pi> ps mnm main"
  shows "procs_compiled \<Pi> (compile_prog \<Pi> ps mnm main)"
  unfolding procs_compiled_def
proof (intro allI impI)
  fix p decl assume pd: "\<Pi> p = Some decl"
  let ?g = "compile_prog \<Pi> ps mnm main"
  obtain n1 Eprocs Kprocs where procs: "compile_procs \<Pi> ps 0 = (n1, Eprocs, Kprocs)"
    by (metis prod_cases3)
  obtain n2 Emain Kmain
    where mainc: "compile_proc \<Pi> mnm (proc_decl_of [] main) n1 = (n2, Emain, Kmain)"
    by (metis prod_cases3)
  have intra_g: "intra ?g = Eprocs \<union> Emain" and calls_g: "calls ?g = Kprocs \<union> Kmain"
    unfolding compile_prog_def by (simp_all add: procs mainc Let_def)
  from wf have setps: "set ps = {p. \<Pi> p \<noteq> None} - {mnm}"
    unfolding wf_compile_input_def by auto
  have mnmdecl: "\<Pi> mnm = Some (proc_decl_of [] main)"
    by (rule wf_compile_input_main_exists[OF wf])
  have spi: "source_pi \<Pi>" by (rule wf_compile_input_source_pi[OF wf])
  have srccom: "source_com (body decl)" using spi pd unfolding source_pi_def by blast
  have frag: "\<exists>m m' Ef Kf. compile_proc \<Pi> p decl m = (m', Ef, Kf)
                \<and> Ef \<subseteq> intra ?g \<and> Kf \<subseteq> calls ?g"
  proof (cases "p = mnm")
    case True
    with pd mnmdecl have "decl = proc_decl_of [] main" by simp
    with mainc True have "compile_proc \<Pi> p decl n1 = (n2, Emain, Kmain)" by simp
    moreover have "Emain \<subseteq> intra ?g" "Kmain \<subseteq> calls ?g" using intra_g calls_g by auto
    ultimately show ?thesis by blast
  next
    case False
    with pd setps have pin: "p \<in> set ps" by auto
    from compile_procs_member_incl[OF procs pin pd] obtain m m' Ef Kf
      where cp: "compile_proc \<Pi> p decl m = (m', Ef, Kf)"
        and Esub: "Ef \<subseteq> Eprocs" and Ksub: "Kf \<subseteq> Kprocs" by blast
    have "Ef \<subseteq> intra ?g" "Kf \<subseteq> calls ?g" using Esub Ksub intra_g calls_g by auto
    with cp show ?thesis by blast
  qed
  from frag obtain m m' Ef Kf where cp: "compile_proc \<Pi> p decl m = (m', Ef, Kf)"
    and Esub: "Ef \<subseteq> intra ?g" and Ksub: "Kf \<subseteq> calls ?g" by blast
  obtain nn en ex Eb where cb: "compile \<Pi> p (body decl) m = (nn, en, ex, Eb, Kf)"
    and Edef: "Ef = insert (FunctionEntry p, EA_Nop, en)
                     (insert (ex, EA_Ret None p, FunctionResult p) Eb)"
    using cp unfolding compile_proc_def by (auto simp: Let_def split: prod.splits)
  have Ebsub: "Eb \<subseteq> intra ?g" using Edef Esub by auto
  have ent: "(FunctionEntry p, EA_Nop, en) \<in> intra ?g" using Edef Esub by auto
  have ext: "(ex, EA_Ret None p, FunctionResult p) \<in> intra ?g" using Edef Esub by auto
  show "\<exists>n n' en ex E K. compile \<Pi> p (body decl) n = (n', en, ex, E, K)
          \<and> E \<subseteq> intra ?g \<and> K \<subseteq> calls ?g
          \<and> (FunctionEntry p, EA_Nop, en) \<in> intra ?g
          \<and> (ex, EA_Ret None p, FunctionResult p) \<in> intra ?g
          \<and> source_com (body decl)"
    using cb Ebsub Ksub ent ext srccom by blast
qed

end
