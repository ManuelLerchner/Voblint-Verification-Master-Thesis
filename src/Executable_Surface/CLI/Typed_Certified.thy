theory Typed_Certified
  imports Analysis_Certified "Voblint_Typed.Typed_Semantics"
begin

section \<open>What a report guarantees about a typed program\<close>

text \<open>
  A typed program is analyzed as its lowering, \<^term>\<open>typed_prog p ds\<close>, and
  \<open>run_voblint_source_sound\<close> speaks about runs of that lowering. The theorem below
  speaks about runs of the typed semantics \<^const>\<open>tstep\<close> instead. Every typed run is
  matched by a run of the lowering that ends in the lowered command, a store related
  to the typed store by \<^const>\<open>srel\<close>, and a node the report describes. In the running
  activation, every variable's typed value is its lowered value converted to the
  variable's kind, so a well-typed expression of that activation has the same value on
  both sides (\<open>teval_lower_scoped\<close>). The guarantee is about the lowered store: the
  theorem does not place the typed store in a typed collecting semantics, and a verdict
  is read over the lowered store, which \<open>teval_lower_scoped\<close> relates to the typed one
  for each well-typed expression of the running activation.
\<close>

theorem run_voblint_typed_sound:
  fixes p :: imp_prog and ds :: kind_decls
  defines G_def: "\<G> \<equiv> declared_global p"
      and k_def: "\<kappa> \<equiv> kenv_of ds"
      and P_def: "P \<equiv> typed_prog p ds"
  assumes t0: "t0 \<in> tinit_stores \<kappa>"
      and run: "\<kappa>, typed_table p ds \<turnstile> (typed_main p ds, t0, []) \<rightarrow>\<^sub>t\<^sup>* (c, t, tfs)"
      and ans: "run_voblint config P = Analysed res"
  shows "\<exists>s0 s fs. s0 \<in> cinit_stores \<G>
       \<and> \<G>, prog_table P \<turnstile> (main_body (prog_table P), s0, []) \<rightarrow>\<^sub>p\<^sup>* (lower_com c, s, fs)
       \<and> srel \<kappa> \<G> (cur_proc tfs) t s
       \<and> (\<exists>v. P, s0 \<turnstile> (lower_com c, s, fs) \<rhd> v)
       \<and> (\<forall>v. P, s0 \<turnstile> (lower_com c, s, fs) \<rhd> v \<longrightarrow>
                s \<in> \<C>\<^bsub>\<G>,prog_cfg P,cinit_stores \<G>\<^esub> v
              \<and> s \<in> \<R>\<^bsub>res\<^esub> v
              \<and> s \<in> \<V>\<^bsub>res\<^esub> v)"
proof -
  have GP: "declared_global P = \<G>" by (simp add: P_def G_def)
  from run_voblint_wf [OF ans] have "wf_source_program \<G> (prog_table P)"
    by (simp add: gwf_compile_input_def GP [symmetric])
  then have wf: "wf_source_program (declared_global p) (prog_table (typed_prog p ds))"
    by (simp add: P_def G_def)
  have nr: "\<not> \<G> ret_var"
    using wf_source_programD(1) [OF wf] by (simp add: greserved_ret_var_def G_def)
  have tab: "tab_rel \<kappa> \<G> (typed_table p ds) (prog_table P)"
    unfolding k_def G_def P_def by (rule tab_rel_typed_table [OF wf])
  note main = typed_main_table [OF wf]
  define s0 where "s0 = lowered_store \<G> prog_main_name t0"
  have s0: "s0 \<in> cinit_stores \<G>"
      and sim0: "sim \<kappa> \<G> (typed_table p ds) (typed_main p ds, t0, [])
                   (lower_com (typed_main p ds), s0, [])"
    unfolding s0_def by (rule tinit_sim [OF t0 nr main(1) tab])+
  from tsteps_sim [OF tab nr run sim0]
  obtain s fs where lrun: "\<G>, prog_table P \<turnstile> (lower_com (typed_main p ds), s0, [])
                              \<rightarrow>\<^sub>p\<^sup>* (lower_com c, s, fs)"
      and simc: "sim \<kappa> \<G> (typed_table p ds) (c, t, tfs) (lower_com c, s, fs)"
    by blast
  have lrun': "\<G>, prog_table P \<turnstile> (main_body (prog_table P), s0, []) \<rightarrow>\<^sub>p\<^sup>* (lower_com c, s, fs)"
    using lrun main(2) by (simp add: P_def)
  from simc have sr: "srel \<kappa> \<G> (cur_proc tfs) t s" by (simp add: sim_def)
  from run_voblint_source_sound [OF s0 [folded GP] lrun' [folded GP] ans]
  show ?thesis using s0 lrun' sr unfolding GP by blast
qed

end
