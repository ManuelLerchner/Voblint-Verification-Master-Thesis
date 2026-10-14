theory Typed_CFG
  imports "Voblint_Compile.Source_To_Trace" "Voblint_Typed.Typed_Semantics"
begin

section \<open>The typed language instance\<close>

text \<open>
  The generic semantic core is parametric in the evaluator, the globals, the return slot
  and the conversion applied when a value is written. The typed language instantiates it
  with \<^const>\<open>teval\<close>, the \<^const>\<open>GlobalId\<close> identities, the shared slot
  \<^const>\<open>ReturnVar\<close>, and conversion to the destination's kind, as C converts on
  assignment. A variable read carries no conversion: an identity holds a value of its own
  kind, since every write converts.
\<close>

definition tconv :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> int" where
  "tconv \<kappa> dst n = (case dst of None \<Rightarrow> n | Some v \<Rightarrow> ik_norm (\<kappa> v) n)"

lemma tconv_simps [simp]:
  "tconv \<kappa> None n = n"
  "tconv \<kappa> (Some v) n = ik_norm (\<kappa> v) n"
  by (simp_all add: tconv_def)

definition tpstep :: "kenv \<Rightarrow> ('a, var_id, texp) gptable
    \<Rightarrow> ('a, var_id, texp) gcom \<times> tstore \<times> var_id gframe list
    \<Rightarrow> ('a, var_id, texp) gcom \<times> tstore \<times> var_id gframe list \<Rightarrow> bool" where
  "tpstep \<kappa> = vimp_sem.gpstep teval tglobal ReturnVar (tconv \<kappa>)"

definition tcstep :: "kenv \<Rightarrow> (var_id, texp) gcfg
    \<Rightarrow> var_id gcconf \<Rightarrow> var_id gcconf \<Rightarrow> bool" where
  "tcstep \<kappa> = cfg_exec_sem.gcstep teval ReturnVar (tconv \<kappa>) tglobal"

text \<open>The stores valid activation traces of the typed graph reach at a node.\<close>

definition tnode_collect :: "kenv \<Rightarrow> (var_id, texp) gcfg \<Rightarrow> tstore set \<Rightarrow> cfg_node \<Rightarrow> tstore set" where
  "tnode_collect \<kappa> = collect_sem.gnode_collect teval ReturnVar (tconv \<kappa>) tglobal"

global_interpretation typed: bridge_sem teval tglobal ReturnVar "tconv \<kappa>"
  rewrites "vimp_sem.gpstep teval tglobal ReturnVar (tconv \<kappa>) = tpstep \<kappa>"
    and "cfg_exec_sem.gcstep teval ReturnVar (tconv \<kappa>) tglobal = tcstep \<kappa>"
    and "collect_sem.gnode_collect teval ReturnVar (tconv \<kappa>) tglobal = tnode_collect \<kappa>"
  for \<kappa> :: kenv
  by (simp_all add: tpstep_def tcstep_def tnode_collect_def)

section \<open>The typed program and its graph\<close>

text \<open>A procedure's typed formals are the identities its formals resolve to, and its typed
  body is its elaboration. The typed graph compiles these procedures directly; no
  expression on it is lowered back to source names.\<close>

definition typed_ptable :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> (unit, var_id, texp) gptable" where
  "typed_ptable p ds q =
     map_option (\<lambda>d. \<lparr>formals = map (resolve_var (declared_global p) q) (formals d),
                      body = elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)\<rparr>)
       (prog_table p q)"

definition typed_cfg :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> (var_id, texp) gcfg" where
  "typed_cfg p ds = compile_prog (typed_ptable p ds) (prog_procs p)"

lemma typed_ptable_None_iff [simp]: "typed_ptable p ds q = None \<longleftrightarrow> prog_table p q = None"
  by (simp add: typed_ptable_def)

subsection \<open>Elaboration keeps the control structure\<close>

lemma elab_com_control [simp]:
  "source_com (elab_com \<G> fm \<kappa> q c) = source_com c"
  "may_fallthrough (elab_com \<G> fm \<kappa> q c) = may_fallthrough c"
  "may_return_none (elab_com \<G> fm \<kappa> q c) = may_return_none c"
  "may_return_value (elab_com \<G> fm \<kappa> q c) = may_return_value c"
  "no_return (elab_com \<G> fm \<kappa> q c) = no_return c"
  by (induction c) auto

lemma value_providing_elab_com [simp]:
  "value_providing (elab_com \<G> fm \<kappa> q c) = value_providing c"
  by (simp add: value_providing_def)

lemma classify_special_map_None_iff [simp]:
  "classify_special d (map f xs) = None \<longleftrightarrow> classify_special d xs = None"
  by (cases "(d, xs)" rule: classify_special.cases) auto

subsection \<open>Well-formedness carries over\<close>

lemma ReturnVar_notin_range_resolve_var [simp]: "ReturnVar \<notin> range (resolve_var \<G> q)"
  by (auto simp: resolve_var_def)

lemma ReturnVar_notin_elaborate [simp]:
  "ReturnVar \<notin> tvars (elaborate (resolve_var \<G> q) \<kappa> ik e)"
  using tvars_elaborate [of "resolve_var \<G> q" \<kappa> ik e]
    ReturnVar_notin_range_resolve_var [of \<G> q] by blast

lemma gsource_exp_elaborate [simp]:
  "gsource_exp tvars ReturnVar (elaborate (resolve_var \<G> q) \<kappa> ik e)"
  "gsource_exp tvars ReturnVar (elaborate_syn (resolve_var \<G> q) \<kappa> e)"
  by (simp_all add: gsource_exp_def elaborate_syn_def)

lemma gsource_exp_elab_args:
  "list_all (gsource_exp tvars ReturnVar) (elab_args (resolve_var \<G> q) \<kappa> fs es)"
  unfolding list_all_iff gsource_exp_def
  using tvars_elab_args ReturnVar_notin_range_resolve_var by blast

lemma gwf_source_com_elab_com:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
    and c: "wf_source_com (prog_table p) c"
  shows "gwf_source_com tvars ReturnVar (typed_ptable p ds)
           (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q c)"
  using c
proof (induction c)
  case (Call i dst r es)
  show ?case
  proof (cases "special_table r")
    case (Some desc)
    with wf have "prog_table p r = None"
      by (auto simp: gwf_source_program_def)
    then have "prog_formals p r = []" by (simp add: prog_formals_def)
    with Call Some show ?thesis
      by (auto simp: list_all_iff split: option.splits)
  next
    case None
    with Call show ?thesis
      by (auto simp: typed_ptable_def prog_formals_def gsource_exp_elab_args
               split: option.splits)
  qed
qed (auto split: option.splits)

lemma typed_ptable_main:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
  shows "typed_ptable p ds prog_main_name
           = Some \<lparr>formals = [], body = main_body (typed_ptable p ds)\<rparr>"
    and "main_body (typed_ptable p ds)
           = elab_com (declared_global p) (prog_formals p) (kenv_of ds) prog_main_name
               (main_body (prog_table p))"
proof -
  from wf have "prog_table p prog_main_name = Some \<lparr>formals = [], body = main_body (prog_table p)\<rparr>"
    by (simp add: gwf_source_program_def)
  then have t: "typed_ptable p ds prog_main_name
      = Some \<lparr>formals = [], body = elab_com (declared_global p) (prog_formals p) (kenv_of ds)
                                      prog_main_name (main_body (prog_table p))\<rparr>"
    by (simp add: typed_ptable_def)
  then show "main_body (typed_ptable p ds)
      = elab_com (declared_global p) (prog_formals p) (kenv_of ds) prog_main_name
          (main_body (prog_table p))"
    by (simp add: main_body_def)
  with t show "typed_ptable p ds prog_main_name
      = Some \<lparr>formals = [], body = main_body (typed_ptable p ds)\<rparr>"
    by simp
qed

lemma gwf_proc_decl_typed:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
    and d: "prog_table p q = Some d"
  shows "gwf_proc_decl tvars ReturnVar tglobal (typed_ptable p ds)
           \<lparr>formals = map (resolve_var (declared_global p) q) (formals d),
            body = elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)\<rparr>"
proof -
  from wf d have pd: "wf_proc_decl (declared_global p) (prog_table p) d"
    by (simp add: gwf_source_program_def)
  then have local: "\<forall>x \<in> set (formals d). \<not> declared_global p x"
    by (auto simp: gwf_proc_decl_def gvalid_formal_def list_all_iff)
  then have "inj_on (resolve_var (declared_global p) q) (set (formals d))"
    by (auto simp: inj_on_def resolve_var_eq_iff)
  with pd have "distinct (map (resolve_var (declared_global p) q) (formals d))"
    by (simp add: gwf_proc_decl_def distinct_map)
  moreover have "list_all (gvalid_formal ReturnVar tglobal)
                   (map (resolve_var (declared_global p) q) (formals d))"
    using local by (auto simp: list_all_iff gvalid_formal_def resolve_var_def)
  moreover have "gwf_source_com tvars ReturnVar (typed_ptable p ds)
                   (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d))"
    using pd by (intro gwf_source_com_elab_com [OF wf]) (simp add: gwf_proc_decl_def)
  ultimately show ?thesis by (simp add: gwf_proc_decl_def)
qed

text \<open>The typed program is a well-formed compiler input whenever the source program is:
  elaboration resolves every name to an identity distinct from the return slot, and keeps
  the control structure the contract inspects.\<close>

theorem typed_wf_compile_input:
  assumes wf: "wf_compile_input (declared_global p) (prog_table p) ps"
  shows "gwf_compile_input tvars ReturnVar tglobal (typed_ptable p ds) ps"
proof -
  from wf have src: "wf_source_program (declared_global p) (prog_table p)"
    by (simp add: gwf_compile_input_def)
  note main = typed_ptable_main [OF src, of ds]
  have "gwf_source_com tvars ReturnVar (typed_ptable p ds) (main_body (typed_ptable p ds))"
    using src by (simp add: main(2) gwf_source_com_elab_com gwf_source_program_def)
  moreover have "no_return (main_body (typed_ptable p ds))"
    using src by (simp add: main(2) gwf_source_program_def)
  moreover have "gwf_proc_decl tvars ReturnVar tglobal (typed_ptable p ds) decl"
    if "typed_ptable p ds q = Some decl" for q decl
    using that gwf_proc_decl_typed [OF src] by (auto simp: typed_ptable_def)
  moreover have "special_table q = None" if "typed_ptable p ds q \<noteq> None" for q
    using that src by (simp add: gwf_source_program_def)
  ultimately show ?thesis
    using wf main(1)
    by (simp add: gwf_compile_input_def gwf_source_program_def greserved_ret_var_def)
qed

section \<open>Typed runs reach the typed graph\<close>

text \<open>Every run of the typed program is simulated on the typed graph, and its store is
  the sink of a valid activation trace there. Both are the generic bridge at the typed
  instance; nothing about kinds enters the simulation proof.\<close>

theorem typed_source_run_has_activation_trace:
  assumes wf: "wf_program_compile_input p"
    and s0: "s0 \<in> S"
    and run: "star (tpstep \<kappa> (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk t. typed_ptable p ds, typed_cfg p ds, prog_main_name
                      \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                   \<and> typed.gactivation_trace_repr \<kappa> (typed_cfg p ds) S (v, s, stk) t"
  unfolding typed_cfg_def
  by (rule typed.source_run_has_activation_trace [OF typed_wf_compile_input [OF wf] s0 run])

text \<open>Hence every store a typed run reaches lies in the typed collecting semantics at the
  node simulating it. This is the inclusion a sound typed analysis result bounds.\<close>

theorem typed_source_reaches_node_collect:
  assumes wf: "wf_program_compile_input p"
    and s0: "s0 \<in> S"
    and run: "star (tpstep \<kappa> (typed_ptable p ds))
                (main_body (typed_ptable p ds), s0, []) (residual, s, frs)"
  shows "\<exists>v stk. typed_ptable p ds, typed_cfg p ds, prog_main_name
                    \<turnstile> (residual, s, frs) \<approx> (v, s, stk)
                 \<and> s \<in> tnode_collect \<kappa> (typed_cfg p ds) S v"
proof -
  from typed_source_run_has_activation_trace [OF wf s0 run] obtain v stk t
    where sim: "typed_ptable p ds, typed_cfg p ds, prog_main_name \<turnstile> (residual, s, frs) \<approx> (v, s, stk)"
      and rep: "typed.gactivation_trace_repr \<kappa> (typed_cfg p ds) S (v, s, stk) t"
    by blast
  from rep have "s \<in> tnode_collect \<kappa> (typed_cfg p ds) S v"
    by (auto simp: typed.gactivation_trace_repr_def typed.gnode_collect_def)
  with sim show ?thesis by blast
qed

end
