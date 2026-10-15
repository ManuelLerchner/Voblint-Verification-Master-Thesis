theory Typed_Semantics
  imports Typed_Com
begin

section \<open>Typed source semantics\<close>

text \<open>
  A typed program runs on typed stores, which hold one value per variable identity. Every
  written value has the kind of the identity it is written to: elaboration already
  converts an assigned value, an actual argument and a returned value, and the semantics
  converts the two values it writes itself, a call result and a library result, to the
  destination's kind. This theory fixes the globals, the result write, the library
  results and the initial stores of that semantics.
\<close>

text \<open>The globals are the \<^const>\<open>GlobalId\<close> identities. A call keeps them and resets
  every other identity, the shared return slot included, as \<^const>\<open>enter_state\<close>
  keeps the declared globals.\<close>

fun tglobal :: "var_id \<Rightarrow> bool" where
  "tglobal (GlobalId _) = True"
| "tglobal _ = False"

text \<open>Writing a call or library result converts it to the destination's kind.\<close>

fun tcombine_assign :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> tstore \<Rightarrow> tstore" where
  "tcombine_assign \<kappa> None _ t = t"
| "tcombine_assign \<kappa> (Some v) n t = t(v := ik_norm (\<kappa> v) n)"

text \<open>A library call yields what \<^const>\<open>special_result\<close> allows, with its arguments
  evaluated by the typed evaluator.\<close>

fun tspecial :: "special_desc \<Rightarrow> texp list \<Rightarrow> tstore \<Rightarrow> int \<Rightarrow> bool" where
  "tspecial SD_Nondet_Int [] t n \<longleftrightarrow> True"
| "tspecial SD_Min [a, b] t n \<longleftrightarrow> n = min (teval a t) (teval b t)"
| "tspecial SD_Max [a, b] t n \<longleftrightarrow> n = max (teval a t) (teval b t)"
| "tspecial _ _ _ _ \<longleftrightarrow> False"

text \<open>A typed program starts with its globals at zero, like \<^const>\<open>cinit_stores\<close>, and
  every other identity holding some value of its kind.\<close>

definition tinit_stores :: "kenv \<Rightarrow> tstore set" where
  "tinit_stores \<kappa> = {t. styped \<kappa> t \<and> (\<forall>x. t (GlobalId x) = 0)}"

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

text \<open>The typed source semantics is the generic one at these parameters.\<close>

global_interpretation typed: vimp_sem teval tglobal ReturnVar "tconv \<kappa>"
  rewrites "vimp_sem.gpstep teval tglobal ReturnVar (tconv \<kappa>) = tpstep \<kappa>"
  for \<kappa> :: kenv
  by (simp add: tpstep_def)

subsection \<open>A declaration without an initializer\<close>

text \<open>
  The frontend writes a local's declaration without an initializer as the library call
  \<open>x = __voblint_nondet_int()\<close> at the declaration's position, so it runs on every
  activation and every loop iteration that reaches it. That call may leave any value of
  \<open>x\<close>'s kind in \<open>x\<close> and changes nothing else. Its outcomes do not depend on what \<open>x\<close> held
  before: the \<open>0\<close> a call entry wrote, or the value of an earlier iteration or activation.
  That the frontend places every use of a local after its declaration is trusted.
\<close>

lemma tpstep_declare:
  assumes "\<Pi> special_pname_nondet_int = None"
  shows "tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) (c', s', frs')
           \<longleftrightarrow> c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
proof
  assume "tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) (c', s', frs')"
  then show "c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
    using assms by (auto elim!: typed.CallSE simp: special_table_def)
next
  assume "c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
  then obtain n where n: "n \<in> ik_range (\<kappa> x)" and eq: "c' = SKIP i" "frs' = frs" "s' = s(x := n)"
    by blast
  have "tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs)
          (SKIP i, s(x := tconv \<kappa> (Some x) n), frs)"
    by (rule typed.Special[where desc = SD_Nondet_Int and sc = "Nondet_Int :: texp gspecial_call"])
       (simp_all add: special_table_def)
  with n eq show "tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) (c', s', frs')"
    by (simp del: ik_range_iff)
qed

corollary tpstep_declare_forgets:
  assumes "\<Pi> special_pname_nondet_int = None"
  shows "tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s(x := m), frs) cfg
           \<longleftrightarrow> tpstep \<kappa> \<Pi> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) cfg"
  by (cases cfg) (simp add: tpstep_declare[where \<Pi> = \<Pi>, OF assms])

section \<open>The typed program\<close>

text \<open>A procedure's typed formals are the identities its formals resolve to, and its typed
  body is its elaboration.\<close>

definition typed_ptable :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> (unit, var_id, texp) gptable" where
  "typed_ptable p ds q =
     map_option (\<lambda>d. \<lparr>formals = map (resolve_var (declared_global p) q) (formals d),
                      body = elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)\<rparr>)
       (prog_table p q)"

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

end
