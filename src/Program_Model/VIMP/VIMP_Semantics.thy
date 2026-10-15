theory VIMP_Semantics
  imports Core_Com
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

fun is_global :: "var_id \<Rightarrow> bool" where
  "is_global (GlobalId _) = True"
| "is_global _ = False"

text \<open>Writing a call or library result converts it to the destination's kind.\<close>

fun combine_assign_conv :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> store \<Rightarrow> store" where
  "combine_assign_conv \<kappa> None _ t = t"
| "combine_assign_conv \<kappa> (Some v) n t = t(v := ik_norm (\<kappa> v) n)"

text \<open>A library call yields what \<^const>\<open>special_result\<close> allows, with its arguments
  evaluated by the typed evaluator.\<close>

fun special_desc_result :: "special_desc \<Rightarrow> exp list \<Rightarrow> store \<Rightarrow> int \<Rightarrow> bool" where
  "special_desc_result SD_Nondet_Int [] t n \<longleftrightarrow> True"
| "special_desc_result SD_Min [a, b] t n \<longleftrightarrow> n = min (eval a t) (eval b t)"
| "special_desc_result SD_Max [a, b] t n \<longleftrightarrow> n = max (eval a t) (eval b t)"
| "special_desc_result _ _ _ _ \<longleftrightarrow> False"

text \<open>A typed program starts with its globals at zero, like \<^const>\<open>cinit_stores\<close>, and
  every other identity holding some value of its kind.\<close>

definition init_stores :: "kenv \<Rightarrow> store set" where
  "init_stores \<kappa> = {t. all_in_kinds \<kappa> t \<and> (\<forall>x. t (GlobalId x) = 0)}"

section \<open>The typed language instance\<close>

text \<open>
  The generic semantic core is parametric in the evaluator, the globals, the return slot
  and the conversion applied when a value is written. The typed language instantiates it
  with \<^const>\<open>eval\<close>, the \<^const>\<open>GlobalId\<close> identities, the shared slot
  \<^const>\<open>ReturnVar\<close>, and conversion to the destination's kind, as C converts on
  assignment. A variable read carries no conversion: an identity holds a value of its own
  kind, since every write converts.
\<close>

definition kind_conv :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> int" where
  "kind_conv \<kappa> dst n = (case dst of None \<Rightarrow> n | Some v \<Rightarrow> ik_norm (\<kappa> v) n)"

lemma kind_conv_simps [simp]:
  "kind_conv \<kappa> None n = n"
  "kind_conv \<kappa> (Some v) n = ik_norm (\<kappa> v) n"
  by (simp_all add: kind_conv_def)

definition pstep :: "kenv \<Rightarrow> ('a, var_id, exp) gptable
    \<Rightarrow> ('a, var_id, exp) gcom \<times> store \<times> var_id gframe list
    \<Rightarrow> ('a, var_id, exp) gcom \<times> store \<times> var_id gframe list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50) where
  "pstep \<kappa> = vimp_sem.gpstep eval is_global ReturnVar (kind_conv \<kappa>)"

abbreviation psteps :: "kenv \<Rightarrow> ('a, var_id, exp) gptable
    \<Rightarrow> ('a, var_id, exp) gcom \<times> store \<times> var_id gframe list
    \<Rightarrow> ('a, var_id, exp) gcom \<times> store \<times> var_id gframe list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p\<^sup>*/ _)" [51, 51, 51, 51] 50) where
  "psteps \<kappa> \<Pi> x y \<equiv> star (pstep \<kappa> \<Pi>) x y"

text \<open>The typed source semantics is the generic one at these parameters.\<close>

global_interpretation vimp: vimp_sem eval is_global ReturnVar "kind_conv \<kappa>"
  rewrites "vimp_sem.gpstep eval is_global ReturnVar (kind_conv \<kappa>) = pstep \<kappa>"
  for \<kappa> :: kenv
  by (simp add: pstep_def)

subsection \<open>A declaration without an initializer\<close>

text \<open>
  The frontend writes a local's declaration without an initializer as the library call
  \<open>x = __voblint_nondet_int()\<close> at the declaration's position, so it runs on every
  activation and every loop iteration that reaches it. That call may leave any value of
  \<open>x\<close>'s kind in \<open>x\<close> and changes nothing else. Its outcomes do not depend on what \<open>x\<close> held
  before: the \<open>0\<close> a call entry wrote, or the value of an earlier iteration or activation.
  That the frontend places every use of a local after its declaration is trusted.
\<close>

lemma pstep_declare:
  assumes "\<Pi> special_pname_nondet_int = None"
  shows "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (c', s', frs')
           \<longleftrightarrow> c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
proof
  assume "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (c', s', frs')"
  then show "c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
    using assms by (auto elim!: vimp.CallSE simp: special_table_def)
next
  assume "c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
  then obtain n where n: "n \<in> ik_range (\<kappa> x)" and eq: "c' = SKIP i" "frs' = frs" "s' = s(x := n)"
    by blast
  have "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) n), frs)"
    by (rule vimp.Special[where desc = SD_Nondet_Int and sc = "Nondet_Int :: exp gspecial_call"])
       (simp_all add: special_table_def)
  with n eq
  show "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (c', s', frs')"
    by (simp del: ik_range_iff)
qed

corollary pstep_declare_forgets:
  assumes "\<Pi> special_pname_nondet_int = None"
  shows "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s(x := m), frs) \<rightarrow>\<^sub>p cfg
           \<longleftrightarrow> \<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p cfg"
  by (cases cfg) (simp add: pstep_declare[where \<Pi> = \<Pi>, OF assms])

section \<open>The typed program\<close>

text \<open>A procedure's typed formals are the identities its formals resolve to, and its typed
  body is its elaboration.\<close>

definition elab_ptable :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> (unit, var_id, exp) gptable" where
  "elab_ptable p ds q =
     map_option (\<lambda>d. \<lparr>formals = map (resolve_var (declared_global p) q) (formals d),
                      body = elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)\<rparr>)
       (prog_table p q)"

lemma elab_ptable_None_iff [simp]: "elab_ptable p ds q = None \<longleftrightarrow> prog_table p q = None"
  by (simp add: elab_ptable_def)

subsection \<open>Elaboration keeps the control structure\<close>

text \<open>Elaboration rewrites expressions only, so every predicate on a command's control
  structure is the same before and after it.\<close>

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

text \<open>Elaborated expressions never mention the return slot, so a well-formed source
  program elaborates to a well-formed typed program.\<close>

lemma ReturnVar_notin_range_resolve_var [simp]: "ReturnVar \<notin> range (resolve_var \<G> q)"
  by (auto simp: resolve_var_def)

lemma ReturnVar_notin_elaborate [simp]:
  "ReturnVar \<notin> exp_vars (elaborate (resolve_var \<G> q) \<kappa> ik e)"
  using exp_vars_elaborate [of "resolve_var \<G> q" \<kappa> ik e]
    ReturnVar_notin_range_resolve_var [of \<G> q] by blast

lemma gsource_exp_elaborate [simp]:
  "gsource_exp exp_vars ReturnVar (elaborate (resolve_var \<G> q) \<kappa> ik e)"
  "gsource_exp exp_vars ReturnVar (elaborate_syn (resolve_var \<G> q) \<kappa> e)"
  by (simp_all add: gsource_exp_def elaborate_syn_def)

lemma gsource_exp_elab_args:
  "list_all (gsource_exp exp_vars ReturnVar) (elab_args (resolve_var \<G> q) \<kappa> fs es)"
  unfolding list_all_iff gsource_exp_def
  using exp_vars_elab_args ReturnVar_notin_range_resolve_var by blast

lemma gwf_source_com_elab_com:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
    and c: "wf_source_com (prog_table p) c"
  shows "gwf_source_com exp_vars ReturnVar (elab_ptable p ds)
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
      by (auto simp: elab_ptable_def prog_formals_def gsource_exp_elab_args
               split: option.splits)
  qed
qed (auto split: option.splits)

lemma elab_ptable_main:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
  shows "elab_ptable p ds prog_main_name
           = Some \<lparr>formals = [], body = main_body (elab_ptable p ds)\<rparr>"
    and "main_body (elab_ptable p ds)
           = elab_com (declared_global p) (prog_formals p) (kenv_of ds) prog_main_name
               (main_body (prog_table p))"
proof -
  from wf have "prog_table p prog_main_name = Some \<lparr>formals = [], body = main_body (prog_table p)\<rparr>"
    by (simp add: gwf_source_program_def)
  then have t: "elab_ptable p ds prog_main_name
      = Some \<lparr>formals = [], body = elab_com (declared_global p) (prog_formals p) (kenv_of ds)
                                      prog_main_name (main_body (prog_table p))\<rparr>"
    by (simp add: elab_ptable_def)
  then show "main_body (elab_ptable p ds)
      = elab_com (declared_global p) (prog_formals p) (kenv_of ds) prog_main_name
          (main_body (prog_table p))"
    by (simp add: main_body_def)
  with t show "elab_ptable p ds prog_main_name
      = Some \<lparr>formals = [], body = main_body (elab_ptable p ds)\<rparr>"
    by simp
qed

lemma gwf_proc_decl_elab:
  assumes wf: "wf_source_program (declared_global p) (prog_table p)"
    and d: "prog_table p q = Some d"
  shows "gwf_proc_decl exp_vars ReturnVar is_global (elab_ptable p ds)
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
  moreover have "list_all (gvalid_formal ReturnVar is_global)
                   (map (resolve_var (declared_global p) q) (formals d))"
    using local by (auto simp: list_all_iff gvalid_formal_def resolve_var_def)
  moreover have "gwf_source_com exp_vars ReturnVar (elab_ptable p ds)
                   (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d))"
    using pd by (intro gwf_source_com_elab_com [OF wf]) (simp add: gwf_proc_decl_def)
  ultimately show ?thesis by (simp add: gwf_proc_decl_def)
qed

end
