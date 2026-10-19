theory VIMP_Semantics
  imports Core_Com
begin

section \<open>Typed source semantics\<close>

text \<open>
  A typed program runs on typed stores, which hold one value per variable identity. Every
  written value has the kind of the identity it is written to: elaboration already
  converts an assigned value, an actual argument and a returned value, and the semantics
  converts the two values it writes itself, a call result and a library result, to the
  destination's kind. This theory fixes the globals and the initial stores of that
  semantics and defines it.
\<close>

text \<open>The globals are the \<^const>\<open>GlobalId\<close> identities. A call keeps them and resets
  every other identity, the shared return slot included, as \<^const>\<open>enter_state\<close>
  keeps the declared globals.\<close>

fun is_global :: "var_id \<Rightarrow> bool" where
  "is_global (GlobalId _) = True"
| "is_global _ = False"

text \<open>A program starts with its globals at zero and every other identity holding some
  value of its kind.\<close>

definition init_stores :: "kenv \<Rightarrow> store set" where
  "init_stores \<kappa> = {t. all_in_kinds \<kappa> t \<and> (\<forall>x. t (GlobalId x) = 0)}"

section \<open>Frame-stack small-step semantics\<close>

text \<open>
  A written value is converted to the kind of its destination, as C converts on
  assignment. \<open>kind_conv\<close> takes the destination as an option because a call without
  a destination converts nothing. A variable read carries no conversion: an identity
  holds a value of its own kind, since every write converts.
\<close>

definition kind_conv :: "kenv \<Rightarrow> var_id option \<Rightarrow> int \<Rightarrow> int" where
  "kind_conv \<kappa> dst n = (case dst of None \<Rightarrow> n | Some v \<Rightarrow> ik_norm (\<kappa> v) n)"

text \<open>Not \<open>[simp]\<close>: the semantics' rules are stated with the conversion folded, and
  unfolding it in a goal would keep them from matching.\<close>

lemma kind_conv_simps:
  "kind_conv \<kappa> None n = n"
  "kind_conv \<kappa> (Some v) n = ik_norm (\<kappa> v) n"
  by (simp_all add: kind_conv_def)

text \<open>A frame records the caller's store and the destination of the pending call.\<close>

datatype frame = Frame (frame_store: store) (frame_dest: "var_id option")

text \<open>The reference semantics every soundness claim is ultimately about.  A configuration is
  a command, a store, and a stack of caller frames; a call pushes one frame and continues in
  the callee body followed by \<open>Restore\<close>, a return writes the return slot and hands control to
  \<open>Unwind\<close>, which discards the rest of the callee body until that \<open>Restore\<close> pops the frame.
  \<open>Restore\<close> and \<open>Unwind\<close> exist only here, in configurations the semantics builds; no source
  program contains them.

  \<^const>\<open>eval\<close> evaluates an expression, \<^const>\<open>is_global\<close> classifies the variables a
  call keeps, \<^const>\<open>ReturnVar\<close> is the return slot (Goblint's single
  \<^verbatim>\<open>return_varinfo\<close>), and \<^const>\<open>kind_conv\<close> converts a value written to a
  destination, as Goblint converts a stored value to its target's declared type. A call
  converts each actual to its formal, as an assignment converts to its destination, so
  every entry store holds each formal at its own kind. Elaboration has already
  converted an actual it produced, as CIL does, and there the conversion changes
  nothing. A returned value is converted once, to the caller's destination.\<close>

inductive pstep :: "kenv \<Rightarrow> ('a, var_id, exp) gptable
    \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50)
  for \<kappa> :: kenv and \<Pi> :: "('a, var_id, exp) gptable"
where
  Assign:  "\<kappa>,\<Pi> \<turnstile> (Assign i x a, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) (eval a s)), frs)"
| Check:   "\<kappa>,\<Pi> \<turnstile> (Check i l c, s, frs) \<rightarrow>\<^sub>p (SKIP i, s, frs)"
| Seq1:    "\<kappa>,\<Pi> \<turnstile> (Seq (SKIP i) c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<kappa>,\<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (eval b s) \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (eval b s) \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<kappa>,\<Pi> \<turnstile> (While i b c, s, frs) \<rightarrow>\<^sub>p (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. eval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl)
                           (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) (formals decl) vals)
                           (enter_state is_global s)
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Call i dst p actuals, s, frs)
                   \<rightarrow>\<^sub>p (Seq (body decl) (Restore i), callee, Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result eval sc s v
             \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Call i (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) v), frs)"
| RestoreStep:
    "\<kappa>,\<Pi> \<turnstile> (Restore i, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (kind_conv \<kappa> dst (s ReturnVar)) (combine_env is_global fr s), frs)"
| ReturnSome:
    "\<kappa>,\<Pi> \<turnstile> (Return i (Some e), s, frs) \<rightarrow>\<^sub>p (Unwind i, s(ReturnVar := eval e s), frs)"
| ReturnNone:
    "\<kappa>,\<Pi> \<turnstile> (Return i None, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Seq (Unwind i) c2, s, frs) \<rightarrow>\<^sub>p (Unwind i, s, frs)"
| UnwindAct:
    "\<kappa>,\<Pi> \<turnstile> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP i, combine_assign dst (kind_conv \<kappa> dst (s ReturnVar)) (combine_env is_global fr s), frs)"

abbreviation psteps :: "kenv \<Rightarrow> ('a, var_id, exp) gptable
    \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> 'a com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p\<^sup>*/ _)" [51, 51, 51, 51] 50) where
  "psteps \<kappa> \<Pi> x y \<equiv> star (pstep \<kappa> \<Pi>) x y"

inductive_cases SkipSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (SKIP i, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases AssignSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (Assign i x a, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases CheckSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (Check i l c, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases SeqSE[elim]: "\<kappa>,\<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases IfSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (If i b c1 c2, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases WhileSE[elim]: "\<kappa>,\<Pi> \<turnstile> (While i b c, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases CallSE[elim]: "\<kappa>,\<Pi> \<turnstile> (Call i dst p actuals, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases RestoreSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (Restore i, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases ReturnSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (Return i e, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases UnwindSE[elim!]: "\<kappa>,\<Pi> \<turnstile> (Unwind i, s, frs) \<rightarrow>\<^sub>p cfg"

declare pstep.intros [simp, intro]

lemma combine_env_rv_irrelevant [simp]:
  "combine_env is_global fr (t(ReturnVar := v)) = combine_env is_global fr t"
  by (rule ext) simp

lemma psteps_Seq2:
  "\<kappa>,\<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p\<^sup>* (c1', s', frs')
   \<Longrightarrow> \<kappa>,\<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p\<^sup>* (Seq c1' c2, s', frs')"
  by (induction rule: star.induct[of "pstep \<kappa> \<Pi>", split_format(complete)])
     (auto intro: star.step)

subsection \<open>Frame-stack extension\<close>

text \<open>A step never inspects the frames below the one it works on, so any run stays valid
  with more callers underneath.  This is what lets a proof about a procedure in isolation be
  reused at an arbitrary call depth.\<close>

lemma pstep_frame_extend:
  "\<kappa>,\<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p (c', s', frs') \<Longrightarrow>
   \<kappa>,\<Pi> \<turnstile> (c, s, frs @ extra) \<rightarrow>\<^sub>p (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: pstep.induct)
     auto

subsection \<open>Call completion\<close>

text \<open>Running a whole call in one step of reasoning: a body that finishes under its own
  frame lets the caller resume with the frame popped and the return slot written.  Callers
  use these instead of replaying the \<open>Restore\<close> bookkeeping at every call site.\<close>

lemma pstep_Call:
  assumes "\<Pi> p = Some decl"
      and "length actuals = length (formals decl)"
      and "distinct (formals decl)"
  shows "\<kappa>,\<Pi> \<turnstile> (Call i dst p actuals, s, frs) \<rightarrow>\<^sub>p (Seq (body decl) (Restore i),
            bind_formals (formals decl)
              (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) (formals decl) (map (\<lambda>e. eval e s) actuals))
              (enter_state is_global s),
            Frame s dst # frs)"
  using assms by (rule pstep.Call) (rule refl)+

lemma pstep_Call_parameterless [intro]:
  assumes "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
  shows
    "\<kappa>,\<Pi> \<turnstile> (Call i dst p [], s, frs) \<rightarrow>\<^sub>p (Seq c (Restore i), enter_state is_global s, Frame s dst # frs)"
proof -
  have "\<kappa>,\<Pi> \<turnstile> (Call i dst p [], s, frs) \<rightarrow>\<^sub>p (Seq (body (\<lparr>formals = [], body = c\<rparr>)) (Restore i),
           bind_formals (formals (\<lparr>formals = [], body = c\<rparr>))
             (map2 (\<lambda>x. kind_conv \<kappa> (Some x)) (formals (\<lparr>formals = [], body = c\<rparr>))
               (map (\<lambda>e. eval e s) []))
             (enter_state is_global s),
           Frame s dst # frs)"
    using assms by (rule pstep_Call) simp_all
  then show ?thesis by simp
qed

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
    using assms by (auto elim!: CallSE simp: special_table_def kind_conv_simps)
next
  assume "c' = SKIP i \<and> frs' = frs \<and> (\<exists>n \<in> ik_range (\<kappa> x). s' = s(x := n))"
  then obtain n where n: "n \<in> ik_range (\<kappa> x)" and eq: "c' = SKIP i" "frs' = frs" "s' = s(x := n)"
    by blast
  have "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (SKIP i, s(x := kind_conv \<kappa> (Some x) n), frs)"
    by (rule pstep.Special[where desc = SD_Nondet_Int and sc = "Nondet_Int :: exp gspecial_call"])
       (simp_all add: special_table_def)
  with n eq
  show "\<kappa>,\<Pi> \<turnstile> (gcom.Call i (Some x) special_pname_nondet_int [], s, frs) \<rightarrow>\<^sub>p (c', s', frs')"
    by (simp add: kind_conv_simps del: ik_range_iff)
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
