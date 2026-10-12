theory Typed_Semantics
  imports Typed_Lower
begin

section \<open>Typed source semantics\<close>

text \<open>
  The typed semantics executes elaborated commands on typed stores, which hold one value
  per variable identity. It has the shape of \<^const>\<open>pstep\<close>: a call pushes a frame and
  continues in the callee body followed by \<^const>\<open>Restore\<close>, a return writes the return
  slot and unwinds. What differs is where kinds act. Every written value has the kind of
  the identity it is written to: elaboration already converts an assigned value, an
  actual argument and a returned value, and the semantics converts the two values it
  writes itself, a call result and a library result, to the destination's kind. A
  procedure's return slot is the identity \<^const>\<open>ReturnId\<close> of that procedure, so a typed
  frame also records which procedure it called.
\<close>

datatype tframe =
  TFrame (tframe_store: tstore) (tframe_dest: "var_id option") (tframe_callee: pname)

type_synonym 'a ttable = "pname \<Rightarrow> (var_id list \<times> 'a tcom) option"

text \<open>The globals are the identities without a scope. A call keeps them and resets
  every other identity, as \<^const>\<open>enter_state\<close> keeps the declared globals.\<close>

definition tglobal :: "var_id \<Rightarrow> bool" where
  "tglobal v \<longleftrightarrow> var_scope v = None"

text \<open>The procedure whose activation is running: the callee of the innermost frame, or
  \<open>main\<close> when no call is pending.\<close>

definition cur_proc :: "tframe list \<Rightarrow> pname" where
  "cur_proc tfs = (case tfs of [] \<Rightarrow> prog_main_name | f # _ \<Rightarrow> tframe_callee f)"

lemma cur_proc_simps [simp]:
  "cur_proc [] = prog_main_name"
  "cur_proc (f # tfs) = tframe_callee f"
  by (simp_all add: cur_proc_def)

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

inductive tstep :: "kenv \<Rightarrow> 'a ttable \<Rightarrow> 'a tcom \<times> tstore \<times> tframe list
                      \<Rightarrow> 'a tcom \<times> tstore \<times> tframe list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>t/ _)" [51, 51, 51, 51] 50)
  for \<kappa> :: kenv and T :: "'a ttable"
where
  TAssign: "\<kappa>, T \<turnstile> (Assign i v e, t, tfs) \<rightarrow>\<^sub>t (SKIP i, t(v := teval e t), tfs)"
| TCheck:  "\<kappa>, T \<turnstile> (Check i l c, t, tfs) \<rightarrow>\<^sub>t (SKIP i, t, tfs)"
| TSeq1:   "\<kappa>, T \<turnstile> (Seq (SKIP i) c2, t, tfs) \<rightarrow>\<^sub>t (c2, t, tfs)"
| TSeq2:   "\<kappa>, T \<turnstile> (c1, t, tfs) \<rightarrow>\<^sub>t (c1', t', tfs')
             \<Longrightarrow> \<kappa>, T \<turnstile> (Seq c1 c2, t, tfs) \<rightarrow>\<^sub>t (Seq c1' c2, t', tfs')"
| TIfTrue: "truthy (teval b t) \<Longrightarrow> \<kappa>, T \<turnstile> (If i b c1 c2, t, tfs) \<rightarrow>\<^sub>t (c1, t, tfs)"
| TIfFalse: "\<not> truthy (teval b t) \<Longrightarrow> \<kappa>, T \<turnstile> (If i b c1 c2, t, tfs) \<rightarrow>\<^sub>t (c2, t, tfs)"
| TWhile:  "\<kappa>, T \<turnstile> (While i b c, t, tfs)
              \<rightarrow>\<^sub>t (If i b (Seq c (While i b c)) (SKIP i), t, tfs)"
| TCall:   "T p = Some (xs, b)
             \<Longrightarrow> length es = length xs
             \<Longrightarrow> distinct xs
             \<Longrightarrow> \<kappa>, T \<turnstile> (Call i dst p es, t, tfs)
                 \<rightarrow>\<^sub>t (Seq b (Restore i),
                    bind_formals xs (map (\<lambda>e. teval e t) es) (enter_frame tglobal 0 t),
                    TFrame t dst p # tfs)"
| TSpecial: "special_table p = Some desc
             \<Longrightarrow> tspecial desc es t n
             \<Longrightarrow> \<kappa>, T \<turnstile> (Call i (Some v) p es, t, tfs) \<rightarrow>\<^sub>t (SKIP i, t(v := ik_norm (\<kappa> v) n), tfs)"
| TRestore:
    "\<kappa>, T \<turnstile> (Restore i, t, TFrame tf dst p # tfs)
       \<rightarrow>\<^sub>t (SKIP i, tcombine_assign \<kappa> dst (t (ReturnId p)) (combine_env tglobal tf t), tfs)"
| TReturnSome:
    "\<kappa>, T \<turnstile> (Return i (Some e), t, tfs) \<rightarrow>\<^sub>t (Unwind i, t(ReturnId (cur_proc tfs) := teval e t), tfs)"
| TReturnNone:
    "\<kappa>, T \<turnstile> (Return i None, t, tfs) \<rightarrow>\<^sub>t (Unwind i, t, tfs)"
| TUnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> \<kappa>, T \<turnstile> (Seq (Unwind i) c2, t, tfs) \<rightarrow>\<^sub>t (Unwind i, t, tfs)"
| TUnwindAct:
    "\<kappa>, T \<turnstile> (Seq (Unwind j) (Restore i), t, TFrame tf dst p # tfs)
       \<rightarrow>\<^sub>t (SKIP i, tcombine_assign \<kappa> dst (t (ReturnId p)) (combine_env tglobal tf t), tfs)"

abbreviation tsteps :: "kenv \<Rightarrow> 'a ttable \<Rightarrow> 'a tcom \<times> tstore \<times> tframe list
                         \<Rightarrow> 'a tcom \<times> tstore \<times> tframe list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>t\<^sup>*/ _)" [51, 51, 51, 51] 50)
where "tsteps \<kappa> T x y \<equiv> star (tstep \<kappa> T) x y"

lemmas tstep_induct = tstep.induct [split_format(complete)]

subsection \<open>The typed program of a source program\<close>

text \<open>A procedure's typed formals are the identities its formals resolve to, and its
  typed body is its elaboration.\<close>

definition typed_table :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> unit ttable" where
  "typed_table p ds q =
     map_option (\<lambda>d. (map (resolve_var (declared_global p) q) (formals d),
                      elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)))
       (prog_table p q)"

text \<open>A typed program starts with its globals at zero, like \<^const>\<open>cinit_stores\<close>, and
  every other identity holding some value of its kind.\<close>

definition tinit_stores :: "kenv \<Rightarrow> tstore set" where
  "tinit_stores \<kappa> = {t. styped \<kappa> t \<and> (\<forall>x. t (GlobalId x) = 0)}"

subsection \<open>Simulation by the lowered program\<close>

text \<open>
  Every typed step is matched by one \<^const>\<open>pstep\<close> of the lowered command. The lowered
  store names a variable by its source name and may hold a value outside the variable's
  kind, since a call or library result is stored as it is. It relates to the typed store
  through the kind: in the running activation of \<open>q\<close>, every identity \<open>q\<close> resolves holds
  the lowered value converted to its kind, which is what a lowered read computes. The
  return slot holds the same value on both sides; a lowered \<^const>\<open>Return\<close> writes a
  value already in the return kind's range.
\<close>

fun tvars :: "texp \<Rightarrow> var_id set" where
  "tvars (TN _ _) = {}"
| "tvars (TVar _ v) = {v}"
| "tvars (TArith _ _ a b) = tvars a \<union> tvars b"
| "tvars (TCast _ a) = tvars a"
| "tvars (TCmp _ a b) = tvars a \<union> tvars b"
| "tvars (TNot a) = tvars a"
| "tvars (TAnd a b) = tvars a \<union> tvars b"
| "tvars (TOr a b) = tvars a \<union> tvars b"

lemma exp_vnames_aop_exp [simp]:
  "exp_vnames (aop_exp op a b) = exp_vnames a \<union> exp_vnames b"
  by (cases op) simp_all

lemma exp_vnames_cop_exp [simp]:
  "exp_vnames (cop_exp op a b) = exp_vnames a \<union> exp_vnames b"
  by (cases op) simp_all

lemma exp_vnames_lower: "exp_vnames (lower e) = var_name ` tvars e"
  by (induction e) auto

text \<open>Lowering is exact on a store that the typed store reads through kinds.\<close>

theorem teval_lower:
  assumes "wt_texp \<kappa> e" and "\<And>v. v \<in> tvars e \<Longrightarrow> t v = ik_norm (\<kappa> v) (s (var_name v))"
  shows "teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
  using assms by (induction e) (auto simp del: lower.simps(4))

definition in_scope :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> var_id \<Rightarrow> bool" where
  "in_scope \<G> q v \<longleftrightarrow> (\<exists>x. v = resolve_var \<G> q x \<and> x \<noteq> ret_var)"

definition escoped :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> texp \<Rightarrow> bool" where
  "escoped \<G> q e \<longleftrightarrow> (\<forall>v \<in> tvars e. in_scope \<G> q v)"

text \<open>A command is scoped to \<open>q\<close> when every identity it reads or writes is one \<open>q\<close>
  resolves, and it contains no activation boundary.\<close>

fun tscoped :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> 'a tcom \<Rightarrow> bool" where
  "tscoped \<G> q (SKIP _) \<longleftrightarrow> True"
| "tscoped \<G> q (Assign _ v e) \<longleftrightarrow> in_scope \<G> q v \<and> escoped \<G> q e"
| "tscoped \<G> q (Check _ _ c) \<longleftrightarrow> escoped \<G> q c"
| "tscoped \<G> q (Seq c1 c2) \<longleftrightarrow> tscoped \<G> q c1 \<and> tscoped \<G> q c2"
| "tscoped \<G> q (If _ b c1 c2) \<longleftrightarrow> escoped \<G> q b \<and> tscoped \<G> q c1 \<and> tscoped \<G> q c2"
| "tscoped \<G> q (While _ b c) \<longleftrightarrow> escoped \<G> q b \<and> tscoped \<G> q c"
| "tscoped \<G> q (Call _ dst _ es) \<longleftrightarrow> pred_option (in_scope \<G> q) dst \<and> list_all (escoped \<G> q) es"
| "tscoped \<G> q (Return _ e) \<longleftrightarrow> pred_option (escoped \<G> q) e"
| "tscoped \<G> q (Restore _) \<longleftrightarrow> False"
| "tscoped \<G> q (Unwind _) \<longleftrightarrow> True"

definition tfids :: "'a ttable \<Rightarrow> pname \<Rightarrow> var_id list" where
  "tfids T p = (case T p of Some (xs, _) \<Rightarrow> xs | None \<Rightarrow> [])"

definition cok :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> 'a ttable \<Rightarrow> pname \<Rightarrow> 'a tcom \<Rightarrow> bool" where
  "cok \<kappa> \<G> T q c \<longleftrightarrow> wt_tcom \<kappa> (tfids T) q c \<and> tscoped \<G> q c"

text \<open>
  A running command nests activations: a call leaves the callee body followed by
  \<^const>\<open>Restore\<close> in place of the call, inside what remains of the caller. \<open>tok L c\<close>
  says that \<open>c\<close> has this shape for the activations \<open>L\<close>, innermost first: the part of
  \<open>c\<close> that runs next belongs to \<open>hd L\<close>, and the rest of \<open>c\<close> to \<open>last L\<close>.
\<close>

inductive tok :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> 'a ttable \<Rightarrow> pname list \<Rightarrow> 'a tcom \<Rightarrow> bool"
  for \<kappa> \<G> T where
  base: "cok \<kappa> \<G> T q c \<Longrightarrow> tok \<kappa> \<G> T [q] c"
| seq: "tok \<kappa> \<G> T L c1 \<Longrightarrow> cok \<kappa> \<G> T (last L) c2 \<Longrightarrow> tok \<kappa> \<G> T L (Seq c1 c2)"
| bnd: "tok \<kappa> \<G> T L c \<Longrightarrow> tok \<kappa> \<G> T (L @ [q]) (Seq c (Restore i))"
| rst: "tok \<kappa> \<G> T [p, q] (Restore i)"

text \<open>The store relation of one activation of \<open>q\<close>, and of a stack of frames: each
  frame holds its caller's store, and the caller of a frame is the callee of the frame
  below it.\<close>

definition srel :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> tstore \<Rightarrow> store \<Rightarrow> bool" where
  "srel \<kappa> \<G> q t s \<longleftrightarrow>
     (\<forall>x. x \<noteq> ret_var \<longrightarrow> t (resolve_var \<G> q x) = ik_norm (\<kappa> (resolve_var \<G> q x)) (s x))
     \<and> t (ReturnId q) = s ret_var"

fun frel :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> tframe list \<Rightarrow> frame list \<Rightarrow> bool" where
  "frel \<kappa> \<G> [] [] \<longleftrightarrow> True"
| "frel \<kappa> \<G> (TFrame tf d p # tfs) (Frame f d' # fs) \<longleftrightarrow>
     d' = map_option var_name d \<and> pred_option (in_scope \<G> (cur_proc tfs)) d \<and>
     srel \<kappa> \<G> (cur_proc tfs) tf f \<and> frel \<kappa> \<G> tfs fs"
| "frel \<kappa> \<G> _ _ \<longleftrightarrow> False"

definition activations :: "tframe list \<Rightarrow> pname list" where
  "activations tfs = map tframe_callee tfs @ [prog_main_name]"

text \<open>The typed table lowers to the untyped one, its formals are local identities of
  their procedure, and its bodies are well-typed and scoped.\<close>

definition tab_rel :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> 'a ttable \<Rightarrow> 'a ptable \<Rightarrow> bool" where
  "tab_rel \<kappa> \<G> T \<Pi> \<longleftrightarrow>
     (\<forall>p xs b. T p = Some (xs, b) \<longrightarrow>
        (\<exists>ys. xs = map (ScopedId p) ys \<and> list_all (valid_formal \<G>) ys \<and>
              \<Pi> p = Some \<lparr>formals = ys, body = lower_com b\<rparr> \<and> cok \<kappa> \<G> T p b))"

definition sim :: "kenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> 'a ttable
                     \<Rightarrow> 'a tcom \<times> tstore \<times> tframe list \<Rightarrow> 'a acom \<times> store \<times> frame list \<Rightarrow> bool"
where
  "sim \<kappa> \<G> T = (\<lambda>(tc, t, tfs) (c, s, fs).
     c = lower_com tc \<and> tok \<kappa> \<G> T (activations tfs) tc \<and>
     srel \<kappa> \<G> (cur_proc tfs) t s \<and> frel \<kappa> \<G> tfs fs)"

subsubsection \<open>Stores\<close>

text \<open>Reads, writes, procedure entry and procedure exit each keep \<^const>\<open>srel\<close>.\<close>

lemma in_scopeE:
  assumes "in_scope \<G> q v"
  obtains x where "v = resolve_var \<G> q x" "x \<noteq> ret_var"
  using assms unfolding in_scope_def by blast

lemma srel_read:
  assumes "srel \<kappa> \<G> q t s" and "in_scope \<G> q v"
  shows "t v = ik_norm (\<kappa> v) (s (var_name v))"
  using assms by (auto simp: srel_def elim!: in_scopeE)

lemma teval_lower_scoped:
  assumes "srel \<kappa> \<G> q t s" and "wt_texp \<kappa> e" and "escoped \<G> q e"
  shows "teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
  using assms by (intro teval_lower) (auto simp: escoped_def intro: srel_read)

text \<open>Writing a value to the lowered store and its conversion to the typed store keeps
  the relation.\<close>

lemma ReturnId_ne_resolve_var [simp]: "ReturnId r \<noteq> resolve_var \<G> q x"
  by (simp add: resolve_var_def)

lemma srel_update:
  assumes "srel \<kappa> \<G> q t s" and "in_scope \<G> q v"
  shows "srel \<kappa> \<G> q (t(v := ik_norm (\<kappa> v) n)) (s(var_name v := n))"
proof -
  from assms(2) obtain x0 where v: "v = resolve_var \<G> q x0" and x0: "x0 \<noteq> ret_var"
    by (rule in_scopeE)
  have "resolve_var \<G> q x = resolve_var \<G> q x0 \<longleftrightarrow> x = x0" for x
    by (simp add: resolve_var_eq_iff)
  with assms(1) x0 show ?thesis
    unfolding srel_def v by (auto simp: x0 [symmetric])
qed

lemma srel_update_in_range:
  assumes "srel \<kappa> \<G> q t s" and "in_scope \<G> q v" and "n \<in> ik_range (\<kappa> v)"
  shows "srel \<kappa> \<G> q (t(v := n)) (s(var_name v := n))"
  using srel_update [OF assms(1,2), of n] assms(3) by simp

lemma srel_return:
  assumes "srel \<kappa> \<G> q t s"
  shows "srel \<kappa> \<G> q (t(ReturnId q := n)) (s(ret_var := n))"
  using assms by (simp add: srel_def)

text \<open>Entering a callee: both sides keep their globals, reset their locals to zero,
  and bind the formals to the same values, each in its formal's range.\<close>

lemma bind_formals_ScopedId:
  assumes "\<And>y. \<not> \<G> y \<Longrightarrow> a (ScopedId p y) = ik_norm (\<kappa> (ScopedId p y)) (b y)"
    and "list_all2 (\<lambda>y n. ik_norm (\<kappa> (ScopedId p y)) n = n) ys ns"
    and "\<not> \<G> x"
  shows "bind_formals (map (ScopedId p) ys) ns a (ScopedId p x)
           = ik_norm (\<kappa> (ScopedId p x)) (bind_formals ys ns b x)"
  using assms(2,1)
proof (induction ys ns arbitrary: a b rule: list_all2_induct)
  case Nil
  then show ?case using assms(3) by simp
next
  case (Cons y ys n ns)
  have "bind_formals (map (ScopedId p) ys) ns (a(ScopedId p y := n)) (ScopedId p x)
          = ik_norm (\<kappa> (ScopedId p x)) (bind_formals ys ns (b(y := n)) x)"
    by (rule Cons.IH) (use Cons.hyps Cons.prems in auto)
  then show ?case by (simp only: list.map zip_Cons_Cons fold_Cons comp_apply prod.case)
qed

lemma srel_enter:
  assumes "srel \<kappa> \<G> q t s" and "\<not> \<G> ret_var"
    and "list_all (valid_formal \<G>) ys"
    and "list_all2 (\<lambda>y n. ik_norm (\<kappa> (ScopedId p y)) n = n) ys ns"
  shows "srel \<kappa> \<G> p (bind_formals (map (ScopedId p) ys) ns (enter_frame tglobal 0 t))
                     (bind_formals ys ns (enter_state \<G> s))"
  unfolding srel_def
proof (intro conjI allI impI)
  have ys: "y \<in> set ys \<Longrightarrow> \<not> \<G> y \<and> y \<noteq> ret_var" for y
    using assms(3) by (auto simp: list_all_iff valid_formal_def)
  fix x assume x: "x \<noteq> ret_var"
  show "bind_formals (map (ScopedId p) ys) ns (enter_frame tglobal 0 t) (resolve_var \<G> p x)
          = ik_norm (\<kappa> (resolve_var \<G> p x)) (bind_formals ys ns (enter_state \<G> s) x)"
  proof (cases "\<G> x")
    case True
    then have "x \<notin> set ys" "GlobalId x \<notin> set (map (ScopedId p) ys)"
      using ys by auto
    with True assms(1) x show ?thesis
      by (auto simp: bind_formals_other resolve_var_def srel_def enter_frame_def
               enter_state_def tglobal_def dest: spec [of _ x])
  next
    case False
    have "bind_formals (map (ScopedId p) ys) ns (enter_frame tglobal 0 t) (ScopedId p x)
            = ik_norm (\<kappa> (ScopedId p x)) (bind_formals ys ns (enter_state \<G> s) x)"
      using assms(4) False
      by (intro bind_formals_ScopedId) (auto simp: enter_frame_def enter_state_def tglobal_def)
    with False show ?thesis by (simp add: resolve_var_def)
  qed
next
  have "ReturnId p \<notin> set (map (ScopedId p) ys)" "ret_var \<notin> set ys"
    using assms(3) by (auto simp: list_all_iff valid_formal_def)
  with assms(2) show "bind_formals (map (ScopedId p) ys) ns (enter_frame tglobal 0 t) (ReturnId p)
                        = bind_formals ys ns (enter_state \<G> s) ret_var"
    by (simp add: bind_formals_other enter_frame_def enter_state_def tglobal_def)
qed

text \<open>Leaving a callee: globals come from the callee, locals from the caller's frame,
  and the destination receives the return slot.\<close>

lemma srel_restore:
  assumes callee: "srel \<kappa> \<G> p t s" and caller: "srel \<kappa> \<G> q tf f"
    and dst: "pred_option (in_scope \<G> q) d" and nr: "\<not> \<G> ret_var"
  shows "srel \<kappa> \<G> q (tcombine_assign \<kappa> d (t (ReturnId p)) (combine_env tglobal tf t))
                     (combine_assign (map_option var_name d) (s ret_var) (combine_env \<G> f s))"
proof -
  have comb: "srel \<kappa> \<G> q (combine_env tglobal tf t) (combine_env \<G> f s)"
    unfolding srel_def
  proof (intro conjI allI impI)
    fix x assume x: "x \<noteq> ret_var"
    show "combine_env tglobal tf t (resolve_var \<G> q x)
            = ik_norm (\<kappa> (resolve_var \<G> q x)) (combine_env \<G> f s x)"
    proof (cases "\<G> x")
      case True
      with callee x show ?thesis
        by (auto simp: srel_def resolve_var_def tglobal_def dest: spec [of _ x])
    next
      case False
      with caller x show ?thesis
        by (auto simp: srel_def resolve_var_def tglobal_def dest: spec [of _ x])
    qed
  next
    show "combine_env tglobal tf t (ReturnId q) = combine_env \<G> f s ret_var"
      using caller nr by (simp add: srel_def tglobal_def)
  qed
  have ret: "t (ReturnId p) = s ret_var"
    using callee by (simp add: srel_def)
  show ?thesis
  proof (cases d)
    case None
    with comb show ?thesis by simp
  next
    case (Some v)
    with dst srel_update [OF comb, of v "s ret_var"] ret show ?thesis by simp
  qed
qed

subsubsection \<open>Commands\<close>

text \<open>The shape facts the step proof inverts: which activations a command can
  belong to, and how a library call evaluates on both sides.\<close>

lemma cok_simps [simp]:
  "cok \<kappa> \<G> T q (SKIP i)"
  "cok \<kappa> \<G> T q (Unwind i)"
  "\<not> cok \<kappa> \<G> T q (Restore i)"
  "cok \<kappa> \<G> T q (Seq c1 c2) \<longleftrightarrow> cok \<kappa> \<G> T q c1 \<and> cok \<kappa> \<G> T q c2"
  "cok \<kappa> \<G> T q (If i b c1 c2) \<longleftrightarrow>
     wt_texp \<kappa> b \<and> escoped \<G> q b \<and> cok \<kappa> \<G> T q c1 \<and> cok \<kappa> \<G> T q c2"
  "cok \<kappa> \<G> T q (While i b c) \<longleftrightarrow> wt_texp \<kappa> b \<and> escoped \<G> q b \<and> cok \<kappa> \<G> T q c"
  by (auto simp: cok_def)

text \<open>A command other than a sequence or an activation boundary runs in a single
  activation.\<close>

lemma tok_single:
  assumes "tok \<kappa> \<G> T L c" and "\<And>c1 c2. c \<noteq> Seq c1 c2" and "\<And>i. c \<noteq> Restore i"
  shows "L = [hd L] \<and> cok \<kappa> \<G> T (hd L) c"
  using assms by (induction rule: tok.induct) auto

lemma tok_Restore:
  assumes "tok \<kappa> \<G> T L (Restore i)"
  obtains p q where "L = [p, q]"
  using assms by (cases rule: tok.cases) (auto simp: cok_def)

lemma frel_ConsE:
  assumes "frel \<kappa> \<G> (TFrame tf d p # tfs) fs"
  obtains f fs0 where "fs = Frame f (map_option var_name d) # fs0"
    "pred_option (in_scope \<G> (cur_proc tfs)) d" "srel \<kappa> \<G> (cur_proc tfs) tf f"
    "frel \<kappa> \<G> tfs fs0"
  using assms by (cases fs; cases "hd fs") auto

lemma activations_hd:
  assumes "L @ R = activations tfs" and "L \<noteq> []"
  shows "cur_proc tfs = hd L"
  using assms by (cases tfs; cases L) (auto simp: activations_def)

lemma activations_Cons [simp]:
  "activations (TFrame tf d p # tfs) = p # activations tfs"
  by (simp add: activations_def)

text \<open>A library call returns the same values on both sides, because its arguments
  evaluate alike.\<close>

lemma tspecial_lower:
  assumes "tspecial desc es t n" and "\<And>e. e \<in> set es \<Longrightarrow> teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
  shows "\<exists>sc. classify_special desc (map lower es) = Some sc \<and> special_result aval sc s n"
  using assms by (cases "(desc, es, t, n)" rule: tspecial.cases) auto

lemma args_ok_range:
  assumes "args_ok \<kappa> fs es" and "length fs = length es"
  shows "list_all2 (\<lambda>f n. ik_norm (\<kappa> f) n = n) fs (map (\<lambda>e. \<lbrakk>lower e\<rbrakk>\<^sub>e s) es)"
  using assms
proof (induction \<kappa> fs es rule: args_ok.induct)
  case (1 \<kappa> f fs e es)
  then show ?case using aval_lower_in_range [of e s] by simp
qed simp_all

subsubsection \<open>One step\<close>

text \<open>The step proof follows \<^const>\<open>tstep\<close> rule by rule. A sequence step
  descends into the part of the command that runs next, which may belong to a deeper
  activation than the rest of the command.\<close>

lemma map_gcom_eq_Restore [simp]:
  "map_gcom f g h c = Restore i \<longleftrightarrow> (\<exists>j. c = Restore j \<and> i = f j)"
  by (cases c) auto

lemma pstep_lower_Seq:
  "\<G>, \<Pi> \<turnstile> (lower_com c1, s, fs) \<rightarrow>\<^sub>p (lower_com c1', s', fs')
   \<Longrightarrow> \<G>, \<Pi> \<turnstile> (lower_com (Seq c1 c2), s, fs) \<rightarrow>\<^sub>p (lower_com (Seq c1' c2), s', fs')"
  by simp

context
  fixes \<kappa> :: kenv and \<G> :: "vname \<Rightarrow> bool" and T :: "'a ttable" and \<Pi> :: "'a ptable"
  assumes tab: "tab_rel \<kappa> \<G> T \<Pi>" and nr: "\<not> \<G> ret_var"
begin

text \<open>The induction rule writes the identity on annotations as \<open>\<lambda>a. a\<close>, so the proof
  works with that form throughout.\<close>

declare id_def [simp]

lemma tstep_sim:
  assumes "\<kappa>, T \<turnstile> (c, t, tfs) \<rightarrow>\<^sub>t (c', t', tfs')"
    and "tok \<kappa> \<G> T L c" and "L @ R = activations tfs"
    and "srel \<kappa> \<G> (cur_proc tfs) t s" and "frel \<kappa> \<G> tfs fs"
  shows "\<exists>s' fs' L'. \<G>, \<Pi> \<turnstile> (lower_com c, s, fs) \<rightarrow>\<^sub>p (lower_com c', s', fs')
           \<and> tok \<kappa> \<G> T L' c' \<and> L' @ R = activations tfs' \<and> last L' = last L
           \<and> srel \<kappa> \<G> (cur_proc tfs') t' s' \<and> frel \<kappa> \<G> tfs' fs'"
  using assms
proof (induction arbitrary: L R s fs rule: tstep_induct)
  case (TAssign i v e t tfs)
  from tok_single [OF TAssign.prems(1)]
  obtain q where L: "L = [q]" and ok: "cok \<kappa> \<G> T q (Assign i v e)"
    by auto
  with TAssign.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  from ok have wt: "wt_texp \<kappa> e" "texp_kind e = \<kappa> v" and sc: "in_scope \<G> q v" "escoped \<G> q e"
    by (simp_all add: cok_def)
  have ev: "teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
    using teval_lower_scoped TAssign.prems(3) wt sc cur by simp
  have rng: "\<lbrakk>lower e\<rbrakk>\<^sub>e s \<in> ik_range (\<kappa> v)"
    using aval_lower_in_range [of e s] wt by simp
  have step: "\<G>, \<Pi> \<turnstile> (lower_com (Assign i v e), s, fs)
      \<rightarrow>\<^sub>p (lower_com (SKIP i), s(var_name v := \<lbrakk>lower e\<rbrakk>\<^sub>e s), fs)"
    by (simp only: gcom.map id_apply) (rule gpstep.Assign)
  have "srel \<kappa> \<G> q (t(v := teval e t)) (s(var_name v := \<lbrakk>lower e\<rbrakk>\<^sub>e s))"
    unfolding ev by (rule srel_update_in_range [OF TAssign.prems(3) [unfolded cur] sc(1) rng])
  moreover have "tok \<kappa> \<G> T [q] (SKIP i)" by (simp add: tok.base)
  ultimately show ?case
    using step TAssign.prems(2,4) L cur by blast
next
  case (TCheck i)
  from tok_single [OF TCheck.prems(1)] obtain q where L: "L = [q]" by auto
  with TCheck.prems show ?case
    by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
next
  case (TSeq1 i c2 t tfs)
  from TSeq1.prems(1) show ?case
  proof (cases rule: tok.cases)
    case (base q)
    with TSeq1.prems show ?thesis
      by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
  next
    case seq
    with tok_single [of \<kappa> \<G> T L "SKIP i"] obtain q where L: "L = [q]"
        and ok: "cok \<kappa> \<G> T q c2"
      by (metis gcom.distinct last_ConsL)
    with TSeq1.prems show ?thesis
      by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
  next
    case (bnd L0 q j)
    with tok_single [of \<kappa> \<G> T L0 "SKIP i"] obtain p where "L0 = [p]"
      by (metis gcom.distinct)
    with bnd have "L = [p, q]" "c2 = Restore j" by simp_all
    with TSeq1.prems show ?thesis
      by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.rst)
  qed
next
  case (TSeq2 c1 t tfs c1' t' tfs' c2)
  from TSeq2.prems(1) show ?case
  proof (cases rule: tok.cases)
    case (base q)
    then have L: "L = [q]" and ok1: "cok \<kappa> \<G> T q c1" and ok2: "cok \<kappa> \<G> T q c2" by auto
    from TSeq2.IH [OF tok.base [OF ok1] TSeq2.prems(2) [unfolded L] TSeq2.prems(3,4)]
    obtain s' fs' L' where st: "\<G>, \<Pi> \<turnstile> (lower_com c1, s, fs) \<rightarrow>\<^sub>p (lower_com c1', s', fs')"
        "tok \<kappa> \<G> T L' c1'" "L' @ R = activations tfs'" "last L' = last [q]"
        "srel \<kappa> \<G> (cur_proc tfs') t' s'" "frel \<kappa> \<G> tfs' fs'"
      by blast
    from st ok2 L show ?thesis
      using pstep_lower_Seq [OF st(1), of c2]
      by (auto simp: id_def intro!: exI [of _ s'] exI [of _ fs'] exI [of _ L'] tok.seq)
  next
    case seq
    then have tok1: "tok \<kappa> \<G> T L c1" and ok2: "cok \<kappa> \<G> T (last L) c2" by auto
    from TSeq2.IH [OF tok1 TSeq2.prems(2-4)]
    obtain s' fs' L' where st: "\<G>, \<Pi> \<turnstile> (lower_com c1, s, fs) \<rightarrow>\<^sub>p (lower_com c1', s', fs')"
        "tok \<kappa> \<G> T L' c1'" "L' @ R = activations tfs'" "last L' = last L"
        "srel \<kappa> \<G> (cur_proc tfs') t' s'" "frel \<kappa> \<G> tfs' fs'"
      by blast
    from st ok2 show ?thesis
      using pstep_lower_Seq [OF st(1), of c2]
      by (auto simp: id_def intro!: exI [of _ s'] exI [of _ fs'] exI [of _ L'] tok.seq)
  next
    case (bnd L0 q i)
    then have tok1: "tok \<kappa> \<G> T L0 c1" and c2: "c2 = Restore i" and L: "L = L0 @ [q]" by auto
    have R: "L0 @ q # R = activations tfs" using TSeq2.prems(2) L by simp
    from TSeq2.IH [OF tok1 R TSeq2.prems(3,4)]
    obtain s' fs' L' where st: "\<G>, \<Pi> \<turnstile> (lower_com c1, s, fs) \<rightarrow>\<^sub>p (lower_com c1', s', fs')"
        "tok \<kappa> \<G> T L' c1'" "L' @ q # R = activations tfs'"
        "srel \<kappa> \<G> (cur_proc tfs') t' s'" "frel \<kappa> \<G> tfs' fs'"
      by blast
    from st c2 L show ?thesis
      using pstep_lower_Seq [OF st(1), of c2]
      by (auto simp: id_def intro!: exI [of _ s'] exI [of _ fs'] exI [of _ "L' @ [q]"] tok.bnd)
  qed
next
  case (TIfTrue b t i c1 c2 tfs)
  from tok_single [OF TIfTrue.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (If i b c1 c2)" by auto
  with TIfTrue.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  with ok TIfTrue.prems(3) have "teval b t = \<lbrakk>lower b\<rbrakk>\<^sub>e s"
    by (intro teval_lower_scoped) auto
  with TIfTrue.hyps TIfTrue.prems ok L show ?case
    by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
next
  case (TIfFalse b t i c1 c2 tfs)
  from tok_single [OF TIfFalse.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (If i b c1 c2)" by auto
  with TIfFalse.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  with ok TIfFalse.prems(3) have "teval b t = \<lbrakk>lower b\<rbrakk>\<^sub>e s"
    by (intro teval_lower_scoped) auto
  with TIfFalse.hyps TIfFalse.prems ok L show ?case
    by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
next
  case (TWhile i b c t tfs)
  from tok_single [OF TWhile.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (While i b c)" by auto
  with TWhile.prems show ?case
    by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
next
  case (TCall p xs b es i dst t tfs)
  from tok_single [OF TCall.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (Call i dst p es)" by auto
  with TCall.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  from tab TCall.hyps(1) obtain ys where xs: "xs = map (ScopedId p) ys"
      and vf: "list_all (valid_formal \<G>) ys"
      and decl: "\<Pi> p = Some \<lparr>formals = ys, body = lower_com b\<rparr>"
      and okb: "cok \<kappa> \<G> T p b"
    unfolding tab_rel_def by blast
  from ok TCall.hyps(1) have wt: "list_all (wt_texp \<kappa>) es" "args_ok \<kappa> xs es"
      and dsc: "pred_option (in_scope \<G> q) dst" and esc: "list_all (escoped \<G> q) es"
    by (simp_all add: cok_def tfids_def)
  have vals: "map (\<lambda>e. teval e t) es = map (\<lambda>e. \<lbrakk>lower e\<rbrakk>\<^sub>e s) es"
    using wt esc TCall.prems(3) cur by (auto simp: list_all_iff intro: teval_lower_scoped)
  have rng: "list_all2 (\<lambda>y n. ik_norm (\<kappa> (ScopedId p y)) n = n) ys (map (\<lambda>e. \<lbrakk>lower e\<rbrakk>\<^sub>e s) es)"
    using args_ok_range [OF wt(2), of s] TCall.hyps(2) xs by (simp add: list_all2_map1)
  have dys: "distinct ys" using TCall.hyps(3) xs by (simp add: distinct_map)
  have lc: "lower_com (Call i dst p es) = Call i (map_option var_name dst) p (map lower es)"
      "lower_com (Seq b (Restore i)) = Seq (lower_com b) (Restore i)"
    by simp_all
  have "\<G>, \<Pi> \<turnstile> (Call i (map_option var_name dst) p (map lower es), s, fs)
      \<rightarrow>\<^sub>p (Seq (body \<lparr>formals = ys, body = lower_com b\<rparr>) (Restore i),
           bind_formals (formals \<lparr>formals = ys, body = lower_com b\<rparr>)
             (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) (map lower es)) (enter_state \<G> s),
           Frame s (map_option var_name dst) # fs)"
    by (rule gpstep.Call [where \<Pi> = \<Pi> and p = p, OF decl]) (use TCall.hyps(2) xs dys in auto)
  then have step: "\<G>, \<Pi> \<turnstile> (lower_com (Call i dst p es), s, fs)
      \<rightarrow>\<^sub>p (lower_com (Seq b (Restore i)),
           bind_formals ys (map (\<lambda>e. \<lbrakk>lower e\<rbrakk>\<^sub>e s) es) (enter_state \<G> s),
           Frame s (map_option var_name dst) # fs)"
    unfolding lc by (simp add: comp_def)
  have tokc: "tok \<kappa> \<G> T [p, q] (Seq b (Restore i))"
    using tok.bnd [OF tok.base [OF okb], of q i] by simp
  show ?case
    using step tokc srel_enter [OF TCall.prems(3) [unfolded cur] nr vf rng] L TCall.prems(2-4) dsc
      cur
    by (intro exI exI exI [of _ "[p, q]"]) (auto simp: vals xs)
next
  case (TSpecial p desc es t n i v tfs)
  from tok_single [OF TSpecial.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (Call i (Some v) p es)" by auto
  with TSpecial.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  from ok have wt: "list_all (wt_texp \<kappa>) es" and dsc: "in_scope \<G> q v"
      and esc: "list_all (escoped \<G> q) es"
    by (simp_all add: cok_def)
  have "\<And>e. e \<in> set es \<Longrightarrow> teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
    using wt esc TSpecial.prems(3) cur by (auto simp: list_all_iff intro: teval_lower_scoped)
  from tspecial_lower [OF TSpecial.hyps(2) this] obtain sc
    where "classify_special desc (map lower es) = Some sc" "special_result aval sc s n" by blast
  with TSpecial.hyps(1) have "\<G>, \<Pi> \<turnstile> (lower_com (Call i (Some v) p es), s, fs)
      \<rightarrow>\<^sub>p (lower_com (SKIP i), s(var_name v := n), fs)"
    by (auto intro: gpstep.Special)
  moreover have "tok \<kappa> \<G> T [q] (SKIP i)" by (simp add: tok.base)
  ultimately show ?case
    using srel_update [OF TSpecial.prems(3) [unfolded cur] dsc, of n] TSpecial.prems(2,4) L cur
    by blast
next
  case (TRestore i t tf dst p tfs)
  from tok_Restore [OF TRestore.prems(1)] obtain p' q where L: "L = [p', q]" .
  with TRestore.prems(2) have p': "p' = p" and R: "q # R = activations tfs"
    by simp_all
  then have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  from TRestore.prems(4) obtain f fs0 where fs: "fs = Frame f (map_option var_name dst) # fs0"
      and dsc: "pred_option (in_scope \<G> q) dst" and caller: "srel \<kappa> \<G> q tf f"
      and fr: "frel \<kappa> \<G> tfs fs0"
    using cur by (auto elim: frel_ConsE)
  have "\<G>, \<Pi> \<turnstile> (lower_com (Restore i), s, fs)
      \<rightarrow>\<^sub>p (lower_com (SKIP i),
           combine_assign (map_option var_name dst) (s ret_var) (combine_env \<G> f s), fs0)"
    by (simp add: fs)
  with srel_restore [OF TRestore.prems(3) [simplified] caller dsc nr] R fr L cur show ?case
    by (intro exI exI exI [of _ "[q]"]) (auto intro: tok.base)
next
  case (TReturnSome i e t tfs)
  from tok_single [OF TReturnSome.prems(1)] obtain q where L: "L = [q]"
      and ok: "cok \<kappa> \<G> T q (Return i (Some e))" by auto
  with TReturnSome.prems(2) have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs]
    by simp
  from ok have "teval e t = \<lbrakk>lower e\<rbrakk>\<^sub>e s"
    using TReturnSome.prems(3) cur by (intro teval_lower_scoped) (auto simp: cok_def)
  then have "\<G>, \<Pi> \<turnstile> (lower_com (Return i (Some e)), s, fs)
      \<rightarrow>\<^sub>p (lower_com (Unwind i), s(ret_var := teval e t), fs)"
    by simp
  moreover have "tok \<kappa> \<G> T [q] (Unwind i)" by (simp add: tok.base)
  ultimately show ?case
    using srel_return [OF TReturnSome.prems(3), of "teval e t"] TReturnSome.prems(2,4) L cur
    by blast
next
  case (TReturnNone i t tfs)
  from tok_single [OF TReturnNone.prems(1)] obtain q where L: "L = [q]" by auto
  with TReturnNone.prems show ?case
    by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
next
  case (TUnwindDead c2 i t tfs)
  from TUnwindDead.prems(1) show ?case
  proof (cases rule: tok.cases)
    case (base q)
    with TUnwindDead.hyps TUnwindDead.prems show ?thesis
      by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
  next
    case seq
    with tok_single [of \<kappa> \<G> T L "Unwind i"] TUnwindDead.hyps TUnwindDead.prems show ?thesis
      by (intro exI [of _ s] exI [of _ fs] exI [of _ L]) (auto intro: tok.base)
  next
    case bnd
    with TUnwindDead.hyps show ?thesis by simp
  qed
next
  case (TUnwindAct j i t tf dst p tfs)
  from TUnwindAct.prems(1) obtain L0 q where L: "L = L0 @ [q]" and tok0: "tok \<kappa> \<G> T L0 (Unwind j)"
    by (cases rule: tok.cases) (auto simp: cok_def)
  from tok_single [OF tok0] have L0: "L0 = [hd L0]" by simp
  with L TUnwindAct.prems(2) have R: "q # R = activations tfs"
    by (metis activations_Cons append_Cons append_Nil list.inject)
  then have cur: "cur_proc tfs = q" using activations_hd [of "[q]" R tfs] by simp
  from TUnwindAct.prems(4) obtain f fs0 where fs: "fs = Frame f (map_option var_name dst) # fs0"
      and dsc: "pred_option (in_scope \<G> q) dst" and caller: "srel \<kappa> \<G> q tf f"
      and fr: "frel \<kappa> \<G> tfs fs0"
    using cur by (auto elim: frel_ConsE)
  have "\<G>, \<Pi> \<turnstile> (lower_com (Seq (Unwind j) (Restore i)), s, fs)
      \<rightarrow>\<^sub>p (lower_com (SKIP i),
           combine_assign (map_option var_name dst) (s ret_var) (combine_env \<G> f s), fs0)"
    by (simp add: fs)
  with srel_restore [OF TUnwindAct.prems(3) [simplified] caller dsc nr] R fr L cur show ?case
    by (intro exI exI exI [of _ "[q]"]) (auto intro: tok.base)
qed

declare id_def [simp del]

subsubsection \<open>Runs\<close>

text \<open>A typed run is matched by a run of the lowered program of any length.\<close>

theorem tsteps_sim:
  assumes "\<kappa>, T \<turnstile> (c, t, tfs) \<rightarrow>\<^sub>t\<^sup>* (c', t', tfs')" and "sim \<kappa> \<G> T (c, t, tfs) (lc, s, fs)"
  shows "\<exists>s' fs'. \<G>, \<Pi> \<turnstile> (lc, s, fs) \<rightarrow>\<^sub>p\<^sup>* (lower_com c', s', fs')
           \<and> sim \<kappa> \<G> T (c', t', tfs') (lower_com c', s', fs')"
  using assms
proof (induction arbitrary: lc s fs rule: star.induct [of "tstep \<kappa> T", split_format(complete)])
  case (refl c t tfs)
  then show ?case by (auto simp: sim_def id_def)
next
  case (step c t tfs c'' t'' tfs'' c' t' tfs')
  from step.prems have lc: "lc = lower_com c" and tk: "tok \<kappa> \<G> T (activations tfs) c"
      and sr: "srel \<kappa> \<G> (cur_proc tfs) t s" and fr: "frel \<kappa> \<G> tfs fs"
    by (simp_all add: sim_def)
  have "activations tfs @ [] = activations tfs" by simp
  from tstep_sim [OF step.hyps(1) tk this sr fr] obtain s'' fs'' L'
    where st: "\<G>, \<Pi> \<turnstile> (lower_com c, s, fs) \<rightarrow>\<^sub>p (lower_com c'', s'', fs'')"
      and "tok \<kappa> \<G> T L' c''" "L' @ [] = activations tfs''"
      and "srel \<kappa> \<G> (cur_proc tfs'') t'' s''" "frel \<kappa> \<G> tfs'' fs''"
    by blast
  then have "sim \<kappa> \<G> T (c'', t'', tfs'') (lower_com c'', s'', fs'')"
    by (simp add: sim_def)
  from step.IH [OF this] obtain s' fs'
    where "\<G>, \<Pi> \<turnstile> (lower_com c'', s'', fs'') \<rightarrow>\<^sub>p\<^sup>* (lower_com c', s', fs')"
      and "sim \<kappa> \<G> T (c', t', tfs') (lower_com c', s', fs')"
    by blast
  with st lc show ?case by (blast intro: star.step)
qed

end

subsection \<open>Typed programs\<close>

text \<open>The table of a typed program meets the simulation's requirements whenever its
  lowering is a well-formed source program, which \<open>run_voblint\<close> checks.\<close>

lemma tvars_elaborate: "tvars (elaborate \<rho> \<kappa> ik e) \<subseteq> range \<rho>"
  by (induction e arbitrary: ik) (auto simp: Let_def tcast_to_def)

lemma tvars_elab_args: "e \<in> set (elab_args \<rho> \<kappa> fs es) \<Longrightarrow> tvars e \<subseteq> range \<rho>"
  by (induction \<rho> \<kappa> fs es rule: elab_args.induct)
     (auto simp: elaborate_syn_def dest: subsetD [OF tvars_elaborate])

lemma escoped_intro:
  assumes "tvars e \<subseteq> range (resolve_var \<G> q)" and "source_exp (lower e)"
  shows "escoped \<G> q e"
  unfolding escoped_def in_scope_def
proof
  fix v assume v: "v \<in> tvars e"
  with assms(1) obtain x where x: "v = resolve_var \<G> q x" by blast
  have "var_name v \<in> exp_vnames (lower e)"
    using v by (simp add: exp_vnames_lower)
  with x assms(2) have "x \<noteq> ret_var"
    by (auto simp: source_exp_def)
  with x show "\<exists>x. v = resolve_var \<G> q x \<and> x \<noteq> ret_var" by blast
qed

lemma tscoped_elab_com:
  "wf_source_com \<Pi> (lower_com (elab_com \<G> fm \<kappa> q c)) \<Longrightarrow> tscoped \<G> q (elab_com \<G> fm \<kappa> q c)"
proof (induction c)
  case (Call i dst p es)
  have vars: "\<And>e. e \<in> set (elab_args (resolve_var \<G> q) \<kappa> (map (resolve_var \<G> p) (fm p)) es)
                \<Longrightarrow> tvars e \<subseteq> range (resolve_var \<G> q)"
    by (rule tvars_elab_args)
  from Call have src: "list_all (\<lambda>e. source_exp (lower e))
      (elab_args (resolve_var \<G> q) \<kappa> (map (resolve_var \<G> p) (fm p)) es)"
    and dst: "pred_option (\<lambda>x. x \<noteq> ret_var) dst"
    by (auto simp: list_all_iff option.map_comp comp_def option.map_ident split: option.splits)
  from src vars have "list_all (escoped \<G> q)
      (elab_args (resolve_var \<G> q) \<kappa> (map (resolve_var \<G> p) (fm p)) es)"
    by (simp add: list_all_iff) (blast intro: escoped_intro)
  with dst show ?case
    by (auto simp: in_scope_def option.pred_set)
next
  case (Return i e)
  then show ?case
    by (cases e) (auto intro!: escoped_intro tvars_elaborate)
qed (auto simp: in_scope_def elaborate_syn_def intro!: escoped_intro tvars_elaborate)

lemma tfids_typed_table:
  "tfids (typed_table p ds) = (\<lambda>q. map (resolve_var (declared_global p) q) (prog_formals p q))"
  by (rule ext) (simp add: tfids_def typed_table_def prog_formals_def split: option.split)

lemma typed_proc_eq:
  "typed_proc p ds q d
     = \<lparr>formals = formals d,
        body = lower_com (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d))\<rparr>"
  by (cases d) (simp add: typed_proc_def)

theorem tab_rel_typed_table:
  assumes "wf_source_program (declared_global p) (prog_table (typed_prog p ds))"
  shows "tab_rel (kenv_of ds) (declared_global p) (typed_table p ds) (prog_table (typed_prog p ds))"
  unfolding tab_rel_def
proof (intro allI impI)
  fix q xs b
  assume "typed_table p ds q = Some (xs, b)"
  then obtain d where d: "prog_table p q = Some d"
    and xs: "xs = map (resolve_var (declared_global p) q) (formals d)"
    and b: "b = elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d)"
    by (auto simp: typed_table_def)
  have tq: "prog_table (typed_prog p ds) q = Some \<lparr>formals = formals d, body = lower_com b\<rparr>"
    by (simp add: prog_table_typed_prog d b typed_proc_eq)
  from wf_source_programD(5) [OF assms tq]
  have vf: "list_all (valid_formal (declared_global p)) (formals d)"
    and wfb: "wf_source_com (prog_table (typed_prog p ds)) (lower_com b)"
    by (simp_all add: wf_proc_decl_def)
  have "xs = map (ScopedId q) (formals d)"
    using vf by (auto simp: xs list_all_iff valid_formal_def resolve_var_def)
  moreover have "cok (kenv_of ds) (declared_global p) (typed_table p ds) q b"
    unfolding cok_def tfids_typed_table b
    using wt_tcom_elab_com tscoped_elab_com [OF wfb [unfolded b]] by blast
  ultimately show "\<exists>ys. xs = map (ScopedId q) ys \<and> list_all (valid_formal (declared_global p)) ys \<and>
      prog_table (typed_prog p ds) q = Some \<lparr>formals = ys, body = lower_com b\<rparr> \<and>
      cok (kenv_of ds) (declared_global p) (typed_table p ds) q b"
    using vf tq by blast
qed

text \<open>The entry procedure of the typed program, and the lowered store a typed initial
  store corresponds to.\<close>

definition typed_main :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> unit tcom" where
  "typed_main p ds =
     elab_com (declared_global p) (prog_formals p) (kenv_of ds) prog_main_name (main_body (prog_table p))"

lemma typed_main_table:
  assumes "wf_source_program (declared_global p) (prog_table (typed_prog p ds))"
  shows "typed_table p ds prog_main_name = Some ([], typed_main p ds)"
    and "main_body (prog_table (typed_prog p ds)) = lower_com (typed_main p ds)"
proof -
  from wf_source_programD(2) [OF assms]
  obtain d where d: "prog_table p prog_main_name = Some d" and f: "formals d = []"
    and mb: "main_body (prog_table (typed_prog p ds))
               = lower_com (elab_com (declared_global p) (prog_formals p) (kenv_of ds)
                   prog_main_name (body d))"
    by (auto simp: prog_table_typed_prog typed_proc_eq)
  have "main_body (prog_table p) = body d" by (simp add: main_body_def d)
  with d f mb show "typed_table p ds prog_main_name = Some ([], typed_main p ds)"
      and "main_body (prog_table (typed_prog p ds)) = lower_com (typed_main p ds)"
    by (simp_all add: typed_table_def typed_main_def)
qed

definition lowered_store :: "(vname \<Rightarrow> bool) \<Rightarrow> pname \<Rightarrow> tstore \<Rightarrow> store" where
  "lowered_store \<G> q t x = (if x = ret_var then t (ReturnId q) else t (resolve_var \<G> q x))"

theorem tinit_sim:
  assumes "t0 \<in> tinit_stores \<kappa>" and "\<not> \<G> ret_var"
    and "T prog_main_name = Some ([], c0)" and "tab_rel \<kappa> \<G> T \<Pi>"
  shows "lowered_store \<G> prog_main_name t0 \<in> cinit_stores \<G>"
    and "sim \<kappa> \<G> T (c0, t0, []) (lower_com c0, lowered_store \<G> prog_main_name t0, [])"
proof -
  from assms(1) have ty: "styped \<kappa> t0" and gl: "\<And>x. t0 (GlobalId x) = 0"
    by (simp_all add: tinit_stores_def)
  show "lowered_store \<G> prog_main_name t0 \<in> cinit_stores \<G>"
    using assms(2) by (auto simp: cinit_stores_def lowered_store_def resolve_var_def gl)
  from assms(3,4) have "cok \<kappa> \<G> T prog_main_name c0"
    unfolding tab_rel_def by blast
  then have "tok \<kappa> \<G> T [prog_main_name] c0" by (rule tok.base)
  moreover have "srel \<kappa> \<G> prog_main_name t0 (lowered_store \<G> prog_main_name t0)"
    using stypedD [OF ty] by (simp add: srel_def lowered_store_def)
  ultimately show "sim \<kappa> \<G> T (c0, t0, []) (lower_com c0, lowered_store \<G> prog_main_name t0, [])"
    by (simp add: sim_def activations_def)
qed

end
