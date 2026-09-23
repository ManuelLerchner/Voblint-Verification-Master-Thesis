theory VIMP_Proc
  imports VIMP_Special "HOL-IMP.Star"
begin

section \<open>Procedure commands and activation frames\<close>

text \<open>
  A call evaluates its actuals in the caller store, binds them in a fresh
  activation, and pushes a frame holding the caller store and the optional
  destination. \<open>Restore\<close> and \<open>Unwind\<close> never occur in source programs:
  \<open>Restore\<close> marks the activation boundary inside sequential syntax, and
  \<open>Unwind\<close> is the state after a \<open>Return\<close> has published its value through
  \<open>ret_var\<close>, discarding pending commands up to the nearest \<open>Restore\<close>.
\<close>

datatype com =
    SKIP
  | Assign (assign_var: vname) (assign_rhs: exp)
  | Check  (check_cond: exp)
  | Seq    (seq_first: com) (seq_second: com)
  | If     (if_cond: exp) (if_then: com) (if_else: com)
  | While  (while_cond: exp) (while_body: com)
  | Call   (call_dest: "vname option") (call_proc: pname) (call_args: "exp list")
  | Return (return_val: "exp option")
  | Restore
  | Unwind

text \<open>Activation -- fresh locals and formal binding -- happens at the call site,
  so a declaration records only what a call site looks up by name.\<close>
record proc_decl =
  formals :: "vname list"
  body    :: com

text \<open>The reserved local \<open>ret_var\<close> carries a published result to the restore
  boundary. It is absent from source programs, so a value-less completion
  leaves it at \<open>enter_state\<close>'s zero.\<close>
definition ret_var :: vname where
  "ret_var = STR ''#ret''"

type_synonym proc_table = "pname \<Rightarrow> proc_decl option"

datatype frame = Frame (frame_store: store) (frame_dest: "vname option")

text \<open>Formal binding is the same fold over the concrete store and over every
  abstract state, so it is one polymorphic abbreviation.\<close>
abbreviation bind_formals :: "vname list \<Rightarrow> 'v list \<Rightarrow> (vname \<Rightarrow> 'v) \<Rightarrow> vname \<Rightarrow> 'v" where
  "bind_formals xs vs s \<equiv> fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

text \<open>Whole procedure entry, for the same reason: reset every local to a chosen
  value, keep the globals, then bind the formals to the actuals evaluated in the
  caller's own state. Which state and which evaluator is all that separates the
  concrete entry from an abstract one -- the concrete semantics runs it at
  \<^const>\<open>aval\<close> and the reset value \<open>0\<close>, an abstract domain at its own
  evaluator and its own \<open>top\<close> -- so it is one definition, not a concrete one
  with an \<open>_abs\<close> copy beside it.\<close>
definition enter_binding ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> (exp \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> 'a)
   \<Rightarrow> vname list \<Rightarrow> exp list \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> (vname \<Rightarrow> 'a)"
where
  "enter_binding \<G> reset_val ev xs es s =
     bind_formals xs (map (\<lambda>e. ev e s) es) (enter_frame \<G> reset_val s)"

text \<open>The concrete instance, spelled out: this is the equation that lets a
  soundness statement about the shared constant be read as one about the entry
  store the source semantics actually builds.\<close>
lemma enter_binding_concrete:
  "enter_binding \<G> 0 aval xs es s
     = bind_formals xs (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) es) (enter_state \<G> s)"
  by (simp add: enter_binding_def enter_state_def)

text \<open>The return-slot write is a pure per-variable update, generic in the codomain:
  the concrete VIMP semantics uses it at \<open>store = vname \<Rightarrow> int\<close>, and every abstract
  domain's own \<open>vname \<Rightarrow> 'a\<close> state reuses the same definition rather than restating
  an \<open>_abs\<close> copy of it.\<close>
fun combine_assign :: "vname option \<Rightarrow> 'a \<Rightarrow> (vname \<Rightarrow> 'a) \<Rightarrow> (vname \<Rightarrow> 'a)" where
  "combine_assign None _ s = s"
| "combine_assign (Some x) v s = s(x := v)"

subsection \<open>Frame-stack small-step semantics\<close>

text \<open>The reference semantics every soundness claim is ultimately about.  A configuration is
  a command, a store, and a stack of caller frames; a call pushes one frame and continues in
  the callee body followed by \<open>Restore\<close>, a return writes the return slot and hands control to
  \<open>Unwind\<close>, which discards the rest of the callee body until that \<open>Restore\<close> pops the frame.
  \<open>Restore\<close> and \<open>Unwind\<close> exist only here, in configurations the semantics builds; no source
  program contains them.\<close>
inductive
  pstep :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                       \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p/ _)" [51, 51, 51, 51] 50)
  for \<G> :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
where
  Assign:  "\<G>, \<Pi> \<turnstile> (Assign x a, s, frs) \<rightarrow>\<^sub>p (SKIP, s(x := \<lbrakk>a\<rbrakk>\<^sub>e s), frs)"
| Check:   "\<G>, \<Pi> \<turnstile> (Check c, s, frs) \<rightarrow>\<^sub>p (SKIP, s, frs)"
| Seq1:    "\<G>, \<Pi> \<turnstile> (Seq SKIP c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| Seq2:    "\<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p (c1', s', frs')
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If b c1 c2, s, frs) \<rightarrow>\<^sub>p (c1, s, frs)"
| IfFalse: "\<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> \<G>, \<Pi> \<turnstile> (If b c1 c2, s, frs) \<rightarrow>\<^sub>p (c2, s, frs)"
| While:   "\<G>, \<Pi> \<turnstile> (While b c, s, frs)
                      \<rightarrow>\<^sub>p (If b (Seq c (While b c)) SKIP, s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state \<G> s)
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call dst p actuals, s, frs)
                 \<rightarrow>\<^sub>p (Seq (body decl) Restore,
                  callee,
                  Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result sc s v
             \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Call (Some x) p actuals, s, frs) \<rightarrow>\<^sub>p (SKIP, s(x := v), frs)"
| RestoreStep:
    "\<G>, \<Pi> \<turnstile> (Restore, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"
| ReturnSome:
    "\<G>, \<Pi> \<turnstile> (Return (Some e), s, frs)
       \<rightarrow>\<^sub>p (Unwind, s(ret_var := \<lbrakk>e\<rbrakk>\<^sub>e s), frs)"
| ReturnNone:
    "\<G>, \<Pi> \<turnstile> (Return None, s, frs) \<rightarrow>\<^sub>p (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq Unwind c2, s, frs) \<rightarrow>\<^sub>p (Unwind, s, frs)"
| UnwindAct:
    "\<G>, \<Pi> \<turnstile> (Seq Unwind Restore, s, Frame fr dst # frs)
       \<rightarrow>\<^sub>p (SKIP, combine_assign dst (s ret_var) (combine_env \<G> fr s), frs)"

abbreviation
  psteps :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
    ("(_,_ \<turnstile>/ _ \<rightarrow>\<^sub>p\<^sup>*/ _)" [51, 51, 51, 51] 50)
where "psteps \<G> \<Pi> x y \<equiv> star (pstep \<G> \<Pi>) x y"

declare pstep.intros [simp, intro]

inductive_cases SkipSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (SKIP, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases AssignSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (Assign x a, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases CheckSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (Check c, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases SeqSE[elim]:
  "\<G>, \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases IfSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (If b c1 c2, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases WhileSE[elim]:
  "\<G>, \<Pi> \<turnstile> (While b c, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases CallSE[elim]:
  "\<G>, \<Pi> \<turnstile> (Call dst p actuals, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases RestoreSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (Restore, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases ReturnSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (Return e, s, frs) \<rightarrow>\<^sub>p cfg"
inductive_cases UnwindSE[elim!]:
  "\<G>, \<Pi> \<turnstile> (Unwind, s, frs) \<rightarrow>\<^sub>p cfg"

lemmas star_pstep_induct =
  star.induct[of "pstep \<G> \<Pi>", split_format(complete), case_names refl step]

subsection \<open>Completing runs\<close>

text \<open>A run completes when it reaches \<open>SKIP\<close> with the frame stack it started
  with; \<open>SKIP\<close> under a non-empty stack is stuck, not finished.\<close>
abbreviation pcompletes :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pcompletes \<G> \<Pi> c s t \<equiv> \<G>, \<Pi> \<turnstile> (c, s, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, [])"

lemma pcompletes_skip: "pcompletes \<G> \<Pi> SKIP s s"
  by (rule star.refl)

lemma pcompletes_assign: "pcompletes \<G> \<Pi> (Assign x a) s (s(x := \<lbrakk>a\<rbrakk>\<^sub>e s))"
  by simp

lemma pcompletes_special_nondet_int:
  "pcompletes \<G> \<Pi> (Call (Some x) special_pname_nondet_int []) s (s(x := v))"
  by (simp add: special_table_def)

lemma psteps_Seq2:
  "\<G>, \<Pi> \<turnstile> (c1, s, frs) \<rightarrow>\<^sub>p\<^sup>* (c1', s', frs')
   \<Longrightarrow> \<G>, \<Pi> \<turnstile> (Seq c1 c2, s, frs) \<rightarrow>\<^sub>p\<^sup>* (Seq c1' c2, s', frs')"
  by (induction rule: star_pstep_induct) (auto intro: star.step)

lemma pcompletes_Seq:
  assumes "pcompletes \<G> \<Pi> c1 s s2" and "pcompletes \<G> \<Pi> c2 s2 t"
  shows "pcompletes \<G> \<Pi> (Seq c1 c2) s t"
  using psteps_Seq2[OF assms(1)] assms(2) by (meson Seq1 star.step star_trans)

lemma pcompletes_IfTrue:
  "truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> pcompletes \<G> \<Pi> c1 s t \<Longrightarrow> pcompletes \<G> \<Pi> (If b c1 c2) s t"
  by (meson IfTrue star.step)

lemma pcompletes_IfFalse:
  "\<not> truthy (\<lbrakk>b\<rbrakk>\<^sub>e s) \<Longrightarrow> pcompletes \<G> \<Pi> c2 s t \<Longrightarrow> pcompletes \<G> \<Pi> (If b c1 c2) s t"
  by (meson IfFalse star.step)

subsection \<open>Frame-stack extension\<close>

text \<open>A step never inspects the frames below the one it works on, so any run stays valid
  with more callers underneath.  This is what lets a proof about a procedure in isolation be
  reused at an arbitrary call depth.\<close>
lemma pstep_frame_extend:
  "\<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p (c', s', frs') \<Longrightarrow>
   \<G>, \<Pi> \<turnstile> (c, s, frs @ extra) \<rightarrow>\<^sub>p (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: pstep.induct)
     auto

lemma psteps_frame_extend:
  "\<G>, \<Pi> \<turnstile> (c, s, frs) \<rightarrow>\<^sub>p\<^sup>* (c', s', frs') \<Longrightarrow>
   \<G>, \<Pi> \<turnstile> (c, s, frs @ extra) \<rightarrow>\<^sub>p\<^sup>* (c', s', frs' @ extra)"
  by (induction rule: star_pstep_induct) (auto intro: pstep_frame_extend star.step)

lemma psteps_frame_mono:
  "\<G>, \<Pi> \<turnstile> (c, s, []) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, []) \<Longrightarrow>
   \<G>, \<Pi> \<turnstile> (c, s, extra) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

subsection \<open>Call completion\<close>

text \<open>Running a whole call in one step of reasoning: a body that finishes under its own
  frame lets the caller resume with the frame popped and the return slot written.  Callers
  use these instead of replaying the \<open>Restore\<close> bookkeeping at every call site.\<close>
lemma combine_env_ret_var_irrelevant [simp]:
  "\<not> \<G> ret_var \<Longrightarrow> combine_env \<G> fr (t(ret_var := v)) = combine_env \<G> fr t"
  by (rule ext) simp

lemma psteps_Seq_Restore_body:
  assumes "\<G>, \<Pi> \<turnstile> (c, s0, [Frame fr dst]) \<rightarrow>\<^sub>p\<^sup>* (SKIP, t', [Frame fr dst])"
  shows "\<G>, \<Pi> \<turnstile> (Seq c Restore, s0, [Frame fr dst])
           \<rightarrow>\<^sub>p\<^sup>* (SKIP, combine_assign dst (t' ret_var) (combine_env \<G> fr t'), [])"
  using psteps_Seq2[OF assms] by (meson Seq1 RestoreStep star.refl star.step star_trans)

lemma pstep_Call:
  assumes "\<Pi> p = Some decl"
      and "length actuals = length (formals decl)"
      and "distinct (formals decl)"
  shows "\<G>, \<Pi> \<turnstile> (Call dst p actuals, s, frs)
           \<rightarrow>\<^sub>p (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s),
            Frame s dst # frs)"
  using assms by (rule Call) (rule refl)+

lemma pstep_Call_parameterless [intro]:
  assumes "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
  shows "\<G>, \<Pi> \<turnstile> (Call dst p [], s, frs) \<rightarrow>\<^sub>p (Seq c Restore, enter_state \<G> s, Frame s dst # frs)"
proof -
  have "\<G>, \<Pi> \<turnstile> (Call dst p [], s, frs)
          \<rightarrow>\<^sub>p (Seq (body (\<lparr>formals = [], body = c\<rparr>)) Restore,
           bind_formals (formals (\<lparr>formals = [], body = c\<rparr>))
             (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) []) (enter_state \<G> s),
           Frame s dst # frs)"
    using assms by (rule pstep_Call) simp_all
  then show ?thesis by simp
qed

text \<open>A value reaches the destination only through an explicit \<open>Return\<close>;
  otherwise the destination receives \<open>ret_var\<close>'s \<open>enter_state\<close> value \<open>0\<close>.\<close>
lemma pcompletes_Call:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and body: "pcompletes \<G> \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>e. \<lbrakk>e\<rbrakk>\<^sub>e s) actuals) (enter_state \<G> s)) t'"
  shows "pcompletes \<G> \<Pi> (Call dst p actuals) s
           (combine_assign dst (t' ret_var) (combine_env \<G> s t'))"
  by (rule star.step, rule pstep_Call[where \<Pi> = \<Pi> and p = p, OF p arity distinct_formals])
     (rule psteps_Seq_Restore_body[OF psteps_frame_mono[OF body]])

lemma pcompletes_Call_parameterless:
  assumes p: "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
      and body: "pcompletes \<G> \<Pi> c (enter_state \<G> s) t'"
  shows "pcompletes \<G> \<Pi> (Call None p []) s (combine_env \<G> s t')"
  using pcompletes_Call[where \<Pi> = \<Pi> and p = p and \<G> = \<G> and actuals = "[]" and dst = None
                          and s = s and t' = t', OF p] body
  by simp

section \<open>Source-program well-formedness\<close>

text \<open>
  Source syntax excludes the runtime markers \<^const>\<open>Restore\<close> and
  \<^const>\<open>Unwind\<close>. The reserved \<^const>\<open>ret_var\<close> belongs to the
  call mechanism, so source expressions, assignments, destinations, and formal
  parameters cannot mention it.
\<close>

subsection \<open>Finite syntactic variable sets\<close>

fun exp_vnames :: "exp \<Rightarrow> vname set" where
  "exp_vnames (N _) = {}"
| "exp_vnames (V x) = {x}"
| "exp_vnames (Plus a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Minus a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Times a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Div a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Mod a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Less a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (LessEq a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Greater a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (GreaterEq a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (NotEq a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Eq a b) = exp_vnames a \<union> exp_vnames b"
| "exp_vnames (Not b) = exp_vnames b"
| "exp_vnames (And b1 b2) = exp_vnames b1 \<union> exp_vnames b2"
| "exp_vnames (Or b1 b2) = exp_vnames b1 \<union> exp_vnames b2"

fun com_vnames :: "com \<Rightarrow> vname set" where
  "com_vnames SKIP = {}"
| "com_vnames (Assign x a) = insert x (exp_vnames a)"
| "com_vnames (Check c) = exp_vnames c"
| "com_vnames (Seq c1 c2) = com_vnames c1 \<union> com_vnames c2"
| "com_vnames (If b c1 c2) =
    exp_vnames b \<union> com_vnames c1 \<union> com_vnames c2"
| "com_vnames (While b c) = exp_vnames b \<union> com_vnames c"
| "com_vnames (Call dst _ actuals) =
    (case dst of None \<Rightarrow> {} | Some x \<Rightarrow> {x}) \<union>
    \<Union> (set (map exp_vnames actuals))"
| "com_vnames (Return e) = (case e of None \<Rightarrow> {} | Some a \<Rightarrow> exp_vnames a)"
| "com_vnames Restore = {}"
| "com_vnames Unwind = {}"

lemma finite_exp_vnames [simp]: "finite (exp_vnames a)"
  by (induction a) auto

lemma finite_com_vnames [simp]: "finite (com_vnames c)"
  by (induction c) (auto split: option.splits)

fun source_com :: "com \<Rightarrow> bool" where
  "source_com SKIP = True"
| "source_com (Assign x a) = True"
| "source_com (Check c) = True"
| "source_com (Seq c1 c2) = (source_com c1 \<and> source_com c2)"
| "source_com (If b c1 c2) = (source_com c1 \<and> source_com c2)"
| "source_com (While b c) = source_com c"
| "source_com (Call dst p actuals) = True"
| "source_com (Return e) = True"
| "source_com Restore = False"
| "source_com Unwind = False"

definition source_pi :: "proc_table \<Rightarrow> bool" where
  "source_pi \<Pi> = (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> source_com (body decl))"

definition source_exp :: "exp \<Rightarrow> bool" where
  "source_exp a \<longleftrightarrow> ret_var \<notin> exp_vnames a"

definition valid_formal :: "(vname \<Rightarrow> bool) \<Rightarrow> vname \<Rightarrow> bool" where
  "valid_formal \<G> x \<longleftrightarrow> \<not> \<G> x \<and> x \<noteq> ret_var"

subsection \<open>Procedure result contract\<close>

text \<open>
  Declarations carry no return-kind annotation. A body is a value provider when
  every syntactic way to finish the body reaches \<^const>\<open>Return\<close> with a value.
  The analysis is conservative: a loop may fall through because its guard may be
  false, and a call resumes normally after its callee completes.
\<close>

fun may_fallthrough :: "com \<Rightarrow> bool" where
  "may_fallthrough SKIP = True"
| "may_fallthrough (Assign _ _) = True"
| "may_fallthrough (Check _) = True"
| "may_fallthrough (Seq c1 c2) = (may_fallthrough c1 \<and> may_fallthrough c2)"
| "may_fallthrough (If _ c1 c2) = (may_fallthrough c1 \<or> may_fallthrough c2)"
| "may_fallthrough (While _ _) = True"
| "may_fallthrough (Call _ _ _) = True"
| "may_fallthrough (Return _) = False"
| "may_fallthrough Restore = False"
| "may_fallthrough Unwind = False"

fun may_return_none :: "com \<Rightarrow> bool" where
  "may_return_none (Seq c1 c2) =
     (may_return_none c1 \<or> (may_fallthrough c1 \<and> may_return_none c2))"
| "may_return_none (If _ c1 c2) = (may_return_none c1 \<or> may_return_none c2)"
| "may_return_none (While _ c) = may_return_none c"
| "may_return_none (Return e) = (e = None)"
| "may_return_none _ = False"

fun may_return_value :: "com \<Rightarrow> bool" where
  "may_return_value (Seq c1 c2) =
     (may_return_value c1 \<or> (may_fallthrough c1 \<and> may_return_value c2))"
| "may_return_value (If _ c1 c2) = (may_return_value c1 \<or> may_return_value c2)"
| "may_return_value (While _ c) = may_return_value c"
| "may_return_value (Return e) = (e \<noteq> None)"
| "may_return_value _ = False"

definition value_providing :: "com \<Rightarrow> bool" where
  "value_providing c \<longleftrightarrow>
     source_com c \<and> \<not> may_fallthrough c \<and>
     \<not> may_return_none c \<and> may_return_value c"

subsection \<open>Commands, declarations, and programs\<close>

text \<open>
  Every call names a declared procedure and supplies one actual per formal. A
  destination requires a value-providing callee; a destination-less call may
  discard a published value. Procedure formals are distinct local names, and the
  distinguished root command contains no return.
\<close>

fun wf_source_com :: "proc_table \<Rightarrow> com \<Rightarrow> bool" where
  "wf_source_com \<Pi> SKIP = True"
| "wf_source_com \<Pi> (Assign x a) = (x \<noteq> ret_var \<and> source_exp a)"
| "wf_source_com \<Pi> (Check c) = source_exp c"
| "wf_source_com \<Pi> (Seq c1 c2) = (wf_source_com \<Pi> c1 \<and> wf_source_com \<Pi> c2)"
| "wf_source_com \<Pi> (If b c1 c2) =
     (source_exp b \<and> wf_source_com \<Pi> c1 \<and> wf_source_com \<Pi> c2)"
| "wf_source_com \<Pi> (While b c) = (source_exp b \<and> wf_source_com \<Pi> c)"
| "wf_source_com \<Pi> (Call dst p actuals) =
     (case special_table p of
        Some desc \<Rightarrow>
          classify_special desc actuals \<noteq> None \<and> list_all source_exp actuals \<and>
          (case dst of None \<Rightarrow> False | Some x \<Rightarrow> x \<noteq> ret_var)
      | None \<Rightarrow>
          (case \<Pi> p of
             None \<Rightarrow> False
           | Some decl \<Rightarrow>
               length actuals = length (formals decl) \<and>
               list_all source_exp actuals \<and>
               (case dst of
                  None \<Rightarrow> True
                | Some x \<Rightarrow> x \<noteq> ret_var \<and> value_providing (body decl))))"
| "wf_source_com \<Pi> (Return e) = (case e of None \<Rightarrow> True | Some a \<Rightarrow> source_exp a)"
| "wf_source_com \<Pi> Restore = False"
| "wf_source_com \<Pi> Unwind = False"

fun no_return :: "com \<Rightarrow> bool" where
  "no_return (Seq c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (If _ c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (While _ c) = no_return c"
| "no_return (Return _) = False"
| "no_return _ = True"

definition wf_proc_decl :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> proc_decl \<Rightarrow> bool" where
  "wf_proc_decl \<G> \<Pi> decl \<longleftrightarrow>
     distinct (formals decl) \<and>
     list_all (valid_formal \<G>) (formals decl) \<and>
     wf_source_com \<Pi> (body decl)"

definition reserved_ret_var :: "(vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "reserved_ret_var \<G> \<longleftrightarrow> \<not> \<G> ret_var"

text \<open>The entry procedure is fixed: a program has exactly one, it is called \<open>main\<close>, and the
  parser rejects formals on it.  Naming it here rather than threading it as a parameter means
  the compiler and its contract take a table and a callee list and nothing else.\<close>
definition prog_main_name :: pname where
  "prog_main_name = STR ''main''"

text \<open>The entry body, looked up rather than passed alongside the table.  The lookup cannot
  fail where \<open>wf_source_program\<close> holds --- its second conjunct is exactly that the entry is
  declared --- so an undeclared entry is an invariant violation, and aborts in generated code
  rather than compiling to a plausible empty program.\<close>
definition main_body :: "proc_table \<Rightarrow> com" where
  "main_body \<Pi> =
     (case \<Pi> prog_main_name of
        Some decl \<Rightarrow> body decl
      | None \<Rightarrow> Code.abort (STR ''main_body: entry procedure not declared'') (\<lambda>_. SKIP))"

text \<open>Deliberately not \<open>[simp]\<close>: \<open>wf_source_program\<close>'s entry conjunct has the shape
  \<open>\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>\<close>, against which
  this rule would rewrite \<open>main_body \<Pi>\<close> to itself.\<close>
definition wf_source_program :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> bool" where
  "wf_source_program \<G> \<Pi> \<longleftrightarrow>
     reserved_ret_var \<G> \<and>
     \<Pi> prog_main_name = Some (\<lparr>formals = [], body = main_body \<Pi>\<rparr>) \<and>
     wf_source_com \<Pi> (main_body \<Pi>) \<and> no_return (main_body \<Pi>) \<and>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> wf_proc_decl \<G> \<Pi> decl) \<and>
     (\<forall>p. \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)"

text \<open>The compiler-input well-formedness defined in the compiler session unfolds
  through this pair before reaching \<^const>\<open>wf_source_com\<close>; every site
  discharging that obligation shares the unfold skeleton, so it is collected
  here and the downstream definition adds itself to the same collection.\<close>
named_theorems wf_compile_input_simps

declare
  wf_proc_decl_def [wf_compile_input_simps]
  wf_source_program_def [wf_compile_input_simps]

lemma wf_source_com_source_com:
  "wf_source_com \<Pi> c \<Longrightarrow> source_com c"
  by (induction c) (auto split: option.splits)

lemma wf_source_programD:
  assumes "wf_source_program \<G> \<Pi>"
  shows "reserved_ret_var \<G>"
    and "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
    and "wf_source_com \<Pi> (main_body \<Pi>)"
    and "no_return (main_body \<Pi>)"
    and "\<Pi> p = Some decl \<Longrightarrow> wf_proc_decl \<G> \<Pi> decl"
    and "\<Pi> p = Some decl \<Longrightarrow> special_table p = None"
    and "source_pi \<Pi>"
    and "source_com (main_body \<Pi>)"
  using assms wf_source_com_source_com
  unfolding wf_source_program_def source_pi_def wf_proc_decl_def by blast+


section \<open>The semantics is inhabited\<close>

text \<open>
  Every theorem above is conditional on a step or a run existing, so this theory ends by
  exhibiting one that exercises the parts most easily got wrong: a procedure call that pushes
  a frame, returns a value, and pops the frame again.  Globals are empty here, so nothing the
  callee wrote survives except the returned value --- which is what has to reach \<open>x\<close>.
\<close>

definition witness_ret1_pi :: proc_table where
  "witness_ret1_pi p =
     (if p = STR ''ret1'' then Some \<lparr>formals = [], body = Return (Some (N 1))\<rparr> else None)"

theorem pcompletes_witness:
  "\<exists>t. pcompletes (\<lambda>_. False) witness_ret1_pi
         (Call (Some (STR ''x'')) (STR ''ret1'') []) s t
     \<and> t (STR ''x'') = 1"
proof -
  let ?\<G> = "\<lambda>_ :: vname. False"
  let ?fr = "[Frame s (Some (STR ''x''))]"
  let ?en = "enter_state ?\<G> s"
  let ?s' = "?en(ret_var := \<lbrakk>N 1\<rbrakk>\<^sub>e ?en)"
  let ?t  = "(combine_env ?\<G> s ?s')(STR ''x'' := \<lbrakk>N 1\<rbrakk>\<^sub>e ?en)"
  have q: "witness_ret1_pi (STR ''ret1'') = Some \<lparr>formals = [], body = Return (Some (N 1))\<rparr>"
    by (simp add: witness_ret1_pi_def)
  have s1: "?\<G>, witness_ret1_pi \<turnstile> (Call (Some (STR ''x'')) (STR ''ret1'') [], s, [])
              \<rightarrow>\<^sub>p (Seq (Return (Some (N 1))) Restore, ?en, ?fr)"
    using q by (rule pstep_Call_parameterless)
  have s2: "?\<G>, witness_ret1_pi \<turnstile> (Seq (Return (Some (N 1))) Restore, ?en, ?fr)
              \<rightarrow>\<^sub>p (Seq Unwind Restore, ?s', ?fr)"
    by (intro Seq2 ReturnSome)
  have s3: "?\<G>, witness_ret1_pi \<turnstile> (Seq Unwind Restore, ?s', ?fr) \<rightarrow>\<^sub>p (SKIP, ?t, [])"
    using UnwindAct[of ?\<G> witness_ret1_pi ?s' s "Some (STR ''x'')" "[]"] by simp
  from s1 s2 s3
  have "pcompletes ?\<G> witness_ret1_pi (Call (Some (STR ''x'')) (STR ''ret1'') []) s ?t"
    by (meson star.refl star.step)
  moreover have "?t (STR ''x'') = 1" by simp
  ultimately show ?thesis by blast
qed

end
