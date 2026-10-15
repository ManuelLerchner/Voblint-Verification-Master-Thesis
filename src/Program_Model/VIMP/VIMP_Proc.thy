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

  A check carries a label naming where it was written. The semantics never reads
  it; compilation copies it onto the check's edge, and the analysis result lists
  each check under it, so a report can be matched to its source check by label
  instead of by position in a list. The CLI parser writes the line and column of
  the check's \<^verbatim>\<open>__voblint_check\<close> keyword; a program written in Isabelle
  notation carries the placeholder \<open>(0, 0)\<close>.
\<close>

type_synonym check_label = "nat \<times> nat"

text \<open>Every statement carries an annotation \<open>'a\<close>. Source programs written by hand or
  produced by the parser carry \<open>()\<close>; elaboration replaces it with a statement identity.
  The semantics never reads it: a step copies the annotation of the command it reduces
  onto what it leaves behind, so a residual still names the statement it came from. The
  variable and expression payloads are parameters too, so a later resolved or typed
  front end instantiates the same command syntax.\<close>
datatype ('a, 'v, 'e) gcom =
    is_SKIP: SKIP 'a
  | Assign 'a (assign_var: 'v) (assign_rhs: 'e)
  | Check  'a check_label (check_cond: 'e)
  | Seq    (seq_first: "('a, 'v, 'e) gcom") (seq_second: "('a, 'v, 'e) gcom")
  | If     'a (if_cond: 'e) (if_then: "('a, 'v, 'e) gcom") (if_else: "('a, 'v, 'e) gcom")
  | While  'a (while_cond: 'e) (while_body: "('a, 'v, 'e) gcom")
  | Call   'a (call_dest: "'v option") (call_proc: pname) (call_args: "'e list")
  | Return 'a (return_val: "'e option")
  | is_Restore: Restore 'a
  | Unwind 'a

type_synonym 'a acom = "('a, vname, exp) gcom"
type_synonym com = "unit acom"

text \<open>The expressions a command evaluates, as a list for the executable checks.\<close>

fun com_exps :: "('a, 'v, 'e) gcom \<Rightarrow> 'e list" where
  "com_exps (SKIP _) = []"
| "com_exps (Assign _ _ e) = [e]"
| "com_exps (Check _ _ e) = [e]"
| "com_exps (Seq c1 c2) = com_exps c1 @ com_exps c2"
| "com_exps (If _ b c1 c2) = b # com_exps c1 @ com_exps c2"
| "com_exps (While _ b c) = b # com_exps c"
| "com_exps (Call _ _ _ es) = es"
| "com_exps (Return _ e) = (case e of Some e \<Rightarrow> [e] | None \<Rightarrow> [])"
| "com_exps (Restore _) = []"
| "com_exps (Unwind _) = []"

lemma set_com_exps [simp]: "set (com_exps c) = set3_gcom c"
  by (induction c) (auto split: option.splits)

text \<open>The discriminators read as the equations they replace, so automation that used to
  substitute \<open>c = SKIP\<close> still finds the constructor.\<close>
lemma is_SKIP_iff [simp]: "is_SKIP c \<longleftrightarrow> (\<exists>i. c = SKIP i)"
  by (cases c) auto

lemma is_Restore_iff [simp]: "is_Restore c \<longleftrightarrow> (\<exists>i. c = Restore i)"
  by (cases c) auto

text \<open>Activation -- fresh locals and formal binding -- happens at the call site,
  so a declaration records only what a call site looks up by name.\<close>
record ('a, 'v, 'e) gproc_decl =
  formals :: "'v list"
  body    :: "('a, 'v, 'e) gcom"

type_synonym proc_decl = "(unit, vname, exp) gproc_decl"

text \<open>The reserved local \<open>ret_var\<close> carries a published result to the restore
  boundary. It is absent from source programs, so a value-less completion
  leaves it at \<open>enter_state\<close>'s zero.\<close>
definition ret_var :: vname where
  "ret_var = STR ''#ret''"

type_synonym ('a, 'v, 'e) gptable = "pname \<Rightarrow> ('a, 'v, 'e) gproc_decl option"
type_synonym 'a ptable = "('a, vname, exp) gptable"
type_synonym proc_table = "unit ptable"

datatype 'v gframe = Frame (frame_store: "'v \<Rightarrow> int") (frame_dest: "'v option")

type_synonym frame = "vname gframe"

text \<open>Formal binding is the same fold over the concrete store, over every abstract
  state, and over a typed store keyed by variable identities, so it is one
  polymorphic abbreviation.\<close>
abbreviation bind_formals :: "'k list \<Rightarrow> 'v list \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> 'k \<Rightarrow> 'v" where
  "bind_formals xs vs s \<equiv> fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

lemma bind_formals_other:
  "x \<notin> set xs \<Longrightarrow> bind_formals xs vs s x = s x"
proof (induction xs arbitrary: vs s)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases vs) simp_all
qed

text \<open>A semantics without conversion binds each value unchanged.\<close>
lemma bind_formals_map2_ident [simp]:
  "bind_formals xs (map2 (\<lambda>_ v. v) xs vs) s = bind_formals xs vs s"
proof (induction xs arbitrary: vs s)
  case Nil then show ?case by simp
next
  case (Cons y ys)
  then show ?case by (cases vs) simp_all
qed

text \<open>Whole procedure entry, for the same reason: reset every local to a chosen
  value, keep the globals, then bind the formals to the actuals evaluated in the
  caller's own state. Which state and which evaluator is all that separates the
  concrete entry from an abstract one -- the concrete semantics runs it at
  \<^const>\<open>aval\<close> and the reset value \<open>0\<close>, an abstract domain at its own
  evaluator and its own \<open>top\<close> -- so it is one definition, not a concrete one
  with an \<open>_abs\<close> copy beside it.\<close>
definition enter_binding ::
  "('k \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('e \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'a)
   \<Rightarrow> 'k list \<Rightarrow> 'e list \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)"
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
fun combine_assign :: "'k option \<Rightarrow> 'a \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('k \<Rightarrow> 'a)" where
  "combine_assign None _ s = s"
| "combine_assign (Some x) v s = s(x := v)"

subsection \<open>Frame-stack small-step semantics\<close>

text \<open>The reference semantics every soundness claim is ultimately about.  A configuration is
  a command, a store, and a stack of caller frames; a call pushes one frame and continues in
  the callee body followed by \<open>Restore\<close>, a return writes the return slot and hands control to
  \<open>Unwind\<close>, which discards the rest of the callee body until that \<open>Restore\<close> pops the frame.
  \<open>Restore\<close> and \<open>Unwind\<close> exist only here, in configurations the semantics builds; no source
  program contains them.\<close>
text \<open>
  The semantics is stated once for any language whose commands use the generic command
  syntax: \<open>ev\<close> evaluates an expression, \<open>glob\<close> classifies the variables a call keeps,
  \<open>rv\<close> is the return slot (Goblint's single \<^verbatim>\<open>return_varinfo\<close>), and \<open>conv\<close> converts a
  value written to a destination, as Goblint converts a stored value to its target's
  declared type. \<open>conv\<close> takes the destination as an option so that the instance without
  conversion, \<open>\<lambda>_ n. n\<close>, gives back exactly the rules without conversion. A call
  converts each actual to its formal, as an assignment converts to its destination, so
  every entry store holds each formal at its own kind. Elaboration has already
  converted an actual it produced, as CIL does, and there the conversion changes
  nothing. A returned value is converted once, to the caller's destination.
\<close>

locale vimp_sem =
  fixes ev :: "'e \<Rightarrow> ('v \<Rightarrow> int) \<Rightarrow> int"
    and glob :: "'v \<Rightarrow> bool"
    and rv :: 'v
    and conv :: "'v option \<Rightarrow> int \<Rightarrow> int"
begin

inductive gpstep :: "('a, 'v, 'e) gptable
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list
    \<Rightarrow> ('a, 'v, 'e) gcom \<times> ('v \<Rightarrow> int) \<times> 'v gframe list \<Rightarrow> bool"
  for \<Pi> :: "('a, 'v, 'e) gptable"
where
  Assign:  "gpstep \<Pi> (Assign i x a, s, frs) (SKIP i, s(x := conv (Some x) (ev a s)), frs)"
| Check:   "gpstep \<Pi> (Check i l c, s, frs) (SKIP i, s, frs)"
| Seq1:    "gpstep \<Pi> (Seq (SKIP i) c2, s, frs) (c2, s, frs)"
| Seq2:    "gpstep \<Pi> (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> gpstep \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (ev b s) \<Longrightarrow> gpstep \<Pi> (If i b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> truthy (ev b s) \<Longrightarrow> gpstep \<Pi> (If i b c1 c2, s, frs) (c2, s, frs)"
| While:   "gpstep \<Pi> (While i b c, s, frs) (If i b (Seq c (While i b c)) (SKIP i), s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. ev e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) (map2 (\<lambda>x. conv (Some x)) (formals decl) vals)
                           (enter_state glob s)
             \<Longrightarrow> gpstep \<Pi> (Call i dst p actuals, s, frs)
                   (Seq (body decl) (Restore i), callee, Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result ev sc s v
             \<Longrightarrow> gpstep \<Pi> (Call i (Some x) p actuals, s, frs) (SKIP i, s(x := conv (Some x) v), frs)"
| RestoreStep:
    "gpstep \<Pi> (Restore i, s, Frame fr dst # frs)
       (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"
| ReturnSome:
    "gpstep \<Pi> (Return i (Some e), s, frs) (Unwind i, s(rv := ev e s), frs)"
| ReturnNone:
    "gpstep \<Pi> (Return i None, s, frs) (Unwind i, s, frs)"
| UnwindDead:
    "\<not> is_Restore c2 \<Longrightarrow> gpstep \<Pi> (Seq (Unwind i) c2, s, frs) (Unwind i, s, frs)"
| UnwindAct:
    "gpstep \<Pi> (Seq (Unwind j) (Restore i), s, Frame fr dst # frs)
       (SKIP i, combine_assign dst (conv dst (s rv)) (combine_env glob fr s), frs)"

inductive_cases SkipSE[elim!]: "gpstep \<Pi> (SKIP i, s, frs) cfg"
inductive_cases AssignSE[elim!]: "gpstep \<Pi> (Assign i x a, s, frs) cfg"
inductive_cases CheckSE[elim!]: "gpstep \<Pi> (Check i l c, s, frs) cfg"
inductive_cases SeqSE[elim]: "gpstep \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]: "gpstep \<Pi> (If i b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim]: "gpstep \<Pi> (While i b c, s, frs) cfg"
inductive_cases CallSE[elim]: "gpstep \<Pi> (Call i dst p actuals, s, frs) cfg"
inductive_cases RestoreSE[elim!]: "gpstep \<Pi> (Restore i, s, frs) cfg"
inductive_cases ReturnSE[elim!]: "gpstep \<Pi> (Return i e, s, frs) cfg"
inductive_cases UnwindSE[elim!]: "gpstep \<Pi> (Unwind i, s, frs) cfg"

declare gpstep.intros [simp, intro]

end

context vimp_sem
begin

lemmas star_gpstep_induct =
  star.induct[of "gpstep \<Pi>", split_format(complete), case_names refl step]

lemma combine_env_rv_irrelevant [simp]:
  "\<not> glob rv \<Longrightarrow> combine_env glob fr (t(rv := v)) = combine_env glob fr t"
  by (rule ext) simp

lemma psteps_Seq2:
  "star (gpstep \<Pi>) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (gpstep \<Pi>) (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
  by (induction rule: star.induct[of "gpstep \<Pi>", split_format(complete)]) (auto intro: star.step)

end

subsection \<open>Frame-stack extension\<close>

text \<open>A step never inspects the frames below the one it works on, so any run stays valid
  with more callers underneath.  This is what lets a proof about a procedure in isolation be
  reused at an arbitrary call depth.\<close>
context vimp_sem
begin

lemma pstep_frame_extend:
  "gpstep \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   gpstep \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: gpstep.induct)
     auto

lemma psteps_frame_extend:
  "star (gpstep \<Pi>) (c, s, frs) (c', s', frs') \<Longrightarrow>
   star (gpstep \<Pi>) (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction rule: star.induct[of "gpstep \<Pi>", split_format(complete)])
     (auto intro: pstep_frame_extend star.step)

lemma psteps_frame_mono:
  "star (gpstep \<Pi>) (c, s, []) (SKIP i, t, []) \<Longrightarrow>
   star (gpstep \<Pi>) (c, s, extra) (SKIP i, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

end

subsection \<open>Call completion\<close>

text \<open>Running a whole call in one step of reasoning: a body that finishes under its own
  frame lets the caller resume with the frame popped and the return slot written.  Callers
  use these instead of replaying the \<open>Restore\<close> bookkeeping at every call site.\<close>
lemma combine_env_ret_var_irrelevant [simp]:
  "\<not> \<G> ret_var \<Longrightarrow> combine_env \<G> fr (t(ret_var := v)) = combine_env \<G> fr t"
  by (rule ext) simp

context vimp_sem
begin

lemma psteps_Seq_Restore_body:
  assumes "star (gpstep \<Pi>) (c, s0, [Frame fr dst]) (SKIP i, t', [Frame fr dst])"
  shows "star (gpstep \<Pi>) (Seq c (Restore j), s0, [Frame fr dst]) (SKIP j, combine_assign dst (conv dst (t' rv)) (combine_env glob fr t'), [])"
  using psteps_Seq2[OF assms] by (meson Seq1 RestoreStep star.refl star.step star_trans)

lemma pstep_Call:
  assumes "\<Pi> p = Some decl"
      and "length actuals = length (formals decl)"
      and "distinct (formals decl)"
  shows "gpstep \<Pi> (Call i dst p actuals, s, frs) (Seq (body decl) (Restore i),
            bind_formals (formals decl)
              (map2 (\<lambda>x. conv (Some x)) (formals decl) (map (\<lambda>e. ev e s) actuals))
              (enter_state glob s),
            Frame s dst # frs)"
  using assms by (rule Call) (rule refl)+

lemma pstep_Call_parameterless [intro]:
  assumes "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
  shows
    "gpstep \<Pi> (Call i dst p [], s, frs) (Seq c (Restore i), enter_state glob s, Frame s dst # frs)"
proof -
  have "gpstep \<Pi> (Call i dst p [], s, frs) (Seq (body (\<lparr>formals = [], body = c\<rparr>)) (Restore i),
           bind_formals (formals (\<lparr>formals = [], body = c\<rparr>))
             (map2 (\<lambda>x. conv (Some x)) (formals (\<lparr>formals = [], body = c\<rparr>)) (map (\<lambda>e. ev e s) []))
             (enter_state glob s),
           Frame s dst # frs)"
    using assms by (rule pstep_Call) simp_all
  then show ?thesis by simp
qed

end

section \<open>Source-program well-formedness\<close>

text \<open>
  Source syntax excludes the runtime markers \<^const>\<open>Restore\<close> and
  \<^const>\<open>Unwind\<close>. The reserved \<^const>\<open>ret_var\<close> belongs to the
  call mechanism, so source expressions, assignments, destinations, and formal
  parameters cannot mention it.
\<close>

subsection \<open>Finite syntactic variable sets\<close>

fun com_vnames :: "'a acom \<Rightarrow> vname set" where
  "com_vnames (SKIP _) = {}"
| "com_vnames (Assign _ x a) = insert x (exp_vnames a)"
| "com_vnames (Check _ l c) = exp_vnames c"
| "com_vnames (Seq c1 c2) = com_vnames c1 \<union> com_vnames c2"
| "com_vnames (If _ b c1 c2) =
    exp_vnames b \<union> com_vnames c1 \<union> com_vnames c2"
| "com_vnames (While _ b c) = exp_vnames b \<union> com_vnames c"
| "com_vnames (Call _ dst _ actuals) =
    (case dst of None \<Rightarrow> {} | Some x \<Rightarrow> {x}) \<union>
    \<Union> (set (map exp_vnames actuals))"
| "com_vnames (Return _ e) = (case e of None \<Rightarrow> {} | Some a \<Rightarrow> exp_vnames a)"
| "com_vnames (Restore _) = {}"
| "com_vnames (Unwind _) = {}"

lemma finite_com_vnames [simp]: "finite (com_vnames c)"
  by (induction c) (auto split: option.splits)

fun source_com :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "source_com (SKIP _) = True"
| "source_com (Assign _ x a) = True"
| "source_com (Check _ l c) = True"
| "source_com (Seq c1 c2) = (source_com c1 \<and> source_com c2)"
| "source_com (If _ b c1 c2) = (source_com c1 \<and> source_com c2)"
| "source_com (While _ b c) = source_com c"
| "source_com (Call _ dst p actuals) = True"
| "source_com (Return _ e) = True"
| "source_com (Restore _) = False"
| "source_com (Unwind _) = False"

definition source_pi :: "('a, 'v, 'e) gptable \<Rightarrow> bool" where
  "source_pi \<Pi> = (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> source_com (body decl))"

text \<open>Well-formedness is stated once for any language: \<open>vars\<close> gives the variables an
  expression reads, and \<open>rv\<close> is the reserved return slot. The untyped predicates are the
  instances at \<^const>\<open>exp_vnames\<close> and \<^const>\<open>ret_var\<close>.\<close>

definition gsource_exp :: "('e \<Rightarrow> 'v set) \<Rightarrow> 'v \<Rightarrow> 'e \<Rightarrow> bool" where
  "gsource_exp vars rv a \<longleftrightarrow> rv \<notin> vars a"

abbreviation source_exp :: "exp \<Rightarrow> bool" where
  "source_exp \<equiv> gsource_exp exp_vnames ret_var"

definition gvalid_formal :: "'v \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> 'v \<Rightarrow> bool" where
  "gvalid_formal rv \<G> x \<longleftrightarrow> \<not> \<G> x \<and> x \<noteq> rv"

abbreviation valid_formal :: "(vname \<Rightarrow> bool) \<Rightarrow> vname \<Rightarrow> bool" where
  "valid_formal \<equiv> gvalid_formal ret_var"

subsection \<open>Procedure result contract\<close>

text \<open>
  Declarations carry no return-kind annotation. A body is a value provider when
  every syntactic way to finish the body reaches \<^const>\<open>Return\<close> with a value.
  The analysis is conservative: a loop may fall through because its guard may be
  false, and a call resumes normally after its callee completes.
\<close>

fun may_fallthrough :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "may_fallthrough (SKIP _) = True"
| "may_fallthrough (Assign _ _ _) = True"
| "may_fallthrough (Check _ _ _) = True"
| "may_fallthrough (Seq c1 c2) = (may_fallthrough c1 \<and> may_fallthrough c2)"
| "may_fallthrough (If _ _ c1 c2) = (may_fallthrough c1 \<or> may_fallthrough c2)"
| "may_fallthrough (While _ _ _) = True"
| "may_fallthrough (Call _ _ _ _) = True"
| "may_fallthrough (Return _ _) = False"
| "may_fallthrough (Restore _) = False"
| "may_fallthrough (Unwind _) = False"

fun may_return_none :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "may_return_none (Seq c1 c2) =
     (may_return_none c1 \<or> (may_fallthrough c1 \<and> may_return_none c2))"
| "may_return_none (If _ _ c1 c2) = (may_return_none c1 \<or> may_return_none c2)"
| "may_return_none (While _ _ c) = may_return_none c"
| "may_return_none (Return _ e) = (e = None)"
| "may_return_none _ = False"

fun may_return_value :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "may_return_value (Seq c1 c2) =
     (may_return_value c1 \<or> (may_fallthrough c1 \<and> may_return_value c2))"
| "may_return_value (If _ _ c1 c2) = (may_return_value c1 \<or> may_return_value c2)"
| "may_return_value (While _ _ c) = may_return_value c"
| "may_return_value (Return _ e) = (e \<noteq> None)"
| "may_return_value _ = False"

definition value_providing :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
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

fun gwf_source_com ::
    "('e \<Rightarrow> 'v set) \<Rightarrow> 'v \<Rightarrow> ('a, 'v, 'e) gptable \<Rightarrow> ('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "gwf_source_com vars rv \<Pi> (SKIP _) = True"
| "gwf_source_com vars rv \<Pi> (Assign _ x a) = (x \<noteq> rv \<and> gsource_exp vars rv a)"
| "gwf_source_com vars rv \<Pi> (Check _ l c) = gsource_exp vars rv c"
| "gwf_source_com vars rv \<Pi> (Seq c1 c2) = (gwf_source_com vars rv \<Pi> c1 \<and> gwf_source_com vars rv \<Pi> c2)"
| "gwf_source_com vars rv \<Pi> (If _ b c1 c2) =
     (gsource_exp vars rv b \<and> gwf_source_com vars rv \<Pi> c1 \<and> gwf_source_com vars rv \<Pi> c2)"
| "gwf_source_com vars rv \<Pi> (While _ b c) = (gsource_exp vars rv b \<and> gwf_source_com vars rv \<Pi> c)"
| "gwf_source_com vars rv \<Pi> (Call _ dst p actuals) =
     (case special_table p of
        Some desc \<Rightarrow>
          classify_special desc actuals \<noteq> None \<and> list_all (gsource_exp vars rv) actuals \<and>
          (case dst of None \<Rightarrow> False | Some x \<Rightarrow> x \<noteq> rv)
      | None \<Rightarrow>
          (case \<Pi> p of
             None \<Rightarrow> False
           | Some decl \<Rightarrow>
               length actuals = length (formals decl) \<and>
               list_all (gsource_exp vars rv) actuals \<and>
               (case dst of
                  None \<Rightarrow> True
                | Some x \<Rightarrow> x \<noteq> rv \<and> value_providing (body decl))))"
| "gwf_source_com vars rv \<Pi> (Return _ e) = (case e of None \<Rightarrow> True | Some a \<Rightarrow> gsource_exp vars rv a)"
| "gwf_source_com vars rv \<Pi> (Restore _) = False"
| "gwf_source_com vars rv \<Pi> (Unwind _) = False"

abbreviation wf_source_com :: "'a ptable \<Rightarrow> 'a acom \<Rightarrow> bool" where
  "wf_source_com \<equiv> gwf_source_com exp_vnames ret_var"

fun no_return :: "('a, 'v, 'e) gcom \<Rightarrow> bool" where
  "no_return (Seq c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (If _ _ c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (While _ _ c) = no_return c"
| "no_return (Return _ _) = False"
| "no_return _ = True"

definition gwf_proc_decl ::
    "('e \<Rightarrow> 'v set) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a, 'v, 'e) gptable
       \<Rightarrow> ('a, 'v, 'e) gproc_decl \<Rightarrow> bool" where
  "gwf_proc_decl vars rv \<G> \<Pi> decl \<longleftrightarrow>
     distinct (formals decl) \<and>
     list_all (gvalid_formal rv \<G>) (formals decl) \<and>
     gwf_source_com vars rv \<Pi> (body decl)"

abbreviation wf_proc_decl :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a ptable \<Rightarrow> ('a, vname, exp) gproc_decl \<Rightarrow> bool" where
  "wf_proc_decl \<equiv> gwf_proc_decl exp_vnames ret_var"

definition greserved_ret_var :: "'v \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> bool" where
  "greserved_ret_var rv \<G> \<longleftrightarrow> \<not> \<G> rv"

abbreviation reserved_ret_var :: "(vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "reserved_ret_var \<equiv> greserved_ret_var ret_var"

text \<open>The entry procedure is fixed: a program has exactly one, it is called \<open>main\<close>, and the
  parser rejects formals on it.  Naming it here rather than threading it as a parameter means
  the compiler and its contract take a table and a callee list and nothing else.\<close>
definition prog_main_name :: pname where
  "prog_main_name = STR ''main''"

text \<open>The entry body, looked up rather than passed alongside the table.  The lookup cannot
  fail where \<open>wf_source_program\<close> holds --- its second conjunct is exactly that the entry is
  declared --- so an undeclared entry is an invariant violation, and aborts in generated code
  rather than compiling to a plausible empty program.\<close>
definition main_body :: "('a, 'v, 'e) gptable \<Rightarrow> ('a, 'v, 'e) gcom" where
  "main_body \<Pi> =
     (case \<Pi> prog_main_name of
        Some decl \<Rightarrow> body decl
      | None \<Rightarrow> Code.abort (STR ''main_body: entry procedure not declared'') (\<lambda>_. SKIP undefined))"

text \<open>Deliberately not \<open>[simp]\<close>: \<open>wf_source_program\<close>'s entry conjunct has the shape
  \<open>\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>\<close>, against which
  this rule would rewrite \<open>main_body \<Pi>\<close> to itself.\<close>
definition gwf_source_program ::
    "('e \<Rightarrow> 'v set) \<Rightarrow> 'v \<Rightarrow> ('v \<Rightarrow> bool) \<Rightarrow> ('a, 'v, 'e) gptable \<Rightarrow> bool" where
  "gwf_source_program vars rv \<G> \<Pi> \<longleftrightarrow>
     greserved_ret_var rv \<G> \<and>
     \<Pi> prog_main_name = Some (\<lparr>formals = [], body = main_body \<Pi>\<rparr>) \<and>
     gwf_source_com vars rv \<Pi> (main_body \<Pi>) \<and> no_return (main_body \<Pi>) \<and>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> gwf_proc_decl vars rv \<G> \<Pi> decl) \<and>
     (\<forall>p. \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)"

abbreviation wf_source_program :: "(vname \<Rightarrow> bool) \<Rightarrow> 'a ptable \<Rightarrow> bool" where
  "wf_source_program \<equiv> gwf_source_program exp_vnames ret_var"

text \<open>The compiler-input well-formedness defined in the compiler session unfolds
  through this pair before reaching \<^const>\<open>wf_source_com\<close>; every site
  discharging that obligation shares the unfold skeleton, so it is collected
  here and the downstream definition adds itself to the same collection.\<close>
named_theorems wf_compile_input_simps

declare
  gwf_proc_decl_def [wf_compile_input_simps]
  gwf_source_program_def [wf_compile_input_simps]

lemma wf_source_com_source_com:
  "gwf_source_com vars rv \<Pi> c \<Longrightarrow> source_com c"
  by (induction c) (auto split: option.splits)

lemma wf_source_programD:
  assumes "gwf_source_program vars rv \<G> \<Pi>"
  shows "greserved_ret_var rv \<G>"
    and "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
    and "gwf_source_com vars rv \<Pi> (main_body \<Pi>)"
    and "no_return (main_body \<Pi>)"
    and "\<Pi> p = Some decl \<Longrightarrow> gwf_proc_decl vars rv \<G> \<Pi> decl"
    and "\<Pi> p = Some decl \<Longrightarrow> special_table p = None"
    and "source_pi \<Pi>"
    and "source_com (main_body \<Pi>)"
  using assms wf_source_com_source_com [of vars rv \<Pi>]
  unfolding gwf_source_program_def source_pi_def gwf_proc_decl_def by blast+

end
