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

fun combine_assign :: "vname option \<Rightarrow> int \<Rightarrow> store \<Rightarrow> store" where
  "combine_assign None _ s = s"
| "combine_assign (Some x) v s = s(x := v)"

subsection \<open>Frame-stack small-step semantics\<close>

inductive
  pstep :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                       \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
  for gs :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
where
  Assign:  "pstep gs \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
| Check:   "pstep gs \<Pi> (Check c, s, frs) (SKIP, s, frs)"
| Seq1:    "pstep gs \<Pi> (Seq SKIP c2, s, frs) (c2, s, frs)"
| Seq2:    "pstep gs \<Pi> (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> pstep gs \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (aval b s) \<Longrightarrow> pstep gs \<Pi> (If b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> truthy (aval b s) \<Longrightarrow> pstep gs \<Pi> (If b c1 c2, s, frs) (c2, s, frs)"
| While:   "pstep gs \<Pi> (While b c, s, frs)
                      (If b (Seq c (While b c)) SKIP, s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. aval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state gs s)
             \<Longrightarrow> pstep gs \<Pi> (Call dst p actuals, s, frs)
                 (Seq (body decl) Restore,
                  callee,
                  Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result sc s v
             \<Longrightarrow> pstep gs \<Pi> (Call (Some x) p actuals, s, frs) (SKIP, s(x := v), frs)"
| RestoreStep:
    "pstep gs \<Pi> (Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign dst (s ret_var) (combine_env gs fr s), frs)"
| ReturnSome:
    "pstep gs \<Pi> (Return (Some e), s, frs)
       (Unwind, s(ret_var := aval e s), frs)"
| ReturnNone:
    "pstep gs \<Pi> (Return None, s, frs) (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> pstep gs \<Pi> (Seq Unwind c2, s, frs) (Unwind, s, frs)"
| UnwindAct:
    "pstep gs \<Pi> (Seq Unwind Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign dst (s ret_var) (combine_env gs fr s), frs)"

abbreviation
  psteps :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps gs \<Pi> x y \<equiv> star (pstep gs \<Pi>) x y"

declare pstep.intros [simp, intro]

inductive_cases SkipSE[elim!]:
  "pstep gs \<Pi> (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:
  "pstep gs \<Pi> (Assign x a, s, frs) cfg"
inductive_cases CheckSE[elim!]:
  "pstep gs \<Pi> (Check c, s, frs) cfg"
inductive_cases SeqSE[elim]:
  "pstep gs \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:
  "pstep gs \<Pi> (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim]:
  "pstep gs \<Pi> (While b c, s, frs) cfg"
inductive_cases CallSE[elim]:
  "pstep gs \<Pi> (Call dst p actuals, s, frs) cfg"
inductive_cases RestoreSE[elim!]:
  "pstep gs \<Pi> (Restore, s, frs) cfg"
inductive_cases ReturnSE[elim!]:
  "pstep gs \<Pi> (Return e, s, frs) cfg"
inductive_cases UnwindSE[elim!]:
  "pstep gs \<Pi> (Unwind, s, frs) cfg"

lemmas star_pstep_induct =
  star.induct[of "pstep gs \<Pi>", split_format(complete), case_names refl step]

subsection \<open>Completing runs\<close>

text \<open>A run completes when it reaches \<open>SKIP\<close> with the frame stack it started
  with; \<open>SKIP\<close> under a non-empty stack is stuck, not finished.\<close>
abbreviation pcompletes :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pcompletes gs \<Pi> c s t \<equiv> psteps gs \<Pi> (c, s, []) (SKIP, t, [])"

lemma pcompletes_skip: "pcompletes gs \<Pi> SKIP s s"
  by (rule star.refl)

lemma pcompletes_assign: "pcompletes gs \<Pi> (Assign x a) s (s(x := aval a s))"
  by simp

lemma pcompletes_special_nondet_int:
  "pcompletes gs \<Pi> (Call (Some x) special_pname_nondet_int []) s (s(x := v))"
  by (simp add: special_table_def)

lemma psteps_Seq2:
  "psteps gs \<Pi> (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> psteps gs \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
  by (induction rule: star_pstep_induct) (auto intro: star.step)

lemma pcompletes_Seq:
  assumes "pcompletes gs \<Pi> c1 s s2" and "pcompletes gs \<Pi> c2 s2 t"
  shows "pcompletes gs \<Pi> (Seq c1 c2) s t"
  using psteps_Seq2[OF assms(1)] assms(2) by (meson Seq1 star.step star_trans)

lemma pcompletes_IfTrue:
  "truthy (aval b s) \<Longrightarrow> pcompletes gs \<Pi> c1 s t \<Longrightarrow> pcompletes gs \<Pi> (If b c1 c2) s t"
  by (meson IfTrue star.step)

lemma pcompletes_IfFalse:
  "\<not> truthy (aval b s) \<Longrightarrow> pcompletes gs \<Pi> c2 s t \<Longrightarrow> pcompletes gs \<Pi> (If b c1 c2) s t"
  by (meson IfFalse star.step)

subsection \<open>Frame-stack extension\<close>

lemma pstep_frame_extend:
  "pstep gs \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   pstep gs \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: pstep.induct)
     auto

lemma psteps_frame_extend:
  "psteps gs \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   psteps gs \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction rule: star_pstep_induct) (auto intro: pstep_frame_extend star.step)

lemma psteps_frame_mono:
  "psteps gs \<Pi> (c, s, []) (SKIP, t, []) \<Longrightarrow>
   psteps gs \<Pi> (c, s, extra) (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

subsection \<open>Call completion\<close>

lemma combine_env_ret_var_irrelevant [simp]:
  "\<not> gs ret_var \<Longrightarrow> combine_env gs fr (t(ret_var := v)) = combine_env gs fr t"
  by (rule ext) simp

lemma psteps_Seq_Restore_body:
  assumes "psteps gs \<Pi> (c, s0, [Frame fr dst]) (SKIP, t', [Frame fr dst])"
  shows "psteps gs \<Pi> (Seq c Restore, s0, [Frame fr dst])
           (SKIP, combine_assign dst (t' ret_var) (combine_env gs fr t'), [])"
  using psteps_Seq2[OF assms] by (meson Seq1 RestoreStep star.refl star.step star_trans)

lemma pstep_Call:
  assumes "\<Pi> p = Some decl"
      and "length actuals = length (formals decl)"
      and "distinct (formals decl)"
  shows "pstep gs \<Pi> (Call dst p actuals, s, frs)
           (Seq (body decl) Restore,
            bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state gs s),
            Frame s dst # frs)"
  using assms by (rule Call) (rule refl)+

lemma pstep_Call_parameterless [intro]:
  assumes "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
  shows "pstep gs \<Pi> (Call dst p [], s, frs) (Seq c Restore, enter_state gs s, Frame s dst # frs)"
proof -
  have "pstep gs \<Pi> (Call dst p [], s, frs)
          (Seq (body (\<lparr>formals = [], body = c\<rparr>)) Restore,
           bind_formals (formals (\<lparr>formals = [], body = c\<rparr>))
             (map (\<lambda>e. aval e s) []) (enter_state gs s),
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
      and body: "pcompletes gs \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state gs s)) t'"
  shows "pcompletes gs \<Pi> (Call dst p actuals) s
           (combine_assign dst (t' ret_var) (combine_env gs s t'))"
  by (rule star.step, rule pstep_Call[where \<Pi> = \<Pi> and p = p, OF p arity distinct_formals])
     (rule psteps_Seq_Restore_body[OF psteps_frame_mono[OF body]])

lemma pcompletes_Call_parameterless:
  assumes p: "\<Pi> p = Some (\<lparr>formals = [], body = c\<rparr>)"
      and body: "pcompletes gs \<Pi> c (enter_state gs s) t'"
  shows "pcompletes gs \<Pi> (Call None p []) s (combine_env gs s t')"
  using pcompletes_Call[where \<Pi> = \<Pi> and p = p and gs = gs and actuals = "[]" and dst = None
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
| "exp_vnames (Less a b) = exp_vnames a \<union> exp_vnames b"
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
  "valid_formal gs x \<longleftrightarrow> \<not> gs x \<and> x \<noteq> ret_var"

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
  "wf_proc_decl gs \<Pi> decl \<longleftrightarrow>
     distinct (formals decl) \<and>
     list_all (valid_formal gs) (formals decl) \<and>
     wf_source_com \<Pi> (body decl)"

definition reserved_ret_var :: "(vname \<Rightarrow> bool) \<Rightarrow> bool" where
  "reserved_ret_var gs \<longleftrightarrow> \<not> gs ret_var"

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
lemma main_body_Some:
  "\<Pi> prog_main_name = Some decl \<Longrightarrow> main_body \<Pi> = body decl"
  by (simp add: main_body_def)

definition wf_source_program :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> bool" where
  "wf_source_program gs \<Pi> \<longleftrightarrow>
     reserved_ret_var gs \<and>
     \<Pi> prog_main_name = Some (\<lparr>formals = [], body = main_body \<Pi>\<rparr>) \<and>
     wf_source_com \<Pi> (main_body \<Pi>) \<and> no_return (main_body \<Pi>) \<and>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> wf_proc_decl gs \<Pi> decl) \<and>
     (\<forall>p. \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)"

text \<open>The compiler-input well-formedness defined in the CFG session unfolds
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
  assumes "wf_source_program gs \<Pi>"
  shows "reserved_ret_var gs"
    and "\<Pi> prog_main_name = Some \<lparr>formals = [], body = main_body \<Pi>\<rparr>"
    and "wf_source_com \<Pi> (main_body \<Pi>)"
    and "no_return (main_body \<Pi>)"
    and "\<Pi> p = Some decl \<Longrightarrow> wf_proc_decl gs \<Pi> decl"
    and "\<Pi> p = Some decl \<Longrightarrow> special_table p = None"
    and "source_pi \<Pi>"
    and "source_com (main_body \<Pi>)"
  using assms wf_source_com_source_com
  unfolding wf_source_program_def source_pi_def wf_proc_decl_def by blast+


section \<open>The semantics is inhabited\<close>

text \<open>
  Every theorem above is conditional on a step or a run existing, so the session ends by
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
  let ?gs = "\<lambda>_ :: vname. False"
  let ?fr = "[Frame s (Some (STR ''x''))]"
  let ?en = "enter_state ?gs s"
  let ?s' = "?en(ret_var := aval (N 1) ?en)"
  let ?t  = "(combine_env ?gs s ?s')(STR ''x'' := aval (N 1) ?en)"
  have q: "witness_ret1_pi (STR ''ret1'') = Some \<lparr>formals = [], body = Return (Some (N 1))\<rparr>"
    by (simp add: witness_ret1_pi_def)
  have s1: "pstep ?gs witness_ret1_pi (Call (Some (STR ''x'')) (STR ''ret1'') [], s, [])
              (Seq (Return (Some (N 1))) Restore, ?en, ?fr)"
    using q by (rule pstep_Call_parameterless)
  have s2: "pstep ?gs witness_ret1_pi (Seq (Return (Some (N 1))) Restore, ?en, ?fr)
              (Seq Unwind Restore, ?s', ?fr)"
    by (intro Seq2 ReturnSome)
  have s3: "pstep ?gs witness_ret1_pi (Seq Unwind Restore, ?s', ?fr) (SKIP, ?t, [])"
    using UnwindAct[of ?gs witness_ret1_pi ?s' s "Some (STR ''x'')" "[]"] by simp
  from s1 s2 s3
  have "pcompletes ?gs witness_ret1_pi (Call (Some (STR ''x'')) (STR ''ret1'') []) s ?t"
    by (meson star.refl star.step)
  moreover have "?t (STR ''x'') = 1" by simp
  ultimately show ?thesis by blast
qed

end
