theory VIMP_Proc
  imports VIMP_Expr VIMP_Globals VIMP_Special VIMP_Typing
begin

section \<open>Procedure commands and activation frames\<close>

text \<open>
  A call evaluates actual arguments in the caller store, binds them in a fresh
  callee activation, and saves the caller store with the optional destination.
  The runtime marker \<open>Restore\<close> identifies the activation boundary inside
  sequential syntax. An explicit \<open>Return\<close> publishes its value through
  \<open>ret_var\<close> and replaces pending callee commands with \<open>Unwind\<close>.
  Restoration keeps callee globals, restores caller locals, and writes the
  published value when the call has a destination.

  \<open>Return\<close> is the source-level early return. It publishes an optional
  value into \<open>ret_var\<close> and unwinds the current activation.
  \<open>Unwind\<close> is a runtime-only marker (like \<open>Restore\<close>, never in source
  programs): once a \<open>Return\<close> has fired, the computation is in \<open>Unwind\<close>
  state, discarding pending statements up to the nearest enclosing activation frame.
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

text \<open>A procedure's declared formals and body -- deliberately thin: activation
  (fresh locals, formal argument binding) happens at the call site via
  \<^const>\<open>enter_state\<close> plus argument evaluation, not as a field here.
  \<open>proc_decl\<close> only records what a call site looks up by name.\<close>
record proc_decl =
  formals :: "vname list"
  body    :: com

definition proc_decl_of :: "vname list => com => proc_decl" where
  "proc_decl_of xs bdy = \<lparr>formals = xs, body = bdy\<rparr>"

text \<open>
  The reserved local \<open>ret_var\<close> carries a published result to the restore
  boundary. It is absent from source programs and local to the callee activation.
  A value-less fall-through therefore leaves it at the initial value zero.
\<close>
definition ret_var :: vname where
  "ret_var = STR ''#ret''"

datatype source_location =
    LocalVar pname
  | GlobalVar

(* Procedure table: names to declarations. *)
type_synonym proc_table = "pname \<Rightarrow> proc_decl option"

(* Runtime frame: the caller's store and the optional destination variable. *)
datatype frame = Frame (frame_store: store) (frame_dest: "vname option")

definition bind_formals :: "vname list \<Rightarrow> int list \<Rightarrow> store \<Rightarrow> store" where
  "bind_formals xs vs s =
     fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

text \<open>
  \<open>combine_assign\<close> writes the published value when a destination exists,
  normed to the destination's kind \<comment> \<open>the conversion an assignment of
  the call result performs.\<close> A destination-less call discards the value and
  leaves the caller store unchanged.
\<close>
fun combine_assign :: "tyenv \<Rightarrow> vname option \<Rightarrow> int \<Rightarrow> store \<Rightarrow> store" where
  "combine_assign \<Gamma> None _ s = s"
| "combine_assign \<Gamma> (Some x) v s = s(x := ik_norm (\<Gamma> x) v)"

(* -- Frame-stack small-step ----------------------------------------- *)

text \<open>
  Every write is converted to its target's kind: an assignment and the
  reserved \<open>ret_var\<close> slot evaluate at the target variable's kind, an
  actual argument at its formal's kind, and a special call's destination
  norms the produced value. A branch condition evaluates at its own
  synthesized kind (\<open>taval_syn\<close>). The typing environment is a
  parameter of the relation, exactly as the globals classifier is.
\<close>

inductive
  pstep :: "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                       \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
  for \<Gamma> :: tyenv and gs :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
where
  Assign:  "pstep \<Gamma> gs \<Pi> (Assign x a, s, frs) (SKIP, s(x := taval \<Gamma> (\<Gamma> x) a s), frs)"
| Check:   "pstep \<Gamma> gs \<Pi> (Check c, s, frs) (SKIP, s, frs)"
| Seq1:    "pstep \<Gamma> gs \<Pi> (Seq SKIP c2, s, frs) (c2, s, frs)"
| Seq2:    "pstep \<Gamma> gs \<Pi> (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> pstep \<Gamma> gs \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "truthy (taval_syn \<Gamma> b s) \<Longrightarrow> pstep \<Gamma> gs \<Pi> (If b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> truthy (taval_syn \<Gamma> b s) \<Longrightarrow> pstep \<Gamma> gs \<Pi> (If b c1 c2, s, frs) (c2, s, frs)"
| While:   "pstep \<Gamma> gs \<Pi> (While b c, s, frs)
                      (If b (Seq c (While b c)) SKIP, s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) (formals decl) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state gs s)
             \<Longrightarrow> pstep \<Gamma> gs \<Pi> (Call dst p actuals, s, frs)
                 (Seq (body decl) Restore,
                  callee,
                  Frame s dst # frs)"
| Special: "special_table p = Some desc
             \<Longrightarrow> classify_special desc actuals = Some sc
             \<Longrightarrow> special_result \<Gamma> sc s v
             \<Longrightarrow> pstep \<Gamma> gs \<Pi> (Call (Some x) p actuals, s, frs)
                 (SKIP, s(x := ik_norm (\<Gamma> x) v), frs)"
| RestoreStep:
    "pstep \<Gamma> gs \<Pi> (Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign \<Gamma> dst (s ret_var) (combine_env gs fr s), frs)"
| ReturnSome:
    "pstep \<Gamma> gs \<Pi> (Return (Some e), s, frs)
       (Unwind, s(ret_var := taval \<Gamma> (\<Gamma> ret_var) e s), frs)"
| ReturnNone:
    "pstep \<Gamma> gs \<Pi> (Return None, s, frs) (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> pstep \<Gamma> gs \<Pi> (Seq Unwind c2, s, frs) (Unwind, s, frs)"
| UnwindAct:
    "pstep \<Gamma> gs \<Pi> (Seq Unwind Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign \<Gamma> dst (s ret_var) (combine_env gs fr s), frs)"

abbreviation
  psteps :: "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps \<Gamma> gs \<Pi> x y \<equiv> star (pstep \<Gamma> gs \<Pi>) x y"

declare pstep.intros [simp, intro]
declare pstep.Seq2[simp del]

inductive_cases SkipSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (Assign x a, s, frs) cfg"
inductive_cases CheckSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (Check c, s, frs) cfg"
inductive_cases SeqSE[elim]:
  "pstep \<Gamma> gs \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim]:
  "pstep \<Gamma> gs \<Pi> (While b c, s, frs) cfg"
inductive_cases CallSE[elim]:
  "pstep \<Gamma> gs \<Pi> (Call dst p actuals, s, frs) cfg"
inductive_cases RestoreSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (Restore, s, frs) cfg"
inductive_cases ReturnSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (Return e, s, frs) cfg"
inductive_cases UnwindSE[elim!]:
  "pstep \<Gamma> gs \<Pi> (Unwind, s, frs) cfg"

(* Structured induction over pstep-runs: split_format states each case on the
   (c, s, frs) components rather than an anonymous configuration product. *)
lemmas star_pstep_induct =
  star.induct[of "pstep \<Gamma> gs \<Pi>", split_format(complete), case_names refl step]

lemma bind_formals_nonformal:
  assumes "x \<notin> set xs"
  shows "bind_formals xs vs s x = s x"
  using assms
proof (induction xs arbitrary: vs s)
  case Nil
  then show ?case
    by (simp add: bind_formals_def)
next
  case (Cons y ys)
  then show ?case
    by (cases vs) (auto simp: bind_formals_def)
qed

(* -- Successful termination ----------------------------------------- *)

text \<open>
  Concrete Semantics calls a configuration final when no small step applies; for
  IMP that coincides with SKIP. Here configurations carry a frame stack, so
  stuckness at SKIP with a non-empty stack is not a successful end.
  \<^term>\<open>pfinal\<close> is the good exit: command finished and frames balanced.
\<close>

fun pfinal :: "com \<times> store \<times> frame list \<Rightarrow> bool" where
  "pfinal (c, s, frs) = (c = SKIP \<and> frs = [])"

definition pcompletes :: "tyenv \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pcompletes \<Gamma> gs \<Pi> c s t = psteps \<Gamma> gs \<Pi> (c, s, []) (SKIP, t, [])"

lemma pcompletes_iff_small_termination[simp]:
  "pcompletes \<Gamma> gs \<Pi> c s t \<longleftrightarrow>
     (\<exists>cfg. psteps \<Gamma> gs \<Pi> (c, s, []) cfg \<and> pfinal cfg \<and> fst (snd cfg) = t)"
  unfolding pcompletes_def by auto

lemma pcompletes_skip: "pcompletes \<Gamma> gs \<Pi> SKIP s s"
  unfolding pcompletes_def by (rule star.refl)

lemma pcompletes_assign:
  "pcompletes \<Gamma> gs \<Pi> (Assign x a) s (s(x := taval \<Gamma> (\<Gamma> x) a s))"
  by (simp add: pcompletes_def)

lemma pcompletes_special_nondet_int:
  "pcompletes \<Gamma> gs \<Pi> (Call (Some x) special_pname_nondet_int []) s
     (s(x := ik_norm (\<Gamma> x) v))"
  by (simp add: pcompletes_def special_table_def)

lemma pcompletes_check: "pcompletes \<Gamma> gs \<Pi> (Check c) s s"
  by (simp add: pcompletes_def)

(* -- Sequencing lifts through the small-step --------------------------- *)

lemma psteps_Seq2:
  "star (pstep \<Gamma> gs \<Pi>) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (pstep \<Gamma> gs \<Pi>) (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
proof (induction rule: star_pstep_induct)
  case refl show ?case by (rule star.refl)
next
  case step then show ?case by (meson Seq2 star.step)
qed

(* -- Structural composition of terminating runs ---------------------- *)

lemma pcompletes_Seq:
  assumes "pcompletes \<Gamma> gs \<Pi> c1 s s2" and "pcompletes \<Gamma> gs \<Pi> c2 s2 t"
  shows "pcompletes \<Gamma> gs \<Pi> (Seq c1 c2) s t"
proof -
  from assms(1) have a: "star (pstep \<Gamma> gs \<Pi>) (Seq c1 c2, s, []) (Seq SKIP c2, s2, [])"
    unfolding pcompletes_def by (rule psteps_Seq2)
  have b: "pstep \<Gamma> gs \<Pi> (Seq SKIP c2, s2, []) (c2, s2, [])" by (rule Seq1)
  from a b assms(2) show ?thesis
    unfolding pcompletes_def by (meson star.step star_trans)
qed

lemma pcompletes_IfTrue:
  "truthy (taval_syn \<Gamma> b s) \<Longrightarrow> pcompletes \<Gamma> gs \<Pi> c1 s t
   \<Longrightarrow> pcompletes \<Gamma> gs \<Pi> (If b c1 c2) s t"
  unfolding pcompletes_def by (meson IfTrue star.step)

lemma pcompletes_IfFalse:
  "\<not> truthy (taval_syn \<Gamma> b s) \<Longrightarrow> pcompletes \<Gamma> gs \<Pi> c2 s t
   \<Longrightarrow> pcompletes \<Gamma> gs \<Pi> (If b c1 c2) s t"
  unfolding pcompletes_def by (meson IfFalse star.step)

lemma pcompletes_WhileFalse:
  "\<not> truthy (taval_syn \<Gamma> b s) \<Longrightarrow> pcompletes \<Gamma> gs \<Pi> (While b c) s s"
  unfolding pcompletes_def by (meson While IfFalse star.refl star.step)

lemma pcompletes_WhileTrue:
  assumes b:    "truthy (taval_syn \<Gamma> b s)"
      and body: "pcompletes \<Gamma> gs \<Pi> c s s2"
      and rest: "pcompletes \<Gamma> gs \<Pi> (While b c) s2 t"
  shows "pcompletes \<Gamma> gs \<Pi> (While b c) s t"
proof -
  have seq: "pcompletes \<Gamma> gs \<Pi> (Seq c (While b c)) s t"
    using body rest by (rule pcompletes_Seq)
  have w: "pstep \<Gamma> gs \<Pi> (While b c, s, [])
                    (If b (Seq c (While b c)) SKIP, s, [])"
    by (rule While)
  have i: "pstep \<Gamma> gs \<Pi> (If b (Seq c (While b c)) SKIP, s, [])
                    (Seq c (While b c), s, [])"
    using b by (rule IfTrue)
  from w i seq show ?thesis unfolding pcompletes_def by (meson star.step)
qed

(* -- Frame-stack extension ------------------------------------------ *)

lemma pstep_frame_extend:
  "pstep \<Gamma> gs \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   pstep \<Gamma> gs \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: pstep.induct)
     auto

lemma psteps_frame_extend:
  "psteps \<Gamma> gs \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   psteps \<Gamma> gs \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
proof (induction rule: star_pstep_induct)
  case refl show ?case by (rule star.refl)
next
  case step then show ?case by (meson pstep_frame_extend star.step)
qed

lemma psteps_frame_mono:
  "psteps \<Gamma> gs \<Pi> (c, s, []) (SKIP, t, []) \<Longrightarrow>
   psteps \<Gamma> gs \<Pi> (c, s, extra) (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

(* -- Call termination ------------------------------------- *)

(* The restore rule pops a call frame: the destination
   rides in the frame and the value in ret_var. *)
lemma psteps_Seq_Restore_body:
  assumes "psteps \<Gamma> gs \<Pi> (c, s0, [Frame fr dst]) (SKIP, t', [Frame fr dst])"
  shows "psteps \<Gamma> gs \<Pi> (Seq c Restore, s0, [Frame fr dst])
           (SKIP, combine_assign \<Gamma> dst (t' ret_var) (combine_env gs fr t'), [])"
proof -
  have body_seq:
    "psteps \<Gamma> gs \<Pi> (Seq c Restore, s0, [Frame fr dst])
       (Seq SKIP Restore, t', [Frame fr dst])"
    using psteps_Seq2[OF assms] .
  have step_seq1:
    "pstep \<Gamma> gs \<Pi> (Seq SKIP Restore, t', [Frame fr dst])
       (Restore, t', [Frame fr dst])"
    by (rule Seq1)
  have step_restore:
    "pstep \<Gamma> gs \<Pi> (Restore, t', [Frame fr dst])
       (SKIP, combine_assign \<Gamma> dst (t' ret_var) (combine_env gs fr t'), [])"
    by (rule RestoreStep)
  have tail:
    "psteps \<Gamma> gs \<Pi> (Seq SKIP Restore, t', [Frame fr dst])
       (SKIP, combine_assign \<Gamma> dst (t' ret_var) (combine_env gs fr t'), [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  show ?thesis using body_seq tail by (rule star_trans)
qed

lemma combine_env_ret_var_irrelevant [simp]:
  "\<not> gs ret_var \<Longrightarrow> combine_env gs fr (t(ret_var := v)) = combine_env gs fr t"
  by (rule ext) simp


text \<open>A completing body drives a call to completion: the callee body runs on the fresh activation,
  then the \<^const>\<open>Restore\<close> pops the frame, keeping callee globals and restoring caller locals, and
  \<^const>\<open>combine_assign\<close> writes the callee's \<^const>\<open>ret_var\<close> to the destination (or discards it for a
  value-less call).  A value is published only if an explicit \<^const>\<open>Return\<close> wrote \<^const>\<open>ret_var\<close>;
  otherwise the destination receives its \<^const>\<open>enter_state\<close> initial 0.\<close>
lemma pcompletes_Call:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and body: "pcompletes \<Gamma> gs \<Pi> (body decl)
                   (bind_formals (formals decl)
                     (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) (formals decl) actuals)
                     (enter_state gs s)) t'"
  shows "pcompletes \<Gamma> gs \<Pi> (Call dst p actuals) s
           (combine_assign \<Gamma> dst (t' ret_var) (combine_env gs s t'))"
  unfolding pcompletes_def
proof (rule star.step)
  let ?vals = "map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) (formals decl) actuals"
  let ?callee = "bind_formals (formals decl) ?vals (enter_state gs s)"
  show "pstep \<Gamma> gs \<Pi> (Call dst p actuals, s, [])
          (Seq (body decl) Restore, ?callee, [Frame s dst])"
    using p arity distinct_formals
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Gamma> gs \<Pi> (body decl, ?callee, [Frame s dst]) (SKIP, t', [Frame s dst])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s dst]"] by simp
  show "psteps \<Gamma> gs \<Pi> (Seq (body decl) Restore, ?callee, [Frame s dst])
          (SKIP, combine_assign \<Gamma> dst (t' ret_var) (combine_env gs s t'), [])"
    using psteps_Seq_Restore_body[OF framed] by simp
qed

text \<open>A value-less fall-through with a destination reads the callee's \<open>ret_var\<close>, which
  \<^const>\<open>enter_state\<close> initialises to 0 and the body never wrote: the destination gets 0, never a
  stale caller or callee value.\<close>
lemma pcompletes_Call_dst_fallthrough_zero:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and body: "pcompletes \<Gamma> gs \<Pi> (body decl)
                   (bind_formals (formals decl)
                     (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) (formals decl) actuals)
                     (enter_state gs s)) t'"
      and fallthrough: "t' ret_var = 0"
  shows "pcompletes \<Gamma> gs \<Pi> (Call (Some x) p actuals) s ((combine_env gs s t')(x := 0))"
  using pcompletes_Call[OF p arity distinct_formals body, where dst = "Some x"] fallthrough
  by simp

lemma pcompletes_Call_parameterless:
  assumes p: "\<Pi> p = Some (proc_decl_of [] c)"
      and body: "pcompletes \<Gamma> gs \<Pi> c (enter_state gs s) t'"
  shows "pcompletes \<Gamma> gs \<Pi> (Call None p []) s (combine_env gs s t')"
proof -
  have "pcompletes \<Gamma> gs \<Pi> (Call None p []) s
          (combine_assign \<Gamma> None (t' ret_var) (combine_env gs s t'))"
  proof (rule pcompletes_Call)
    show "\<Pi> p = Some (proc_decl_of [] c)" by (rule p)
    show "length [] = length (formals (proc_decl_of [] c))"
      by (simp add: proc_decl_of_def)
    show "distinct (formals (proc_decl_of [] c))"
      by (simp add: proc_decl_of_def)
    show "pcompletes \<Gamma> gs \<Pi> (body (proc_decl_of [] c))
            (bind_formals (formals (proc_decl_of [] c))
              (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) (formals (proc_decl_of [] c)) [])
              (enter_state gs s)) t'"
      using body by (simp add: proc_decl_of_def bind_formals_def)
  qed
  thus ?thesis by simp
qed

text \<open>
  A frame-generic building block: a parameterless call whose body returns a value completes,
  writing the value to dst and leaving the surrounding stack \<^term>\<open>frs\<close> exactly as it was.  The
  Return unwinds only to the call's own -- the run is frame-balanced -- so this
  is the witness that a return never escapes its nearest activation.
\<close>

lemma call_return_completes:
  assumes q: "\<Pi> p = Some (proc_decl_of [] (Return (Some e)))"
  shows "psteps \<Gamma> gs \<Pi> (Call (Some x) p [], s, frs)
           (SKIP,
            (combine_env gs s
              ((enter_state gs s)
                (ret_var := taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs s))))
              (x := ik_norm (\<Gamma> x) (taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs s))),
            frs)"
proof -
  let ?se = "enter_state gs s"
  let ?s' = "?se(ret_var := taval \<Gamma> (\<Gamma> ret_var) e ?se)"
  let ?F = "Frame s (Some x)"
  have c1: "pstep \<Gamma> gs \<Pi> (Call (Some x) p [], s, frs)
              (Seq (Return (Some e)) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Gamma> gs \<Pi> (Call (Some x) p [], s, frs)
            (Seq (body (proc_decl_of [] (Return (Some e)))) Restore,
             bind_formals (formals (proc_decl_of [] (Return (Some e))))
               (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s)
                  (formals (proc_decl_of [] (Return (Some e)))) [])
               (enter_state gs s), ?F # frs)"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus ?thesis by (simp add: proc_decl_of_def bind_formals_def)
  qed
  have c2: "pstep \<Gamma> gs \<Pi> (Seq (Return (Some e)) Restore, ?se, ?F # frs)
              (Seq Unwind Restore, ?s', ?F # frs)"
    by (intro pstep.Seq2 pstep.ReturnSome)
  have c4: "pstep \<Gamma> gs \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
              (SKIP, (combine_env gs s ?s')
                       (x := ik_norm (\<Gamma> x) (taval \<Gamma> (\<Gamma> ret_var) e ?se)), frs)"
  proof -
    have "pstep \<Gamma> gs \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
            (SKIP, combine_assign \<Gamma> (Some x) (?s' ret_var) (combine_env gs s ?s'), frs)"
      by (rule UnwindAct)
    thus ?thesis by simp
  qed
  from c1 c2 c4 show ?thesis by (meson star.refl star.step)
qed

text \<open>
  The same control path without a destination: \<^term>\<open>Return None\<close> under a \<^term>\<open>Call None\<close>
  reaches the good exit with no assignment (combine_assign drops the value).
\<close>

lemma call_return_none_completes:
  assumes q: "\<Pi> p = Some (proc_decl_of [] (Return None))"
  shows "psteps \<Gamma> gs \<Pi> (Call None p [], s, frs)
           (SKIP, combine_env gs s (enter_state gs s), frs)"
proof -
  let ?se = "enter_state gs s"
  let ?F = "Frame s None"
  have c1: "pstep \<Gamma> gs \<Pi> (Call None p [], s, frs) (Seq (Return None) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Gamma> gs \<Pi> (Call None p [], s, frs)
            (Seq (body (proc_decl_of [] (Return None))) Restore,
             bind_formals (formals (proc_decl_of [] (Return None)))
               (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s)
                  (formals (proc_decl_of [] (Return None))) [])
               (enter_state gs s), ?F # frs)"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus ?thesis by (simp add: proc_decl_of_def bind_formals_def)
  qed
  have c2: "pstep \<Gamma> gs \<Pi> (Seq (Return None) Restore, ?se, ?F # frs) (Seq Unwind Restore, ?se, ?F # frs)"
    by (intro pstep.Seq2 pstep.ReturnNone)
  have c3: "pstep \<Gamma> gs \<Pi> (Seq Unwind Restore, ?se, ?F # frs)
              (SKIP, combine_env gs s ?se, frs)"
  proof -
    have "pstep \<Gamma> gs \<Pi> (Seq Unwind Restore, ?se, ?F # frs)
            (SKIP, combine_assign \<Gamma> None (?se ret_var) (combine_env gs s ?se), frs)"
      by (rule UnwindAct)
    thus ?thesis by simp
  qed
  from c1 c2 c3 show ?thesis by (meson star.refl star.step)
qed

text \<open>
  Nested calls: an outer procedure calls an inner procedure that returns, then continues.  The
  inner return is caught by the inner (\<^term>\<open>call_return_completes\<close> under stack
  \<^term>\<open>[Fout]\<close>): the run is frame-balanced, so the outer \<^term>\<open>Fout\<close> stays on the
  stack, the residual command is \<^term>\<open>SKIP\<close> (no unwind crosses the outer boundary), and execution
  resumes at the outer continuation \<^term>\<open>after\<close>.
\<close>

theorem nested_call_return_trace:
  assumes qin: "\<Pi> pin = Some (proc_decl_of [] (Return (Some e)))"
      and qout: "\<Pi> pout = Some (proc_decl_of []
                   (Seq (Call (Some rin) pin []) after))"
  shows "psteps \<Gamma> gs \<Pi> (Call (Some rout) pout [], s0, [])
           (Seq after Restore,
            (combine_env gs (enter_state gs s0)
              ((enter_state gs (enter_state gs s0))
                (ret_var := taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs (enter_state gs s0)))))
                (rin := ik_norm (\<Gamma> rin)
                          (taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs (enter_state gs s0)))),
            [Frame s0 (Some rout)])"
proof -
  let ?s1 = "enter_state gs s0"
  let ?Fout = "Frame s0 (Some rout)"
  let ?inner = "(combine_env gs ?s1
                    ((enter_state gs ?s1)
                      (ret_var := taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs ?s1))))
                  (rin := ik_norm (\<Gamma> rin) (taval \<Gamma> (\<Gamma> ret_var) e (enter_state gs ?s1)))"
  \<comment> \<open>outer call pushes the outer\<close>
  have K01: "pstep \<Gamma> gs \<Pi> (Call (Some rout) pout [], s0, [])
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])"
  proof -
    have "pstep \<Gamma> gs \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (body (proc_decl_of [] (Seq (Call (Some rin) pin []) after))) Restore,
             bind_formals (formals (proc_decl_of []
                 (Seq (Call (Some rin) pin []) after)))
               (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s0)
                  (formals (proc_decl_of [] (Seq (Call (Some rin) pin []) after))) [])
               (enter_state gs s0),
             Frame s0 (Some rout) # [])"
      using qout by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Gamma> gs \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  \<comment> \<open>inner call runs to completion, caught by the inner; ?Fout survives\<close>
  have inner: "psteps \<Gamma> gs \<Pi> (Call (Some rin) pin [], ?s1, [?Fout]) (SKIP, ?inner, [?Fout])"
    by (rule call_return_completes[where \<Pi> = \<Pi> and p = pin, OF qin])
  have K15: "psteps \<Gamma> gs \<Pi>
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])"
    by (intro psteps_Seq2 inner)
  \<comment> \<open>the outer continuation is exposed: execution resumes in the outer procedure\<close>
  have K56: "pstep \<Gamma> gs \<Pi>
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])
      (Seq after Restore, ?inner, [?Fout])"
    by (intro pstep.Seq2 pstep.Seq1)
  from K01 K15 K56 show ?thesis by (meson star.refl star.step star_trans)
qed


section \<open>Kind preservation\<close>

text \<open>
  Every store a run reaches stays within its declared kinds: each write in
  the small step is normed at \<comment> \<open>or evaluated at\<close> its target
  variable's kind, activation entry resets locals to \<open>0\<close>, and the
  restore boundary selects pointwise between two typed stores.
\<close>

definition frames_typed :: "tyenv \<Rightarrow> frame list \<Rightarrow> bool" where
  "frames_typed \<Gamma> frs \<longleftrightarrow> (\<forall>f \<in> set frs. styped \<Gamma> (frame_store f))"

lemma frames_typed_Nil [simp]: "frames_typed \<Gamma> []"
  by (simp add: frames_typed_def)

lemma frames_typed_Cons [simp]:
  "frames_typed \<Gamma> (Frame fr dst # frs) \<longleftrightarrow> styped \<Gamma> fr \<and> frames_typed \<Gamma> frs"
  by (simp add: frames_typed_def)

lemma styped_enter_state [simp, intro]:
  "styped \<Gamma> s \<Longrightarrow> styped \<Gamma> (enter_state gs s)"
  unfolding styped_def enter_state_def by auto

lemma styped_combine_env [simp, intro]:
  "styped \<Gamma> s \<Longrightarrow> styped \<Gamma> t \<Longrightarrow> styped \<Gamma> (combine_env gs s t)"
  unfolding styped_def by auto

lemma styped_combine_assign [simp, intro]:
  "styped \<Gamma> s \<Longrightarrow> styped \<Gamma> (combine_assign \<Gamma> dst v s)"
  by (cases dst) auto

lemma styped_bind_formals:
  assumes "styped \<Gamma> s"
    and "\<forall>(x, v) \<in> set (zip xs vs). v \<in> ik_range (\<Gamma> x)"
  shows "styped \<Gamma> (bind_formals xs vs s)"
  using assms
proof (induction xs arbitrary: vs s)
  case Nil
  then show ?case by (simp add: bind_formals_def)
next
  case (Cons y ys)
  note IH = Cons.IH and Pst = Cons.prems(1) and Pzip = Cons.prems(2)
  show ?case
  proof (cases vs)
    case Nil
    with Pst show ?thesis by (simp add: bind_formals_def)
  next
    case (Cons v vs')
    have unfold: "bind_formals (y # ys) vs s = bind_formals ys vs' (s(y := v))"
      by (simp add: bind_formals_def Cons)
    have vy: "v \<in> ik_range (\<Gamma> y)" using Pzip Cons by simp
    have st': "styped \<Gamma> (s(y := v))" using Pst vy by (rule styped_update)
    have tail: "\<forall>(x, w) \<in> set (zip ys vs'). w \<in> ik_range (\<Gamma> x)"
      using Pzip Cons by simp
    show ?thesis using IH[OF st' tail] unfold by (simp add: fun_upd_def)
  qed
qed

lemma map2_taval_ranges:
  "\<forall>(x, v) \<in> set (zip xs (map2 (\<lambda>x e. taval \<Gamma> (\<Gamma> x) e s) xs es)).
     v \<in> ik_range (\<Gamma> x)"
  by (auto simp: set_zip)

theorem pstep_preserves_styped:
  assumes "pstep \<Gamma> gs \<Pi> (c, s, frs) (c', s', frs')"
    and "styped \<Gamma> s" and "frames_typed \<Gamma> frs"
  shows "styped \<Gamma> s' \<and> frames_typed \<Gamma> frs'"
  using assms
proof (induction "(c, s, frs)" "(c', s', frs')"
         arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case (Call p decl actuals vals s callee dst frs)
  have "styped \<Gamma> callee"
    unfolding Call.hyps(5) Call.hyps(4)
    by (intro styped_bind_formals styped_enter_state map2_taval_ranges Call.prems)
  with Call.prems show ?case by simp
qed auto

theorem psteps_preserves_styped:
  assumes "psteps \<Gamma> gs \<Pi> (c, s, frs) (c', s', frs')"
    and "styped \<Gamma> s" and "frames_typed \<Gamma> frs"
  shows "styped \<Gamma> s' \<and> frames_typed \<Gamma> frs'"
  using assms
proof (induction rule: star_pstep_induct)
  case refl then show ?case by simp
next
  case step then show ?case by (meson pstep_preserves_styped)
qed

corollary pcompletes_preserves_styped:
  "pcompletes \<Gamma> gs \<Pi> c s t \<Longrightarrow> styped \<Gamma> s \<Longrightarrow> styped \<Gamma> t"
  unfolding pcompletes_def
  using psteps_preserves_styped frames_typed_Nil by blast


section \<open>Source-program well-formedness\<close>

text \<open>
  Source syntax excludes the runtime markers \<^const>\<open>Restore\<close> and
  \<^const>\<open>Unwind\<close>. The reserved \<^const>\<open>ret_var\<close> belongs to the
  call mechanism, so source expressions, assignments, destinations, and formal
  parameters cannot mention it.
\<close>

subsection \<open>Finite syntactic variable sets\<close>

fun exp_vnames :: "exp => vname set" where
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

fun com_vnames :: "com => vname set" where
  "com_vnames SKIP = {}"
| "com_vnames (Assign x a) = insert x (exp_vnames a)"
| "com_vnames (Check c) = exp_vnames c"
| "com_vnames (Seq c1 c2) = com_vnames c1 \<union> com_vnames c2"
| "com_vnames (If b c1 c2) =
    exp_vnames b \<union> com_vnames c1 \<union> com_vnames c2"
| "com_vnames (While b c) = exp_vnames b \<union> com_vnames c"
| "com_vnames (Call dst _ actuals) =
    (case dst of None => {} | Some x => {x}) \<union>
    \<Union> (set (map exp_vnames actuals))"
| "com_vnames (Return None) = {}"
| "com_vnames (Return (Some a)) = exp_vnames a"
| "com_vnames Restore = {}"
| "com_vnames Unwind = {}"

lemma finite_exp_vnames [simp]: "finite (exp_vnames a)"
  by (induction a) auto

lemma finite_com_vnames [simp]: "finite (com_vnames c)"
proof (induction c)
  case SKIP
  then show ?case by simp
next
  case Assign
  then show ?case by simp
next
  case Check
  then show ?case by simp
next
  case Seq
  then show ?case by simp
next
  case If
  then show ?case by simp
next
  case While
  then show ?case by simp
next
  case Call
  then show ?case by (auto split: option.splits)
next
  case (Return opt)
  show ?case
  proof (cases opt)
    case None
    then show ?thesis by simp
  next
    case (Some a)
    then show ?thesis by simp
  qed
next
  case Restore
  then show ?case by simp
next
  case Unwind
  then show ?case by simp
qed

fun source_com :: "com => bool" where
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

definition source_pi :: "proc_table => bool" where
  "source_pi \<Pi> = (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> source_com (body decl))"

text \<open>
  Occurrence of one specific variable is the same syntax-directed walk as
  @{const exp_mentions_global} (\<open>VIMP_Expr\<close>), with the leaf predicate
  specialised to an equality test instead of an arbitrary classifier.
\<close>

definition exp_mentions :: "vname => exp => bool" where
  "exp_mentions x = exp_mentions_where ((=) x)"

lemmas mentions_defs [simp] =
  exp_mentions_def

definition source_exp :: "exp => bool" where
  "source_exp a \<longleftrightarrow> \<not> exp_mentions ret_var a"

definition valid_formal :: "(vname => bool) => vname => bool" where
  "valid_formal gs x \<longleftrightarrow> \<not> gs x \<and> x ~= ret_var"

subsection \<open>Procedure result contract\<close>

text \<open>
  Declarations carry no return-kind annotation. A body is a value provider when
  every syntactic way to finish the body reaches \<^const>\<open>Return\<close> with a value.
  The analysis is conservative: a loop may fall through because its guard may be
  false, and a call resumes normally after its callee completes.
\<close>

fun may_fallthrough :: "com => bool" where
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

fun may_return_none :: "com => bool" where
  "may_return_none (Seq c1 c2) =
     (may_return_none c1 \<or> (may_fallthrough c1 \<and> may_return_none c2))"
| "may_return_none (If _ c1 c2) = (may_return_none c1 \<or> may_return_none c2)"
| "may_return_none (While _ c) = may_return_none c"
| "may_return_none (Return e) = (e = None)"
| "may_return_none _ = False"

fun may_return_value :: "com => bool" where
  "may_return_value (Seq c1 c2) =
     (may_return_value c1 \<or> (may_fallthrough c1 \<and> may_return_value c2))"
| "may_return_value (If _ c1 c2) = (may_return_value c1 \<or> may_return_value c2)"
| "may_return_value (While _ c) = may_return_value c"
| "may_return_value (Return e) = (e \<noteq> None)"
| "may_return_value _ = False"

definition value_providing :: "com => bool" where
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

fun wf_source_com :: "proc_table => com => bool" where
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

fun no_return :: "com => bool" where
  "no_return (Seq c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (If _ c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (While _ c) = no_return c"
| "no_return (Return _) = False"
| "no_return _ = True"

definition wf_proc_decl :: "(vname => bool) => proc_table => proc_decl => bool" where
  "wf_proc_decl gs \<Pi> decl \<longleftrightarrow>
     distinct (formals decl) \<and>
     list_all (valid_formal gs) (formals decl) \<and>
     wf_source_com \<Pi> (body decl)"

definition reserved_ret_var :: "(vname => bool) => bool" where
  "reserved_ret_var gs \<longleftrightarrow> \<not> gs ret_var"

definition wf_source_program :: "(vname => bool) => proc_table => pname => com => bool" where
  "wf_source_program gs \<Pi> mnm main \<longleftrightarrow>
     reserved_ret_var gs \<and>
     \<Pi> mnm = Some (proc_decl_of [] main) \<and>
     wf_source_com \<Pi> main \<and> no_return main \<and>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> wf_proc_decl gs \<Pi> decl) \<and>
     (\<forall>p. \<Pi> p \<noteq> None \<longrightarrow> special_table p = None)"

text \<open>
  Compiler-input well-formedness, defined downstream in the CFG session, unfolds
  through this pair before reaching \<^const>\<open>wf_source_com\<close> and
  \<^const>\<open>valid_formal\<close>. Call sites that discharge that obligation share this
  unfold skeleton verbatim, so it is collected here rather than repeated per site;
  the downstream definition adds itself to the same collection.
\<close>
named_theorems wf_compile_input_simps

declare
  wf_proc_decl_def [wf_compile_input_simps]
  wf_source_program_def [wf_compile_input_simps]

lemma wf_source_com_source_com:
  "wf_source_com \<Pi> c \<Longrightarrow> source_com c"
  by (induction c) (auto split: option.splits)

lemma wf_source_program_main_exists:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> \<Pi> mnm = Some (proc_decl_of [] main)"
  by (simp add: wf_source_program_def)

lemma wf_source_program_main:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> wf_source_com \<Pi> main"
  by (simp add: wf_source_program_def)

lemma wf_source_program_no_return:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> no_return main"
  by (simp add: wf_source_program_def)

lemma wf_source_program_decl:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> \<Pi> p = Some decl
   \<Longrightarrow> wf_proc_decl gs \<Pi> decl"
  by (simp add: wf_source_program_def)

lemma wf_source_program_source_pi:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> source_pi \<Pi>"
  unfolding wf_source_program_def source_pi_def wf_proc_decl_def
  using wf_source_com_source_com by blast

lemma wf_source_program_source_com:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> source_com main"
  using wf_source_program_main wf_source_com_source_com by blast

lemma wf_source_program_special_table_none:
  "wf_source_program gs \<Pi> mnm main \<Longrightarrow> \<Pi> p = Some decl \<Longrightarrow> special_table p = None"
  by (simp add: wf_source_program_def)

end
