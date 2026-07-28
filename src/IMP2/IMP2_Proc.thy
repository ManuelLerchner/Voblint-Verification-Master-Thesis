theory IMP2_Proc
  imports IMP2_Expr IMP2_Globals
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
\<close>

datatype com =
    SKIP
  | Assign vname aexp
  | Seq    com com
  | If     bexp com com
  | While  bexp com
  | Call   "vname option" pname "aexp list"
  | Return "aexp option"
  | Restore
  | Unwind

text \<open>
  \<^const>\<open>Return\<close> is the source-level early return. It publishes an optional
  value into \<open>ret_var\<close> and unwinds the current activation.
  \<^const>\<open>Unwind\<close> is a runtime-only marker (like \<^const>\<open>Restore\<close>, never in source
  programs): once a \<^const>\<open>Return\<close> has fired, the computation is in \<^const>\<open>Unwind\<close>
  state, discarding pending statements up to the nearest enclosing activation frame.
\<close>

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
  "ret_var = ''#ret''"

lemma ret_var_not_global [simp]: "\<not> is_global ret_var"
  by (simp add: ret_var_def is_global_def)

(* Procedure table: names to declarations. *)
type_synonym proc_table = "pname \<Rightarrow> proc_decl option"

(* Runtime frame: the caller's store and the optional destination variable. *)
datatype frame = Frame store "vname option"

definition bind_formals :: "vname list \<Rightarrow> int list \<Rightarrow> store \<Rightarrow> store" where
  "bind_formals xs vs s =
     fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

text \<open>
  \<open>combine_assign\<close> writes the published value when a destination exists.
  A destination-less call discards the value and leaves the caller store unchanged.
\<close>
fun combine_assign :: "vname option \<Rightarrow> int \<Rightarrow> store \<Rightarrow> store" where
  "combine_assign None _ s = s"
| "combine_assign (Some x) v s = s(x := v)"

(* -- Frame-stack small-step ----------------------------------------- *)

inductive
  pstep :: "proc_table \<Rightarrow> com \<times> store \<times> frame list
                       \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
  for \<Pi> :: proc_table
where
  Assign:  "pstep \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
| Seq1:    "pstep \<Pi> (Seq SKIP c2, s, frs) (c2, s, frs)"
| Seq2:    "pstep \<Pi> (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> pstep \<Pi> (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "bval b s \<Longrightarrow> pstep \<Pi> (If b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> bval b s \<Longrightarrow> pstep \<Pi> (If b c1 c2, s, frs) (c2, s, frs)"
| While:   "pstep \<Pi> (While b c, s, frs)
                      (If b (Seq c (While b c)) SKIP, s, frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> vals = map (\<lambda>e. aval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state s)
             \<Longrightarrow> pstep \<Pi> (Call dst p actuals, s, frs)
                 (Seq (body decl) Restore,
                  callee,
                  Frame s dst # frs)"
| RestoreStep:
    "pstep \<Pi> (Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign dst (s ret_var) (<fr|s>), frs)"
| ReturnSome:
    "pstep \<Pi> (Return (Some e), s, frs)
       (Unwind, s(ret_var := aval e s), frs)"
| ReturnNone:
    "pstep \<Pi> (Return None, s, frs) (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> pstep \<Pi> (Seq Unwind c2, s, frs) (Unwind, s, frs)"
| UnwindAct:
    "pstep \<Pi> (Seq Unwind Restore, s, Frame fr dst # frs)
       (SKIP, combine_assign dst (s ret_var) (<fr|s>), frs)"

abbreviation
  psteps :: "proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps \<Pi> x y \<equiv> star (pstep \<Pi>) x y"

declare pstep.intros [simp, intro]
declare pstep.Seq2[simp del]

inductive_cases SkipSE[elim!]:
  "pstep \<Pi> (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:
  "pstep \<Pi> (Assign x a, s, frs) cfg"
inductive_cases SeqSE[elim]:
  "pstep \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:
  "pstep \<Pi> (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim]:
  "pstep \<Pi> (While b c, s, frs) cfg"
inductive_cases CallSE[elim]:
  "pstep \<Pi> (Call dst p actuals, s, frs) cfg"
inductive_cases RestoreSE[elim!]:
  "pstep \<Pi> (Restore, s, frs) cfg"
inductive_cases ReturnSE[elim!]:
  "pstep \<Pi> (Return e, s, frs) cfg"
inductive_cases UnwindSE[elim!]:
  "pstep \<Pi> (Unwind, s, frs) cfg"

(* Structured induction over pstep-runs: split_format states each case on the
   (c, s, frs) components rather than an anonymous configuration product. *)
lemmas star_pstep_induct =
  star.induct[of "pstep \<Pi>", split_format(complete), case_names refl step]

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

definition pcompletes :: "proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pcompletes \<Pi> c s t = psteps \<Pi> (c, s, []) (SKIP, t, [])"

lemma pcompletes_iff_small_termination[simp]:
  "pcompletes \<Pi> c s t \<longleftrightarrow>
     (\<exists>cfg. psteps \<Pi> (c, s, []) cfg \<and> pfinal cfg \<and> fst (snd cfg) = t)"
  unfolding pcompletes_def by auto

lemma pcompletes_skip: "pcompletes \<Pi> SKIP s s"
  unfolding pcompletes_def by (rule star.refl)

lemma pcompletes_assign: "pcompletes \<Pi> (Assign x a) s (s(x := aval a s))"
  by (simp add: pcompletes_def)

(* -- Sequencing lifts through the small-step --------------------------- *)

lemma psteps_Seq2:
  "star (pstep \<Pi>) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (pstep \<Pi>) (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
proof (induction rule: star_pstep_induct)
  case refl show ?case by (rule star.refl)
next
  case step then show ?case by (meson Seq2 star.step)
qed

(* -- Structural composition of terminating runs ---------------------- *)

lemma pcompletes_Seq:
  assumes "pcompletes \<Pi> c1 s s2" and "pcompletes \<Pi> c2 s2 t"
  shows "pcompletes \<Pi> (Seq c1 c2) s t"
proof -
  from assms(1) have a: "star (pstep \<Pi>) (Seq c1 c2, s, []) (Seq SKIP c2, s2, [])"
    unfolding pcompletes_def by (rule psteps_Seq2)
  have b: "pstep \<Pi> (Seq SKIP c2, s2, []) (c2, s2, [])" by (rule Seq1)
  from a b assms(2) show ?thesis
    unfolding pcompletes_def by (meson star.step star_trans)
qed

lemma pcompletes_IfTrue:
  "bval b s \<Longrightarrow> pcompletes \<Pi> c1 s t \<Longrightarrow> pcompletes \<Pi> (If b c1 c2) s t"
  unfolding pcompletes_def by (meson IfTrue star.step)

lemma pcompletes_IfFalse:
  "\<not> bval b s \<Longrightarrow> pcompletes \<Pi> c2 s t \<Longrightarrow> pcompletes \<Pi> (If b c1 c2) s t"
  unfolding pcompletes_def by (meson IfFalse star.step)

lemma pcompletes_WhileFalse:
  "\<not> bval b s \<Longrightarrow> pcompletes \<Pi> (While b c) s s"
  unfolding pcompletes_def by (meson While IfFalse star.refl star.step)

lemma pcompletes_WhileTrue:
  assumes b:    "bval b s"
      and body: "pcompletes \<Pi> c s s2"
      and rest: "pcompletes \<Pi> (While b c) s2 t"
  shows "pcompletes \<Pi> (While b c) s t"
proof -
  have seq: "pcompletes \<Pi> (Seq c (While b c)) s t"
    using body rest by (rule pcompletes_Seq)
  have w: "pstep \<Pi> (While b c, s, [])
                    (If b (Seq c (While b c)) SKIP, s, [])"
    by (rule While)
  have i: "pstep \<Pi> (If b (Seq c (While b c)) SKIP, s, [])
                    (Seq c (While b c), s, [])"
    using b by (rule IfTrue)
  from w i seq show ?thesis unfolding pcompletes_def by (meson star.step)
qed

(* -- Frame-stack extension ------------------------------------------ *)

lemma pstep_frame_extend:
  "pstep \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   pstep \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  by (induction "(c, s, frs)" "(c', s', frs')"
        arbitrary: c s frs c' s' frs' rule: pstep.induct)
     (auto intro: pstep.intros)

lemma psteps_frame_extend:
  "psteps \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   psteps \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
proof (induction rule: star_pstep_induct)
  case refl show ?case by (rule star.refl)
next
  case step then show ?case by (meson pstep_frame_extend star.step)
qed

lemma psteps_frame_mono:
  "psteps \<Pi> (c, s, []) (SKIP, t, []) \<Longrightarrow>
   psteps \<Pi> (c, s, extra) (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

(* -- Call termination ------------------------------------- *)

(* The restore rule pops a call frame: the destination
   rides in the frame and the value in ret_var. *)
lemma psteps_Seq_Restore_body:
  assumes "psteps \<Pi> (c, s0, [Frame fr dst]) (SKIP, t', [Frame fr dst])"
  shows "psteps \<Pi> (Seq c Restore, s0, [Frame fr dst])
           (SKIP, combine_assign dst (t' ret_var) (<fr|t'>), [])"
proof -
  have body_seq:
    "psteps \<Pi> (Seq c Restore, s0, [Frame fr dst])
       (Seq SKIP Restore, t', [Frame fr dst])"
    using psteps_Seq2[OF assms] .
  have step_seq1:
    "pstep \<Pi> (Seq SKIP Restore, t', [Frame fr dst])
       (Restore, t', [Frame fr dst])"
    by (rule Seq1)
  have step_restore:
    "pstep \<Pi> (Restore, t', [Frame fr dst])
       (SKIP, combine_assign dst (t' ret_var) (<fr|t'>), [])"
    by (rule RestoreStep)
  have tail:
    "psteps \<Pi> (Seq SKIP Restore, t', [Frame fr dst])
       (SKIP, combine_assign dst (t' ret_var) (<fr|t'>), [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  show ?thesis using body_seq tail by (rule star_trans)
qed

lemma combine_states_ret_var_irrelevant [simp]:
  "<fr|t(ret_var := v)> = <fr|t>"
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
      and body: "pcompletes \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)) t'"
  shows "pcompletes \<Pi> (Call dst p actuals) s (combine_assign dst (t' ret_var) (<s|t'>))"
  unfolding pcompletes_def
proof (rule star.step)
  let ?vals = "map (\<lambda>e. aval e s) actuals"
  let ?callee = "bind_formals (formals decl) ?vals (enter_state s)"
  show "pstep \<Pi> (Call dst p actuals, s, [])
          (Seq (body decl) Restore, ?callee, [Frame s dst])"
    using p arity distinct_formals
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s dst]) (SKIP, t', [Frame s dst])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s dst]"] by simp
  show "psteps \<Pi> (Seq (body decl) Restore, ?callee, [Frame s dst])
          (SKIP, combine_assign dst (t' ret_var) (<s|t'>), [])"
    using psteps_Seq_Restore_body[OF framed] by simp
qed

text \<open>A value-less fall-through with a destination reads the callee's \<open>ret_var\<close>, which
  \<^const>\<open>enter_state\<close> initialises to 0 and the body never wrote: the destination gets 0, never a
  stale caller or callee value.\<close>
lemma pcompletes_Call_dst_fallthrough_zero:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and body: "pcompletes \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)) t'"
      and fallthrough: "t' ret_var = 0"
  shows "pcompletes \<Pi> (Call (Some x) p actuals) s ((<s|t'>)(x := 0))"
  using pcompletes_Call[OF p arity distinct_formals body, where dst = "Some x"] fallthrough by simp

lemma pcompletes_Call_parameterless:
  assumes p: "\<Pi> p = Some (proc_decl_of [] c)"
      and body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Call None p []) s (<s|t'>)"
proof -
  have "pcompletes \<Pi> (Call None p []) s (combine_assign None (t' ret_var) (<s|t'>))"
  proof (rule pcompletes_Call)
    show "\<Pi> p = Some (proc_decl_of [] c)" by (rule p)
    show "length [] = length (formals (proc_decl_of [] c))"
      by (simp add: proc_decl_of_def)
    show "distinct (formals (proc_decl_of [] c))"
      by (simp add: proc_decl_of_def)
    show "pcompletes \<Pi> (body (proc_decl_of [] c))
            (bind_formals (formals (proc_decl_of [] c)) (map (\<lambda>e. aval e s) []) (enter_state s)) t'"
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
  shows "psteps \<Pi> (Call (Some x) p [], s, frs)
           (SKIP,
            (<s | (enter_state s)(ret_var := aval e (enter_state s))>)(x := aval e (enter_state s)),
            frs)"
proof -
  let ?se = "enter_state s"
  let ?s' = "?se(ret_var := aval e ?se)"
  let ?F = "Frame s (Some x)"
  have c1: "pstep \<Pi> (Call (Some x) p [], s, frs)
              (Seq (Return (Some e)) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Pi> (Call (Some x) p [], s, frs)
            (Seq (body (proc_decl_of [] (Return (Some e)))) Restore,
             bind_formals (formals (proc_decl_of [] (Return (Some e))))
               (map (\<lambda>a. aval a s) []) (enter_state s), ?F # frs)"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus ?thesis by (simp add: proc_decl_of_def bind_formals_def)
  qed
  have c2: "pstep \<Pi> (Seq (Return (Some e)) Restore, ?se, ?F # frs)
              (Seq Unwind Restore, ?s', ?F # frs)"
    by (intro pstep.Seq2 pstep.ReturnSome)
  have c4: "pstep \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
              (SKIP, (<s | ?s'>)(x := aval e ?se), frs)"
  proof -
    have "pstep \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
            (SKIP, combine_assign (Some x) (?s' ret_var) (<s | ?s'>), frs)"
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
  shows "psteps \<Pi> (Call None p [], s, frs) (SKIP, <s | enter_state s>, frs)"
proof -
  let ?se = "enter_state s"
  let ?F = "Frame s None"
  have c1: "pstep \<Pi> (Call None p [], s, frs) (Seq (Return None) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Pi> (Call None p [], s, frs)
            (Seq (body (proc_decl_of [] (Return None))) Restore,
             bind_formals (formals (proc_decl_of [] (Return None)))
               (map (\<lambda>a. aval a s) []) (enter_state s), ?F # frs)"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus ?thesis by (simp add: proc_decl_of_def bind_formals_def)
  qed
  have c2: "pstep \<Pi> (Seq (Return None) Restore, ?se, ?F # frs) (Seq Unwind Restore, ?se, ?F # frs)"
    by (intro pstep.Seq2 pstep.ReturnNone)
  have c3: "pstep \<Pi> (Seq Unwind Restore, ?se, ?F # frs) (SKIP, <s | ?se>, frs)"
  proof -
    have "pstep \<Pi> (Seq Unwind Restore, ?se, ?F # frs)
            (SKIP, combine_assign None (?se ret_var) (<s | ?se>), frs)"
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
  shows "psteps \<Pi> (Call (Some rout) pout [], s0, [])
           (Seq after Restore,
            (<enter_state s0 |
              (enter_state (enter_state s0))(ret_var := aval e (enter_state (enter_state s0)))>)
                (rin := aval e (enter_state (enter_state s0))),
            [Frame s0 (Some rout)])"
proof -
  let ?s1 = "enter_state s0"
  let ?Fout = "Frame s0 (Some rout)"
  let ?inner = "(<?s1 | (enter_state ?s1)(ret_var := aval e (enter_state ?s1))>)
                  (rin := aval e (enter_state ?s1))"
  \<comment> \<open>outer call pushes the outer\<close>
  have K01: "pstep \<Pi> (Call (Some rout) pout [], s0, [])
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])"
  proof -
    have "pstep \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (body (proc_decl_of [] (Seq (Call (Some rin) pin []) after))) Restore,
             bind_formals (formals (proc_decl_of []
                 (Seq (Call (Some rin) pin []) after)))
               (map (\<lambda>a. aval a s0) []) (enter_state s0),
             Frame s0 (Some rout) # [])"
      using qout by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  \<comment> \<open>inner call runs to completion, caught by the inner; ?Fout survives\<close>
  have inner: "psteps \<Pi> (Call (Some rin) pin [], ?s1, [?Fout]) (SKIP, ?inner, [?Fout])"
    by (rule call_return_completes[where \<Pi> = \<Pi> and p = pin, OF qin])
  have K15: "psteps \<Pi>
      (Seq (Seq (Call (Some rin) pin []) after) Restore, ?s1, [?Fout])
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])"
    by (intro psteps_Seq2 inner)
  \<comment> \<open>the outer continuation is exposed: execution resumes in the outer procedure\<close>
  have K56: "pstep \<Pi>
      (Seq (Seq SKIP after) Restore, ?inner, [?Fout])
      (Seq after Restore, ?inner, [?Fout])"
    by (intro pstep.Seq2 pstep.Seq1)
  from K01 K15 K56 show ?thesis by (meson star.refl star.step star_trans)
qed


section \<open>Source-program well-formedness\<close>

text \<open>
  Source syntax excludes the runtime markers \<^const>\<open>Restore\<close> and
  \<^const>\<open>Unwind\<close>. The reserved \<^const>\<open>ret_var\<close> belongs to the
  call mechanism, so source expressions, assignments, destinations, and formal
  parameters cannot mention it.
\<close>

fun source_com :: "com => bool" where
  "source_com SKIP = True"
| "source_com (Assign x a) = True"
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
  @{const aexp_mentions_global} (\<open>IMP2_Expr\<close>), with the leaf predicate
  specialised to an equality test instead of @{const is_global}.
\<close>

definition aexp_n_mentions :: "vname => AExp.aexp => bool" where
  "aexp_n_mentions x = aexp_n_mentions_where ((=) x)"

definition aexp_mentions :: "vname => aexp => bool" where
  "aexp_mentions x = aexp_mentions_where ((=) x)"

definition bexp_n_mentions :: "vname => BExp.bexp => bool" where
  "bexp_n_mentions x = bexp_n_mentions_where ((=) x)"

definition bexp_mentions :: "vname => bexp => bool" where
  "bexp_mentions x = bexp_mentions_where ((=) x)"

lemmas mentions_defs [simp] =
  aexp_n_mentions_def aexp_mentions_def bexp_n_mentions_def bexp_mentions_def

definition source_aexp :: "aexp => bool" where
  "source_aexp a \<longleftrightarrow> \<not> aexp_mentions ret_var a"

definition source_bexp :: "bexp => bool" where
  "source_bexp b \<longleftrightarrow> \<not> bexp_mentions ret_var b"

definition valid_formal :: "vname => bool" where
  "valid_formal x \<longleftrightarrow> \<not> is_global x \<and> x \<noteq> ret_var"

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
| "wf_source_com \<Pi> (Assign x a) = (x \<noteq> ret_var \<and> source_aexp a)"
| "wf_source_com \<Pi> (Seq c1 c2) = (wf_source_com \<Pi> c1 \<and> wf_source_com \<Pi> c2)"
| "wf_source_com \<Pi> (If b c1 c2) =
     (source_bexp b \<and> wf_source_com \<Pi> c1 \<and> wf_source_com \<Pi> c2)"
| "wf_source_com \<Pi> (While b c) = (source_bexp b \<and> wf_source_com \<Pi> c)"
| "wf_source_com \<Pi> (Call dst p actuals) =
     (case \<Pi> p of
        None \<Rightarrow> False
      | Some decl \<Rightarrow>
          length actuals = length (formals decl) \<and>
          list_all source_aexp actuals \<and>
          (case dst of
             None \<Rightarrow> True
           | Some x \<Rightarrow> x \<noteq> ret_var \<and> value_providing (body decl)))"
| "wf_source_com \<Pi> (Return e) = (case e of None \<Rightarrow> True | Some a \<Rightarrow> source_aexp a)"
| "wf_source_com \<Pi> Restore = False"
| "wf_source_com \<Pi> Unwind = False"

fun no_return :: "com => bool" where
  "no_return (Seq c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (If _ c1 c2) = (no_return c1 \<and> no_return c2)"
| "no_return (While _ c) = no_return c"
| "no_return (Return _) = False"
| "no_return _ = True"

definition wf_proc_decl :: "proc_table => proc_decl => bool" where
  "wf_proc_decl \<Pi> decl \<longleftrightarrow>
     distinct (formals decl) \<and>
     list_all valid_formal (formals decl) \<and>
     wf_source_com \<Pi> (body decl)"

definition wf_source_program :: "proc_table => pname => com => bool" where
  "wf_source_program \<Pi> mnm main \<longleftrightarrow>
     \<Pi> mnm = Some (proc_decl_of [] main) \<and>
     wf_source_com \<Pi> main \<and> no_return main \<and>
     (\<forall>p decl. \<Pi> p = Some decl \<longrightarrow> wf_proc_decl \<Pi> decl)"

lemma wf_source_com_source_com:
  "wf_source_com \<Pi> c \<Longrightarrow> source_com c"
  by (induction c) (auto split: option.splits)

lemma wf_source_program_main_exists:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> \<Pi> mnm = Some (proc_decl_of [] main)"
  by (simp add: wf_source_program_def)

lemma wf_source_program_main:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> wf_source_com \<Pi> main"
  by (simp add: wf_source_program_def)

lemma wf_source_program_no_return:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> no_return main"
  by (simp add: wf_source_program_def)

lemma wf_source_program_decl:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> \<Pi> p = Some decl
   \<Longrightarrow> wf_proc_decl \<Pi> decl"
  by (simp add: wf_source_program_def)

lemma wf_source_program_source_pi:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> source_pi \<Pi>"
  unfolding wf_source_program_def source_pi_def wf_proc_decl_def
  using wf_source_com_source_com by blast

lemma wf_source_program_source_com:
  "wf_source_program \<Pi> mnm main \<Longrightarrow> source_com main"
  using wf_source_program_main wf_source_com_source_com by blast

end
