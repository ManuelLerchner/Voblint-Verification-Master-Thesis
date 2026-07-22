theory IMP2_Proc
  imports IMP2_Expr IMP2_Globals
begin

(*
  Procedure-extended command language `com` with a frame-stack small-step
  semantics, defined separately from the scalar command type `com`.

  Procedures may now declare call-by-value formals and an optional final result
  expression. A Call saves the caller's locals on entry and restores them on exit
  via combine_states (globals from the callee's final store, locals from the saved
  frame).

  The restore boundary is made explicit by the runtime-only marker Restore: the
  frame stack alone cannot locate a call's end inside a Seq, so entry rewrites a
  Call to a Seq ending in Restore. It never appears in source programs.

  A procedure's result expression is not carried by Restore. Following Goblint
  (base.ml: return / combine_assign), call entry appends an assignment of the
  result expression to the reserved local ret_var at the end of the callee body,
  and Restore assigns ret_var's callee-exit value to the caller's destination.
  ret_var is local, so the callee's copy is dropped by combine_states and the
  caller's own copy is restored from the frame.
*)

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
  \<^const>\<open>Return\<close> is the source-level early return (Goblint's \<open>Ret of Exp option\<close>):
  it publishes the optional value into \<open>ret_var\<close> and unwinds the current activation.
  \<^const>\<open>Unwind\<close> is a runtime-only marker (like \<^const>\<open>Restore\<close>, never in source
  programs): once a \<^const>\<open>Return\<close> has fired, the computation is in \<^const>\<open>Unwind\<close>
  state, discarding pending statements up to the nearest enclosing activation frame.
\<close>

record proc_decl =
  formals :: "vname list"
  body    :: com
  result  :: "aexp option"

definition proc_decl_of :: "vname list => com => aexp option => proc_decl" where
  "proc_decl_of xs bdy res = \<lparr>formals = xs, body = bdy, result = res\<rparr>"

(* Reserved local holding a procedure's result across the restore boundary.
   Goblint's return_varinfo. Local, so it never escapes into the caller. *)
definition ret_var :: vname where
  "ret_var = ''#ret''"

lemma ret_var_not_global [simp]: "\<not> is_global ret_var"
  by (simp add: ret_var_def is_global_def)

(* Callee control: run the body, then publish the result into ret_var. *)
fun with_result :: "com => aexp option => com" where
  "with_result c None = c"
| "with_result c (Some e) = Seq c (Assign ret_var e)"

(* Procedure table: names to declarations. *)
type_synonym proc_table = "pname \<Rightarrow> proc_decl option"

(* Runtime frame: the caller's store and the optional destination variable. *)
datatype frame = Frame store "vname option"

definition bind_formals :: "vname list \<Rightarrow> int list \<Rightarrow> store \<Rightarrow> store" where
  "bind_formals xs vs s =
     fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

(* Goblint's combine_assign: write the returned value into the destination, or
   leave the caller untouched when the call discards it. Total: the value is read
   out of ret_var, which every store maps. *)
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
             \<Longrightarrow> (\<forall>x. dst = Some x \<longrightarrow> result decl \<noteq> None)
             \<Longrightarrow> vals = map (\<lambda>e. aval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state s)
             \<Longrightarrow> pstep \<Pi> (Call dst p actuals, s, frs)
                 (Seq (with_result (body decl) (result decl)) Restore,
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

(* Publishing the result leaves everything but ret_var alone, and ret_var is
   local, so the restored caller store is unaffected by it. *)
lemma psteps_with_result_Some:
  assumes "psteps \<Pi> (c, s0, frs) (SKIP, t', frs)"
  shows "psteps \<Pi> (with_result c (Some e), s0, frs)
           (SKIP, t'(ret_var := aval e t'), frs)"
proof -
  have body_seq:
    "psteps \<Pi> (Seq c (Assign ret_var e), s0, frs)
       (Seq SKIP (Assign ret_var e), t', frs)"
    using psteps_Seq2[OF assms] .
  have tail:
    "psteps \<Pi> (Seq SKIP (Assign ret_var e), t', frs)
       (SKIP, t'(ret_var := aval e t'), frs)"
    by (meson Seq1 Assign star.refl star.step)
  from body_seq tail have "psteps \<Pi> (Seq c (Assign ret_var e), s0, frs)
       (SKIP, t'(ret_var := aval e t'), frs)"
    by (rule star_trans)
  then show ?thesis by simp
qed

lemma combine_states_ret_var_irrelevant [simp]:
  "<fr|t(ret_var := v)> = <fr|t>"
  by (rule ext) simp


lemma pcompletes_Call_none:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and no_ret: "dst = None"
      and body: "pcompletes \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>e. aval e s) actuals) (enter_state s)) t'"
  shows "pcompletes \<Pi> (Call dst p actuals) s (<s|t'>)"
  unfolding pcompletes_def
proof (rule star.step)
  let ?vals = "map (\<lambda>e. aval e s) actuals"
  let ?callee = "bind_formals (formals decl) ?vals (enter_state s)"
  show "pstep \<Pi> (Call dst p actuals, s, [])
          (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s dst])"
    using p arity distinct_formals no_ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s None]) (SKIP, t', [Frame s None])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s None]"] by simp
  (* The result, if any, only lands in ret_var, which the restore drops. *)
  have published:
    "\<exists>t''. psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s None])
             (SKIP, t'', [Frame s None]) \<and> <s|t''> = <s|t'>"
  proof (cases "result decl")
    case None
    then show ?thesis using framed by auto
  next
    case (Some e)
    then show ?thesis
      using psteps_with_result_Some[OF framed, where e = e] by auto
  qed
  then obtain t'' where
    pub: "psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s None])
            (SKIP, t'', [Frame s None])" and
    agree: "<s|t''> = <s|t'>" by blast
  have restored:
    "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s None])
       (SKIP, <s|t'>, [])"
    using psteps_Seq_Restore_body[OF pub] agree by simp
  from no_ret restored
  show "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s dst])
          (SKIP, <s|t'>, [])"
    by simp
qed

lemma pcompletes_Call_some:
  assumes p: "\<Pi> p = Some decl"
      and arity: "length actuals = length (formals decl)"
      and distinct_formals: "distinct (formals decl)"
      and ret: "result decl = Some e"
      and body: "pcompletes \<Pi> (body decl)
                   (bind_formals (formals decl) (map (\<lambda>a. aval a s) actuals) (enter_state s)) t'"
  shows "pcompletes \<Pi> (Call (Some x) p actuals) s ((<s|t'>)(x := aval e t'))"
  unfolding pcompletes_def
proof (rule star.step)
  let ?vals = "map (\<lambda>a. aval a s) actuals"
  let ?callee = "bind_formals (formals decl) ?vals (enter_state s)"
  show "pstep \<Pi> (Call (Some x) p actuals, s, [])
          (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s (Some x)])"
    using p arity distinct_formals ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s (Some x)]) (SKIP, t', [Frame s (Some x)])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s (Some x)]"] by simp
  (* The callee publishes the result into ret_var, which the restore reads back. *)
  have pub:
    "psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s (Some x)])
       (SKIP, t'(ret_var := aval e t'), [Frame s (Some x)])"
    using ret psteps_with_result_Some[OF framed, where e = e] by simp
  show "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s (Some x)])
          (SKIP, (<s|t'>)(x := aval e t'), [])"
    using psteps_Seq_Restore_body[OF pub] by simp
qed

lemma pcompletes_Call_parameterless:
  assumes p: "\<Pi> p = Some (proc_decl_of [] c None)"
      and body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Call None p []) s (<s|t'>)"
proof (rule pcompletes_Call_none)
  show "\<Pi> p = Some (proc_decl_of [] c None)" by (rule p)
  show "length [] = length (formals (proc_decl_of [] c None))"
    by (simp add: proc_decl_of_def)
  show "distinct (formals (proc_decl_of [] c None))"
    by (simp add: proc_decl_of_def)
  show "None = None" by simp
  show "pcompletes \<Pi> (body (proc_decl_of [] c None))
          (bind_formals (formals (proc_decl_of [] c None)) (map (\<lambda>e. aval e s) []) (enter_state s)) t'"
    using body by (simp add: proc_decl_of_def bind_formals_def)
qed

text \<open>
  A frame-generic building block: a parameterless call whose body returns a value completes,
  writing the value to dst and leaving the surrounding stack \<^term>\<open>frs\<close> exactly as it was.  The
  Return unwinds only to the call's own -- the run is frame-balanced -- so this
  is the witness that a return never escapes its nearest activation.
\<close>

lemma call_return_completes:
  assumes q: "\<Pi> p = Some (proc_decl_of [] (Return (Some e)) (Some e0))"
  shows "psteps \<Pi> (Call (Some x) p [], s, frs)
           (SKIP,
            (<s | (enter_state s)(ret_var := aval e (enter_state s))>)(x := aval e (enter_state s)),
            frs)"
proof -
  let ?se = "enter_state s"
  let ?s' = "?se(ret_var := aval e ?se)"
  let ?F = "Frame s (Some x)"
  have c1: "pstep \<Pi> (Call (Some x) p [], s, frs)
              (Seq (Seq (Return (Some e)) (Assign ret_var e0)) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Pi> (Call (Some x) p [], s, frs)
            (Seq (with_result (body (proc_decl_of [] (Return (Some e)) (Some e0)))
                 (result (proc_decl_of [] (Return (Some e)) (Some e0)))) Restore,
             bind_formals (formals (proc_decl_of [] (Return (Some e)) (Some e0)))
               (map (\<lambda>a. aval a s) []) (enter_state s), ?F # frs)"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus ?thesis by (simp add: proc_decl_of_def bind_formals_def)
  qed
  have c2: "pstep \<Pi> (Seq (Seq (Return (Some e)) (Assign ret_var e0)) Restore, ?se, ?F # frs)
              (Seq (Seq Unwind (Assign ret_var e0)) Restore, ?s', ?F # frs)"
    by (intro pstep.Seq2 pstep.ReturnSome)
  have c3: "pstep \<Pi> (Seq (Seq Unwind (Assign ret_var e0)) Restore, ?s', ?F # frs)
              (Seq Unwind Restore, ?s', ?F # frs)"
    by (intro pstep.Seq2 pstep.UnwindDead) simp
  have c4: "pstep \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
              (SKIP, (<s | ?s'>)(x := aval e ?se), frs)"
  proof -
    have "pstep \<Pi> (Seq Unwind Restore, ?s', ?F # frs)
            (SKIP, combine_assign (Some x) (?s' ret_var) (<s | ?s'>), frs)"
      by (rule UnwindAct)
    thus ?thesis by simp
  qed
  from c1 c2 c3 c4 show ?thesis by (meson star.refl star.step)
qed

text \<open>
  The same control path without a destination: \<^term>\<open>Return None\<close> under a \<^term>\<open>Call None\<close>
  reaches the good exit with no assignment (combine_assign drops the value).
\<close>

lemma call_return_none_completes:
  assumes q: "\<Pi> p = Some (proc_decl_of [] (Return None) None)"
  shows "psteps \<Pi> (Call None p [], s, frs) (SKIP, <s | enter_state s>, frs)"
proof -
  let ?se = "enter_state s"
  let ?F = "Frame s None"
  have c1: "pstep \<Pi> (Call None p [], s, frs) (Seq (Return None) Restore, ?se, ?F # frs)"
  proof -
    have "pstep \<Pi> (Call None p [], s, frs)
            (Seq (with_result (body (proc_decl_of [] (Return None) None))
                 (result (proc_decl_of [] (Return None) None))) Restore,
             bind_formals (formals (proc_decl_of [] (Return None) None))
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
  assumes qin: "\<Pi> pin = Some (proc_decl_of [] (Return (Some e)) (Some e0))"
      and qout: "\<Pi> pout = Some (proc_decl_of []
                   (Seq (Call (Some rin) pin []) after) (Some e0'))"
  shows "psteps \<Pi> (Call (Some rout) pout [], s0, [])
           (Seq (Seq after (Assign ret_var e0')) Restore,
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
      (Seq (Seq (Seq (Call (Some rin) pin []) after) (Assign ret_var e0')) Restore, ?s1, [?Fout])"
  proof -
    have "pstep \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (with_result (body (proc_decl_of []
                 (Seq (Call (Some rin) pin []) after) (Some e0')))
                 (result (proc_decl_of [] (Seq (Call (Some rin) pin []) after) (Some e0')))) Restore,
             bind_formals (formals (proc_decl_of []
                 (Seq (Call (Some rin) pin []) after) (Some e0')))
               (map (\<lambda>a. aval a s0) []) (enter_state s0),
             Frame s0 (Some rout) # [])"
      using qout by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (Seq (Seq (Call (Some rin) pin []) after) (Assign ret_var e0')) Restore, ?s1, [?Fout])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  \<comment> \<open>inner call runs to completion, caught by the inner; ?Fout survives\<close>
  have inner: "psteps \<Pi> (Call (Some rin) pin [], ?s1, [?Fout]) (SKIP, ?inner, [?Fout])"
    by (rule call_return_completes[where \<Pi> = \<Pi> and p = pin, OF qin])
  have K15: "psteps \<Pi>
      (Seq (Seq (Seq (Call (Some rin) pin []) after) (Assign ret_var e0')) Restore, ?s1, [?Fout])
      (Seq (Seq (Seq SKIP after) (Assign ret_var e0')) Restore, ?inner, [?Fout])"
    by (intro psteps_Seq2 inner)
  \<comment> \<open>the outer continuation is exposed: execution resumes in the outer procedure\<close>
  have K56: "pstep \<Pi>
      (Seq (Seq (Seq SKIP after) (Assign ret_var e0')) Restore, ?inner, [?Fout])
      (Seq (Seq after (Assign ret_var e0')) Restore, ?inner, [?Fout])"
    by (intro pstep.Seq2 pstep.Seq1)
  from K01 K15 K56 show ?thesis by (meson star.refl star.step star_trans)
qed


subsection \<open>Source-program admissibility\<close>

text \<open>
  Restore is runtime-only and never appears in source programs. source_com
  captures that source-language property; source_pi lifts it to every procedure
  body of a table. These are the well-formedness predicates the compiler and the
  end-to-end soundness theorems run on.
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

(* Publishing the result appends an assignment, which stays in the source language. *)
lemma source_com_with_result [simp]:
  "source_com (with_result c r) = source_com c"
  by (cases r) auto

end
