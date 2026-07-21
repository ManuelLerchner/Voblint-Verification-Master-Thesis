theory IMP2_Proc
  imports IMP2_Expr IMP2_Globals
begin

(*
  Procedure-extended command language `com` with a frame-stack small-step
  semantics, defined separately from the scalar command type `com`.

  Procedures may now declare call-by-value formals and an optional final result
  expression. Scope and Call both save the caller's locals on entry and restore
  them on exit via combine_states (globals from the callee's final store,
  locals from the saved frame).

  The restore boundary is made explicit by the runtime-only marker Restore: the
  frame stack alone cannot locate a scope's end inside a Seq, so entry rewrites
  Scope/Call to a Seq ending in Restore. It never appears in source programs.

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
  | Scope  com
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

(* Handler kind of a runtime frame (I.3): a Scope pushes a lexical frame, transparent
   to Return; a Call pushes an activation frame, the handler that catches Return. *)
datatype frame_kind = LexicalFrame | ActivationFrame

(* Runtime frame: the caller's store, the optional destination variable, and the
   handler kind that decides whether an unwinding Return stops here. *)
datatype frame = Frame store "vname option" frame_kind

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
| Scope:   "pstep \<Pi> (Scope c, s, frs)
              (Seq c Restore, enter_state s, Frame s None LexicalFrame # frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> (\<forall>x. dst = Some x \<longrightarrow> result decl \<noteq> None)
             \<Longrightarrow> vals = map (\<lambda>e. aval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state s)
             \<Longrightarrow> pstep \<Pi> (Call dst p actuals, s, frs)
                 (Seq (with_result (body decl) (result decl)) Restore,
                  callee,
                  Frame s dst ActivationFrame # frs)"
| RestoreStep:
    "pstep \<Pi> (Restore, s, Frame fr dst k # frs)
       (SKIP, combine_assign dst (s ret_var) (<fr|s>), frs)"
| ReturnSome:
    "pstep \<Pi> (Return (Some e), s, frs)
       (Unwind, s(ret_var := aval e s), frs)"
| ReturnNone:
    "pstep \<Pi> (Return None, s, frs) (Unwind, s, frs)"
| UnwindDead:
    "c2 \<noteq> Restore
     \<Longrightarrow> pstep \<Pi> (Seq Unwind c2, s, frs) (Unwind, s, frs)"
| UnwindScope:
    "pstep \<Pi> (Seq Unwind Restore, s, Frame fr dst LexicalFrame # frs)
       (Unwind, s, frs)"
| UnwindAct:
    "pstep \<Pi> (Seq Unwind Restore, s, Frame fr dst ActivationFrame # frs)
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
inductive_cases ScopeSE[elim!]:
  "pstep \<Pi> (Scope c, s, frs) cfg"
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

(* -- Scope and Call termination ------------------------------------- *)

(* One restore rule covers both scopes and result-bearing calls: the destination
   rides in the frame and the value in ret_var. *)
lemma psteps_Seq_Restore_body:
  assumes "psteps \<Pi> (c, s0, [Frame fr dst k]) (SKIP, t', [Frame fr dst k])"
  shows "psteps \<Pi> (Seq c Restore, s0, [Frame fr dst k])
           (SKIP, combine_assign dst (t' ret_var) (<fr|t'>), [])"
proof -
  have body_seq:
    "psteps \<Pi> (Seq c Restore, s0, [Frame fr dst k])
       (Seq SKIP Restore, t', [Frame fr dst k])"
    using psteps_Seq2[OF assms] .
  have step_seq1:
    "pstep \<Pi> (Seq SKIP Restore, t', [Frame fr dst k])
       (Restore, t', [Frame fr dst k])"
    by (rule Seq1)
  have step_restore:
    "pstep \<Pi> (Restore, t', [Frame fr dst k])
       (SKIP, combine_assign dst (t' ret_var) (<fr|t'>), [])"
    by (rule RestoreStep)
  have tail:
    "psteps \<Pi> (Seq SKIP Restore, t', [Frame fr dst k])
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

lemma pcompletes_Scope:
  assumes body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Scope c) s (<s|t'>)"
  unfolding pcompletes_def
  apply (rule star.step)
   apply (rule Scope)
  using psteps_Seq_Restore_body[OF psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s None LexicalFrame]"]]
  by simp

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
          (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s dst ActivationFrame])"
    using p arity distinct_formals no_ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s None ActivationFrame]) (SKIP, t', [Frame s None ActivationFrame])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s None ActivationFrame]"] by simp
  (* The result, if any, only lands in ret_var, which the restore drops. *)
  have published:
    "\<exists>t''. psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s None ActivationFrame])
             (SKIP, t'', [Frame s None ActivationFrame]) \<and> <s|t''> = <s|t'>"
  proof (cases "result decl")
    case None
    then show ?thesis using framed by auto
  next
    case (Some e)
    then show ?thesis
      using psteps_with_result_Some[OF framed, where e = e] by auto
  qed
  then obtain t'' where
    pub: "psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s None ActivationFrame])
            (SKIP, t'', [Frame s None ActivationFrame])" and
    agree: "<s|t''> = <s|t'>" by blast
  have restored:
    "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s None ActivationFrame])
       (SKIP, <s|t'>, [])"
    using psteps_Seq_Restore_body[OF pub] agree by simp
  from no_ret restored
  show "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s dst ActivationFrame])
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
          (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s (Some x) ActivationFrame])"
    using p arity distinct_formals ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s (Some x) ActivationFrame]) (SKIP, t', [Frame s (Some x) ActivationFrame])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s (Some x) ActivationFrame]"] by simp
  (* The callee publishes the result into ret_var, which the restore reads back. *)
  have pub:
    "psteps \<Pi> (with_result (body decl) (result decl), ?callee, [Frame s (Some x) ActivationFrame])
       (SKIP, t'(ret_var := aval e t'), [Frame s (Some x) ActivationFrame])"
    using ret psteps_with_result_Some[OF framed, where e = e] by simp
  show "psteps \<Pi> (Seq (with_result (body decl) (result decl)) Restore, ?callee, [Frame s (Some x) ActivationFrame])
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
  The bottom frame of a run is only inspected when it is finally popped; every step
  either preserves it or (when it is the only frame) pops it to the empty stack.  The
  Seq2 case, where a step happens inside a pending sequence, is discharged by the
  induction hypothesis on the sub-step.
\<close>
lemma pstep_bottom_frame:
  assumes "pstep \<Pi> cf cf'"
  shows "\<forall>extra. snd (snd cf) = extra @ [f]
           \<longrightarrow> (\<exists>extra'. snd (snd cf') = extra' @ [f]) \<or> (extra = [] \<and> snd (snd cf') = [])"
  using assms
proof (induction rule: pstep.induct)
  case (Seq2 c1 s frs c1' s' frs' c2)
  then show ?case by auto
qed (auto simp: Cons_eq_append_conv)

text \<open>
  A parameterless procedure call completes exactly like the scope of its body.  Under the
  procedure-aware frames the call pushes an ActivationFrame where the scope pushes a
  LexicalFrame, so the two runs differ only in the handler kind of the bottom frame; a run
  that reaches the empty stack pops that frame with the kind-agnostic RestoreStep, so the
  final store is the same.  The frame-kind-swap metatheory below (psteps_bottom_Lex_to_Act)
  discharges this: a completing run never pops the bottom frame with the LexicalFrame-only
  UnwindScope rule, which would strand at a stuck bare Unwind.
\<close>
(* Unwinding commands: a fired Return sits in Unwind state, either bare or under a pending
   Seq.  On the empty stack such a command cannot manufacture a frame or reach SKIP. *)
fun unwinding :: "com \<Rightarrow> bool" where
  "unwinding Unwind = True"
| "unwinding (Seq c1 c2) = unwinding c1"
| "unwinding SKIP = False"
| "unwinding (Assign x a) = False"
| "unwinding (If b c1 c2) = False"
| "unwinding (While b c) = False"
| "unwinding (Scope c) = False"
| "unwinding (Call d p a) = False"
| "unwinding (Return e) = False"
| "unwinding Restore = False"

lemma unwinding_pstep_empty:
  "pstep \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow> frs = [] \<Longrightarrow> unwinding c
     \<Longrightarrow> frs' = [] \<and> unwinding c'"
proof (induction "(c, s, frs)" "(c', s', frs')"
    arbitrary: c s frs c' s' frs' rule: pstep.induct)
  case (Seq2 c1 s frs c1' s' frs' c2)
  then show ?case by simp
qed simp_all

lemma unwinding_psteps_empty:
  "psteps \<Pi> (c, s, frs) (c', s', frs')
     \<Longrightarrow> frs = [] \<and> unwinding c \<longrightarrow> frs' = [] \<and> unwinding c'"
proof (induction rule: star_pstep_induct)
  case refl then show ?case by simp
next
  case (step a aa b ab ac ba ad ae bb)
  show ?case
  proof
    assume "b = [] \<and> unwinding a"
    hence "ba = [] \<and> unwinding ab" using unwinding_pstep_empty[OF step.hyps(1)] by blast
    thus "bb = [] \<and> unwinding ad" using step.IH by simp
  qed
qed

(* A pending unwind on the empty stack never reaches the good exit: bare Unwind is stuck. *)
lemma no_complete_unwinding:
  "unwinding c \<Longrightarrow> \<not> psteps \<Pi> (c, s, []) (SKIP, t, [])"
  using unwinding_psteps_empty by fastforce

(* Popping a single Lexical bottom frame: either the very same step pops an Activation bottom
   frame (RestoreStep is kind-agnostic), or the residual command is unwinding (UnwindScope). *)
lemma pstep_pop_Lex:
  "pstep \<Pi> (c, s, frs) (c1, s1, frs2) \<Longrightarrow> frs = [Frame fr dst LexicalFrame] \<Longrightarrow> frs2 = []
     \<Longrightarrow> pstep \<Pi> (c, s, [Frame fr dst ActivationFrame]) (c1, s1, []) \<or> unwinding c1"
proof (induction "(c, s, frs)" "(c1, s1, frs2)"
    arbitrary: c s frs c1 s1 frs2 rule: pstep.induct)
  case (Seq2 a s0 fra a' s0' fra' b)
  from Seq2(2)[OF Seq2(3) Seq2(4)] show ?case
    by (metis pstep.Seq2 unwinding.simps(2))
qed (auto intro: pstep.RestoreStep)

(* A step that keeps the bottom frame does not read its handler kind: the same step runs under
   either kind.  The frame-consuming rules read the top frame, which lies strictly above the
   preserved bottom frame. *)
lemma pstep_kind_swap_preserve:
  "pstep \<Pi> (c, s, frs) (c1, s1, frs2)
     \<Longrightarrow> frs = E @ [Frame fr dst k1] \<Longrightarrow> frs2 = E1 @ [Frame fr dst k1]
     \<Longrightarrow> pstep \<Pi> (c, s, E @ [Frame fr dst k2]) (c1, s1, E1 @ [Frame fr dst k2])"
proof (induction "(c, s, frs)" "(c1, s1, frs2)"
    arbitrary: c s frs c1 s1 frs2 E E1 rule: pstep.induct)
  case (Seq2 a s0 fra a' s0' fra' b)
  from Seq2(2)[OF Seq2(3) Seq2(4)] show ?case
    by (rule pstep.Seq2)
next
  case Scope then show ?case
    by (fastforce simp: Cons_eq_append_conv intro: pstep.Scope)
next
  case (Call p0 decl0 actuals0 dst0 vals0 s0 callee0 frs0)
  have e1: "E1 = Frame s0 dst0 ActivationFrame # E"
    using Call.prems by (auto simp: Cons_eq_append_conv)
  show ?case
    using Call.hyps e1 by (auto intro!: pstep.Call)
qed (auto simp: Cons_eq_append_conv intro: pstep.intros)

(* Keystone.  A run under a Lexical bottom frame that reaches the good exit also reaches it,
   unchanged, under an Activation bottom frame.  A Return that reached the bottom frame would
   pop it by the LexicalFrame-only UnwindScope, stranding at a stuck bare Unwind, which
   contradicts completion (no_complete_unwinding).  So the bottom frame is popped by the
   kind-agnostic RestoreStep, and the Activation run replays it identically. *)
lemma psteps_bottom_Lex_to_Act:
  "psteps \<Pi> (c, s, frs) (SKIP, t, []) \<Longrightarrow> frs = extra @ [Frame fr dst LexicalFrame]
     \<Longrightarrow> psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])"
proof (induction "(c, s, frs)" "(SKIP :: com, t, [] :: frame list)"
    arbitrary: c s frs extra rule: star.induct)
  case refl then show ?case by simp
next
  case (step y)
  obtain c1 s1 frs1 where y_eq: "y = (c1, s1, frs1)" by (cases y)
  from step.hyps(1) y_eq have fstep: "pstep \<Pi> (c, s, frs) (c1, s1, frs1)" by simp
  from step.hyps(2) y_eq have tail: "psteps \<Pi> (c1, s1, frs1) (SKIP, t, [])" by simp
  have frseq: "frs = extra @ [Frame fr dst LexicalFrame]" using step.prems by simp
  have split: "(\<exists>e'. frs1 = e' @ [Frame fr dst LexicalFrame]) \<or> (extra = [] \<and> frs1 = [])"
    using pstep_bottom_frame[OF fstep, of "Frame fr dst LexicalFrame"] frseq by simp
  from split show "psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])"
  proof (elim disjE)
    assume "\<exists>e'. frs1 = e' @ [Frame fr dst LexicalFrame]"
    then obtain e' where e': "frs1 = e' @ [Frame fr dst LexicalFrame]" ..
    have swap: "pstep \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame])
                  (c1, s1, e' @ [Frame fr dst ActivationFrame])"
      using pstep_kind_swap_preserve[OF fstep frseq e'] .
    have ih: "psteps \<Pi> (c1, s1, e' @ [Frame fr dst ActivationFrame]) (SKIP, t, [])"
      using step.hyps(3)[OF y_eq e'] .
    from star.step[OF swap ih]
    show "psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])" .
  next
    assume "extra = [] \<and> frs1 = []"
    hence e0: "extra = []" and f0: "frs1 = []" by auto
    from fstep frseq e0 f0
    have fstep': "pstep \<Pi> (c, s, [Frame fr dst LexicalFrame]) (c1, s1, [])" by simp
    have tail0: "psteps \<Pi> (c1, s1, []) (SKIP, t, [])" using tail f0 by simp
    have popres: "pstep \<Pi> (c, s, [Frame fr dst ActivationFrame]) (c1, s1, []) \<or> unwinding c1"
      using pstep_pop_Lex[OF fstep'] by blast
    from popres show "psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])"
    proof (elim disjE)
      assume h1: "pstep \<Pi> (c, s, [Frame fr dst ActivationFrame]) (c1, s1, [])"
      from star.step[OF h1 tail0]
      show "psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])" using e0 by simp
    next
      assume "unwinding c1"
      with no_complete_unwinding tail0
      show "psteps \<Pi> (c, s, extra @ [Frame fr dst ActivationFrame]) (SKIP, t, [])" by blast
    qed
  qed
qed

lemma pcompletes_Scope_Call_parameterless:
  assumes p: "\<Pi> p = Some (proc_decl_of [] c None)"
      and run: "pcompletes \<Pi> (Scope c) s t"
  shows "pcompletes \<Pi> (Call None p []) s t"
proof -
  from run have r: "psteps \<Pi> (Scope c, s, []) (SKIP, t, [])"
    by (simp add: pcompletes_def)
  have body_lex:
    "psteps \<Pi> (Seq c Restore, enter_state s, [Frame s None LexicalFrame]) (SKIP, t, [])"
  proof -
    from r have "(Scope c, s, []) = (SKIP, t, [])
        \<or> (\<exists>z. pstep \<Pi> (Scope c, s, []) z \<and> psteps \<Pi> z (SKIP, t, []))"
      by (cases rule: star.cases) auto
    then obtain z where s1: "pstep \<Pi> (Scope c, s, []) z"
        and s2: "psteps \<Pi> z (SKIP, t, [])"
      by auto
    from s1 have "z = (Seq c Restore, enter_state s, [Frame s None LexicalFrame])"
      by (auto elim!: ScopeSE)
    with s2 show
      "psteps \<Pi> (Seq c Restore, enter_state s, [Frame s None LexicalFrame]) (SKIP, t, [])"
      by simp
  qed
  have body_act:
    "psteps \<Pi> (Seq c Restore, enter_state s, [Frame s None ActivationFrame]) (SKIP, t, [])"
    using psteps_bottom_Lex_to_Act[OF body_lex, of "[]" s None] by simp
  have call_step:
    "pstep \<Pi> (Call None p [], s, []) (Seq c Restore, enter_state s, [Frame s None ActivationFrame])"
  proof -
    have "pstep \<Pi> (Call None p [], s, [])
            (Seq (with_result (body (proc_decl_of [] c None)) (result (proc_decl_of [] c None)))
                 Restore,
             bind_formals (formals (proc_decl_of [] c None)) (map (\<lambda>e. aval e s) [])
               (enter_state s),
             Frame s None ActivationFrame # [])"
      using p by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Pi> (Call None p [], s, [])
            (Seq c Restore, enter_state s, [Frame s None ActivationFrame])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  from star.step[OF call_step body_act]
  show "pcompletes \<Pi> (Call None p []) s t" by (simp add: pcompletes_def)
qed

subsection \<open>Worked trace: a call into a scope with an early return\<close>

text \<open>
  Production witnesses for the critical Call / Scope / Return interaction, run as concrete
  small-step traces rather than only start and end states.  The callee body is
  \<^term>\<open>Scope (Seq (Return (Some e)) dead)\<close>: a scoped block that returns early, past dead
  code.  The named configurations K0..K8 make the frame-stack evolution reviewable:

    K0  Seq (Call ...) cont            []                 caller continuation installed
    K1  after Call                     [Fa]               ActivationFrame pushed
    K2  after Scope                    [Fl, Fa]           LexicalFrame pushed
    K3  after Return (Some e)          [Fl, Fa]           unwinding; value in ret_var (once)
    K4  after UnwindDead (dead)        [Fl, Fa]           dead code discarded
    K5  after UnwindScope              [Fa]               LexicalFrame popped, unwind pending
    K6  after UnwindDead (result)      [Fa]               trailing result assign discarded
    K7  after UnwindAct                []                 ActivationFrame handles unwind; dst := value
    K8  after Seq1                     []                 caller continuation now executing
\<close>

theorem call_scope_return_trace:
  fixes \<Pi> :: proc_table and s0 :: store and x yv :: vname and p :: pname
    and e e0 ay :: aexp and cont :: com
  assumes q: "\<Pi> p = Some (proc_decl_of []
                (Scope (Seq (Return (Some e)) (Assign yv ay))) (Some e0))"
  shows "psteps \<Pi>
     (Seq (Call (Some x) p []) cont, s0, [])
     (cont,
      (<s0 | (enter_state (enter_state s0))(ret_var := aval e (enter_state (enter_state s0)))>)
        (x := aval e (enter_state (enter_state s0))),
      [])"
proof -
  let ?s1 = "enter_state s0"
  let ?s2 = "enter_state (enter_state s0)"
  let ?s3 = "?s2(ret_var := aval e ?s2)"
  let ?Fa = "Frame s0 (Some x) ActivationFrame"
  let ?Fl = "Frame (enter_state s0) None LexicalFrame"
  let ?dead = "Assign yv ay"
  let ?ret = "Assign ret_var e0"
  \<comment> \<open>K0 -> K1: the Call fires and pushes the ActivationFrame\<close>
  have K01: "pstep \<Pi>
      (Seq (Call (Some x) p []) cont, s0, [])
      (Seq (Seq (Seq (Scope (Seq (Return (Some e)) ?dead)) ?ret) Restore) cont, ?s1, [?Fa])"
  proof (rule Seq2)
    have "pstep \<Pi> (Call (Some x) p [], s0, [])
            (Seq (with_result (body (proc_decl_of []
                 (Scope (Seq (Return (Some e)) ?dead)) (Some e0)))
                 (result (proc_decl_of [] (Scope (Seq (Return (Some e)) ?dead)) (Some e0)))) Restore,
             bind_formals (formals (proc_decl_of [] (Scope (Seq (Return (Some e)) ?dead)) (Some e0)))
               (map (\<lambda>a. aval a s0) []) (enter_state s0),
             Frame s0 (Some x) ActivationFrame # [])"
      using q by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Pi> (Call (Some x) p [], s0, [])
            (Seq (Seq (Scope (Seq (Return (Some e)) ?dead)) ?ret) Restore, ?s1, [?Fa])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  \<comment> \<open>K1 -> K2: entering the Scope pushes the LexicalFrame\<close>
  have K12: "pstep \<Pi>
      (Seq (Seq (Seq (Scope (Seq (Return (Some e)) ?dead)) ?ret) Restore) cont, ?s1, [?Fa])
      (Seq (Seq (Seq (Seq (Seq (Return (Some e)) ?dead) Restore) ?ret) Restore) cont, ?s2, [?Fl, ?Fa])"
    by (intro pstep.Seq2 pstep.Scope)
  \<comment> \<open>K2 -> K3: Return evaluates e once into ret_var and enters the unwind state\<close>
  have K23: "pstep \<Pi>
      (Seq (Seq (Seq (Seq (Seq (Return (Some e)) ?dead) Restore) ?ret) Restore) cont, ?s2, [?Fl, ?Fa])
      (Seq (Seq (Seq (Seq (Seq Unwind ?dead) Restore) ?ret) Restore) cont, ?s3, [?Fl, ?Fa])"
    by (intro pstep.Seq2 pstep.ReturnSome)
  \<comment> \<open>K3 -> K4: the dead code after the return is discarded\<close>
  have K34: "pstep \<Pi>
      (Seq (Seq (Seq (Seq (Seq Unwind ?dead) Restore) ?ret) Restore) cont, ?s3, [?Fl, ?Fa])
      (Seq (Seq (Seq (Seq Unwind Restore) ?ret) Restore) cont, ?s3, [?Fl, ?Fa])"
    by (intro pstep.Seq2 pstep.UnwindDead) simp
  \<comment> \<open>K4 -> K5: the LexicalFrame is popped while the unwind stays pending\<close>
  have K45: "pstep \<Pi>
      (Seq (Seq (Seq (Seq Unwind Restore) ?ret) Restore) cont, ?s3, [?Fl, ?Fa])
      (Seq (Seq (Seq Unwind ?ret) Restore) cont, ?s3, [?Fa])"
    by (intro pstep.Seq2 pstep.UnwindScope)
  \<comment> \<open>K5 -> K6: the trailing result assignment is also discarded by the unwind\<close>
  have K56: "pstep \<Pi>
      (Seq (Seq (Seq Unwind ?ret) Restore) cont, ?s3, [?Fa])
      (Seq (Seq Unwind Restore) cont, ?s3, [?Fa])"
    by (intro pstep.Seq2 pstep.UnwindDead) simp
  \<comment> \<open>K6 -> K7: the ActivationFrame handles the unwind and assigns the value to dst\<close>
  have K67: "pstep \<Pi>
      (Seq (Seq Unwind Restore) cont, ?s3, [?Fa])
      (Seq SKIP cont, (<s0 | ?s3>)(x := aval e ?s2), [])"
  proof (rule Seq2)
    have "pstep \<Pi> (Seq Unwind Restore, ?s3, [?Fa])
            (SKIP, combine_assign (Some x) (?s3 ret_var) (<s0 | ?s3>), [])"
      by (rule UnwindAct)
    thus "pstep \<Pi> (Seq Unwind Restore, ?s3, [?Fa])
            (SKIP, (<s0 | ?s3>)(x := aval e ?s2), [])"
      by simp
  qed
  \<comment> \<open>K7 -> K8: the caller continuation is exposed and starts executing\<close>
  have K78: "pstep \<Pi>
      (Seq SKIP cont, (<s0 | ?s3>)(x := aval e ?s2), [])
      (cont, (<s0 | ?s3>)(x := aval e ?s2), [])"
    by (rule Seq1)
  from K01 K12 K23 K34 K45 K56 K67 K78
  show ?thesis by (meson star.refl star.step)
qed

text \<open>
  A frame-generic building block: a parameterless call whose body returns a value completes,
  writing the value to dst and leaving the surrounding stack \<^term>\<open>frs\<close> exactly as it was.  The
  Return unwinds only to the call's own ActivationFrame -- the run is frame-balanced -- so this
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
  let ?F = "Frame s (Some x) ActivationFrame"
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
  let ?F = "Frame s None ActivationFrame"
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
  inner return is caught by the inner ActivationFrame (\<^term>\<open>call_return_completes\<close> under stack
  \<^term>\<open>[Fout]\<close>): the run is frame-balanced, so the outer ActivationFrame \<^term>\<open>Fout\<close> stays on the
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
            [Frame s0 (Some rout) ActivationFrame])"
proof -
  let ?s1 = "enter_state s0"
  let ?Fout = "Frame s0 (Some rout) ActivationFrame"
  let ?inner = "(<?s1 | (enter_state ?s1)(ret_var := aval e (enter_state ?s1))>)
                  (rin := aval e (enter_state ?s1))"
  \<comment> \<open>outer call pushes the outer ActivationFrame\<close>
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
             Frame s0 (Some rout) ActivationFrame # [])"
      using qout by (intro Call) (auto simp: proc_decl_of_def)
    thus "pstep \<Pi> (Call (Some rout) pout [], s0, [])
            (Seq (Seq (Seq (Call (Some rin) pin []) after) (Assign ret_var e0')) Restore, ?s1, [?Fout])"
      by (simp add: proc_decl_of_def bind_formals_def)
  qed
  \<comment> \<open>inner call runs to completion, caught by the inner ActivationFrame; ?Fout survives\<close>
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
| "source_com (Scope c) = source_com c"
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
