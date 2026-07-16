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
  | Restore

record proc_decl =
  formals :: "vname list"
  body    :: com
  result  :: "aexp option"

definition proc_decl_of :: "vname list => com => aexp option => proc_decl" where
  "proc_decl_of xs bdy res = \<lparr>formals = xs, body = bdy, result = res\<rparr>"

abbreviation proc_decl_legacy :: "com => proc_decl" where
  "proc_decl_legacy c \<equiv> proc_decl_of [] c None"

lemma proc_decl_legacy:
  "formals (proc_decl_legacy c) = []"
  "body (proc_decl_legacy c) = c"
  "result (proc_decl_legacy c) = None"
  "proc_decl_legacy c = proc_decl_of [] c None"
  by (simp_all add: proc_decl_of_def)

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

(* Runtime frame: the caller's store plus the optional destination variable. *)
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
| Scope:   "pstep \<Pi> (Scope c, s, frs)
              (Seq c Restore, enter_state s, Frame s None # frs)"
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

lemma pfinalD[elim]:
  assumes "pfinal (c, s, frs)"
  shows "c = SKIP \<and> frs = []"
  using assms unfolding pfinal.simps by simp

lemma pfinal_iff_SKIP_empty[simp]:
  "pfinal (c, s, frs) = (c = SKIP \<and> frs = [])"
  unfolding pfinal.simps by simp

definition pno_step :: "proc_table \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool" where
  "pno_step \<Pi> cfg \<longleftrightarrow> \<not> (\<exists>cfg'. pstep \<Pi> cfg cfg')"

lemma pfinal_imp_pno_step:
  assumes pf: "pfinal (c, s, frs)"
  shows "pno_step \<Pi> (c, s, frs)"
  using pf unfolding pno_step_def pfinal.simps
  by (auto elim!: SkipSE)

definition pcompletes :: "proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pcompletes \<Pi> c s t = psteps \<Pi> (c, s, []) (SKIP, t, [])"

lemma pcompletes_iff_small_termination:
  "pcompletes \<Pi> c s t \<longleftrightarrow>
     (\<exists>cfg. psteps \<Pi> (c, s, []) cfg \<and> pfinal cfg \<and> fst (snd cfg) = t)"
  unfolding pcompletes_def by auto

lemma pcompletes_iff_reaches_pfinal[simp]:
  "pcompletes \<Pi> c s t \<longleftrightarrow>
     (\<exists>cfg. psteps \<Pi> (c, s, []) cfg \<and> pfinal cfg \<and> fst (snd cfg) = t)"
  unfolding pcompletes_def by auto

lemma pcompletes_skip: "pcompletes \<Pi> SKIP s s"
  unfolding pcompletes_def by (rule star.refl)

lemma pcompletes_assign: "pcompletes \<Pi> (Assign x a) s (s(x := aval a s))"
  by (simp add: pcompletes_def)

(* -- Sequencing lifts through the small-step --------------------------- *)

lemma psteps_Seq2_cfg:
  assumes "star (pstep \<Pi>) X Y"
  shows "star (pstep \<Pi>)
           (Seq (fst X) c2, fst (snd X), snd (snd X))
           (Seq (fst Y) c2, fst (snd Y), snd (snd Y))"
  using assms
proof (induction rule: star.induct)
  case (refl a)
  show ?case by (rule star.refl)
next
  case (step a b c)
  obtain ca sa fa where a: "a = (ca, sa, fa)" by (cases a) auto
  obtain cb sb fb where b: "b = (cb, sb, fb)" by (cases b) auto
  from step.hyps(1) a b have "pstep \<Pi> (ca, sa, fa) (cb, sb, fb)" by simp
  hence "pstep \<Pi> (Seq ca c2, sa, fa) (Seq cb c2, sb, fb)" by (rule Seq2)
  with step.IH a b show ?case by (auto intro: star.step)
qed

lemma psteps_Seq2:
  "star (pstep \<Pi>) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (pstep \<Pi>) (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
  using psteps_Seq2_cfg[where X = "(c1, s, frs)" and Y = "(c1', s', frs')"] by simp

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

lemma pstep_frame_extend_cfg:
  assumes "pstep \<Pi> X Y"
  shows "pstep \<Pi> (fst X, fst (snd X), snd (snd X) @ extra)
                  (fst Y, fst (snd Y), snd (snd Y) @ extra)"
  using assms
proof (induction rule: pstep.induct)
  case Assign
  show ?case by (simp only: fst_conv snd_conv) (rule pstep.Assign)
next
  case RestoreStep
  show ?case by (simp only: fst_conv snd_conv append_Cons) (rule pstep.RestoreStep)
next
  case Seq2
  then show ?case by auto
qed simp_all

lemma pstep_frame_extend:
  "pstep \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   pstep \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  using pstep_frame_extend_cfg[where X = "(c, s, frs)" and Y = "(c', s', frs')"]
  by simp

lemma psteps_frame_extend_cfg:
  assumes "star (pstep \<Pi>) X Y"
  shows "star (pstep \<Pi>)
           (fst X, fst (snd X), snd (snd X) @ extra)
           (fst Y, fst (snd Y), snd (snd Y) @ extra)"
  using assms
proof (induction rule: star.induct)
  case (refl a)
  show ?case by (rule star.refl)
next
  case (step a b d)
  obtain ca sa fa where a: "a = (ca, sa, fa)" by (cases a) auto
  obtain cb sb fb where b: "b = (cb, sb, fb)" by (cases b) auto
  from step.hyps(1) a b have "pstep \<Pi> (ca, sa, fa) (cb, sb, fb)" by simp
  hence "pstep \<Pi> (ca, sa, fa @ extra) (cb, sb, fb @ extra)"
    by (rule pstep_frame_extend)
  with step.IH a b show ?case by (auto intro: star.step)
qed

lemma psteps_frame_extend:
  "psteps \<Pi> (c, s, frs) (c', s', frs') \<Longrightarrow>
   psteps \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  using psteps_frame_extend_cfg[where X = "(c, s, frs)" and Y = "(c', s', frs')"]
  by simp

lemma psteps_frame_mono:
  "psteps \<Pi> (c, s, []) (SKIP, t, []) \<Longrightarrow>
   psteps \<Pi> (c, s, extra) (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

(* -- Scope and Call termination ------------------------------------- *)

(* One restore rule covers both scopes and result-bearing calls: the destination
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

lemma pcompletes_Scope:
  assumes body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Scope c) s (<s|t'>)"
  unfolding pcompletes_def
  apply (rule star.step)
   apply (rule Scope)
  using psteps_Seq_Restore_body[OF psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s None]"]]
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

lemma pcompletes_Legacy_Call:
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

lemma pcompletes_Scope_Call_legacy:
  assumes p: "\<Pi> p = Some (proc_decl_of [] c None)"
      and run: "pcompletes \<Pi> (Scope c) s t"
  shows "pcompletes \<Pi> (Call None p []) s t"
proof -
  have step_scope:
    "pstep \<Pi> (Scope c, s, [])
       (Seq c Restore, enter_state s, [Frame s None])"
    by (rule Scope)
  have p': "\<Pi> p = Some (proc_decl_of [] c None)"
    by (rule p)
  have step_call_raw:
    "pstep \<Pi> (Call None p [], s, [])
       (Seq (with_result (body (proc_decl_of [] c None))
                         (result (proc_decl_of [] c None)))
            Restore,
        bind_formals (formals (proc_decl_of [] c None)) [] (enter_state s),
        [Frame s None])"
  proof (rule pstep.Call[where vals = "[]"
                            and callee = "bind_formals (formals (proc_decl_of [] c None)) [] (enter_state s)"])
    show "\<Pi> p = Some (proc_decl_of [] c None)" by (rule p')
    show "length [] = length (formals (proc_decl_of [] c None))"
      by (simp add: proc_decl_of_def)
    show "distinct (formals (proc_decl_of [] c None))"
      by (simp add: proc_decl_of_def)
    show "\<forall>x. None = Some x \<longrightarrow> result (proc_decl_of [] c None) \<noteq> None"
      by simp
    show "[] = map (\<lambda>e. aval e s) []" by simp
    show "bind_formals (formals (proc_decl_of [] c None)) [] (enter_state s)
          = bind_formals (formals (proc_decl_of [] c None)) [] (enter_state s)" by simp
  qed
  (* A legacy procedure has no result, so with_result leaves the body alone and
     the call enters exactly the configuration a Scope enters. *)
  have step_call:
    "pstep \<Pi> (Call None p [], s, [])
       (Seq c Restore, enter_state s, [Frame s None])"
    using step_call_raw by (simp add: proc_decl_legacy bind_formals_def proc_decl_of_def)
  from run[unfolded pcompletes_def] have tail:
    "psteps \<Pi> (Seq c Restore, enter_state s, [Frame s None]) (SKIP, t, [])"
  (* Only the step case survives: Scope c is not SKIP, and ScopeSE pins the
     successor configuration. *)
  proof (cases rule: star.cases)
    case (step y)
    then show ?thesis by auto
  qed
  show ?thesis
    unfolding pcompletes_def using step_call tail by (meson star.step)
qed

end
