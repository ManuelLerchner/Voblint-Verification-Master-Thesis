theory IMP2_Proc
  imports IMP2_Expr IMP2_Globals
begin

(*
  Procedure-extended command language `com` with a frame-stack small-step
  semantics, defined separately from the scalar command type `com`.

  Procedures are parameterless (Call p); parameters are passed via globals.
  Scope and Call both save the caller's locals on entry and restore them on
  exit via combine_states (globals from the callee's final store, locals from
  the saved frame).

  The restore boundary is made explicit by the runtime-only marker Restore:
  the frame stack alone cannot locate a scope's end inside a Seq, so entry
  rewrites `Scope c` to `Seq c Restore` (frame pushed) and Restore performs
  the pop.  Restore never appears in source programs.
*)

datatype com =
    SKIP
  | Assign vname aexp
  | Seq    com com
  | If     bexp com com
  | While  bexp com
  | Scope  com          (* local scope: save locals, restore on exit       *)
  | Call   pname         (* call parameterless procedure from the table     *)
  | Restore              (* runtime-only: pop a frame, restore caller locals *)

(* Procedure table: names to bodies. *)
type_synonym proc_table = "pname \<Rightarrow> com option"

(* Runtime frame: the caller's store, whose locals are restored on return. *)
type_synonym frame = store

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
| Scope:   "pstep \<Pi> (Scope c, s, frs) (Seq c Restore, enter_state s, s # frs)"
| Call:    "\<Pi> p = Some c
             \<Longrightarrow> pstep \<Pi> (Call p, s, frs) (Seq c Restore, enter_state s, s # frs)"
| Restore: "pstep \<Pi> (Restore, s, fr # frs) (SKIP, <fr|s>, frs)"

abbreviation
  psteps :: "proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps \<Pi> x y \<equiv> star (pstep \<Pi>) x y"

declare pstep.intros [simp, intro]
declare pstep.Seq2[simp del]

inductive_cases SkipSE[elim!]:    "pstep \<Pi> (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:  "pstep \<Pi> (Assign x a, s, frs) cfg"
inductive_cases SeqSE[elim]:      "pstep \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:      "pstep \<Pi> (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim]:   "pstep \<Pi> (While b c, s, frs) cfg"
inductive_cases ScopeSE[elim!]:   "pstep \<Pi> (Scope c, s, frs) cfg"
inductive_cases CallSE[elim]:     "pstep \<Pi> (Call p, s, frs) cfg"
inductive_cases RestoreSE[elim!]: "pstep \<Pi> (Restore, s, frs) cfg"
(* -- Successful termination ----------------------------------------- *)

text \<open>
  Concrete Semantics calls a configuration final when no small step applies; for
  IMP that coincides with SKIP.  Here configurations carry a frame stack, so
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

(* A run of c from store s completes in t when it reaches a pfinal configuration
   whose store is t. *)
definition pruns_to :: "proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pruns_to \<Pi> c s t = psteps \<Pi> (c, s, []) (SKIP, t, [])"

lemma pruns_to_iff_reaches_pfinal:
  "pruns_to \<Pi> c s t \<longleftrightarrow>
     (\<exists>cfg. psteps \<Pi> (c, s, []) cfg \<and> pfinal cfg \<and> fst (snd cfg) = t)"
  unfolding pruns_to_def by auto

lemma pruns_to_skip: "pruns_to \<Pi> SKIP s s"
  unfolding pruns_to_def by (rule star.refl)

lemma pruns_to_assign: "pruns_to \<Pi> (Assign x a) s (s(x := aval a s))"
  by (simp add: pruns_to_def)

(* -- Sequencing lifts through the small-step --------------------------- *)

(* Reducing the first component of a sequence mirrors reducing it alone, with
   the frame stack threaded unchanged.  (Frame-aware analogue of star_seq2.) *)
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

(* Running c1 to s2 then c2 to t is a run of the sequence. *)
lemma pruns_to_Seq:
  assumes "pruns_to \<Pi> c1 s s2" and "pruns_to \<Pi> c2 s2 t"
  shows "pruns_to \<Pi> (Seq c1 c2) s t"
proof -
  from assms(1) have a: "star (pstep \<Pi>) (Seq c1 c2, s, []) (Seq SKIP c2, s2, [])"
    unfolding pruns_to_def by (rule psteps_Seq2)
  have b: "pstep \<Pi> (Seq SKIP c2, s2, []) (c2, s2, [])" by (rule Seq1)
  from a b assms(2) show ?thesis
    unfolding pruns_to_def by (meson star.step star_trans)
qed

lemma pruns_to_IfTrue:
  "bval b s \<Longrightarrow> pruns_to \<Pi> c1 s t \<Longrightarrow> pruns_to \<Pi> (If b c1 c2) s t"
  unfolding pruns_to_def by (meson IfTrue star.step)

lemma pruns_to_IfFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to \<Pi> c2 s t \<Longrightarrow> pruns_to \<Pi> (If b c1 c2) s t"
  unfolding pruns_to_def by (meson IfFalse star.step)

(* A false guard exits the loop with the store unchanged. *)
lemma pruns_to_WhileFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to \<Pi> (While b c) s s"
  unfolding pruns_to_def by (meson While IfFalse star.refl star.step)

(* A true guard runs the body then re-enters the loop. *)
lemma pruns_to_WhileTrue:
  assumes b:    "bval b s"
      and body: "pruns_to \<Pi> c s s2"
      and rest: "pruns_to \<Pi> (While b c) s2 t"
  shows "pruns_to \<Pi> (While b c) s t"
proof -
  have seq: "pruns_to \<Pi> (Seq c (While b c)) s t"
    using body rest by (rule pruns_to_Seq)
  have w: "pstep \<Pi> (While b c, s, [])
                    (If b (Seq c (While b c)) SKIP, s, [])"
    by (rule While)
  have i: "pstep \<Pi> (If b (Seq c (While b c)) SKIP, s, [])
                    (Seq c (While b c), s, [])"
    using b by (rule IfTrue)
  from w i seq show ?thesis unfolding pruns_to_def by (meson star.step)
qed


(* -- Frame-stack extension ------------------------------------------ *)

(* Extra frames appended at the bottom survive unchanged through any step. *)
lemma pstep_frame_extend_cfg:
  assumes "pstep \<Pi> X Y"
  shows "pstep \<Pi> (fst X, fst (snd X), snd (snd X) @ extra)
                  (fst Y, fst (snd Y), snd (snd Y) @ extra)"
  using assms
proof (induction rule: pstep.induct)
  case Assign show ?case by (simp only: fst_conv snd_conv) (rule pstep.Assign)
next
  case Restore
  show ?case by (simp only: fst_conv snd_conv append_Cons) (rule pstep.Restore)
next
  case Seq2 thus ?case by auto
qed simp_all

lemma pstep_frame_extend:
  "pstep \<Pi> (c, s, frs) (c', s', frs') ==>
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
  case (refl a) show ?case by (rule star.refl)
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
  "psteps \<Pi> (c, s, frs) (c', s', frs') ==>
   psteps \<Pi> (c, s, frs @ extra) (c', s', frs' @ extra)"
  using psteps_frame_extend_cfg[where X = "(c, s, frs)" and Y = "(c', s', frs')"]
  by simp

(* Lift body termination from empty stack to an arbitrary extra bottom. *)
lemma psteps_frame_mono:
  "psteps \<Pi> (c, s, []) (SKIP, t, []) ==>
   psteps \<Pi> (c, s, extra) (SKIP, t, extra)"
  using psteps_frame_extend[where frs = "[]" and frs' = "[]" and extra = extra]
  by simp

(* -- Scope and Call termination ------------------------------------- *)

(* After Scope/Call entry the body runs inside Seq c Restore with one saved
   caller frame.  Run the body to SKIP, then Restore pops back to empty stack. *)
lemma psteps_Seq_Restore_body:
  assumes "psteps \<Pi> (c, enter_state s, [s]) (SKIP, t', [s])"
  shows "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (SKIP, <s|t'>, [])"
proof -
  have body_seq: "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (Seq SKIP Restore, t', [s])"
    using psteps_Seq2[OF assms] .
  have step_seq1: "pstep \<Pi> (Seq SKIP Restore, t', [s]) (Restore, t', [s])"
    by (rule Seq1)
  have step_restore: "pstep \<Pi> (Restore, t', [s]) (SKIP, <s|t'>, [])"
    by (rule Restore)
  have tail: "psteps \<Pi> (Seq SKIP Restore, t', [s]) (SKIP, <s|t'>, [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  show ?thesis using body_seq tail by (rule star_trans)
qed

(* Scope and Call share the same entry configuration; only the first step
   differs. *)
lemma psteps_framed_entry:
  assumes entry: "pstep \<Pi> (cmd, s, []) (Seq c Restore, enter_state s, [s])"
  assumes body: "psteps \<Pi> (c, enter_state s, [s]) (SKIP, t', [s])"
  shows "psteps \<Pi> (cmd, s, []) (SKIP, <s|t'>, [])"
  using entry body psteps_Seq_Restore_body by (meson star.step star_trans)

lemma pruns_to_Scope:
  assumes body: "pruns_to \<Pi> c (enter_state s) t'"
  shows "pruns_to \<Pi> (Scope c) s (<s|t'>)"
  unfolding pruns_to_def
  by (rule psteps_framed_entry[OF Scope])
     (rule psteps_frame_mono[OF body[unfolded pruns_to_def], where extra = "[s]"])

lemma pruns_to_Call:
  assumes p: "\<Pi> p = Some c"
  assumes body: "pruns_to \<Pi> c (enter_state s) t'"
  shows "pruns_to \<Pi> (Call p) s (<s|t'>)"
  unfolding pruns_to_def
proof (rule psteps_framed_entry)
  show "pstep \<Pi> (Call p, s, []) (Seq c Restore, enter_state s, [s])"
    using p by (rule Call)
  show "psteps \<Pi> (c, enter_state s, [s]) (SKIP, t', [s])"
    using psteps_frame_mono[OF body[unfolded pruns_to_def], where extra = "[s]"] by simp
qed

(* A Scope body and a Call to the same body reduce to the identical
   configuration after their first step, so they have the same terminating
   runs.  This bridges IMP2's PCall (no scope) translated as Scope (...) back
   to our Call. *)
lemma pruns_to_Scope_Call:
  assumes p: "\<Pi> p = Some c"
  assumes run: "pruns_to \<Pi> (Scope c) s t"
  shows "pruns_to \<Pi> (Call p) s t"
proof -
  have run': "psteps \<Pi> (Scope c, s, []) (SKIP, t, [])"
    using run unfolding pruns_to_def .
  show ?thesis
  proof (cases rule: star.cases[OF run'])
    case 1
    then show ?thesis by auto
  next
    case (2 X Mid Z)
    from 2 have hd: "pstep \<Pi> (Scope c, s, []) Mid"
             and tl: "psteps \<Pi> Mid (SKIP, t, [])" by auto
    from hd have Yval: "Mid = (Seq c Restore, enter_state s, [s])"
      by auto
    have "pstep \<Pi> (Call p, s, []) (Seq c Restore, enter_state s, [s])"
      using p by (rule Call)
    with tl Yval show ?thesis
      unfolding pruns_to_def by (auto intro: star.step)
  qed
qed

end
