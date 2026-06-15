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

inductive_cases SkipSE[elim!]:    "pstep \<Pi> (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:  "pstep \<Pi> (Assign x a, s, frs) cfg"
inductive_cases SeqSE[elim]:      "pstep \<Pi> (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:      "pstep \<Pi> (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim!]:   "pstep \<Pi> (While b c, s, frs) cfg"
inductive_cases ScopeSE[elim!]:   "pstep \<Pi> (Scope c, s, frs) cfg"
inductive_cases CallSE[elim]:     "pstep \<Pi> (Call p, s, frs) cfg"
inductive_cases RestoreSE[elim!]: "pstep \<Pi> (Restore, s, frs) cfg"

(* -- The semantics is deterministic --------------------------------- *)

lemma pstep_deterministic:
  "pstep \<Pi> cs cs' \<Longrightarrow> pstep \<Pi> cs cs'' \<Longrightarrow> cs'' = cs'"
proof (induction arbitrary: cs'' rule: pstep.induct)
  case (Assign x a s frs) then show ?case by blast
next
  case (Seq1 c2 s frs) then show ?case by (blast elim: SeqSE)
next
  case (Seq2 c1 s frs c1' s' frs' c2)
  from Seq2.prems Seq2.hyps obtain c1'' s'' frs'' where
    cs'': "cs'' = (Seq c1'' c2, s'', frs'')" and
    step: "pstep \<Pi> (c1, s, frs) (c1'', s'', frs'')"
    by (auto elim: SeqSE)
  from Seq2.IH[OF step] cs'' show ?case by simp
next
  case (IfTrue b s c1 c2 frs) then show ?case by blast
next
  case (IfFalse b s c1 c2 frs) then show ?case by blast
next
  case (While b c s frs) then show ?case by blast
next
  case (Scope c s frs) then show ?case by blast
next
  case (Call p c s frs) then show ?case by (auto elim: CallSE)
next
  case (Restore s fr frs) then show ?case by auto
qed

(* -- Frame mechanism: a scope restores locals, commits globals ------ *)

text \<open>
  Validation of the frame mechanism.  Assigning a local variable inside a
  scope has no net effect on the store: the body's write is undone by the
  restore (locals come from the saved frame), so the run returns to the
  starting store.
\<close>

lemma combine_after_local_assign:
  assumes "\<not> is_global x"
  shows "<s | s(x := v)> = s"
  using assms by (rule_tac ext) auto

lemma scope_local_assign_noop:
  assumes "\<not> is_global x"
  shows "psteps \<Pi> (Scope (Assign x a), s, []) (SKIP, s, [])"
proof -
  (* Entry zeroes locals; the local write is then undone by the restore. *)
  let ?es = "enter_state s"
  let ?s1 = "?es(x := aval a ?es)"
  have eq: "<s | ?s1> = s"
    by (rule ext) (auto simp: enter_state_def assms)
  have a: "pstep \<Pi> (Scope (Assign x a), s, []) (Seq (Assign x a) Restore, ?es, [s])"
    by (rule Scope)
  have b: "pstep \<Pi> (Seq (Assign x a) Restore, ?es, [s]) (Seq SKIP Restore, ?s1, [s])"
    by (rule Seq2[OF Assign])
  have c: "pstep \<Pi> (Seq SKIP Restore, ?s1, [s]) (Restore, ?s1, [s])"
    by (rule Seq1)
  have d: "pstep \<Pi> (Restore, ?s1, [s]) (SKIP, <s | ?s1>, [])"
    by (rule Restore)
  have "psteps \<Pi> (Scope (Assign x a), s, []) (SKIP, <s | ?s1>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis by simp
qed

(* -- Terminating runs ----------------------------------------------- *)

(* A run of c from store s terminates in t when it reaches SKIP with an empty
   frame stack. *)
definition pruns_to :: "proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pruns_to \<Pi> c s t = psteps \<Pi> (c, s, []) (SKIP, t, [])"

lemma pruns_to_skip: "pruns_to \<Pi> SKIP s s"
  unfolding pruns_to_def by (rule star.refl)

(* SKIP is a normal form: no step leaves it (for any frame stack). *)
lemma pstep_SKIP_stuck: "\<not> pstep \<Pi> (SKIP, s, frs) cs"
  by (auto elim: SkipSE)

lemma pruns_to_assign: "pruns_to \<Pi> (Assign x a) s (s(x := aval a s))"
proof -
  have "pstep \<Pi> (Assign x a, s, []) (SKIP, s(x := aval a s), [])"
    by (rule Assign)
  thus ?thesis unfolding pruns_to_def by (meson star.refl star.step)
qed

(* A write to a global commits: combining over a global update keeps the new
   value (dual to combine_after_local_assign). *)
lemma combine_after_global_assign:
  assumes "is_global x"
  shows "<s | s(x := v)> = s(x := v)"
  using assms by (rule_tac ext) auto

(* A procedure call runs the callee body and commits its writes to globals,
   while the caller's locals are restored.  Here the body increments the global
   ''Gx'', and the increment persists in the returned store. *)
lemma pcall_global_increment:
  assumes p: "\<Pi> ''p'' = Some (Assign ''Gx'' (Plus (V ''Gx'') (N 1)))"
  shows "pruns_to \<Pi> (Call ''p'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "Assign ''Gx'' (Plus (V ''Gx'') (N 1))"
  let ?es = "enter_state s"
  let ?v = "aval (Plus (V ''Gx'') (N 1)) ?es"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  (* Entry zeroes locals; Gx is global, so the increment reads s ''Gx''. *)
  have a: "pstep \<Pi> (Call ''p'', s, []) (Seq ?body Restore, ?es, [s])"
    using p by (blast intro: Call)
  have b: "pstep \<Pi> (Seq ?body Restore, ?es, [s])
                    (Seq SKIP Restore, ?es(''Gx'' := ?v), [s])"
    by (rule Seq2[OF Assign])
  have c: "pstep \<Pi> (Seq SKIP Restore, ?es(''Gx'' := ?v), [s])
                    (Restore, ?es(''Gx'' := ?v), [s])"
    by (rule Seq1)
  have d: "pstep \<Pi> (Restore, ?es(''Gx'' := ?v), [s])
                    (SKIP, <s | ?es(''Gx'' := ?v)>, [])"
    by (rule Restore)
  have eq: "<s | ?es(''Gx'' := ?v)> = s(''Gx'' := s ''Gx'' + 1)"
    by (rule ext) (simp add: enter_state_def is_global_def)
  have "psteps \<Pi> (Call ''p'', s, []) (SKIP, <s | ?es(''Gx'' := ?v)>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis unfolding pruns_to_def by simp
qed

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
  case Seq2 thus ?case by (auto intro: pstep.Seq2)
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

lemma pruns_to_Scope:
  assumes body: "pruns_to \<Pi> c (enter_state s) t'"
  shows "pruns_to \<Pi> (Scope c) s (<s|t'>)"
unfolding pruns_to_def
proof -
  have step_scope: "pstep \<Pi> (Scope c, s, []) (Seq c Restore, enter_state s, [s])"
    by (rule Scope)
  have body_lifted: "psteps \<Pi> (c, enter_state s, [s]) (SKIP, t', [s])"
    using psteps_frame_mono[OF body[unfolded pruns_to_def], where extra = "[s]"] by simp
  have body_seq: "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (Seq SKIP Restore, t', [s])"
    using psteps_Seq2[OF body_lifted] .
  have step_seq1: "pstep \<Pi> (Seq SKIP Restore, t', [s]) (Restore, t', [s])"
    by (rule Seq1)
  have step_restore: "pstep \<Pi> (Restore, t', [s]) (SKIP, <s|t'>, [])"
    by (rule Restore)
  have tail: "psteps \<Pi> (Seq SKIP Restore, t', [s]) (SKIP, <s|t'>, [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  have mid: "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (SKIP, <s|t'>, [])"
    using body_seq tail by (rule star_trans)
  show "psteps \<Pi> (Scope c, s, []) (SKIP, <s|t'>, [])"
    by (rule star.step[OF step_scope mid])
qed

lemma pruns_to_Call:
  assumes p: "\<Pi> p = Some c"
  assumes body: "pruns_to \<Pi> c (enter_state s) t'"
  shows "pruns_to \<Pi> (Call p) s (<s|t'>)"
unfolding pruns_to_def
proof -
  have step_call: "pstep \<Pi> (Call p, s, []) (Seq c Restore, enter_state s, [s])"
    using p by (rule Call)
  have body_lifted: "psteps \<Pi> (c, enter_state s, [s]) (SKIP, t', [s])"
    using psteps_frame_mono[OF body[unfolded pruns_to_def], where extra = "[s]"] by simp
  have body_seq: "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (Seq SKIP Restore, t', [s])"
    using psteps_Seq2[OF body_lifted] .
  have step_seq1: "pstep \<Pi> (Seq SKIP Restore, t', [s]) (Restore, t', [s])"
    by (rule Seq1)
  have step_restore: "pstep \<Pi> (Restore, t', [s]) (SKIP, <s|t'>, [])"
    by (rule Restore)
  have tail: "psteps \<Pi> (Seq SKIP Restore, t', [s]) (SKIP, <s|t'>, [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  have mid: "psteps \<Pi> (Seq c Restore, enter_state s, [s]) (SKIP, <s|t'>, [])"
    using body_seq tail by (rule star_trans)
  show "psteps \<Pi> (Call p, s, []) (SKIP, <s|t'>, [])"
    by (rule star.step[OF step_call mid])
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
      by (auto elim!: ScopeSE)
    have "pstep \<Pi> (Call p, s, []) (Seq c Restore, enter_state s, [s])"
      using p by (rule Call)
    with tl Yval show ?thesis
      unfolding pruns_to_def by (auto intro: star.step)
  qed
qed



(* A deterministic relation reaches at most one normal form. *)
lemma pstep_star_determ:
  "star (pstep \<Pi>) a b \<Longrightarrow> star (pstep \<Pi>) a c \<Longrightarrow>
   (\<And>x. \<not> pstep \<Pi> b x) \<Longrightarrow> (\<And>x. \<not> pstep \<Pi> c x) \<Longrightarrow> b = c"
proof (induction arbitrary: c rule: star.induct)
  case (refl a)
  from refl.prems(1) show ?case
  proof (cases rule: star.cases)
    case refl
    then show ?thesis by simp
  next
    case (step d)
    then have "pstep \<Pi> a d" by auto
    with refl.prems(2) show ?thesis by blast
  qed
next
  case (step a a' b)
  note outer_step = step.hyps(1) and outer_ih = step.IH
    and nb = step.prems(2) and nc = step.prems(3)
  from step.prems(1) show ?case
  proof (cases rule: star.cases)
    case refl
    with outer_step nc show ?thesis by blast
  next
    case (step d)
    then have ad: "pstep \<Pi> a d" and dc: "star (pstep \<Pi>) d c" by auto
    from pstep_deterministic[OF outer_step ad] have da: "d = a'" .
    have "star (pstep \<Pi>) a' c" using dc da by simp
    from outer_ih[OF this nb nc] show ?thesis .
  qed
qed

(* Hence a run is functional: the terminating result is unique. *)
lemma pruns_to_determ:
  assumes "pruns_to \<Pi> c s t" and "pruns_to \<Pi> c s t'"
  shows "t = t'"
proof -
  from assms have s1: "star (pstep \<Pi>) (c, s, []) (SKIP, t, [])"
              and s2: "star (pstep \<Pi>) (c, s, []) (SKIP, t', [])"
    unfolding pruns_to_def by auto
  have nb: "\<And>x. \<not> pstep \<Pi> (SKIP, t, []) x" by (rule pstep_SKIP_stuck)
  have nc: "\<And>x. \<not> pstep \<Pi> (SKIP, t', []) x" by (rule pstep_SKIP_stuck)
  from pstep_star_determ[OF s1 s2 nb nc] show ?thesis by simp
qed

end
