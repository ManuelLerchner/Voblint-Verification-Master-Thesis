theory IMP2_Proc
  imports IMP2_SmallStep IMP2_Globals
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
  for pi :: proc_table
where
  Assign:  "pstep pi (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
| Seq1:    "pstep pi (Seq SKIP c2, s, frs) (c2, s, frs)"
| Seq2:    "pstep pi (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> pstep pi (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
| IfTrue:  "bval b s \<Longrightarrow> pstep pi (If b c1 c2, s, frs) (c1, s, frs)"
| IfFalse: "\<not> bval b s \<Longrightarrow> pstep pi (If b c1 c2, s, frs) (c2, s, frs)"
| While:   "pstep pi (While b c, s, frs)
                      (If b (Seq c (While b c)) SKIP, s, frs)"
| Scope:   "pstep pi (Scope c, s, frs) (Seq c Restore, s, s # frs)"
| Call:    "pi p = Some c
             \<Longrightarrow> pstep pi (Call p, s, frs) (Seq c Restore, s, s # frs)"
| Restore: "pstep pi (Restore, s, fr # frs) (SKIP, <fr|s>, frs)"

abbreviation
  psteps :: "proc_table \<Rightarrow> com \<times> store \<times> frame list
                        \<Rightarrow> com \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps pi x y \<equiv> star (pstep pi) x y"

declare pstep.intros [simp, intro]

inductive_cases SkipSE[elim!]:    "pstep pi (SKIP, s, frs) cfg"
inductive_cases AssignSE[elim!]:  "pstep pi (Assign x a, s, frs) cfg"
inductive_cases SeqSE[elim]:      "pstep pi (Seq c1 c2, s, frs) cfg"
inductive_cases IfSE[elim!]:      "pstep pi (If b c1 c2, s, frs) cfg"
inductive_cases WhileSE[elim!]:   "pstep pi (While b c, s, frs) cfg"
inductive_cases ScopeSE[elim!]:   "pstep pi (Scope c, s, frs) cfg"
inductive_cases CallSE[elim]:     "pstep pi (Call p, s, frs) cfg"
inductive_cases RestoreSE[elim!]: "pstep pi (Restore, s, frs) cfg"

(* -- The semantics is deterministic --------------------------------- *)

lemma pstep_deterministic:
  "pstep pi cs cs' \<Longrightarrow> pstep pi cs cs'' \<Longrightarrow> cs'' = cs'"
proof (induction arbitrary: cs'' rule: pstep.induct)
  case (Assign x a s frs) then show ?case by blast
next
  case (Seq1 c2 s frs) then show ?case by (blast elim: SeqSE)
next
  case (Seq2 c1 s frs c1' s' frs' c2)
  from Seq2.prems Seq2.hyps obtain c1'' s'' frs'' where
    cs'': "cs'' = (Seq c1'' c2, s'', frs'')" and
    step: "pstep pi (c1, s, frs) (c1'', s'', frs'')"
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
  shows "psteps pi (Scope (Assign x a), s, []) (SKIP, s, [])"
proof -
  have eq: "<s | s(x := aval a s)> = s"
    by (rule combine_after_local_assign[OF assms])
  let ?s1 = "s(x := aval a s)"
  have a: "pstep pi (Scope (Assign x a), s, []) (Seq (Assign x a) Restore, s, [s])"
    by (rule Scope)
  have b: "pstep pi (Seq (Assign x a) Restore, s, [s]) (Seq SKIP Restore, ?s1, [s])"
    by (rule Seq2[OF Assign])
  have c: "pstep pi (Seq SKIP Restore, ?s1, [s]) (Restore, ?s1, [s])"
    by (rule Seq1)
  have d: "pstep pi (Restore, ?s1, [s]) (SKIP, <s | ?s1>, [])"
    by (rule Restore)
  have "psteps pi (Scope (Assign x a), s, []) (SKIP, <s | ?s1>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis by simp
qed

(* -- Terminating runs ----------------------------------------------- *)

(* A run of c from store s terminates in t when it reaches SKIP with an empty
   frame stack. *)
definition pruns_to :: "proc_table \<Rightarrow> com \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pruns_to pi c s t = psteps pi (c, s, []) (SKIP, t, [])"

lemma pruns_to_skip: "pruns_to pi SKIP s s"
  unfolding pruns_to_def by (rule star.refl)

(* SKIP is a normal form: no step leaves it (for any frame stack). *)
lemma pstep_SKIP_stuck: "\<not> pstep pi (SKIP, s, frs) cs"
  by (auto elim: SkipSE)

lemma pruns_to_assign: "pruns_to pi (Assign x a) s (s(x := aval a s))"
proof -
  have "pstep pi (Assign x a, s, []) (SKIP, s(x := aval a s), [])"
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
  assumes p: "pi ''p'' = Some (Assign ''Gx'' (Plus (V ''Gx'') (N 1)))"
  shows "pruns_to pi (Call ''p'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "Assign ''Gx'' (Plus (V ''Gx'') (N 1))"
  let ?v = "aval (Plus (V ''Gx'') (N 1)) s"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  have a: "pstep pi (Call ''p'', s, []) (Seq ?body Restore, s, [s])"
    using p by (blast intro: Call)
  have b: "pstep pi (Seq ?body Restore, s, [s])
                    (Seq SKIP Restore, s(''Gx'' := ?v), [s])"
    by (rule Seq2[OF Assign])
  have c: "pstep pi (Seq SKIP Restore, s(''Gx'' := ?v), [s])
                    (Restore, s(''Gx'' := ?v), [s])"
    by (rule Seq1)
  have d: "pstep pi (Restore, s(''Gx'' := ?v), [s]) (SKIP, <s | s(''Gx'' := ?v)>, [])"
    by (rule Restore)
  have eq: "<s | s(''Gx'' := ?v)> = s(''Gx'' := s ''Gx'' + 1)"
    using combine_after_global_assign[OF g] by simp
  have "psteps pi (Call ''p'', s, []) (SKIP, <s | s(''Gx'' := ?v)>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis unfolding pruns_to_def by simp
qed

(* -- Sequencing lifts through the small-step --------------------------- *)

(* Reducing the first component of a sequence mirrors reducing it alone, with
   the frame stack threaded unchanged.  (Frame-aware analogue of star_seq2.) *)
lemma psteps_Seq2_cfg:
  assumes "star (pstep pi) X Y"
  shows "star (pstep pi)
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
  from step.hyps(1) a b have "pstep pi (ca, sa, fa) (cb, sb, fb)" by simp
  hence "pstep pi (Seq ca c2, sa, fa) (Seq cb c2, sb, fb)" by (rule Seq2)
  with step.IH a b show ?case by (auto intro: star.step)
qed

lemma psteps_Seq2:
  "star (pstep pi) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (pstep pi) (Seq c1 c2, s, frs) (Seq c1' c2, s', frs')"
  using psteps_Seq2_cfg[where X = "(c1, s, frs)" and Y = "(c1', s', frs')"] by simp

(* -- Structural composition of terminating runs ---------------------- *)

(* Running c1 to s2 then c2 to t is a run of the sequence. *)
lemma pruns_to_Seq:
  assumes "pruns_to pi c1 s s2" and "pruns_to pi c2 s2 t"
  shows "pruns_to pi (Seq c1 c2) s t"
proof -
  from assms(1) have a: "star (pstep pi) (Seq c1 c2, s, []) (Seq SKIP c2, s2, [])"
    unfolding pruns_to_def by (rule psteps_Seq2)
  have b: "pstep pi (Seq SKIP c2, s2, []) (c2, s2, [])" by (rule Seq1)
  from a b assms(2) show ?thesis
    unfolding pruns_to_def by (meson star.step star_trans)
qed

lemma pruns_to_IfTrue:
  "bval b s \<Longrightarrow> pruns_to pi c1 s t \<Longrightarrow> pruns_to pi (If b c1 c2) s t"
  unfolding pruns_to_def by (meson IfTrue star.step)

lemma pruns_to_IfFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to pi c2 s t \<Longrightarrow> pruns_to pi (If b c1 c2) s t"
  unfolding pruns_to_def by (meson IfFalse star.step)

(* A false guard exits the loop with the store unchanged. *)
lemma pruns_to_WhileFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to pi (While b c) s s"
  unfolding pruns_to_def by (meson While IfFalse star.refl star.step)

(* A true guard runs the body then re-enters the loop. *)
lemma pruns_to_WhileTrue:
  assumes b:    "bval b s"
      and body: "pruns_to pi c s s2"
      and rest: "pruns_to pi (While b c) s2 t"
  shows "pruns_to pi (While b c) s t"
proof -
  have seq: "pruns_to pi (Seq c (While b c)) s t"
    using body rest by (rule pruns_to_Seq)
  have w: "pstep pi (While b c, s, [])
                    (If b (Seq c (While b c)) SKIP, s, [])"
    by (rule While)
  have i: "pstep pi (If b (Seq c (While b c)) SKIP, s, [])
                    (Seq c (While b c), s, [])"
    using b by (rule IfTrue)
  from w i seq show ?thesis unfolding pruns_to_def by (meson star.step)
qed

(* -- Determinism of terminating runs --------------------------------- *)

(* A deterministic relation reaches at most one normal form. *)
lemma pstep_star_determ:
  "star (pstep pi) a b \<Longrightarrow> star (pstep pi) a c \<Longrightarrow>
   (\<And>x. \<not> pstep pi b x) \<Longrightarrow> (\<And>x. \<not> pstep pi c x) \<Longrightarrow> b = c"
proof (induction arbitrary: c rule: star.induct)
  case (refl a)
  from refl.prems(1) show ?case
  proof (cases rule: star.cases)
    case refl
    then show ?thesis by simp
  next
    case (step d)
    then have "pstep pi a d" by auto
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
    then have ad: "pstep pi a d" and dc: "star (pstep pi) d c" by auto
    from pstep_deterministic[OF outer_step ad] have da: "d = a'" .
    have "star (pstep pi) a' c" using dc da by simp
    from outer_ih[OF this nb nc] show ?thesis .
  qed
qed

(* Hence a run is functional: the terminating result is unique. *)
lemma pruns_to_determ:
  assumes "pruns_to pi c s t" and "pruns_to pi c s t'"
  shows "t = t'"
proof -
  from assms have s1: "star (pstep pi) (c, s, []) (SKIP, t, [])"
              and s2: "star (pstep pi) (c, s, []) (SKIP, t', [])"
    unfolding pruns_to_def by auto
  have nb: "\<And>x. \<not> pstep pi (SKIP, t, []) x" by (rule pstep_SKIP_stuck)
  have nc: "\<And>x. \<not> pstep pi (SKIP, t', []) x" by (rule pstep_SKIP_stuck)
  from pstep_star_determ[OF s1 s2 nb nc] show ?thesis by simp
qed

end
