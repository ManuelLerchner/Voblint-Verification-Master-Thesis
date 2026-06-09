theory IMP2_Proc
  imports IMP2_SmallStep IMP2_Globals
begin

(*
  Procedure-extended command language `pcom` with a frame-stack small-step
  semantics, defined separately from the scalar command type `com`.

  Procedures are parameterless (PCall p); parameters are passed via globals.
  PScope and PCall both save the caller's locals on entry and restore them on
  exit via combine_states (globals from the callee's final store, locals from
  the saved frame).

  The restore boundary is made explicit by the runtime-only marker PRestore:
  the frame stack alone cannot locate a scope's end inside a PSeq, so entry
  rewrites `PScope c` to `PSeq c PRestore` (frame pushed) and PRestore performs
  the pop.  PRestore never appears in source programs.
*)

datatype pcom =
    PSKIP
  | PAssign vname aexp
  | PSeq    pcom pcom
  | PIf     bexp pcom pcom
  | PWhile  bexp pcom
  | PScope  pcom          (* local scope: save locals, restore on exit       *)
  | PCall   pname         (* call parameterless procedure from the table     *)
  | PRestore              (* runtime-only: pop a frame, restore caller locals *)

(* Procedure table: names to bodies. *)
type_synonym proc_table = "pname \<Rightarrow> pcom option"

(* Runtime frame: the caller's store, whose locals are restored on return. *)
type_synonym frame = store

(* -- Frame-stack small-step ----------------------------------------- *)

inductive
  pstep :: "proc_table \<Rightarrow> pcom \<times> store \<times> frame list
                       \<Rightarrow> pcom \<times> store \<times> frame list \<Rightarrow> bool"
  for pi :: proc_table
where
  PAssign:  "pstep pi (PAssign x a, s, frs) (PSKIP, s(x := aval a s), frs)"
| PSeq1:    "pstep pi (PSeq PSKIP c2, s, frs) (c2, s, frs)"
| PSeq2:    "pstep pi (c1, s, frs) (c1', s', frs')
             \<Longrightarrow> pstep pi (PSeq c1 c2, s, frs) (PSeq c1' c2, s', frs')"
| PIfTrue:  "bval b s \<Longrightarrow> pstep pi (PIf b c1 c2, s, frs) (c1, s, frs)"
| PIfFalse: "\<not> bval b s \<Longrightarrow> pstep pi (PIf b c1 c2, s, frs) (c2, s, frs)"
| PWhile:   "pstep pi (PWhile b c, s, frs)
                      (PIf b (PSeq c (PWhile b c)) PSKIP, s, frs)"
| PScope:   "pstep pi (PScope c, s, frs) (PSeq c PRestore, s, s # frs)"
| PCall:    "pi p = Some c
             \<Longrightarrow> pstep pi (PCall p, s, frs) (PSeq c PRestore, s, s # frs)"
| PRestore: "pstep pi (PRestore, s, fr # frs) (PSKIP, <fr|s>, frs)"

abbreviation
  psteps :: "proc_table \<Rightarrow> pcom \<times> store \<times> frame list
                        \<Rightarrow> pcom \<times> store \<times> frame list \<Rightarrow> bool"
where "psteps pi x y \<equiv> star (pstep pi) x y"

declare pstep.intros [simp, intro]

inductive_cases PSkipSE[elim!]:    "pstep pi (PSKIP, s, frs) cfg"
inductive_cases PAssignSE[elim!]:  "pstep pi (PAssign x a, s, frs) cfg"
inductive_cases PSeqSE[elim]:      "pstep pi (PSeq c1 c2, s, frs) cfg"
inductive_cases PIfSE[elim!]:      "pstep pi (PIf b c1 c2, s, frs) cfg"
inductive_cases PWhileSE[elim!]:   "pstep pi (PWhile b c, s, frs) cfg"
inductive_cases PScopeSE[elim!]:   "pstep pi (PScope c, s, frs) cfg"
inductive_cases PCallSE[elim]:     "pstep pi (PCall p, s, frs) cfg"
inductive_cases PRestoreSE[elim!]: "pstep pi (PRestore, s, frs) cfg"

(* -- The semantics is deterministic --------------------------------- *)

lemma pstep_deterministic:
  "pstep pi cs cs' \<Longrightarrow> pstep pi cs cs'' \<Longrightarrow> cs'' = cs'"
proof (induction arbitrary: cs'' rule: pstep.induct)
  case (PAssign x a s frs) then show ?case by blast
next
  case (PSeq1 c2 s frs) then show ?case by (blast elim: PSeqSE)
next
  case (PSeq2 c1 s frs c1' s' frs' c2)
  from PSeq2.prems PSeq2.hyps obtain c1'' s'' frs'' where
    cs'': "cs'' = (PSeq c1'' c2, s'', frs'')" and
    step: "pstep pi (c1, s, frs) (c1'', s'', frs'')"
    by (auto elim: PSeqSE)
  from PSeq2.IH[OF step] cs'' show ?case by simp
next
  case (PIfTrue b s c1 c2 frs) then show ?case by blast
next
  case (PIfFalse b s c1 c2 frs) then show ?case by blast
next
  case (PWhile b c s frs) then show ?case by blast
next
  case (PScope c s frs) then show ?case by blast
next
  case (PCall p c s frs) then show ?case by (auto elim: PCallSE)
next
  case (PRestore s fr frs) then show ?case by auto
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
  shows "psteps pi (PScope (PAssign x a), s, []) (PSKIP, s, [])"
proof -
  have eq: "<s | s(x := aval a s)> = s"
    by (rule combine_after_local_assign[OF assms])
  let ?s1 = "s(x := aval a s)"
  have a: "pstep pi (PScope (PAssign x a), s, []) (PSeq (PAssign x a) PRestore, s, [s])"
    by (rule PScope)
  have b: "pstep pi (PSeq (PAssign x a) PRestore, s, [s]) (PSeq PSKIP PRestore, ?s1, [s])"
    by (rule PSeq2[OF PAssign])
  have c: "pstep pi (PSeq PSKIP PRestore, ?s1, [s]) (PRestore, ?s1, [s])"
    by (rule PSeq1)
  have d: "pstep pi (PRestore, ?s1, [s]) (PSKIP, <s | ?s1>, [])"
    by (rule PRestore)
  have "psteps pi (PScope (PAssign x a), s, []) (PSKIP, <s | ?s1>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis by simp
qed

(* -- Terminating runs ----------------------------------------------- *)

(* A run of c from store s terminates in t when it reaches PSKIP with an empty
   frame stack. *)
definition pruns_to :: "proc_table \<Rightarrow> pcom \<Rightarrow> store \<Rightarrow> store \<Rightarrow> bool" where
  "pruns_to pi c s t = psteps pi (c, s, []) (PSKIP, t, [])"

lemma pruns_to_skip: "pruns_to pi PSKIP s s"
  unfolding pruns_to_def by (rule star.refl)

(* PSKIP is a normal form: no step leaves it (for any frame stack). *)
lemma pstep_PSKIP_stuck: "\<not> pstep pi (PSKIP, s, frs) cs"
  by (auto elim: PSkipSE)

lemma pruns_to_assign: "pruns_to pi (PAssign x a) s (s(x := aval a s))"
proof -
  have "pstep pi (PAssign x a, s, []) (PSKIP, s(x := aval a s), [])"
    by (rule PAssign)
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
  assumes p: "pi ''p'' = Some (PAssign ''Gx'' (Plus (V ''Gx'') (N 1)))"
  shows "pruns_to pi (PCall ''p'') s (s(''Gx'' := s ''Gx'' + 1))"
proof -
  let ?body = "PAssign ''Gx'' (Plus (V ''Gx'') (N 1))"
  let ?v = "aval (Plus (V ''Gx'') (N 1)) s"
  have g: "is_global ''Gx''" by (simp add: is_global_def)
  have a: "pstep pi (PCall ''p'', s, []) (PSeq ?body PRestore, s, [s])"
    using p by (blast intro: PCall)
  have b: "pstep pi (PSeq ?body PRestore, s, [s])
                    (PSeq PSKIP PRestore, s(''Gx'' := ?v), [s])"
    by (rule PSeq2[OF PAssign])
  have c: "pstep pi (PSeq PSKIP PRestore, s(''Gx'' := ?v), [s])
                    (PRestore, s(''Gx'' := ?v), [s])"
    by (rule PSeq1)
  have d: "pstep pi (PRestore, s(''Gx'' := ?v), [s]) (PSKIP, <s | s(''Gx'' := ?v)>, [])"
    by (rule PRestore)
  have eq: "<s | s(''Gx'' := ?v)> = s(''Gx'' := s ''Gx'' + 1)"
    using combine_after_global_assign[OF g] by simp
  have "psteps pi (PCall ''p'', s, []) (PSKIP, <s | s(''Gx'' := ?v)>, [])"
    using a b c d by (meson star.refl star.step)
  with eq show ?thesis unfolding pruns_to_def by simp
qed

(* -- Sequencing lifts through the small-step --------------------------- *)

(* Reducing the first component of a sequence mirrors reducing it alone, with
   the frame stack threaded unchanged.  (Frame-aware analogue of star_seq2.) *)
lemma psteps_PSeq2_cfg:
  assumes "star (pstep pi) X Y"
  shows "star (pstep pi)
           (PSeq (fst X) c2, fst (snd X), snd (snd X))
           (PSeq (fst Y) c2, fst (snd Y), snd (snd Y))"
  using assms
proof (induction rule: star.induct)
  case (refl a)
  show ?case by (rule star.refl)
next
  case (step a b c)
  obtain ca sa fa where a: "a = (ca, sa, fa)" by (cases a) auto
  obtain cb sb fb where b: "b = (cb, sb, fb)" by (cases b) auto
  from step.hyps(1) a b have "pstep pi (ca, sa, fa) (cb, sb, fb)" by simp
  hence "pstep pi (PSeq ca c2, sa, fa) (PSeq cb c2, sb, fb)" by (rule PSeq2)
  with step.IH a b show ?case by (auto intro: star.step)
qed

lemma psteps_PSeq2:
  "star (pstep pi) (c1, s, frs) (c1', s', frs')
   \<Longrightarrow> star (pstep pi) (PSeq c1 c2, s, frs) (PSeq c1' c2, s', frs')"
  using psteps_PSeq2_cfg[where X = "(c1, s, frs)" and Y = "(c1', s', frs')"] by simp

(* -- Structural composition of terminating runs ---------------------- *)

(* Running c1 to s2 then c2 to t is a run of the sequence. *)
lemma pruns_to_PSeq:
  assumes "pruns_to pi c1 s s2" and "pruns_to pi c2 s2 t"
  shows "pruns_to pi (PSeq c1 c2) s t"
proof -
  from assms(1) have a: "star (pstep pi) (PSeq c1 c2, s, []) (PSeq PSKIP c2, s2, [])"
    unfolding pruns_to_def by (rule psteps_PSeq2)
  have b: "pstep pi (PSeq PSKIP c2, s2, []) (c2, s2, [])" by (rule PSeq1)
  from a b assms(2) show ?thesis
    unfolding pruns_to_def by (meson star.step star_trans)
qed

lemma pruns_to_PIfTrue:
  "bval b s \<Longrightarrow> pruns_to pi c1 s t \<Longrightarrow> pruns_to pi (PIf b c1 c2) s t"
  unfolding pruns_to_def by (meson PIfTrue star.step)

lemma pruns_to_PIfFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to pi c2 s t \<Longrightarrow> pruns_to pi (PIf b c1 c2) s t"
  unfolding pruns_to_def by (meson PIfFalse star.step)

(* A false guard exits the loop with the store unchanged. *)
lemma pruns_to_PWhileFalse:
  "\<not> bval b s \<Longrightarrow> pruns_to pi (PWhile b c) s s"
  unfolding pruns_to_def by (meson PWhile PIfFalse star.refl star.step)

(* A true guard runs the body then re-enters the loop. *)
lemma pruns_to_PWhileTrue:
  assumes b:    "bval b s"
      and body: "pruns_to pi c s s2"
      and rest: "pruns_to pi (PWhile b c) s2 t"
  shows "pruns_to pi (PWhile b c) s t"
proof -
  have seq: "pruns_to pi (PSeq c (PWhile b c)) s t"
    using body rest by (rule pruns_to_PSeq)
  have w: "pstep pi (PWhile b c, s, [])
                    (PIf b (PSeq c (PWhile b c)) PSKIP, s, [])"
    by (rule PWhile)
  have i: "pstep pi (PIf b (PSeq c (PWhile b c)) PSKIP, s, [])
                    (PSeq c (PWhile b c), s, [])"
    using b by (rule PIfTrue)
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
  from assms have s1: "star (pstep pi) (c, s, []) (PSKIP, t, [])"
              and s2: "star (pstep pi) (c, s, []) (PSKIP, t', [])"
    unfolding pruns_to_def by auto
  have nb: "\<And>x. \<not> pstep pi (PSKIP, t, []) x" by (rule pstep_PSKIP_stuck)
  have nc: "\<And>x. \<not> pstep pi (PSKIP, t', []) x" by (rule pstep_PSKIP_stuck)
  from pstep_star_determ[OF s1 s2 nb nc] show ?thesis by simp
qed

end
