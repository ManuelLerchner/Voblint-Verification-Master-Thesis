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

  The restore boundary is made explicit by the runtime-only marker
  RestoreInternal: the frame stack alone cannot locate a scope's end inside a
  Seq, so entry rewrites Scope/Call to a Seq ending in RestoreInternal. It
  never appears in source programs.
*)

datatype com =
    SKIP
  | Assign vname aexp
  | Seq    com com
  | If     bexp com com
  | While  bexp com
  | Scope  com
  | Call   "vname option" pname "aexp list"
  | RestoreInternal "aexp option"

record proc_decl =
  formals :: "vname list"
  body    :: com
  result  :: "aexp option"

abbreviation proc_decl_legacy :: "com => proc_decl" where
  "proc_decl_legacy c \<equiv> \<lparr>formals = [], body = c, result = None\<rparr>"

abbreviation Restore :: com where
  "Restore \<equiv> RestoreInternal None"

(* Procedure table: names to declarations. *)
type_synonym proc_table = "pname \<Rightarrow> proc_decl option"

(* Runtime frame: the caller's store plus the optional destination variable. *)
datatype frame = Frame store "vname option"

definition bind_formals :: "vname list \<Rightarrow> int list \<Rightarrow> store \<Rightarrow> store" where
  "bind_formals xs vs s =
     fold (\<lambda>(x, v) st. st(x := v)) (zip xs vs) s"

fun combine_assign :: "vname option \<Rightarrow> int option \<Rightarrow> store \<Rightarrow> store option" where
  "combine_assign None _ s = Some s"
| "combine_assign (Some x) (Some v) s = Some (s(x := v))"
| "combine_assign (Some x) None s = None"

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
              (Seq c (RestoreInternal None), enter_state s, Frame s None # frs)"
| Call:    "\<Pi> p = Some decl
             \<Longrightarrow> length actuals = length (formals decl)
             \<Longrightarrow> distinct (formals decl)
             \<Longrightarrow> (\<forall>x. dst = Some x \<longrightarrow> result decl \<noteq> None)
             \<Longrightarrow> vals = map (\<lambda>e. aval e s) actuals
             \<Longrightarrow> callee = bind_formals (formals decl) vals (enter_state s)
             \<Longrightarrow> pstep \<Pi> (Call dst p actuals, s, frs)
                 (Seq (body decl) (RestoreInternal (result decl)),
                  callee,
                  Frame s dst # frs)"
| RestoreNone:
    "pstep \<Pi> (RestoreInternal r, s, Frame fr None # frs) (SKIP, <fr|s>, frs)"
| RestoreSome:
    "pstep \<Pi> (RestoreInternal (Some e), s, Frame fr (Some x) # frs)
       (SKIP, (<fr|s>)(x := aval e s), frs)"

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
  "pstep \<Pi> (RestoreInternal r, s, frs) cfg"

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
  case RestoreNone
  show ?case by (simp only: fst_conv snd_conv append_Cons) (rule pstep.RestoreNone)
next
  case RestoreSome
  show ?case by (simp only: fst_conv snd_conv append_Cons) (rule pstep.RestoreSome)
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

lemma psteps_Seq_Restore_None_body:
  assumes "psteps \<Pi> (c, s0, [Frame fr None]) (SKIP, t', [Frame fr None])"
  shows "psteps \<Pi> (Seq c (RestoreInternal r), s0, [Frame fr None])
           (SKIP, <fr|t'>, [])"
proof -
  have body_seq:
    "psteps \<Pi> (Seq c (RestoreInternal r), s0, [Frame fr None])
       (Seq SKIP (RestoreInternal r), t', [Frame fr None])"
    using psteps_Seq2[OF assms] .
  have step_seq1:
    "pstep \<Pi> (Seq SKIP (RestoreInternal r), t', [Frame fr None])
       (RestoreInternal r, t', [Frame fr None])"
    by (rule Seq1)
  have step_restore:
    "pstep \<Pi> (RestoreInternal r, t', [Frame fr None]) (SKIP, <fr|t'>, [])"
    by (rule RestoreNone)
  have tail:
    "psteps \<Pi> (Seq SKIP (RestoreInternal r), t', [Frame fr None])
       (SKIP, <fr|t'>, [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  show ?thesis using body_seq tail by (rule star_trans)
qed

lemma psteps_Seq_Restore_Some_body:
  assumes "psteps \<Pi> (c, s0, [Frame fr (Some x)])
             (SKIP, t', [Frame fr (Some x)])"
  shows "psteps \<Pi> (Seq c (RestoreInternal (Some e)), s0, [Frame fr (Some x)])
           (SKIP, (<fr|t'>)(x := aval e t'), [])"
proof -
  have body_seq:
    "psteps \<Pi> (Seq c (RestoreInternal (Some e)), s0, [Frame fr (Some x)])
       (Seq SKIP (RestoreInternal (Some e)), t', [Frame fr (Some x)])"
    using psteps_Seq2[OF assms] .
  have step_seq1:
    "pstep \<Pi> (Seq SKIP (RestoreInternal (Some e)), t', [Frame fr (Some x)])
       (RestoreInternal (Some e), t', [Frame fr (Some x)])"
    by (rule Seq1)
  have step_restore:
    "pstep \<Pi> (RestoreInternal (Some e), t', [Frame fr (Some x)])
       (SKIP, (<fr|t'>)(x := aval e t'), [])"
    by (rule RestoreSome)
  have tail:
    "psteps \<Pi> (Seq SKIP (RestoreInternal (Some e)), t', [Frame fr (Some x)])
       (SKIP, (<fr|t'>)(x := aval e t'), [])"
    using step_seq1 step_restore by (meson star.refl star.step)
  show ?thesis using body_seq tail by (rule star_trans)
qed

lemma pcompletes_Scope:
  assumes body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Scope c) s (<s|t'>)"
  unfolding pcompletes_def
  apply (rule star.step)
   apply (rule Scope)
  using psteps_Seq_Restore_None_body[OF psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s None]"]]
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
          (Seq (body decl) (RestoreInternal (result decl)), ?callee, [Frame s dst])"
    using p arity distinct_formals no_ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s dst]) (SKIP, t', [Frame s dst])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s dst]"] by simp
  have framed_none:
    "psteps \<Pi> (body decl, ?callee, [Frame s None]) (SKIP, t', [Frame s None])"
    using no_ret framed by simp
  have restored:
    "psteps \<Pi> (Seq (body decl) (RestoreInternal (result decl)), ?callee, [Frame s None])
       (SKIP, <s|t'>, [])"
    by (rule psteps_Seq_Restore_None_body[OF framed_none])
  from no_ret restored show "psteps \<Pi> (Seq (body decl) (RestoreInternal (result decl)), ?callee, [Frame s dst])
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
          (Seq (body decl) (RestoreInternal (result decl)), ?callee, [Frame s (Some x)])"
    using p arity distinct_formals ret
    by (intro Call[where vals = ?vals and callee = ?callee]) auto
  have framed:
    "psteps \<Pi> (body decl, ?callee, [Frame s (Some x)]) (SKIP, t', [Frame s (Some x)])"
    using psteps_frame_mono[OF body[unfolded pcompletes_def], where extra = "[Frame s (Some x)]"] by simp
  show "psteps \<Pi> (Seq (body decl) (RestoreInternal (result decl)), ?callee, [Frame s (Some x)])
          (SKIP, (<s|t'>)(x := aval e t'), [])"
    using ret framed
    by simp (rule psteps_Seq_Restore_Some_body)
qed

lemma pcompletes_Legacy_Call:
  assumes p: "\<Pi> p = Some (proc_decl_legacy c)"
      and body: "pcompletes \<Pi> c (enter_state s) t'"
  shows "pcompletes \<Pi> (Call None p []) s (<s|t'>)"
proof (rule pcompletes_Call_none)
  show "\<Pi> p = Some (proc_decl_legacy c)" by (rule p)
  show "length [] = length (formals (proc_decl_legacy c))" by simp
  show "distinct (formals (proc_decl_legacy c))" by simp
  show "None = None" by simp
  show "pcompletes \<Pi> (body (proc_decl_legacy c))
          (bind_formals (formals (proc_decl_legacy c)) (map (\<lambda>e. aval e s) []) (enter_state s)) t'"
    using body by (simp add: bind_formals_def)
qed

lemma pcompletes_Scope_Call_legacy:
  assumes p: "\<Pi> p = Some (proc_decl_legacy c)"
      and run: "pcompletes \<Pi> (Scope c) s t"
  shows "pcompletes \<Pi> (Call None p []) s t"
proof -
  have step_scope:
    "pstep \<Pi> (Scope c, s, [])
       (Seq c (RestoreInternal None), enter_state s, [Frame s None])"
    by (rule Scope)
  have p': "\<Pi> p = Some \<lparr>formals = [], body = c, result = None\<rparr>"
    using p by simp
  have step_call_raw:
    "pstep \<Pi> (Call None p [], s, [])
       (Seq (body \<lparr>formals = [], body = c, result = None\<rparr>)
            (RestoreInternal (result \<lparr>formals = [], body = c, result = None\<rparr>)),
        bind_formals (formals \<lparr>formals = [], body = c, result = None\<rparr>) [] (enter_state s),
        [Frame s None])"
    using p'
    by (intro pstep.Call[where vals = "[]"
                              and callee = "bind_formals (formals \<lparr>formals = [], body = c, result = None\<rparr>) [] (enter_state s)"])
       auto
  have step_call:
    "pstep \<Pi> (Call None p [], s, [])
       (Seq c (RestoreInternal None), enter_state s, [Frame s None])"
    using step_call_raw by (simp add: bind_formals_def)
  from run[unfolded pcompletes_def] step_scope have tail:
    "psteps \<Pi> (Seq c (RestoreInternal None), enter_state s, [Frame s None]) (SKIP, t, [])"
    by (metis Pair_inject ScopeSE com.distinct(9) star.cases)
  show ?thesis
    unfolding pcompletes_def using step_call tail by (meson star.step)
qed

end

