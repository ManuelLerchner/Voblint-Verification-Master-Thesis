theory IMP2_Bridge
  imports IMP2_Proc "IMP2.Semantics"
begin

(*
  One-way bridge: our structural expressions/state -> AFP IMP2.

  Direction is strict: structural -> IMP2. We never read IMP2's reflected
  int=>int=>int operators back, so the analyzer stays executable. See
  docs/AFP_IMP2_REBASE_MIGRATION.md (Phase 1) and AFP_IMP2_REUSE_DECISION.md.

  Two structural gaps bridged here:
    1. Operators: our tags Plus/Minus/Times/Less/Eq/And/Or map forward to
       IMP2's reflected Binop (+), Cmpop (<), BBinop conj, ...
    2. State: our scalar store (vname => int) embeds into IMP2's array state
       (vname => int => int) as an index-agnostic constant array. Our
       expressions never index, so the array dimension is inert and the
       default scalar index (IMP2 uses N 0) never matters.

  Qualified names disambiguate the heavy clash between three layers:
    - ours      : IMP2_Syntax.aexp/bexp, IMP2_Expr.aval/bval
    - Nipkow    : AExp.aexp/aval, BExp.bexp/bval (wrapped under BaseN/BaseB)
    - AFP IMP2  : Syntax.aexp/bexp, Semantics.aval/bval/state
*)

(* -- State embedding ------------------------------------------------- *)

(* Scalar store as an index-agnostic constant array. *)
definition embed :: "store => (vname => int => int)" where
  "embed s = (%x i. s x)"

(* -- Nipkow leaf -> IMP2 (BaseN/BaseB wrap whole Nipkow subtrees) ----- *)

fun nip_aexp :: "AExp.aexp => Syntax.aexp" where
  "nip_aexp (AExp.N n)      = Syntax.N n"
| "nip_aexp (AExp.V x)      = Syntax.Vidx x (Syntax.N 0)"
| "nip_aexp (AExp.Plus a b) = Syntax.Binop (+) (nip_aexp a) (nip_aexp b)"

lemma aval_nip: "AExp.aval a s = Semantics.aval (nip_aexp a) (embed s)"
  by (induction a) (simp_all add: embed_def)

fun nip_bexp :: "BExp.bexp => Syntax.bexp" where
  "nip_bexp (BExp.Bc v)      = Syntax.Bc v"
| "nip_bexp (BExp.Not b)     = Syntax.Not (nip_bexp b)"
| "nip_bexp (BExp.And b1 b2) = Syntax.BBinop conj (nip_bexp b1) (nip_bexp b2)"
| "nip_bexp (BExp.Less a b)  = Syntax.Cmpop (<) (nip_aexp a) (nip_aexp b)"

lemma bval_nip: "BExp.bval b s = Semantics.bval (nip_bexp b) (embed s)"
  by (induction b) (simp_all add: aval_nip)

(* -- Our (extended) expressions -> IMP2 ------------------------------ *)

fun to_imp2_aexp :: "IMP2_Syntax.aexp => Syntax.aexp" where
  "to_imp2_aexp (BaseN a)              = nip_aexp a"
| "to_imp2_aexp (IMP2_Syntax.Plus a b) = Syntax.Binop (+) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_aexp (Minus a b)            = Syntax.Binop (-) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_aexp (Times a b)            = Syntax.Binop times (to_imp2_aexp a) (to_imp2_aexp b)"

lemma aval_to_imp2: "IMP2_Expr.aval e s = Semantics.aval (to_imp2_aexp e) (embed s)"
  by (induction e) (simp_all add: aval_nip)

fun to_imp2_bexp :: "IMP2_Syntax.bexp => Syntax.bexp" where
  "to_imp2_bexp (BaseB b)              = nip_bexp b"
| "to_imp2_bexp (IMP2_Syntax.Not b)    = Syntax.Not (to_imp2_bexp b)"
| "to_imp2_bexp (IMP2_Syntax.And b1 b2) = Syntax.BBinop conj (to_imp2_bexp b1) (to_imp2_bexp b2)"
| "to_imp2_bexp (Or b1 b2)             = Syntax.BBinop disj (to_imp2_bexp b1) (to_imp2_bexp b2)"
| "to_imp2_bexp (IMP2_Syntax.Less a b) = Syntax.Cmpop (<) (to_imp2_aexp a) (to_imp2_aexp b)"
| "to_imp2_bexp (Eq a b)               = Syntax.Cmpop (=) (to_imp2_aexp a) (to_imp2_aexp b)"

lemma bval_to_imp2: "IMP2_Expr.bval e s = Semantics.bval (to_imp2_bexp e) (embed s)"
  by (induction e) (simp_all add: aval_to_imp2 bval_nip)

(* -- Commands --------------------------------------------------------- *)

(*
  to_imp2_com maps our procedure-extended command language to IMP2's com.
  Assignment goes to an array write at the default index N 0; Call maps to
  IMP2's PCall. Restore is runtime-only (never in source programs); it is
  mapped to SKIP for totality and never reached on translated source.

  Procedure-table translation wraps every body in Syntax.Scope: our Call
  saves/restores the caller's locals via the frame stack, and IMP2's PCall
  has no scope of its own, so the scoping must live in the translated body.

  Scope/Call entry matches IMP2 exactly: pstep Scope/Call zeros the locals
  on entry (enter_state s = <<>|s>) and restores the caller's locals on exit
  via the frame stack (<fr|s'>). IMP2's SCOPE does the same (<<>|s> on entry,
  <s|s'> on exit). The translation is a faithful correspondence for the full
  language; the forward command/collecting simulation covers the full language
  including scope and call.
*)

fun to_imp2_com :: "IMP2_Proc.com => Syntax.com" where
  "to_imp2_com IMP2_Proc.com.SKIP           = Syntax.SKIP"
| "to_imp2_com (IMP2_Proc.com.Assign x a)   = Syntax.AssignIdx x (Syntax.N 0) (to_imp2_aexp a)"
| "to_imp2_com (IMP2_Proc.com.Seq c1 c2)    = Syntax.Seq (to_imp2_com c1) (to_imp2_com c2)"
| "to_imp2_com (IMP2_Proc.com.If b c1 c2)   = Syntax.If (to_imp2_bexp b) (to_imp2_com c1) (to_imp2_com c2)"
| "to_imp2_com (IMP2_Proc.com.While b c)    = Syntax.While (to_imp2_bexp b) (to_imp2_com c)"
| "to_imp2_com (IMP2_Proc.com.Scope c)      = Syntax.Scope (to_imp2_com c)"
| "to_imp2_com (IMP2_Proc.com.Call p)       = Syntax.PCall p"
| "to_imp2_com IMP2_Proc.com.Restore        = Syntax.SKIP"

definition to_imp2_pi :: "proc_table => Syntax.program" where
  "to_imp2_pi \<Pi> = (%p. map_option (%c. Syntax.Scope (to_imp2_com c)) (\<Pi> p))"

(* -- State projection: read every array back at the default index ---- *)

definition proj0 :: "(vname => int => int) => store" where
  "proj0 S = (%x. S x 0)"

lemma proj0_embed: "proj0 (embed s) = s"
  by (simp add: proj0_def embed_def)

(* -- Per-command agreement: assignment at the default array index ----- *)

(*
  An assignment translates to an IMP2 array write at index 0. From an
  embedded state, IMP2's big-step produces the array updated at index 0;
  projecting back at index 0 recovers exactly our scalar update
  s(x := aval a s).
*)

lemma to_imp2_Assign_bigstep:
  "Semantics.big_step P (to_imp2_com (IMP2_Proc.com.Assign x a), embed s)
        ((embed s)(x := ((embed s) x)(0 := IMP2_Expr.aval a s)))"
proof -
  have "Semantics.big_step P
          (Syntax.AssignIdx x (Syntax.N 0) (to_imp2_aexp a), embed s)
          ((embed s)(x := ((embed s) x)
             (Semantics.aval (Syntax.N 0) (embed s) := Semantics.aval (to_imp2_aexp a) (embed s))))"
    by (rule Semantics.AssignIdx)
  thus ?thesis by (simp add: aval_to_imp2)
qed

lemma proj0_Assign:
  "proj0 ((embed s)(x := ((embed s) x)(0 := IMP2_Expr.aval a s)))
     = s(x := IMP2_Expr.aval a s)"
  by (rule ext) (simp add: proj0_def embed_def)

(* -- Expression agreement under projection ----------------------------- *)

(*
  embed is not preserved by IMP2 array assignment: an assignment writes only
  index 0, so after one write the array is no longer the constant array embed
  produces. The right invariant for a command simulation is therefore the
  weaker projection relation proj0 S = s, not strict S = embed s.

  Our translated expressions only ever read index 0 (Vidx x (N 0)), so the
  expression agreement holds under the projection relation alone. These
  generalise aval_to_imp2 / bval_to_imp2 (recovered by proj0_embed) and are
  the reusable core for a command/collecting simulation.
*)

lemma aval_nip_sim:
  "proj0 S = s ==> Semantics.aval (nip_aexp a) S = AExp.aval a s"
  by (induction a) (auto simp: proj0_def fun_eq_iff)

lemma aval_to_imp2_sim:
  "proj0 S = s ==> Semantics.aval (to_imp2_aexp e) S = IMP2_Expr.aval e s"
  by (induction e) (simp_all add: aval_nip_sim)

lemma bval_nip_sim:
  "proj0 S = s ==> Semantics.bval (nip_bexp b) S = BExp.bval b s"
  by (induction b) (simp_all add: aval_nip_sim)

lemma bval_to_imp2_sim:
  "proj0 S = s ==> Semantics.bval (to_imp2_bexp e) S = IMP2_Expr.bval e s"
  by (induction e) (simp_all add: aval_to_imp2_sim bval_nip_sim)

(* -- Locals/globals split agrees with IMP2 --------------------------- *)

(*
  Our is_global (IMP2_Globals) now matches AFP IMP2's is_global (Syntax)
  exactly: the empty name and names starting with 'G' are global, all others
  local.  Hence combine_states / enter_state correspond on the nose under
  proj0, with no side condition on variable names.
*)

lemma is_global_eq: "Syntax.is_global x = IMP2_Globals.is_global x"
  by (cases x rule: Syntax.is_global.cases) (auto simp: is_global_def)

(* Projecting an IMP2 state combination at index 0 is our state combination. *)
lemma proj0_combine_states:
  "proj0 (Semantics.combine_states S T)
     = IMP2_Globals.combine_states (proj0 S) (proj0 T)"
  by (rule ext)
     (simp add: proj0_def Semantics.combine_states_def combine_states_def is_global_eq)

(* Projecting IMP2's scope-entry state recovers our enter_state. *)
lemma proj0_null_combine:
  "proj0 (Semantics.combine_states Semantics.null_state s) = enter_state (proj0 s)"
  by (rule ext)
     (simp add: proj0_def Semantics.combine_states_def Semantics.null_state_def
                enter_state_def is_global_eq)

(* -- Source programs: no runtime-only Restore ------------------------ *)

(*
  Restore is a runtime-only marker pushed by Scope/Call; it never occurs in a
  source program.  source_com pins this down structurally, and source_pi lifts
  it to every body in a procedure table.
*)

fun source_com :: "IMP2_Proc.com => bool" where
  "source_com IMP2_Proc.com.SKIP         = True"
| "source_com (IMP2_Proc.com.Assign x a) = True"
| "source_com (IMP2_Proc.com.Seq c1 c2)  = (source_com c1 \<and> source_com c2)"
| "source_com (IMP2_Proc.com.If b c1 c2) = (source_com c1 \<and> source_com c2)"
| "source_com (IMP2_Proc.com.While b c)  = source_com c"
| "source_com (IMP2_Proc.com.Scope c)    = source_com c"
| "source_com (IMP2_Proc.com.Call p)     = True"
| "source_com IMP2_Proc.com.Restore      = False"

definition source_pi :: "proc_table => bool" where
  "source_pi \<Pi> = (\<forall>p c. \<Pi> p = Some c \<longrightarrow> source_com c)"

(* -- Backward simulation: IMP2 big-step -> our small-step ------------- *)

(*
  Every terminating AFP IMP2 run of a translated source command is reproduced
  by our frame-stack small-step semantics, read back through proj0.  The proof
  is by rule induction on IMP2's big-step derivation; each rule maps to the
  matching pruns_to combinator.  source_pi pins down that procedure bodies are
  source commands (no runtime-only Restore); the runtime-only IMP2 commands
  (ArrayCpy, CLEAR, Assign_Locals, PScope) are never in the range of
  to_imp2_com and hence vacuous.
*)

lemma backward_sim_aux:
  assumes sp: "source_pi \<Pi>"
  shows "big_step Pg (cm, S) T ==> Pg = to_imp2_pi \<Pi> ==> cm = to_imp2_com c
          ==> source_com c ==> pruns_to \<Pi> c (proj0 S) (proj0 T)"
proof (induction arbitrary: c rule: big_step_induct)
  case (Skip Pg s)
  hence "c = IMP2_Proc.com.SKIP" by (cases c) auto
  thus ?case by (simp add: pruns_to_skip)
next
  case (AssignIdx Pg x i a s)
  then obtain a0 where c: "c = IMP2_Proc.com.Assign x a0"
      and ae: "a = to_imp2_aexp a0" and ie: "i = Syntax.N 0"
    by (cases c) auto
  have run: "pruns_to \<Pi> (IMP2_Proc.com.Assign x a0) (proj0 s)
               ((proj0 s)(x := IMP2_Expr.aval a0 (proj0 s)))"
    by (rule pruns_to_assign)
  have res: "proj0 (s(x := (s x)(Semantics.aval i s := Semantics.aval a s)))
               = (proj0 s)(x := IMP2_Expr.aval a0 (proj0 s))"
    using ae ie by (auto simp: proj0_def aval_to_imp2_sim fun_eq_iff)
  show ?case using c run res by (simp add: fun_upd_def)
next
  case (ArrayCpy Pg x y s)
  thus ?case by (cases c) auto
next
  case (ArrayClear Pg x s)
  thus ?case by (cases c) auto
next
  case (Assign_Locals Pg l s)
  thus ?case by (cases c) auto
next
  case (Seq Pg cm1 s1 s2 cm2 s3)
  then obtain a b where c: "c = IMP2_Proc.com.Seq a b"
      and 1: "cm1 = to_imp2_com a" and 2: "cm2 = to_imp2_com b"
    by (cases c) auto
  from Seq.prems c have sa: "source_com a" and sb: "source_com b" by auto
  have r1: "pruns_to \<Pi> a (proj0 s1) (proj0 s2)"
    using Seq.IH(1)[OF Seq.prems(1) 1 sa] .
  have r2: "pruns_to \<Pi> b (proj0 s2) (proj0 s3)"
    using Seq.IH(2)[OF Seq.prems(1) 2 sb] .
  from r1 r2 have "pruns_to \<Pi> (IMP2_Proc.com.Seq a b) (proj0 s1) (proj0 s3)"
    by (rule pruns_to_Seq)
  thus ?case using c by simp
next
  case (IfTrue b s Pg cm1 t cm2)
  then obtain b0 a d where c: "c = IMP2_Proc.com.If b0 a d"
      and be: "b = to_imp2_bexp b0" and 1: "cm1 = to_imp2_com a"
      and 2: "cm2 = to_imp2_com d"
    by (cases c) auto
  from IfTrue.prems c have sa: "source_com a" by auto
  have guard: "IMP2_Expr.bval b0 (proj0 s)"
    using IfTrue.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pruns_to \<Pi> a (proj0 s) (proj0 t)"
    using IfTrue.IH[OF IfTrue.prems(1) 1 sa] .
  from guard bodyrun have "pruns_to \<Pi> (IMP2_Proc.com.If b0 a d) (proj0 s) (proj0 t)"
    by (rule pruns_to_IfTrue)
  thus ?case using c by simp
next
  case (IfFalse b s Pg cm2 t cm1)
  then obtain b0 a d where c: "c = IMP2_Proc.com.If b0 a d"
      and be: "b = to_imp2_bexp b0" and 1: "cm1 = to_imp2_com a"
      and 2: "cm2 = to_imp2_com d"
    by (cases c) auto
  from IfFalse.prems c have sd: "source_com d" by auto
  have guard: "\<not> IMP2_Expr.bval b0 (proj0 s)"
    using IfFalse.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pruns_to \<Pi> d (proj0 s) (proj0 t)"
    using IfFalse.IH[OF IfFalse.prems(1) 2 sd] .
  from guard bodyrun have "pruns_to \<Pi> (IMP2_Proc.com.If b0 a d) (proj0 s) (proj0 t)"
    by (rule pruns_to_IfFalse)
  thus ?case using c by simp
next
  case (Scope Pg cm0 s s')
  then obtain a where c: "c = IMP2_Proc.com.Scope a" and 0: "cm0 = to_imp2_com a"
    by (cases c) auto
  from Scope.prems c have sa: "source_com a" by auto
  have body: "pruns_to \<Pi> a (enter_state (proj0 s)) (proj0 s')"
    using Scope.IH[OF Scope.prems(1) 0 sa] by (simp add: proj0_null_combine)
  have "pruns_to \<Pi> (IMP2_Proc.com.Scope a) (proj0 s)
          (IMP2_Globals.combine_states (proj0 s) (proj0 s'))"
    using body by (rule pruns_to_Scope)
  hence "pruns_to \<Pi> (IMP2_Proc.com.Scope a) (proj0 s)
          (proj0 (Semantics.combine_states s s'))"
    by (simp add: proj0_combine_states)
  thus ?case using c by simp
next
  case (WhileFalse b s Pg cm0)
  then obtain b0 a where c: "c = IMP2_Proc.com.While b0 a"
      and be: "b = to_imp2_bexp b0" and 0: "cm0 = to_imp2_com a"
    by (cases c) auto
  have guard: "\<not> IMP2_Expr.bval b0 (proj0 s)"
    using WhileFalse.hyps(1) be by (auto simp: bval_to_imp2_sim)
  from guard have "pruns_to \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s) (proj0 s)"
    by (rule pruns_to_WhileFalse)
  thus ?case using c by simp
next
  case (WhileTrue b s1 Pg cm0 s2 s3)
  then obtain b0 a where c: "c = IMP2_Proc.com.While b0 a"
      and be: "b = to_imp2_bexp b0" and ce: "cm0 = to_imp2_com a"
    by (cases c) auto
  from WhileTrue.prems c have sa: "source_com a" by auto
  have guard: "IMP2_Expr.bval b0 (proj0 s1)"
    using WhileTrue.hyps(1) be by (auto simp: bval_to_imp2_sim)
  have bodyrun: "pruns_to \<Pi> a (proj0 s1) (proj0 s2)"
    using WhileTrue.IH(1)[OF WhileTrue.prems(1) ce sa] .
  have eqw: "Syntax.While b cm0 = to_imp2_com (IMP2_Proc.com.While b0 a)"
    using be ce by simp
  have sw: "source_com (IMP2_Proc.com.While b0 a)" using sa by simp
  have looprun: "pruns_to \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s2) (proj0 s3)"
    using WhileTrue.IH(2)[OF WhileTrue.prems(1) eqw sw] .
  from guard bodyrun looprun
  have "pruns_to \<Pi> (IMP2_Proc.com.While b0 a) (proj0 s1) (proj0 s3)"
    by (rule pruns_to_WhileTrue)
  thus ?case using c by simp
next
  case (PCall Pg p cbody s t)
  then have c: "c = IMP2_Proc.com.Call p" by (cases c) auto
  from PCall.hyps(1) PCall.prems(1) obtain c0 where pip: "\<Pi> p = Some c0"
      and cb: "cbody = Syntax.Scope (to_imp2_com c0)"
    by (auto simp: to_imp2_pi_def split: option.splits)
  from sp pip have s0: "source_com c0" by (auto simp: source_pi_def)
  have eq: "cbody = to_imp2_com (IMP2_Proc.com.Scope c0)" using cb by simp
  have sc0: "source_com (IMP2_Proc.com.Scope c0)" using s0 by simp
  have scoperun: "pruns_to \<Pi> (IMP2_Proc.com.Scope c0) (proj0 s) (proj0 t)"
    using PCall.IH[OF PCall.prems(1) eq sc0] .
  have "pruns_to \<Pi> (IMP2_Proc.com.Call p) (proj0 s) (proj0 t)"
    by (rule pruns_to_Scope_Call[OF pip scoperun])
  thus ?case using c by simp
next
  case (PScope Pg pi' cm0 s t)
  thus ?case by (cases c) auto
qed

(*
  Headline restatement: the analyzer's soundness is now expressible against AFP
  IMP2's standard concrete semantics.  Whenever the translated source program
  terminates under IMP2 big-step, our small-step semantics reaches the same
  final store (read back through proj0).  Composed with the existing pipeline
  soundness (stated against pruns_to / cfg_collect), this transfers soundness to
  AFP IMP2 with no further proof obligation on the analyzer side.
*)

theorem backward_sim:
  assumes bs: "big_step (to_imp2_pi \<Pi>) (cm, S) T"
      and sp: "source_pi \<Pi>"
      and cc: "cm = to_imp2_com c"
      and sc: "source_com c"
  shows "pruns_to \<Pi> c (proj0 S) (proj0 T)"
  using backward_sim_aux[OF sp bs refl cc sc] .

subsection \<open>Executable examples\<close>

value "source_com IMP2_Proc.com.SKIP"
value "source_com IMP2_Proc.com.Restore"
value "source_com (IMP2_Proc.com.Seq IMP2_Proc.com.SKIP IMP2_Proc.com.SKIP)"

value "to_imp2_com IMP2_Proc.com.SKIP"
value "to_imp2_com (IMP2_Proc.com.Scope IMP2_Proc.com.SKIP)"
value "to_imp2_com (IMP2_Proc.com.Seq IMP2_Proc.com.SKIP IMP2_Proc.com.SKIP)"

value "embed (\<lambda>_. 5::int) ''x'' 0"
value "proj0 (\<lambda>v (n::int). 7::int) ''x''"

end
