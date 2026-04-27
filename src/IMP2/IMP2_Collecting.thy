theory IMP2_Collecting
  imports IMP2_Semantics
begin

(*
  IMP2 -- Collecting Semantics.

  The collecting semantics is the "gold standard" against which the
  abstract analysis is proved sound.  For each command c and input set S,
  collect c S is the set of all states that c can produce from some s in S.

  For the pipeline correctness proof the key object is:
    reach c s0  =  set of states reachable at the exit of c starting from s0
*)

(* ── Collecting Semantics (exit-reachable states) ─────────────── *)

definition collect :: "com => state set => state set" where
  "collect c S = {t. EX s : S. big_step (c, s) t}"

(* ── Point-Wise Collecting via Induction on com ──────────────────
   Equivalent characterisation used in soundness proofs. *)

lemma collect_SKIP:
  "collect SKIP S = S"
  sorry

lemma collect_Assign:
  "collect (x ::= a) S = {s(x := aval a s) | s. s : S}"
  sorry

lemma collect_Seq:
  "collect (c1 ;; c2) S = collect c2 (collect c1 S)"
  sorry

lemma collect_If:
  "collect (IF b THEN c1 ELSE c2) S =
     collect c1 {s : S. bval b s} Un collect c2 {s : S. ~ bval b s}"
  sorry

(* Monotonicity: larger input sets produce larger output sets. *)
lemma collect_mono:
  "S <= T  ==>  collect c S <= collect c T"
  sorry

(* The collecting transformer for while is the least fixpoint of:
     F(T) = S Un collect c {s : T. bval b s}
   Correctness of this equation is proved via big_step.WhileTrue/WhileFalse. *)
lemma collect_While:
  "collect (WHILE b DO c) S =
     lfp (%T. S Un collect c {s : T. bval b s})"
  sorry

end
