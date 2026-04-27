theory IMP2_Semantics
  imports IMP2_Syntax
begin

(*
  IMP2 -- Operational Semantics.

  Expression evaluation and big-step semantics for commands.
  Big-step style: big_step (c, s) t  means  c run from s halts in t.
  (Tuple argument style follows HOL-IMP.Big_Step convention.)
*)

(* ── Expression Evaluation ────────────────────────────────────── *)

fun aval :: "aexp => state => int" where
    "aval (N n)       _  = n"
  | "aval (V x)       s  = s x"
  | "aval (Plus  a b) s  = aval a s + aval b s"
  | "aval (Minus a b) s  = aval a s - aval b s"
  | "aval (Times a b) s  = aval a s * aval b s"

fun bval :: "bexp => state => bool" where
    "bval (Bc v)      _  = v"
  | "bval (Not b)     s  = (~ bval b s)"
  | "bval (And b1 b2) s  = (bval b1 s & bval b2 s)"
  | "bval (Or  b1 b2) s  = (bval b1 s | bval b2 s)"
  | "bval (Less a b)  s  = (aval a s < aval b s)"
  | "bval (Eq   a b)  s  = (aval a s = aval b s)"

(* ── Big-Step Semantics ───────────────────────────────────────── *)

inductive
  big_step :: "com * state => state => bool"
where
    Skip:
      "big_step (SKIP, s) s"
  | Assign:
      "big_step (x ::= a, s) (s(x := aval a s))"
  | Seq:
      "big_step (c1, s) s'  ==>  big_step (c2, s') s''
       ==>  big_step (c1 ;; c2, s) s''"
  | IfTrue:
      "bval b s  ==>  big_step (c1, s) s'
       ==>  big_step (IF b THEN c1 ELSE c2, s) s'"
  | IfFalse:
      "~ bval b s  ==>  big_step (c2, s) s'
       ==>  big_step (IF b THEN c1 ELSE c2, s) s'"
  | WhileFalse:
      "~ bval b s
       ==>  big_step (WHILE b DO c, s) s"
  | WhileTrue:
      "bval b s  ==>  big_step (c, s) s'
       ==>  big_step (WHILE b DO c, s') s''
       ==>  big_step (WHILE b DO c, s) s''"

lemmas big_step_induct = big_step.induct[split_format(complete)]

(* ── Basic Properties ─────────────────────────────────────────── *)

lemma big_step_determ:
  "big_step (c, s) t1  ==>  big_step (c, s) t2  ==>  t1 = t2"
  sorry

end
