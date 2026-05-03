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

lemma big_step_SeqE:
  assumes "big_step (c1 ;; c2, s) u"
  obtains s' where "big_step (c1, s) s'" and "big_step (c2, s') u"
  using assms by cases

lemma big_step_IfE:
  assumes "big_step (IF b THEN c1 ELSE c2, s) u"
  obtains (true) "bval b s" "big_step (c1, s) u"
    | (false) "\<not> bval b s" "big_step (c2, s) u"
  using assms by cases

lemma big_step_WhileE:
  assumes "big_step (WHILE b DO c, s) u"
  obtains (exit) "\<not> bval b s" "u = s"
    | (loop) s' where "bval b s" "big_step (c, s) s'" "big_step (WHILE b DO c, s') u"
  using assms by cases

lemma big_step_If_iff:
  "big_step (IF b THEN c1 ELSE c2, s) u \<longleftrightarrow>
   (bval b s \<and> big_step (c1, s) u) \<or> (\<not> bval b s \<and> big_step (c2, s) u)"
proof (intro iffI)
  assume H: "big_step (IF b THEN c1 ELSE c2, s) u"
  show "(bval b s \<and> big_step (c1, s) u) \<or> (\<not> bval b s \<and> big_step (c2, s) u)"
    using H by (cases rule: big_step.cases) auto
next
  assume "(bval b s \<and> big_step (c1, s) u) \<or> (\<not> bval b s \<and> big_step (c2, s) u)"
  then show "big_step (IF b THEN c1 ELSE c2, s) u"
    by (auto intro: IfTrue IfFalse)
qed

lemma big_step_determ:
  "big_step (c, s) t1 \<Longrightarrow> big_step (c, s) t2 \<Longrightarrow> t1 = t2"
proof (induction arbitrary: t2 rule: big_step.induct)
  case Skip
  then show ?case by (cases rule: big_step.cases) auto
next
  case Assign
  then show ?case by (cases rule: big_step.cases) auto
next
  case (Seq c1 s s' c2 s'')
  from Seq.prems obtain u where u1: "big_step (c1, s) u" and u2: "big_step (c2, u) t2"
    by (rule big_step_SeqE)
  from u1 Seq.IH(1) have "u = s'" by blast
  with u2 Seq.IH(2) show ?case by blast
next
  case (IfTrue b s c1 s' c2)
  from IfTrue.prems show ?case
  proof (cases rule: big_step_IfE)
    case true
    with IfTrue.hyps(2) IfTrue.IH show ?thesis by blast
  next
    case false
    with IfTrue.hyps(1) show ?thesis by simp
  qed
next
  case (IfFalse b s c2 s' c1)
  from IfFalse.prems show ?case
  proof (cases rule: big_step_IfE)
    case true
    with IfFalse.hyps(1) show ?thesis by simp
  next
    case false
    with IfFalse.hyps(2) IfFalse.IH show ?thesis by blast
  qed
next
  case (WhileFalse b s c)
  from WhileFalse.prems show ?case
  proof (cases rule: big_step_WhileE)
    case exit
    then show ?thesis by simp
  next
    case loop
    with WhileFalse.hyps(1) show ?thesis by simp
  qed
next
  case (WhileTrue b s c s' s'')
  from WhileTrue.prems show ?case
  proof (cases rule: big_step_WhileE)
    case exit
    with WhileTrue.hyps(1) show ?thesis by simp
  next
    case (loop s2)
    from loop(2) WhileTrue.hyps(2) have "s2 = s'"
      using WhileTrue.IH(1) by blast
    with loop(3) WhileTrue.hyps(3) WhileTrue.IH(2) show ?thesis by blast
  qed
qed

end
