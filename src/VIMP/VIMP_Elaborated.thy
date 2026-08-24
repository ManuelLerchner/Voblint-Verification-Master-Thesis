theory VIMP_Elaborated
  imports VIMP_Typing
begin

section \<open>Elaborated expressions\<close>

text \<open>
  \<open>texp\<close> is \<open>exp\<close> with every arithmetic/literal node's operating kind
  baked in by \<open>elaborate\<close>, so \<open>teval\<close> can evaluate it with no
  \<open>tyenv\<close>/\<open>ikind\<close> parameter at all -- every consumer downstream of
  elaboration reads whatever kind it needs directly off the node in hand,
  the same way a CIL \<open>Var varinfo\<close> node already carries its resolved
  type. \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> need no kind of their own: their
  result is always a context-free \<open>0\<close>/\<open>1\<close>, exactly as \<open>taval\<close>'s own
  equations for them never call \<open>ik_norm\<close> on that result -- only their
  operands, each elaborated at its own synthesized kind, carry one.
\<close>

datatype texp =
    TN ikind int
  | TV ikind vname
  | TPlus  ikind texp texp
  | TMinus ikind texp texp
  | TTimes ikind texp texp
  | TLess texp texp
  | TEq texp texp
  | TNot texp
  | TAnd texp texp
  | TOr texp texp

text \<open>
  \<open>elaborate \<Gamma> ik e\<close> mirrors \<open>taval \<Gamma> ik e\<close>'s own recursion exactly,
  node for node: \<open>ik\<close> propagates unchanged through \<open>Plus\<close>/\<open>Minus\<close>/
  \<open>Times\<close>, and \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> each recompute a fresh
  operating kind for their operand(s) from \<open>esyn\<close>, exactly where \<open>taval\<close>
  does. \<open>elaborate_syn\<close> is the top-level entry with no externally given
  \<open>ik\<close>, mirroring \<open>taval_syn\<close>.
\<close>

fun elaborate :: "tyenv => ikind => exp => texp" where
  "elaborate \<Gamma> ik (N n) = TN ik n"
| "elaborate \<Gamma> ik (V x) = TV ik x"
| "elaborate \<Gamma> ik (Plus e1 e2) = TPlus ik (elaborate \<Gamma> ik e1) (elaborate \<Gamma> ik e2)"
| "elaborate \<Gamma> ik (Minus e1 e2) = TMinus ik (elaborate \<Gamma> ik e1) (elaborate \<Gamma> ik e2)"
| "elaborate \<Gamma> ik (Times e1 e2) = TTimes ik (elaborate \<Gamma> ik e1) (elaborate \<Gamma> ik e2)"
| "elaborate \<Gamma> ik (Less e1 e2) =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in TLess (elaborate \<Gamma> k e1) (elaborate \<Gamma> k e2))"
| "elaborate \<Gamma> ik (Eq e1 e2) =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in TEq (elaborate \<Gamma> k e1) (elaborate \<Gamma> k e2))"
| "elaborate \<Gamma> ik (Not e) = TNot (elaborate \<Gamma> (opk (esyn \<Gamma> e)) e)"
| "elaborate \<Gamma> ik (And e1 e2) =
     TAnd (elaborate \<Gamma> (opk (esyn \<Gamma> e1)) e1) (elaborate \<Gamma> (opk (esyn \<Gamma> e2)) e2)"
| "elaborate \<Gamma> ik (Or e1 e2) =
     TOr (elaborate \<Gamma> (opk (esyn \<Gamma> e1)) e1) (elaborate \<Gamma> (opk (esyn \<Gamma> e2)) e2)"

definition elaborate_syn :: "tyenv => exp => texp" where
  "elaborate_syn \<Gamma> e = elaborate \<Gamma> (opk (esyn \<Gamma> e)) e"

text \<open>
  \<open>teval\<close> is \<open>taval\<close> with the kind bookkeeping already done: every
  arithmetic/literal node norms at its own embedded kind, and every
  comparison/logical node evaluates its (already correctly-kinded)
  operands with no further parameter.
\<close>

fun teval :: "texp => store => int" where
  "teval (TN ik n) s = ik_norm ik n"
| "teval (TV ik x) s = ik_norm ik (s x)"
| "teval (TPlus ik a b) s = ik_norm ik (teval a s + teval b s)"
| "teval (TMinus ik a b) s = ik_norm ik (teval a s - teval b s)"
| "teval (TTimes ik a b) s = ik_norm ik (teval a s * teval b s)"
| "teval (TLess a b) s = (if teval a s < teval b s then 1 else 0)"
| "teval (TEq a b) s = (if teval a s = teval b s then 1 else 0)"
| "teval (TNot a) s = (if teval a s = 0 then 1 else 0)"
| "teval (TAnd a b) s = (if teval a s \<noteq> 0 \<and> teval b s \<noteq> 0 then 1 else 0)"
| "teval (TOr a b) s = (if teval a s \<noteq> 0 \<or> teval b s \<noteq> 0 then 1 else 0)"

section \<open>Elaboration is faithful to the typed evaluator\<close>

theorem teval_elaborate [simp]: "teval (elaborate \<Gamma> ik e) s = taval \<Gamma> ik e s"
  by (induction e arbitrary: ik) (simp_all add: Let_def)

theorem teval_elaborate_syn [simp]: "teval (elaborate_syn \<Gamma> e) s = taval_syn \<Gamma> e s"
  by (simp add: elaborate_syn_def taval_syn_def)

end
