theory VIMP_Elaborated
  imports VIMP_Typing VIMP_Expr
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

  \<open>TCast\<close> is the one node with no \<open>exp\<close> counterpart: it is the explicit
  conversion a write site performs, in the role of CIL's \<open>CastE\<close>. An
  assignment, an actual-argument binding, a returned value, and a special
  call's destination each evaluate a subexpression at its own synthesized
  kind and then convert the result to the target's declared kind; baking
  that conversion into the elaborated tree is what lets a consumer of a
  \<open>texp\<close> reproduce the whole write, target conversion included, with
  no typing environment in hand.
\<close>

datatype texp =
    TN ikind int
  | TVar ikind vname
  | TPlus  ikind texp texp
  | TMinus ikind texp texp
  | TTimes ikind texp texp
  | TCast  ikind texp
  | TLess texp texp
  | TEq texp texp
  | TNot texp
  | TAnd texp texp
  | TOr texp texp

instance texp :: countable
  by countable_datatype

text \<open>The executable linear order gives \<^const>\<open>sorted_list_of_set\<close> a deterministic
  representation of the compiled edge sets a \<^typ>\<open>texp\<close> payload sits in,
  exactly as \<^typ>\<open>exp\<close>'s own derivation does for the untyped syntax.\<close>
derive linorder texp

text \<open>
  \<open>elaborate \<Gamma> ik e\<close> mirrors \<open>taval \<Gamma> ik e\<close>'s own recursion exactly,
  node for node: \<open>ik\<close> propagates unchanged through \<open>Plus\<close>/\<open>Minus\<close>/
  \<open>Times\<close>, and \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/\<open>And\<close>/\<open>Or\<close> each recompute a fresh
  operating kind for their operand(s) from \<open>esyn\<close>, exactly where \<open>taval\<close>
  does. \<open>elaborate_syn\<close> is the entry with no externally given \<open>ik\<close>,
  mirroring \<open>taval_syn\<close>; \<open>elaborate_to\<close> is that entry followed by a
  conversion to a write target's own kind, emitted only where that kind
  genuinely differs from the one the expression synthesizes.
\<close>

fun elaborate :: "tyenv => ikind => exp => texp" where
  "elaborate \<Gamma> ik (N n) = TN ik n"
| "elaborate \<Gamma> ik (V x) =
     (if ik = \<Gamma> x then TVar (\<Gamma> x) x else TCast ik (TVar (\<Gamma> x) x))"
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

definition elaborate_to :: "tyenv => ikind => exp => texp" where
  "elaborate_to \<Gamma> ik e =
     (if ik = opk (esyn \<Gamma> e) then elaborate_syn \<Gamma> e
      else TCast ik (elaborate_syn \<Gamma> e))"

text \<open>
  The same-kind guard mirrors \<^const>\<open>elaborate\<close>'s own \<open>TVar\<close> clause and C's
  typing: a conversion to the kind an expression already synthesizes is not a
  conversion at all, since \<^const>\<open>taval_syn\<close> already lands in that kind's
  range. Emitting the node anyway would be semantically harmless -- \<^const>\<open>ik_norm\<close>
  is idempotent -- but every domain's \<open>a_cast\<close> must answer a genuine narrowing
  question at it, and a magnitude-free domain such as sign can only answer
  \<open>top\<close>. Goblint's own value cast is the identity on a same-kind conversion
  for exactly this reason, so the redundant node is dropped here rather than
  compensated for in each domain.
\<close>

text \<open>
  \<open>teval\<close> is \<open>taval\<close> with the kind bookkeeping already done: every
  arithmetic/literal node norms at its own embedded kind, \<open>TCast\<close> norms
  its operand at the target kind, and every comparison/logical node
  evaluates its (already correctly-kinded) operands with no further
  parameter.
\<close>

fun teval :: "texp => store => int" where
  "teval (TN ik n) s = ik_norm ik n"
| "teval (TVar ik x) s = s x"
| "teval (TPlus ik a b) s = ik_norm ik (teval a s + teval b s)"
| "teval (TMinus ik a b) s = ik_norm ik (teval a s - teval b s)"
| "teval (TTimes ik a b) s = ik_norm ik (teval a s * teval b s)"
| "teval (TCast ik a) s = ik_norm ik (teval a s)"
| "teval (TLess a b) s = (if teval a s < teval b s then 1 else 0)"
| "teval (TEq a b) s = (if teval a s = teval b s then 1 else 0)"
| "teval (TNot a) s = (if teval a s = 0 then 1 else 0)"
| "teval (TAnd a b) s = (if teval a s \<noteq> 0 \<and> teval b s \<noteq> 0 then 1 else 0)"
| "teval (TOr a b) s = (if teval a s \<noteq> 0 \<or> teval b s \<noteq> 0 then 1 else 0)"

section \<open>The kind a node produces\<close>

text \<open>
  Every node's result kind is readable off the node itself: an arithmetic or
  literal node carries it, a conversion carries its target, and a comparison or
  logical node yields a C truth value, which is an \<open>I32\<close> \<open>0\<close>/\<open>1\<close>. The
  operation is total, so at \<open>TCast ik a\<close> the \<^emph>\<open>source\<close> kind of the
  converted value is \<open>texp_kind a\<close> -- the fact a conversion's abstract
  counterpart needs when it wants to know whether the conversion can wrap at
  all, and the counterpart of the \<open>from_ik\<close> argument Goblint's own integer
  domains take alongside the target kind. Recording it here rather than in the
  abstract values keeps kinds on the syntax, where elaboration already put
  them, instead of pairing one with every abstract value.
\<close>

fun texp_kind :: "texp \<Rightarrow> ikind" where
  "texp_kind (TN ik _) = ik"
| "texp_kind (TVar ik _) = ik"
| "texp_kind (TPlus ik _ _) = ik"
| "texp_kind (TMinus ik _ _) = ik"
| "texp_kind (TTimes ik _ _) = ik"
| "texp_kind (TCast ik _) = ik"
| "texp_kind (TLess _ _) = I32"
| "texp_kind (TEq _ _) = I32"
| "texp_kind (TNot _) = I32"
| "texp_kind (TAnd _ _) = I32"
| "texp_kind (TOr _ _) = I32"

theorem teval_in_texp_kind_range [intro]:
  assumes "\<And>ik x. e = TVar ik x \<Longrightarrow> s x \<in> ik_range ik"
  shows "teval e s \<in> ik_range (texp_kind e)"
  using assms by (cases e) simp_all

text \<open>A conversion whose target range already contains the source's is the
  identity on every value the operand can produce -- the guard Goblint's
  \<open>cast_to\<close> checks through \<open>from_ik\<close> before letting a value pass a narrowing
  conversion unchanged.\<close>

lemma teval_TCast_no_wrap:
  assumes "ik_range (texp_kind a) \<subseteq> ik_range ik"
    and "\<And>ik' x. a = TVar ik' x \<Longrightarrow> s x \<in> ik_range ik'"
  shows "teval (TCast ik a) s = teval a s"
  using assms teval_in_texp_kind_range [of a s] by auto

section \<open>Elaboration is faithful to the typed evaluator\<close>

text \<open>
  The elaborated form agrees with the typed source evaluator on every
  \<^emph>\<open>well-typed\<close> store. The premise is needed at one place and is exactly
  what makes the migration honest: \<^const>\<open>taval\<close> converts on a variable
  read, the elaborated form does not, and the two coincide precisely because
  \<^const>\<open>styped\<close> keeps every slot inside its declared kind's range, which
  makes that conversion the identity. Where the read kind genuinely differs
  from the declared one, \<^const>\<open>elaborate\<close> emits an explicit
  \<^const>\<open>TCast\<close> and the agreement needs no premise at all -- the same
  split CIL makes when it inserts a conversion only at a genuine mismatch.
\<close>

theorem teval_elaborate [simp]:
  assumes "styped \<Gamma> s"
  shows "teval (elaborate \<Gamma> ik e) s = taval \<Gamma> ik e s"
proof -
  have norm_id: "ik_norm (\<Gamma> y) (s y) = s y" for y
    by (rule ik_norm_id[OF stypedD[OF assms]])
  show ?thesis
    by (induction e arbitrary: ik) (simp_all add: Let_def norm_id)
qed

theorem teval_elaborate_syn [simp]:
  assumes "styped \<Gamma> s"
  shows "teval (elaborate_syn \<Gamma> e) s = taval_syn \<Gamma> e s"
  using assms by (simp add: elaborate_syn_def taval_syn_def)

theorem teval_elaborate_to [simp]:
  assumes "styped \<Gamma> s"
  shows "teval (elaborate_to \<Gamma> ik e) s = ik_norm ik (taval_syn \<Gamma> e s)"
  using assms by (simp add: elaborate_to_def)

text \<open>Every \<^const>\<open>teval\<close> result at a kind-carrying node lies in that node's
  range, the \<open>taval_in_range\<close> counterpart a consumer needs once the
  typing environment is no longer in scope to restate it through.\<close>

lemma teval_TCast_in_range [simp, intro]: "teval (TCast ik e) s \<in> ik_range ik"
  by simp

section \<open>Syntactic global-variable occurrence\<close>

text \<open>
  \<^const>\<open>exp_mentions_where\<close>'s counterpart on the elaborated tree: the same
  syntax-directed walk, since elaboration changes no variable occurrence.
  \<open>texp_mentions_global_elaborate\<close> is the fact every locality argument
  carried over from the untyped syntax needs.
\<close>

fun texp_mentions_where :: "(vname \<Rightarrow> bool) \<Rightarrow> texp \<Rightarrow> bool" where
  "texp_mentions_where P (TN _ _) = False"
| "texp_mentions_where P (TVar _ x) = P x"
| "texp_mentions_where P (TPlus _ a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TMinus _ a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TTimes _ a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TCast _ a) = texp_mentions_where P a"
| "texp_mentions_where P (TLess a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TEq a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TNot a) = texp_mentions_where P a"
| "texp_mentions_where P (TAnd a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"
| "texp_mentions_where P (TOr a b) = (texp_mentions_where P a \<or> texp_mentions_where P b)"

definition texp_mentions_global :: "(vname \<Rightarrow> bool) \<Rightarrow> texp \<Rightarrow> bool" where
  "texp_mentions_global gs = texp_mentions_where gs"

lemmas texp_mentions_global_defs [simp] = texp_mentions_global_def

lemma texp_mentions_where_elaborate [simp]:
  "texp_mentions_where P (elaborate \<Gamma> ik e) = exp_mentions_where P e"
  by (induction e arbitrary: ik) (simp_all add: Let_def)

lemma texp_mentions_where_elaborate_syn [simp]:
  "texp_mentions_where P (elaborate_syn \<Gamma> e) = exp_mentions_where P e"
  by (simp add: elaborate_syn_def)

lemma texp_mentions_where_elaborate_to [simp]:
  "texp_mentions_where P (elaborate_to \<Gamma> ik e) = exp_mentions_where P e"
  by (simp add: elaborate_to_def)

lemma texp_mentions_global_elaborate [simp]:
  "texp_mentions_global gs (elaborate \<Gamma> ik e) = exp_mentions_global gs e"
  by simp

lemma texp_mentions_global_elaborate_syn [simp]:
  "texp_mentions_global gs (elaborate_syn \<Gamma> e) = exp_mentions_global gs e"
  by simp

lemma texp_mentions_global_elaborate_to [simp]:
  "texp_mentions_global gs (elaborate_to \<Gamma> ik e) = exp_mentions_global gs e"
  by simp

lemma teval_eq_on_locals:
  assumes "\<not> texp_mentions_global gs e"
    and "\<And>x. \<not> gs x \<Longrightarrow> s1 x = s2 x"
  shows "teval e s1 = teval e s2"
  using assms by (induction e) auto

section \<open>Collapse to the unbounded interpretation\<close>

text \<open>
  \<^const>\<open>teval\<close> collapses to the untyped \<^const>\<open>aval\<close> whenever
  \<^const>\<open>ik_norm\<close> never actually truncates any value it is handed: every
  kind-carrying node of \<^const>\<open>teval\<close> norms once more than \<^const>\<open>aval\<close>
  does, and nothing else about the recursion differs. This is the bridge a
  soundness proof stated against the unbounded semantics needs in order to
  reach an obligation stated against the machine one.
\<close>

lemma teval_eq_aval:
  assumes triv: "\<And>ik v. ik_norm ik v = v"
  shows "teval (elaborate \<Gamma> ik e) s = aval e s"
  by (induction e arbitrary: ik) (auto simp: Let_def triv)

lemma teval_syn_eq_aval:
  assumes triv: "\<And>ik v. ik_norm ik v = v"
  shows "teval (elaborate_syn \<Gamma> e) s = aval e s"
  unfolding elaborate_syn_def by (rule teval_eq_aval[OF triv])

section \<open>Forgetting the elaboration\<close>

text \<open>
  \<open>texp_erase\<close> drops every baked kind, recovering the source expression
  elaboration started from. It is not part of any semantics -- \<open>teval\<close> and
  \<^const>\<open>aval\<close> genuinely disagree wherever a machine kind truncates -- and
  exists for presentation only: a renderer that shows a compiled edge to a
  reader wants the expression the source wrote, not its kind annotations.
\<close>

fun texp_erase :: "texp \<Rightarrow> exp" where
  "texp_erase (TN _ n) = N n"
| "texp_erase (TVar _ x) = V x"
| "texp_erase (TPlus _ a b) = Plus (texp_erase a) (texp_erase b)"
| "texp_erase (TMinus _ a b) = Minus (texp_erase a) (texp_erase b)"
| "texp_erase (TTimes _ a b) = Times (texp_erase a) (texp_erase b)"
| "texp_erase (TCast _ a) = texp_erase a"
| "texp_erase (TLess a b) = Less (texp_erase a) (texp_erase b)"
| "texp_erase (TEq a b) = exp.Eq (texp_erase a) (texp_erase b)"
| "texp_erase (TNot a) = exp.Not (texp_erase a)"
| "texp_erase (TAnd a b) = And (texp_erase a) (texp_erase b)"
| "texp_erase (TOr a b) = Or (texp_erase a) (texp_erase b)"

lemma texp_erase_elaborate [simp]: "texp_erase (elaborate \<Gamma> ik e) = e"
  by (induction e arbitrary: ik) (simp_all add: Let_def)

lemma texp_erase_elaborate_syn [simp]: "texp_erase (elaborate_syn \<Gamma> e) = e"
  by (simp add: elaborate_syn_def)

lemma texp_erase_elaborate_to [simp]: "texp_erase (elaborate_to \<Gamma> ik e) = e"
  by (simp add: elaborate_to_def)

end
