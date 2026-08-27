theory VIMP_Typing
  imports VIMP_Ikind VIMP_Syntax
begin

section \<open>Expression typing\<close>

text \<open>
  A typing environment assigns every variable a machine-integer kind. What
  this theory settles is the kind each operation computes at, not whether a
  source expression is admissible: \<open>esyn\<close> synthesizes an expression's
  own kind, \<open>kjoin\<close> and \<open>opk\<close> combine two operands' kinds into
  the one their operator uses, and \<open>taval\<close> evaluates at that kind.

  Synthesis is what makes the semantics unambiguous \<comment> \<open>the value of
  \<open>200 + 100 < 250\<close> depends on the kind the sum wraps at\<close> --- and it follows
  C: an operand keeps its declared kind, a bare decimal constant takes the
  first kind that represents it, and a comparison or logical operator yields
  an \<^const>\<open>I32\<close> truth value whatever its operands were.

  Admissibility is checked after elaboration rather than before it, for the
  reason recorded below.
\<close>

type_synonym tyenv = "vname \<Rightarrow> ikind"

text \<open>
  The default environment types every variable \<open>I32\<close>; an untyped
  declaration means \<open>int\<close>.
\<close>

definition default_tyenv :: tyenv where
  "default_tyenv = (\<lambda>_. I32)"

subsection \<open>Typed variables\<close>

text \<open>
  A name paired with the kind it was declared at -- the shape a
  declaration list (a program's declared globals, a formal's
  annotation) takes wherever the source actually named a kind, as
  opposed to \<open>tyenv\<close> itself, which is total and always answers
  with a default. \<open>tv_env\<close> is the one operation every such list
  needs: turn it into a \<open>tyenv\<close>, falling back to \<open>I32\<close> for
  every name the list does not mention.
\<close>

datatype typed_var = TV (tv_name: vname) (tv_kind: ikind)

instance typed_var :: countable
  by countable_datatype

derive linorder typed_var

definition tv_env :: "typed_var list \<Rightarrow> tyenv" where
  "tv_env tvs =
     (\<lambda>x. case map_of (map (\<lambda>tv. (tv_name tv, tv_kind tv)) tvs) x of
            None \<Rightarrow> I32 | Some k \<Rightarrow> k)"

lemma tv_env_Nil [simp]: "tv_env [] = default_tyenv"
  by (simp add: tv_env_def default_tyenv_def)

lemma tv_env_Cons [simp]:
  "tv_env (TV x k # tvs) = (tv_env tvs)(x := k)"
  by (rule ext) (simp add: tv_env_def)

lemma tv_env_pins:
  "tv_env [TV (STR ''x'') U8] (STR ''x'') = U8"
  "tv_env [TV (STR ''x'') U8] (STR ''y'') = I32"
  "tv_env [TV (STR ''x'') U8, TV (STR ''y'') I16] (STR ''y'') = I16"
  by eval+

subsection \<open>Kind synthesis\<close>

text \<open>
  \<open>esyn\<close> returns the kind an expression has of its own accord, before any
  context converts it: a variable's declared kind, a literal's chosen kind,
  \<^const>\<open>I32\<close> for a comparison or a logical operator. It is the kind C's
  grammar assigns the expression, so a \<open>uint8\<close> variable synthesizes
  \<^const>\<open>U8\<close> and not \<^const>\<open>I32\<close>.

  Integer promotion (\<open>ik_promote\<close>, ISO/IEC 9899 6.3.1.1p2) is not applied
  here. C promotes in named contexts, not at every occurrence of a narrow
  operand: the usual arithmetic conversions promote both operands of a binary
  arithmetic or relational operator, and the unary operators and shifts
  promote their own. It does not promote across an assignment, so
  \<open>uint8 b; uint8 a; b := a\<close> converts \<^const>\<open>U8\<close> straight to \<^const>\<open>U8\<close>
  rather than through \<^const>\<open>I32\<close>. That round trip left the concrete value
  alone but cost abstract precision at each leg, since a domain must answer a
  genuine narrowing question at every conversion node it is given.

  The promotion therefore sits in \<^const>\<open>usual_kind\<close>, which \<open>kjoin\<close> calls
  and which promotes both of its arguments before choosing a common kind.
  Every context that performs the usual arithmetic conversions reaches it
  through \<open>kjoin\<close> -- \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>, \<open>Less\<close>/\<open>Eq\<close>, and
  \<open>special_result\<close>'s \<open>Min\<close>/\<open>Max\<close> -- while \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>, which test
  their operands against zero and convert nothing, do not.

  \<open>None\<close> is left as the answer for an operand that constrains nothing. No
  clause produces it, since every leaf now names a kind, but \<open>kjoin\<close> still
  accepts it, and \<open>opk\<close> still supplies \<^const>\<open>I32\<close> for it.
\<close>

text \<open>
  \<open>kjoin\<close> combines the kinds two operands synthesize. Where both synthesize
  one, that is C's usual arithmetic conversions (\<^const>\<open>usual_kind\<close>,
  ISO/IEC 9899 6.3.1.8), not a preference for either position: a rule that took
  the left operand's kind would make evaluation depend on operand order, so
  \<open>u32 == i64\<close> and \<open>i64 == u32\<close> could disagree. \<open>None\<close> means the operand
  constrains nothing -- a bare literal -- and contributes no kind.
\<close>

fun kjoin :: "ikind option \<Rightarrow> ikind option \<Rightarrow> ikind option" where
  "kjoin None r = r"
| "kjoin l None = l"
| "kjoin (Some a) (Some b) = Some (usual_kind a b)"

lemma kjoin_commute: "kjoin a b = kjoin b a"
  by (cases a; cases b) (simp_all add: usual_kind_commute)

text \<open>
  An unsuffixed decimal constant takes the first of \<open>int\<close>, \<open>long int\<close>,
  \<open>long long int\<close> that can represent it (ISO/IEC 9899 6.4.4.1p5) -- never an
  unsigned type, and never a type too narrow for its own value. VIMP collapses
  the three signed candidates onto \<^const>\<open>I32\<close> and \<^const>\<open>I64\<close>.

  Giving a literal no kind at all, and letting \<open>opk\<close> default it to
  \<^const>\<open>I32\<close>, silently truncated every constant outside the 32-bit range:
  \<open>4294967296\<close> elaborated as \<open>TN I32 4294967296\<close> and \<^const>\<open>ik_norm\<close>
  turned it into \<open>0\<close> before it reached its destination.

  A constant that fits \<^const>\<open>I32\<close> still types as \<^const>\<open>I32\<close>, which is what
  it defaulted to before, so nothing that already fitted changes kind.
\<close>

definition ik_of_lit :: "int \<Rightarrow> ikind" where
  "ik_of_lit n = (if n \<in> ik_range I32 then I32 else I64)"

lemma ik_of_lit_small [simp]: "n \<in> ik_range I32 \<Longrightarrow> ik_of_lit n = I32"
  by (simp add: ik_of_lit_def)

fun esyn :: "tyenv \<Rightarrow> exp \<Rightarrow> ikind option" where
  "esyn \<Gamma> (N n) = Some (ik_of_lit n)"
| "esyn \<Gamma> (V x) = Some (\<Gamma> x)"
| "esyn \<Gamma> (Plus e1 e2) = kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)"
| "esyn \<Gamma> (Minus e1 e2) = kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)"
| "esyn \<Gamma> (Times e1 e2) = kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2)"
| "esyn \<Gamma> (Less e1 e2) = Some I32"
| "esyn \<Gamma> (Eq e1 e2) = Some I32"
| "esyn \<Gamma> (Not e) = Some I32"
| "esyn \<Gamma> (And e1 e2) = Some I32"
| "esyn \<Gamma> (Or e1 e2) = Some I32"

definition opk :: "ikind option \<Rightarrow> ikind" where
  "opk k = (case k of None \<Rightarrow> I32 | Some k' \<Rightarrow> k')"

subsection \<open>Where the typing judgment lives\<close>

text \<open>
  There is no source-level typing judgment here, and that is the point. An
  earlier one checked an \<^typ>\<open>exp\<close> against an expected kind and required the
  operands of an arithmetic operator to share it, so a mixed-kind operation
  needed a cast the programmer wrote. \<open>elaborate\<close> does not work that
  way: it inserts the conversion itself, at each operand that reaches an
  operator at another kind, which is what C's usual arithmetic conversions
  describe and what CIL emits. A judgment demanding source-level casts
  therefore described a different language from the one being compiled, and
  nothing consumed it.

  The obligation it was reaching for is discharged on the other side of
  elaboration instead, by \<open>wt_texp\<close> and \<open>wt_texp_elaborate\<close>, which are stated
  where \<open>elaborate\<close> itself is: whatever source expression and target kind it
  is given, elaboration produces a typed expression whose nodes agree with
  each other. That is the property every consumer downstream actually relies
  on, since each reads an operand's kind off the operand.
\<close>

text \<open>
  Truthiness is kind-independent (a value is true iff it is nonzero), so
  the operands of \<open>And\<close>/\<open>Or\<close>/\<open>Not\<close> each check at their
  own synthesized kind, while a comparison relates two values of one kind.
\<close>

subsection \<open>Kind-aware evaluation\<close>

text \<open>
  \<open>taval \<Gamma> ik e s\<close> evaluates \<open>e\<close> at expected kind \<open>ik\<close>,
  in the role of the expression's C type: arithmetic wraps at that kind
  through \<open>ik_norm\<close>, leaves are normed into it, and a comparison or
  logical operator evaluates its operands at their synthesized kind and
  yields \<open>0\<close>/\<open>1\<close>. Every result therefore lies in the expected
  kind's range, with no typing premise.
\<close>

text \<open>
  A binary operation evaluates at the kind its operands agree on under the
  usual arithmetic conversions, wraps there, and only then converts to the
  kind its context asked for. Evaluating it directly at the context's kind
  would use the wrong width: in \<open>4294967295 < u32 + 1\<close> the comparison agrees
  on 64 bits, but \<open>u32 + 1\<close> is an unsigned 32-bit addition that wraps to zero
  before the comparison sees it. \<open>Less\<close> and \<open>Eq\<close> already derive their operand
  kind this way.
\<close>

fun taval :: "tyenv \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval \<Gamma> ik (N n) s = ik_norm ik n"
| "taval \<Gamma> ik (V x) s = ik_norm ik (s x)"
| "taval \<Gamma> ik (Plus e1 e2) s =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in ik_norm ik (ik_norm k (taval \<Gamma> k e1 s + taval \<Gamma> k e2 s)))"
| "taval \<Gamma> ik (Minus e1 e2) s =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in ik_norm ik (ik_norm k (taval \<Gamma> k e1 s - taval \<Gamma> k e2 s)))"
| "taval \<Gamma> ik (Times e1 e2) s =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in ik_norm ik (ik_norm k (taval \<Gamma> k e1 s * taval \<Gamma> k e2 s)))"
| "taval \<Gamma> ik (Less e1 e2) s =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in if taval \<Gamma> k e1 s < taval \<Gamma> k e2 s then 1 else 0)"
| "taval \<Gamma> ik (Eq e1 e2) s =
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in if taval \<Gamma> k e1 s = taval \<Gamma> k e2 s then 1 else 0)"
| "taval \<Gamma> ik (Not e) s = (if taval \<Gamma> (opk (esyn \<Gamma> e)) e s = 0 then 1 else 0)"
| "taval \<Gamma> ik (And e1 e2) s =
     (if taval \<Gamma> (opk (esyn \<Gamma> e1)) e1 s \<noteq> 0 \<and>
         taval \<Gamma> (opk (esyn \<Gamma> e2)) e2 s \<noteq> 0 then 1 else 0)"
| "taval \<Gamma> ik (Or e1 e2) s =
     (if taval \<Gamma> (opk (esyn \<Gamma> e1)) e1 s \<noteq> 0 \<or>
         taval \<Gamma> (opk (esyn \<Gamma> e2)) e2 s \<noteq> 0 then 1 else 0)"

theorem taval_in_range [simp, intro]: "taval \<Gamma> ik e s \<in> ik_range ik"
  by (cases e) (simp_all add: Let_def)

lemma taval_ge_min [simp]: "ik_min ik \<le> taval \<Gamma> ik e s"
  using taval_in_range [of \<Gamma> ik e s] by simp

lemma taval_le_max [simp]: "taval \<Gamma> ik e s \<le> ik_max ik"
  using taval_in_range [of \<Gamma> ik e s] by simp

text \<open>
  \<open>taval_syn\<close> evaluates an expression at its own synthesized kind --
  the evaluation a context without an expected kind performs: a branch
  condition, or the argument pair of a value-producing special call.
\<close>

definition taval_syn :: "tyenv \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval_syn \<Gamma> e s = taval \<Gamma> (opk (esyn \<Gamma> e)) e s"

text \<open>\<^const>\<open>taval_syn\<close> already lands in the kind it synthesizes, so
  norming it there again changes nothing. This is the fact that lets a
  conversion to an expression's own synthesized kind be dropped rather
  than emitted.\<close>

lemma ik_norm_taval_syn [simp]:
  "ik_norm (opk (esyn \<Gamma> e)) (taval_syn \<Gamma> e s) = taval_syn \<Gamma> e s"
  unfolding taval_syn_def by (rule ik_norm_id[OF taval_in_range])

subsection \<open>Store typedness\<close>

text \<open>
  A store is typed when every variable holds a value in its declared
  kind's range. The zero store is typed for every environment, and an
  update stays typed when the written value is normed to \<comment> \<open>or
  already lies in\<close> the variable's range.
\<close>

definition styped :: "tyenv \<Rightarrow> store \<Rightarrow> bool" where
  "styped \<Gamma> s \<longleftrightarrow> (\<forall>x. s x \<in> ik_range (\<Gamma> x))"

lemma styped_zero [simp, intro]: "styped \<Gamma> (\<lambda>_. 0)"
  unfolding styped_def by simp

lemma stypedD [dest]: "styped \<Gamma> s \<Longrightarrow> s x \<in> ik_range (\<Gamma> x)"
  unfolding styped_def by simp

lemma styped_update [intro]:
  "styped \<Gamma> s \<Longrightarrow> v \<in> ik_range (\<Gamma> x) \<Longrightarrow> styped \<Gamma> (s(x := v))"
  unfolding styped_def by auto

lemma styped_update_norm [simp, intro]:
  "styped \<Gamma> s \<Longrightarrow> styped \<Gamma> (s(x := ik_norm (\<Gamma> x) v))"
  unfolding styped_def by auto

lemma styped_update_taval [simp, intro]:
  "styped \<Gamma> s \<Longrightarrow> styped \<Gamma> (s(x := taval \<Gamma> (\<Gamma> x) e s))"
  unfolding styped_def using taval_in_range by auto

subsection \<open>Executable pins\<close>

text \<open>
  The comparison triple pins promotion at the synthesis rule: a
  \<open>U8\<close>-declared operand and an \<open>I32\<close>-declared one now compare
  identically -- promoting \<open>x\<close> to \<open>I32\<close> before the sum is computed
  matches the literal-only default \<open>I32\<close> exactly, unlike an
  unpromoted synthesis that would wrap the sum at \<open>U8\<close> and flip
  the comparison. Wraparound still happens, but only where C puts
  it: at an explicit narrower destination kind, not inside the
  comparison itself.
\<close>

lemma taval_pins:
  "taval (\<lambda>_. U8) U8 (Plus (V (STR ''x'')) (N 1))
     ((\<lambda>_. 0)(STR ''x'' := 2 ^ 8 - 1)) = 0"
  "taval (\<lambda>_. I32) I32 (Less (Plus (N 200) (N 100)) (N 250)) (\<lambda>_. 0) = 0"
  "taval (\<lambda>_. U8) I32 (Less (Plus (V (STR ''x'')) (N 100)) (N 250))
     ((\<lambda>_. 0)(STR ''x'' := 200)) = 0"
  "taval (\<lambda>_. I32) U8 (Plus (N 200) (N 100)) (\<lambda>_. 0) = 44"
  by eval+

end
