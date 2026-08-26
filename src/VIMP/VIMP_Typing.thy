theory VIMP_Typing
  imports VIMP_Ikind VIMP_Syntax
begin

section \<open>Expression typing\<close>

text \<open>
  A typing environment assigns every variable a machine-integer kind. The
  judgment \<open>wt_exp \<Gamma> e ik\<close> checks \<open>e\<close> against an expected kind
  \<open>ik\<close>: the operands of an arithmetic operator share its kind, so a
  mixed-kind operation needs an explicit source-level cast, exactly as in a
  CIL-normalized program where every conversion is an explicit cast node; a
  comparison or logical operator yields a C-style \<open>I32\<close> truth value;
  and a literal is admissible at any kind whose range contains its value.

  A comparison's operand kind is not part of the expected kind, so it is
  synthesized from the operands themselves: a variable forces its declared
  kind, and a literal-only operand pair defaults to \<open>I32\<close>, exactly as
  C types a bare integer constant \<open>int\<close>. Synthesis is what makes the
  judgment semantically unambiguous \<comment> \<open>the value of
  \<open>200 + 100 < 250\<close> depends on the kind the sum wraps at.\<close>
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
  \<open>esyn\<close> returns the kind the variables inside an expression force,
  or \<open>None\<close> for a literal-only expression, which is kind-polymorphic. A
  variable's forced kind is already promoted (\<open>ik_promote\<close>, C's integer
  promotion, ISO/IEC 9899 6.3.1.1p2): promoting only at this one leaf is enough,
  because \<open>kjoin\<close> only ever selects between two already-forced
  operand kinds, so promoting every leaf promotes every kind \<open>esyn\<close>
  can produce, with no separate promotion step needed anywhere \<open>esyn\<close>,
  \<open>kjoin\<close>, or \<open>opk\<close> is used -- \<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>,
  \<open>Less\<close>/\<open>Eq\<close>, \<open>Not\<close>/\<open>And\<close>/\<open>Or\<close>, and \<open>special_result\<close>'s
  \<open>Min\<close>/\<open>Max\<close> alike.
  Where both operands force a kind, \<open>kjoin\<close> combines them by C's usual
  arithmetic conversions; see its own note below.
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

fun esyn :: "tyenv \<Rightarrow> exp \<Rightarrow> ikind option" where
  "esyn \<Gamma> (N n) = None"
| "esyn \<Gamma> (V x) = Some (ik_promote (\<Gamma> x))"
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

subsection \<open>The typing judgment\<close>

text \<open>
  A variable checks at its own declared kind directly -- the \<open>Plus\<close>/
  \<open>Minus\<close>/\<open>Times\<close> case below checks both operands at a caller-given
  \<open>ik\<close>, matching them exactly -- or at its promoted kind, which is the
  kind \<^const>\<open>esyn\<close> actually reports and so the kind \<open>Less\<close>/\<open>Eq\<close>/\<open>Not\<close>/
  \<open>And\<close>/\<open>Or\<close> check their own operands at. Both are genuine: \<open>total :=
  x + 1\<close> checks \<open>x\<close> at its own declared kind (\<open>wt_exp \<Gamma> (Plus (V x) (N
  1)) (\<Gamma> x)\<close>), while \<open>x < 5\<close> checks it at its promoted one.
\<close>

fun wt_exp :: "tyenv \<Rightarrow> exp \<Rightarrow> ikind \<Rightarrow> bool" where
  "wt_exp \<Gamma> (N n) ik \<longleftrightarrow> n \<in> ik_range ik"
| "wt_exp \<Gamma> (V x) ik \<longleftrightarrow> ik = \<Gamma> x \<or> ik = ik_promote (\<Gamma> x)"
| "wt_exp \<Gamma> (Plus e1 e2) ik \<longleftrightarrow> wt_exp \<Gamma> e1 ik \<and> wt_exp \<Gamma> e2 ik"
| "wt_exp \<Gamma> (Minus e1 e2) ik \<longleftrightarrow> wt_exp \<Gamma> e1 ik \<and> wt_exp \<Gamma> e2 ik"
| "wt_exp \<Gamma> (Times e1 e2) ik \<longleftrightarrow> wt_exp \<Gamma> e1 ik \<and> wt_exp \<Gamma> e2 ik"
| "wt_exp \<Gamma> (Less e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and>
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in wt_exp \<Gamma> e1 k \<and> wt_exp \<Gamma> e2 k)"
| "wt_exp \<Gamma> (Eq e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and>
     (let k = opk (kjoin (esyn \<Gamma> e1) (esyn \<Gamma> e2))
      in wt_exp \<Gamma> e1 k \<and> wt_exp \<Gamma> e2 k)"
| "wt_exp \<Gamma> (Not e) ik \<longleftrightarrow> ik = I32 \<and> wt_exp \<Gamma> e (opk (esyn \<Gamma> e))"
| "wt_exp \<Gamma> (And e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and> wt_exp \<Gamma> e1 (opk (esyn \<Gamma> e1)) \<and> wt_exp \<Gamma> e2 (opk (esyn \<Gamma> e2))"
| "wt_exp \<Gamma> (Or e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and> wt_exp \<Gamma> e1 (opk (esyn \<Gamma> e1)) \<and> wt_exp \<Gamma> e2 (opk (esyn \<Gamma> e2))"

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

fun taval :: "tyenv \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval \<Gamma> ik (N n) s = ik_norm ik n"
| "taval \<Gamma> ik (V x) s = ik_norm ik (s x)"
| "taval \<Gamma> ik (Plus e1 e2) s = ik_norm ik (taval \<Gamma> ik e1 s + taval \<Gamma> ik e2 s)"
| "taval \<Gamma> ik (Minus e1 e2) s = ik_norm ik (taval \<Gamma> ik e1 s - taval \<Gamma> ik e2 s)"
| "taval \<Gamma> ik (Times e1 e2) s = ik_norm ik (taval \<Gamma> ik e1 s * taval \<Gamma> ik e2 s)"
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

lemma wt_exp_pins:
  "wt_exp (\<lambda>_. U8) (Plus (V (STR ''x'')) (N 1)) U8"
  "\<not> wt_exp (\<lambda>_. U8) (N (2 ^ 8)) U8"
  "wt_exp (\<lambda>_. U8) (N (2 ^ 8)) U16"
  "wt_exp (\<lambda>_. U8) (Less (V (STR ''x'')) (N 5)) I32"
  "\<not> wt_exp (\<lambda>_. U8) (Plus (V (STR ''x'')) (N (2 ^ 8))) U8"
  "\<not> wt_exp (\<lambda>_. I32) (Plus (V (STR ''x'')) (V (STR ''x''))) U8"
  "wt_exp (\<lambda>_. I32) (And (V (STR ''x'')) (N 1)) I32"
  "wt_exp (\<lambda>_. U8) (Less (N 300) (N 250)) I32"
  by eval+

lemma taval_pins:
  "taval (\<lambda>_. U8) U8 (Plus (V (STR ''x'')) (N 1))
     ((\<lambda>_. 0)(STR ''x'' := 2 ^ 8 - 1)) = 0"
  "taval (\<lambda>_. I32) I32 (Less (Plus (N 200) (N 100)) (N 250)) (\<lambda>_. 0) = 0"
  "taval (\<lambda>_. U8) I32 (Less (Plus (V (STR ''x'')) (N 100)) (N 250))
     ((\<lambda>_. 0)(STR ''x'' := 200)) = 0"
  "taval (\<lambda>_. I32) U8 (Plus (N 200) (N 100)) (\<lambda>_. 0) = 44"
  by eval+

end
