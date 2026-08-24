theory VIMP_Typing
  imports VIMP_Ikind VIMP_Syntax
begin

section \<open>Expression typing\<close>

text \<open>
  A typing environment assigns every variable a machine-integer kind. The
  judgment \<open>wt_exp G e ik\<close> checks \<open>e\<close> against an expected kind
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

subsection \<open>Kind synthesis\<close>

text \<open>
  \<open>esyn\<close> returns the kind the variables inside an expression force,
  or \<open>None\<close> for a literal-only expression, which is kind-polymorphic.
  \<open>kjoin\<close> prefers the left forced kind; the typing judgment requires
  both sides to check at the joined kind, so the preference is only ever
  exercised on agreeing kinds or on ill-typed expressions.
\<close>

fun kjoin :: "ikind option \<Rightarrow> ikind option \<Rightarrow> ikind option" where
  "kjoin None r = r"
| "kjoin l None = l"
| "kjoin (Some a) (Some b) = Some a"

fun esyn :: "tyenv \<Rightarrow> exp \<Rightarrow> ikind option" where
  "esyn G (N n) = None"
| "esyn G (V x) = Some (G x)"
| "esyn G (Plus e1 e2) = kjoin (esyn G e1) (esyn G e2)"
| "esyn G (Minus e1 e2) = kjoin (esyn G e1) (esyn G e2)"
| "esyn G (Times e1 e2) = kjoin (esyn G e1) (esyn G e2)"
| "esyn G (Less e1 e2) = Some I32"
| "esyn G (Eq e1 e2) = Some I32"
| "esyn G (Not e) = Some I32"
| "esyn G (And e1 e2) = Some I32"
| "esyn G (Or e1 e2) = Some I32"

definition opk :: "ikind option \<Rightarrow> ikind" where
  "opk k = (case k of None \<Rightarrow> I32 | Some k' \<Rightarrow> k')"

subsection \<open>The typing judgment\<close>

fun wt_exp :: "tyenv \<Rightarrow> exp \<Rightarrow> ikind \<Rightarrow> bool" where
  "wt_exp G (N n) ik \<longleftrightarrow> n \<in> ik_range ik"
| "wt_exp G (V x) ik \<longleftrightarrow> G x = ik"
| "wt_exp G (Plus e1 e2) ik \<longleftrightarrow> wt_exp G e1 ik \<and> wt_exp G e2 ik"
| "wt_exp G (Minus e1 e2) ik \<longleftrightarrow> wt_exp G e1 ik \<and> wt_exp G e2 ik"
| "wt_exp G (Times e1 e2) ik \<longleftrightarrow> wt_exp G e1 ik \<and> wt_exp G e2 ik"
| "wt_exp G (Less e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and>
     (let k = opk (kjoin (esyn G e1) (esyn G e2))
      in wt_exp G e1 k \<and> wt_exp G e2 k)"
| "wt_exp G (Eq e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and>
     (let k = opk (kjoin (esyn G e1) (esyn G e2))
      in wt_exp G e1 k \<and> wt_exp G e2 k)"
| "wt_exp G (Not e) ik \<longleftrightarrow> ik = I32 \<and> wt_exp G e (opk (esyn G e))"
| "wt_exp G (And e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and> wt_exp G e1 (opk (esyn G e1)) \<and> wt_exp G e2 (opk (esyn G e2))"
| "wt_exp G (Or e1 e2) ik \<longleftrightarrow>
     ik = I32 \<and> wt_exp G e1 (opk (esyn G e1)) \<and> wt_exp G e2 (opk (esyn G e2))"

text \<open>
  Truthiness is kind-independent (a value is true iff it is nonzero), so
  the operands of \<open>And\<close>/\<open>Or\<close>/\<open>Not\<close> each check at their
  own synthesized kind, while a comparison relates two values of one kind.
\<close>

subsection \<open>Kind-aware evaluation\<close>

text \<open>
  \<open>taval G ik e s\<close> evaluates \<open>e\<close> at expected kind \<open>ik\<close>,
  in the role of the expression's C type: arithmetic wraps at that kind
  through \<open>ik_norm\<close>, leaves are normed into it, and a comparison or
  logical operator evaluates its operands at their synthesized kind and
  yields \<open>0\<close>/\<open>1\<close>. Every result therefore lies in the expected
  kind's range, with no typing premise.
\<close>

fun taval :: "tyenv \<Rightarrow> ikind \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval G ik (N n) s = ik_norm ik n"
| "taval G ik (V x) s = ik_norm ik (s x)"
| "taval G ik (Plus e1 e2) s = ik_norm ik (taval G ik e1 s + taval G ik e2 s)"
| "taval G ik (Minus e1 e2) s = ik_norm ik (taval G ik e1 s - taval G ik e2 s)"
| "taval G ik (Times e1 e2) s = ik_norm ik (taval G ik e1 s * taval G ik e2 s)"
| "taval G ik (Less e1 e2) s =
     (let k = opk (kjoin (esyn G e1) (esyn G e2))
      in if taval G k e1 s < taval G k e2 s then 1 else 0)"
| "taval G ik (Eq e1 e2) s =
     (let k = opk (kjoin (esyn G e1) (esyn G e2))
      in if taval G k e1 s = taval G k e2 s then 1 else 0)"
| "taval G ik (Not e) s = (if taval G (opk (esyn G e)) e s = 0 then 1 else 0)"
| "taval G ik (And e1 e2) s =
     (if taval G (opk (esyn G e1)) e1 s \<noteq> 0 \<and>
         taval G (opk (esyn G e2)) e2 s \<noteq> 0 then 1 else 0)"
| "taval G ik (Or e1 e2) s =
     (if taval G (opk (esyn G e1)) e1 s \<noteq> 0 \<or>
         taval G (opk (esyn G e2)) e2 s \<noteq> 0 then 1 else 0)"

theorem taval_in_range [simp, intro]: "taval G ik e s \<in> ik_range ik"
  by (cases e) (simp_all add: Let_def)

lemma taval_ge_min [simp]: "ik_min ik \<le> taval G ik e s"
  using taval_in_range [of G ik e s] by simp

lemma taval_le_max [simp]: "taval G ik e s \<le> ik_max ik"
  using taval_in_range [of G ik e s] by simp

text \<open>
  \<open>taval_syn\<close> evaluates an expression at its own synthesized kind --
  the evaluation a context without an expected kind performs: a branch
  condition, or the argument pair of a value-producing special call.
\<close>

definition taval_syn :: "tyenv \<Rightarrow> exp \<Rightarrow> store \<Rightarrow> int" where
  "taval_syn G e s = taval G (opk (esyn G e)) e s"

subsection \<open>Store typedness\<close>

text \<open>
  A store is typed when every variable holds a value in its declared
  kind's range. The zero store is typed for every environment, and an
  update stays typed when the written value is normed to \<comment> \<open>or
  already lies in\<close> the variable's range.
\<close>

definition styped :: "tyenv \<Rightarrow> store \<Rightarrow> bool" where
  "styped G s \<longleftrightarrow> (\<forall>x. s x \<in> ik_range (G x))"

lemma styped_zero [simp, intro]: "styped G (\<lambda>_. 0)"
  unfolding styped_def by simp

lemma stypedD [dest]: "styped G s \<Longrightarrow> s x \<in> ik_range (G x)"
  unfolding styped_def by simp

lemma styped_update [intro]:
  "styped G s \<Longrightarrow> v \<in> ik_range (G x) \<Longrightarrow> styped G (s(x := v))"
  unfolding styped_def by auto

lemma styped_update_norm [simp, intro]:
  "styped G s \<Longrightarrow> styped G (s(x := ik_norm (G x) v))"
  unfolding styped_def by auto

lemma styped_update_taval [simp, intro]:
  "styped G s \<Longrightarrow> styped G (s(x := taval G (G x) e s))"
  unfolding styped_def using taval_in_range by auto

subsection \<open>Executable pins\<close>

text \<open>
  The comparison pair pins the synthesis rule: the same syntactic sum
  wraps below the comparison bound at \<open>U8\<close> but not at the
  literal-only default \<open>I32\<close>.
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
     ((\<lambda>_. 0)(STR ''x'' := 200)) = 1"
  by eval+

end
