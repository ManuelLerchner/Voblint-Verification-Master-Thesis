theory Three_Valued
  imports Main
begin

section \<open>Three-valued Boolean combinators\<close>

text \<open>
  \<open>and_opt\<close>/\<open>or_opt\<close> give \<open>bool option\<close> the same short-circuit reading
  \<open>\<and>\<close>/\<open>\<or>\<close> already have: a definite \<open>False\<close> operand decides an \<open>and_opt\<close>
  regardless of the other side (symmetrically, a definite \<open>True\<close> operand
  decides an \<open>or_opt\<close>), and only two agreeing definite operands decide the
  other direction. Anything else is \<open>None\<close> -- neither operand alone can be
  blamed for the unknown.

  Both expression evaluation and check classification combine three-valued
  answers this way, so the combinators sit below either of them.
\<close>

definition and_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "and_opt x y = (if x = Some False \<or> y = Some False then Some False
                   else if x = Some True \<and> y = Some True then Some True
                   else None)"

definition or_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "or_opt x y = (if x = Some True \<or> y = Some True then Some True
                  else if x = Some False \<and> y = Some False then Some False
                  else None)"

text \<open>
  The semantic reading a caller actually wants: given what \<open>x\<close>/\<open>y\<close> mean
  (\<open>px\<close>/\<open>py\<close>, via the same Horn-clause shape an induction hypothesis already
  has), \<open>and_opt\<close>/\<open>or_opt\<close>'s answer agrees with plain Boolean \<open>\<and>\<close>/\<open>\<or>\<close> on those
  meanings. Stated this way, a consumer never has to know \<open>and_opt\<close>/\<open>or_opt\<close>'s
  own three-way case split.
\<close>

lemma and_opt_sound:
  assumes "and_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<and> py) = r"
  using assms unfolding and_opt_def by (cases r) (auto split: if_splits)

lemma or_opt_sound:
  assumes "or_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<or> py) = r"
  using assms unfolding or_opt_def by (cases r) (auto split: if_splits)

text \<open>
  A definite answer survives widening the operands, so the combinators keep every
  definite answer of their wider inputs.
\<close>

lemma and_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "and_opt x2 y2 = Some b \<Longrightarrow> and_opt x1 y1 = Some b"
  using assms(1)[of True] assms(1)[of False] assms(2)[of True] assms(2)[of False]
  unfolding and_opt_def by (cases b) (auto split: if_splits)

lemma or_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "or_opt x2 y2 = Some b \<Longrightarrow> or_opt x1 y1 = Some b"
  using assms(1)[of True] assms(1)[of False] assms(2)[of True] assms(2)[of False]
  unfolding or_opt_def by (cases b) (auto split: if_splits)

end
