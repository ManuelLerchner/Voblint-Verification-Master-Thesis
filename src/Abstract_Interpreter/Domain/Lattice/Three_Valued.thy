theory Three_Valued
  imports Main
begin

section \<open>Three-valued Boolean combinators\<close>

text \<open>
  \<open>bin_log f ann\<close> lifts a Boolean connective \<open>f\<close> to \<open>bool option\<close> with the
  short-circuit reading \<open>f\<close> already has: one definite operand equal to the
  annihilator \<open>ann\<close> decides the result regardless of the other side, two
  definite operands are combined by \<open>f\<close>, and anything else is \<open>None\<close>.
  Goblint's \<open>id_binary_log\<close> (\<open>base.ml\<close>) has the same shape; \<open>and_opt\<close> and
  \<open>or_opt\<close> are its two instances.

  Both expression evaluation and check classification combine three-valued
  answers this way, so the combinators sit below either of them.
\<close>

definition bin_log ::
  "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bool \<Rightarrow> bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "bin_log f ann x y =
     (if x = Some ann \<or> y = Some ann then Some ann
      else case (x, y) of (Some a, Some b) \<Rightarrow> Some (f a b) | _ \<Rightarrow> None)"

abbreviation and_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "and_opt \<equiv> bin_log (\<and>) False"

abbreviation or_opt :: "bool option \<Rightarrow> bool option \<Rightarrow> bool option" where
  "or_opt \<equiv> bin_log (\<or>) True"

text \<open>
  The semantic reading a caller actually wants: given what \<open>x\<close>/\<open>y\<close> mean
  (\<open>px\<close>/\<open>py\<close>, via the same Horn-clause shape an induction hypothesis already
  has), the combined answer agrees with \<open>f\<close> on those meanings, provided \<open>ann\<close>
  really annihilates \<open>f\<close>. Stated this way, a consumer never has to know
  \<open>bin_log\<close>'s own case split.
\<close>

lemma bin_log_sound:
  assumes "bin_log f ann x y = Some r"
    and "\<And>b. f ann b = ann" and "\<And>b. f b ann = ann"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "f px py = r"
  using assms unfolding bin_log_def
  by (cases x; cases y) (auto split: if_splits)

lemma and_opt_sound:
  assumes "and_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<and> py) = r"
  using bin_log_sound[OF assms(1) _ _ assms(2,3)] by simp

lemma or_opt_sound:
  assumes "or_opt x y = Some r"
    and "\<And>b. x = Some b \<Longrightarrow> px = b"
    and "\<And>b. y = Some b \<Longrightarrow> py = b"
  shows "(px \<or> py) = r"
  using bin_log_sound[OF assms(1) _ _ assms(2,3)] by simp

text \<open>
  A definite answer survives widening the operands, so the combinators keep every
  definite answer of their wider inputs.
\<close>

lemma bin_log_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "bin_log f ann x2 y2 = Some b \<Longrightarrow> bin_log f ann x1 y1 = Some b"
  using assms unfolding bin_log_def
  by (cases x2; cases y2) (auto split: if_splits)

lemma and_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "and_opt x2 y2 = Some b \<Longrightarrow> and_opt x1 y1 = Some b"
  using bin_log_mono[OF assms] .

lemma or_opt_mono:
  assumes "\<And>b. x2 = Some b \<Longrightarrow> x1 = Some b" and "\<And>b. y2 = Some b \<Longrightarrow> y1 = Some b"
  shows "or_opt x2 y2 = Some b \<Longrightarrow> or_opt x1 y1 = Some b"
  using bin_log_mono[OF assms] .

end
