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

end
