theory Voblint_OCaml_Check
  imports Voblint_Examples.Example_Codegen_API
begin

text \<open>
  CI-only OCaml compilation check for the \<open>export_code\<close> declarations in
  \<^theory>\<open>Voblint_Examples.Example_Codegen_API\<close>. Kept in a separate
  session, built only by CI's Linux job (see \<open>.github/workflows/ci.yml\<close>),
  not by the default \<open>Voblint_Examples\<close> build.

  On Apple Silicon macOS, Isabelle's bundled \<open>opam\<close> (2.0.7) is an x86_64
  binary, so its managed OCaml toolchain links against an x86_64
  \<open>libgmp\<close> while the platform (and Homebrew's own \<open>libgmp\<close>) is arm64 ---
  an environment/toolchain mismatch, not evidence that the generated OCaml
  itself is broken. GHC (via \<open>isabelle_stack\<close>) builds arm64-native
  correctly, which is why Haskell checking stays in the main session (see
  \<open>Example_Analysis_Dispatch.thy\<close>'s own \<open>checking Haskell\<close> clause) while
  OCaml checking is isolated here, built only on Linux CI where this
  architecture mismatch does not occur.
\<close>

export_code
  analyse Sign_Analysis Interval_Analysis
  imp_prog.make
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  api_var api_assign api_random api_call api_proc api_program
  checking OCaml

end
