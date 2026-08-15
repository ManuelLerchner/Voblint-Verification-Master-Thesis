theory Voblint_OCaml_Check
  imports Voblint_Codegen.Voblint_Codegen
begin

text \<open>
  CI-only OCaml compilation check for the \<open>export_code\<close> declarations in
  \<^theory>\<open>Voblint_Codegen.Voblint_Codegen\<close>. Kept in a separate
  session, built only by CI's Linux job (see \<open>.github/workflows/ci.yml\<close>),
  not by the default \<open>Voblint_Examples\<close> or \<open>Voblint_Codegen\<close> build.

  On Apple Silicon macOS, Isabelle's bundled \<open>opam\<close> (2.0.7) is an x86_64
  binary, so its managed OCaml toolchain links against an x86_64
  \<open>libgmp\<close> while the platform (and Homebrew's own \<open>libgmp\<close>) is arm64 ---
  an environment/toolchain mismatch, not evidence that the generated OCaml
  itself is broken. Isolating this check in its own session keeps the
  default \<open>Voblint_Examples\<close> and \<open>Voblint_Codegen\<close> builds free of it;
  CI only builds this session on Linux, where the architecture mismatch does
  not occur.

\<close>

export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_ctx Ctx_None Ctx_EntryState
  mk_program proc_decl_of
  SKIP com.Call com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  checking OCaml

end
