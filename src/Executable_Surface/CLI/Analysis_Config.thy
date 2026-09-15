theory Analysis_Config
  imports "Voblint_Solver.Globals_Rule"
begin

section \<open>What a caller chooses\<close>

text \<open>
  Three choices change what gets solved: the abstract domain, the rule that merges
  contributions to a side-effected global (\<^typ>\<open>globals_rule\<close>), and how activations
  are told apart. Each is a plain value, and every combination is analysed: there is no
  default a caller inherits and no pairing that is refused. Presentation choices are
  absent --- they select how a solved result is drawn, never what is solved, and stay
  with the handwritten renderers.

  This theory names every domain, so it sits in \<open>Voblint_CLI\<close> rather than under
  \<open>Analyses/Shared/\<close>, whose layer carries no domain-specific content.

  A call string of length zero is an ordinary context policy: every activation shares
  the empty context, over an equation system that is still call-string keyed.
\<close>

datatype analysis_domain =
    Sign_Analysis | Interval_Analysis | Int_Analysis | Parity_Analysis
  | Congruence_Analysis

datatype context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString nat

end

