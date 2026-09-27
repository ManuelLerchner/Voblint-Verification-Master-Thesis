theory Analysis_Config
  imports "Voblint_Solver.Globals_Rule"
begin

section \<open>What a caller chooses\<close>

text \<open>
  Three choices change what gets solved: which analyses run, the rule that merges
  contributions to a side-effected global (\<^typ>\<open>globals_rule\<close>), and how activations
  are told apart. Each is a plain value, and every combination is analysed: there is no
  default a caller inherits and no pairing that is refused. Presentation choices are
  absent --- they select how a solved result is drawn, never what is solved, and stay
  with the handwritten renderers.

  The analyses a caller may activate are generated from the analysis manifest into
  \<open>MCP_Carrier\<close>; this theory holds the other two choices.

  A call string of length zero is an ordinary context policy: every activation shares
  the empty context, over an equation system that is still call-string keyed.
\<close>

datatype context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString nat

end
