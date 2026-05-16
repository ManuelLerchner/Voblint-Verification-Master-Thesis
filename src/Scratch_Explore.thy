(* Dev-only scratch theory for MCP `explore` query='proof'.
   Imports Isar_Explore so the isar_explore print function is registered
   for any cursor position inside this file. Don't import Isar_Explore
   from production theories — keep it scoped here. *)
theory Scratch_Explore
  imports
    Main
    "iq.Isar_Explore"
begin

lemma demo_explore: "(x::nat) + 0 = x"
  sorry

end
