(* src/Program_Model/CFG/CFG_Def.thy *)
record cfg =
  intra     :: "(cfg_node \<times> edge_action \<times> cfg_node) set"
  calls     :: "(cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
  cfg_entry :: cfg_node
  checks    :: "(cfg_node \<times> exp) set"
