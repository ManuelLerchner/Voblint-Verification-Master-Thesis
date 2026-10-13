(* src/Program_Model/CFG/CFG_Def.thy *)
record ('v, 'e) gcfg =
  intra     :: "(cfg_node \<times> ('v, 'e) gedge_action \<times> cfg_node) set"
  calls     :: "(cfg_node \<times> ('v, 'e) gcall_action \<times> cfg_node \<times> cfg_node) set"
  cfg_entry :: cfg_node
