theory Typed_Run
  imports "Voblint_Typed_Int.Int_Tuple_Kind" "Voblint_Typed_Order.Typed_Order_Analysis"
    "Voblint_Typed_Sign.Sign_Kind" "Voblint_Typed_Parity.Parity_Kind"
begin

section \<open>Running a typed analysis\<close>

text \<open>
  The vocabulary of a typed run: the typed analyses a caller activates and the context
  policy. \<open>run_voblint\<close> runs the activated analyses as one.
\<close>

text \<open>Each refinement mode of Int is an analysis of its own.\<close>

datatype typed_domain =
  Typed_Interval | Typed_Congruence | Typed_Int refine_mode | Typed_Order | Typed_Sign | Typed_Parity

lemma typed_domain_cases [case_names Interval Congruence Int_Never Int_Once Int_Fixpoint Order Sign Parity]:
  obtains "a = Typed_Interval" | "a = Typed_Congruence" | "a = Typed_Int Refine_Never"
    | "a = Typed_Int Refine_Once" | "a = Typed_Int Refine_Fixpoint" | "a = Typed_Order"
    | "a = Typed_Sign" | "a = Typed_Parity"
  by (metis refine_mode.exhaust typed_domain.exhaust)

text \<open>Contexts are call strings of bound \<open>k\<close> (\<open>0\<close> is context-insensitive) or entry states.\<close>

datatype typed_context = Typed_Call_String nat | Typed_Entry_State

text \<open>
  Where a program's globals live: in every point's own state, flow-sensitively, or
  each at its own global unknown, as a flow-insensitive value read only by the
  edges that mention it.
\<close>

datatype program_globals = Program_Globals_Flow_Sensitive | Program_Globals_Flow_Insensitive

text \<open>
  The options of a run as one value, in the role of Goblint's configuration tree: the
  activated analyses (\<^verbatim>\<open>ana.activated\<close>), the context policy, the update rule of the
  globals, where the program's globals live, and the options the domains read
  (\<^verbatim>\<open>sem\<close>). Goblint reads an option from its global tree where it is used; here the
  value is passed down, and a further option is a further field.
\<close>

record voblint_conf =
  conf_analyses :: "typed_domain list"
  conf_context :: typed_context
  conf_globals :: globals_rule
  conf_program_globals :: program_globals
  conf_sem :: sem_conf

text \<open>The typed stores that reach a node from a store whose globals are zero at their
  kinds: what every soundness theorem of a typed run is stated over.\<close>

abbreviation reaching :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> tstore set" where
  "reaching ds p v \<equiv> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v"

end

