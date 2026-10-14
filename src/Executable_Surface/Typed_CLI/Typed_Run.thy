theory Typed_Run
  imports "Voblint_Typed_Int.Int_Tuple_Kind" "Voblint_Typed_Order.Typed_Order_Analysis"
    "Voblint_Typed_Sign.Sign_Kind" "Voblint_Typed_Parity.Parity_Kind"
begin

section \<open>Running a typed analysis\<close>

text \<open>
  The vocabulary of a typed run: the typed analyses a caller activates, the context
  policy, and the answer. The entry point that runs the activated analyses as one is
  \<open>run_typed\<close> in \<open>Typed_MCP\<close>.
\<close>

text \<open>Each refinement mode of Int is an analysis of its own, as in the untyped carrier.\<close>

datatype typed_domain =
  Typed_Interval | Typed_Congruence | Typed_Int refine_mode | Typed_Order | Typed_Sign | Typed_Parity

lemma typed_domain_cases [case_names Interval Congruence Int_Never Int_Once Int_Fixpoint Order Sign Parity]:
  obtains "a = Typed_Interval" | "a = Typed_Congruence" | "a = Typed_Int Refine_Never"
    | "a = Typed_Int Refine_Once" | "a = Typed_Int Refine_Fixpoint" | "a = Typed_Order"
    | "a = Typed_Sign" | "a = Typed_Parity"
  by (metis refine_mode.exhaust typed_domain.exhaust)

datatype typed_answer =
    Typed_Malformed
  | Typed_No_Answer
  | Typed_Analysed "(pp \<times> texp \<times> check_result) list"

type_synonym ('c, 's) typed_eqs =
  "cfg_node \<times> 'c \<Rightarrow> (cfg_node \<times> 'c, (unit, 'c) global_unknown,
     ('s lifted, 's lifted) dg_state) strategy_tree"

text \<open>
  A run answers one verdict per check, aggregated over every context that reaches it. A
  check no context reaches is answered \<open>Check_Unknown\<close>: the run makes no reachability
  claim. Contexts are call strings of bound \<open>k\<close> (\<open>0\<close> is context-insensitive) or entry
  states.
\<close>

definition verdict_result :: "contextual_verdict \<Rightarrow> check_result" where
  "verdict_result v = (case v of Lifted r \<Rightarrow> r | Bot \<Rightarrow> Check_Unknown)"

datatype typed_context = Typed_Call_String nat | Typed_Entry_State

text \<open>
  The options of a run as one value, in the role of Goblint's configuration tree: the
  activated analyses (\<^verbatim>\<open>ana.activated\<close>), the context policy, the update rule of the
  globals, and the options the domains read (\<^verbatim>\<open>sem\<close>). Goblint reads an option from its
  global tree where it is used; here the value is passed down, and a further option is a
  further field.
\<close>

record voblint_conf =
  conf_analyses :: "typed_domain list"
  conf_context :: typed_context
  conf_globals :: globals_rule
  conf_sem :: sem_conf

subsection \<open>Soundness\<close>

text \<open>A verdict the entry point answers is sound for every typed store that reaches its
  node from a store whose globals are zero at their kinds. A proved check holds there and
  a refuted one fails; neither says that the node is reached.\<close>

abbreviation reaching :: "kind_decls \<Rightarrow> imp_prog \<Rightarrow> cfg_node \<Rightarrow> tstore set" where
  "reaching ds p v \<equiv> tnode_collect (kenv_of ds) (typed_cfg p ds) (tinit_stores (kenv_of ds)) v"

abbreviation run_sound :: "typed_answer \<Rightarrow> kind_decls \<Rightarrow> imp_prog \<Rightarrow> bool" where
  "run_sound a ds p \<equiv> \<forall>rs v c res. a = Typed_Analysed rs \<longrightarrow> (v, c, res) \<in> set rs \<longrightarrow>
     (res = Check_Proved \<longrightarrow> (\<forall>s \<in> reaching ds p v. truthy (teval c s)))
     \<and> (res = Check_Refuted \<longrightarrow> (\<forall>s \<in> reaching ds p v. \<not> truthy (teval c s)))"

end

