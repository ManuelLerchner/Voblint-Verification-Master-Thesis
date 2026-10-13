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

datatype typed_domain =
  Typed_Interval | Typed_Congruence | Typed_Int | Typed_Order | Typed_Sign | Typed_Parity

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

