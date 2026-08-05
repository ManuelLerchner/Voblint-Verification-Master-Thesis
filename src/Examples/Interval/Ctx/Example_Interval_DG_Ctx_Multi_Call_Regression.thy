theory Example_Interval_DG_Ctx_Multi_Call_Regression
  imports Example_Interval_DG_Ctx_Flagship
begin

section \<open>Regression: a call site with more than one outgoing call edge\<close>

text \<open>
  \<open>twice_cfg\<close>'s two calls share one callee entry and never share a call site, so it
  cannot exercise the case \<^const>\<open>routed_cmb\<close>'s routing comment warns about: a call site
  with more than one outgoing call edge, where reconstructing the triggering call action
  from the call site alone (\<^const>\<open>call_successor_list\<close>, taking its head) is ambiguous,
  while \<^const>\<open>return_call_action_list\<close> --- keyed on the return's continuation, not the
  call site --- picks the exact edge unambiguously.

  \<open>multi_call_cfg\<close> is a minimal hand-built witness: one call site, \<open>Statement 0\<close>, with
  two outgoing edges to two different callees and two different continuations.
\<close>

definition mc_f1 :: pname where "mc_f1 = ''f1''"
definition mc_f2 :: pname where "mc_f2 = ''f2''"

definition mc_ca1 :: call_action where
  "mc_ca1 = CallEdge (Some ''x'') [''p''] [VIMP_Syntax.N 3]"
definition mc_ca2 :: call_action where
  "mc_ca2 = CallEdge (Some ''y'') [''p''] [VIMP_Syntax.N 10]"

definition multi_call_cfg :: cfg where
  "multi_call_cfg =
     \<lparr> intra =
         { (FunctionEntry mc_f1, EA_Ret None mc_f1, FunctionResult mc_f1),
           (FunctionEntry mc_f2, EA_Ret None mc_f2, FunctionResult mc_f2) },
       calls =
         { (Statement 0, mc_ca1, FunctionEntry mc_f1, Statement 1),
           (Statement 0, mc_ca2, FunctionEntry mc_f2, Statement 2) },
       cfg_entry = Statement 0 \<rparr>"

lemmas mc_defs = multi_call_cfg_def mc_ca1_def mc_ca2_def mc_f1_def mc_f2_def

text \<open>One call site, two outgoing edges to distinct continuations with distinct actions.\<close>
lemma multi_call_shares_call_site:
  "(Statement 0, mc_ca1, FunctionEntry mc_f1, Statement 1) \<in> calls multi_call_cfg"
  "(Statement 0, mc_ca2, FunctionEntry mc_f2, Statement 2) \<in> calls multi_call_cfg"
  "Statement 1 \<noteq> Statement 2"
  "mc_ca1 \<noteq> mc_ca2"
  by (simp_all add: mc_defs)

lemma multi_call_finite: "finite (calls multi_call_cfg)"
  by (simp add: multi_call_cfg_def)

subsection \<open>\<open>call_successor_list\<close> cannot distinguish the two returns\<close>

text \<open>Both outgoing edges are visible from the shared call site, so a return-side
  reconstruction that only knows the call site --- \<^term>\<open>hd (call_successor_list g cc)\<close>,
  the pattern \<^const>\<open>routed_cmb\<close> avoids --- returns the same call action
  irrespective of which continuation triggered the return.\<close>

lemma multi_call_successor_list_set:
  "set (call_successor_list multi_call_cfg (Statement 0)) =
     {(FunctionEntry mc_f1, mc_ca1, Statement 1), (FunctionEntry mc_f2, mc_ca2, Statement 2)}"
  by (simp add: call_successor_list_def mc_defs)

subsection \<open>\<open>return_call_action_list\<close> selects the exact edge by continuation\<close>

lemma multi_call_return_action_by_continuation:
  "return_call_action_list multi_call_cfg (Statement 1) =
     [(Statement 0, mc_ca1, FunctionResult mc_f1)]"
  "return_call_action_list multi_call_cfg (Statement 2) =
     [(Statement 0, mc_ca2, FunctionResult mc_f2)]"
  by eval+

subsection \<open>The naive reconstruction is wrong for at least one of the two returns\<close>

text \<open>Selecting the first successor of the call site yields one fixed call action for
  \<^emph>\<open>both\<close> continuations, but the two continuations' correct actions differ
  (\<open>multi_call_shares_call_site\<close>).  A single fixed choice cannot equal both, so it is
  wrong for at least one return --- the failure \<^const>\<open>return_call_action_list\<close> avoids by
  keying on the continuation instead of the call site.\<close>

lemma multi_call_naive_head_reconstruction_is_wrong_for_some_return:
  "let (_, ca, _) = hd (call_successor_list multi_call_cfg (Statement 0))
   in ca \<noteq> mc_ca1 \<or> ca \<noteq> mc_ca2"
  using multi_call_shares_call_site(4) by (cases "hd (call_successor_list multi_call_cfg (Statement 0))") auto

end
