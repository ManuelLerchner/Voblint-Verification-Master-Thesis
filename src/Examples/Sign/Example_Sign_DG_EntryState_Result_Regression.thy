theory Example_Sign_DG_EntryState_Result_Regression
  imports
    "Voblint_Formalization.Sign_Entry_State_Ctx_Sound"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: the Sign entry-state solved-result table\<close>

text \<open>
  Acceptance witness for \<^const>\<open>analyse_sign_entry_state_result\<close>: \<open>main\<close> calls
  \<open>f\<close> from two call sites with a positive and a negative literal argument, so
  Sign's own entry-state routing separates the two activations of \<open>f\<close> into
  two distinct contexts, \<open>[SPos]\<close> and \<open>[SNeg]\<close>, rather than joining them at
  \<open>f\<close>'s single \<^const>\<open>FunctionEntry\<close> node. What is under test is that the
  generic \<open>entry_state_routed_context\<close> pipeline (Voblint_Core), freshly
  derived for Sign this pass, actually keeps two contextually distinct
  activations apart end to end -- not merely that \<open>Ctx_EntryState\<close> resolves
  for Sign.
\<close>

definition sign_es_program :: imp_prog where
  "sign_es_program = program {
     void f(p) { t := p + p; return t }
     void main() { x := f(3); y := f(-10) }
   }"

definition sign_es_result :: "(sign list, sign abs_state) analysis_result" where
  "sign_es_result = analyse_sign_entry_state_result sign_es_program"

abbreviation f_entry :: cfg_node where
  "f_entry \<equiv> FunctionEntry (STR ''f'')"

subsection \<open>Two activations of \<open>f\<close> stay apart as two distinct contexts\<close>

lemma sign_es_result_f_contexts:
  "contexts_at sign_es_result f_entry = {[SPos], [SNeg]}"
  by eval

lemma sign_es_result_f_context_count:
  "card (contexts_at sign_es_result f_entry) = 2"
  by eval

subsection \<open>Each context carries its own entry value for the formal\<close>

lemma sign_es_result_f_entry_pos:
  "map_point_state (\<lambda>st. st (STR ''p'')) (lookup_context sign_es_result f_entry [SPos])
     = Reachable SPos"
  by eval

lemma sign_es_result_f_entry_neg:
  "map_point_state (\<lambda>st. st (STR ''p'')) (lookup_context sign_es_result f_entry [SNeg])
     = Reachable SNeg"
  by eval

text \<open>The two contexts' own states are not one shared unknown collapsed to a name.\<close>

lemma sign_es_result_f_entry_contexts_distinct:
  "map_point_state (\<lambda>st. st (STR ''p'')) (lookup_context sign_es_result f_entry [SPos])
     \<noteq> map_point_state (\<lambda>st. st (STR ''p'')) (lookup_context sign_es_result f_entry [SNeg])"
  by eval

subsection \<open>Each returned value propagates back to the caller, per call site\<close>

text \<open>
  \<open>main\<close> runs under the single context \<open>[]\<close>. After both calls, \<open>x\<close> and \<open>y\<close>
  carry the sign each activation of \<open>f\<close> actually computed for \<open>p + p\<close>, not a
  join of both: \<open>3 + 3\<close> stays \<open>SPos\<close>, \<open>-10 + -10\<close> stays \<open>SNeg\<close>.
\<close>

lemma sign_es_result_after_both_calls:
  "map_point_state (\<lambda>st. (st (STR ''x''), st (STR ''y'')))
     (lookup_context sign_es_result (Statement 5) [])
   = Reachable (SPos, SNeg)"
  by eval

end

