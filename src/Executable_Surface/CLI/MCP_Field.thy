theory MCP_Field
  imports
    "Voblint_Framework.Local_Spec_Product"
    "Voblint_Framework.Oracle_Wrappers"
    "Voblint_Framework.Solved_Table"
    "Voblint_Exec.DG_Local_State_Exec_Refinement"
begin

section \<open>One analysis on one field of the combined state\<close>

text \<open>
  The combined state nests one reachability-lifted field per registered analysis
  in \<^typ>\<open>('a, 'b) analysis_product\<close>s. An analysis runs on its field through
  \<^const>\<open>lift_get\<close> and \<^const>\<open>lift_put\<close>; the two lemmas below turn its own
  soundness into soundness on the field, and show that it leaves every other field
  alone. They are stated once for any field, so the generated carrier only cites them.
\<close>

lemma pleft_pright_bot [simp]:
  "pleft (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  "pright (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  by (simp_all add: bot_analysis_product_def)

lemma field_component_sound:
  fixes f :: "'r::{semilattice_sup, order_bot} \<Rightarrow> 'c::order_bot"
  assumes sound: "sound_local_spec \<G> g cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = \<bottom>"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "sound_local_spec \<G> (\<lambda>x. g (lift_get f x)) (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule lens_of_sound[OF sound, where get = "lift_get f"])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])

text \<open>
  A field's concretization that no write to another field changes is left alone
  by that field's component.
\<close>

lemma field_frame:
  assumes "\<And>x v. g (lift_put u x v) = g x"
  shows "mcp_frame (lens_of get (lift_put u) cmp) g"
  unfolding mcp_frame_def lens_of_def by (auto simp: assms)

lemma single_entry_exec_local_spec:
  "single_entry (exec_local_spec \<G> empty_pred tf_st enter_st)"
  by (simp add: single_entry_def exec_local_spec_def)

end
