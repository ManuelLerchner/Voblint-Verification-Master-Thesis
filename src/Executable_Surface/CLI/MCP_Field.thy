theory MCP_Field
  imports
    "Voblint_Framework.Local_Spec_Product"
    "Voblint_Framework.MCP_Spec"
    "Voblint_Framework.Analysis_Result"
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

lemma pleft_pright_mono:
  "p \<le> q \<Longrightarrow> pleft p \<le> pleft q" "p \<le> q \<Longrightarrow> pright p \<le> pright q"
  by (simp_all add: less_eq_analysis_product_def)

lemma field_component_sound:
  fixes f :: "'r::{semilattice_sup, order_bot} \<Rightarrow> 'c::semilattice_sup lifted"
  assumes sound: "mcp_component_sound \<G> (\<lambda>d. gamma_point (map_lift R d)) cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = Bot"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "mcp_component_sound \<G> (\<lambda>x. gamma_point (map_lift R (lift_get f x)))
           (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule lens_of_sound[OF sound, where get = "lift_get f"])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])

lemma field_frame:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = Bot"
  shows "mcp_frame (lens_of (lift_get f1) (lift_put u1) cmp)
           (\<lambda>x. gamma_point (map_lift R (lift_get f2 x)))"
  unfolding mcp_frame_def lens_of_def by (auto simp: lift_get_put_other[OF assms])

end
