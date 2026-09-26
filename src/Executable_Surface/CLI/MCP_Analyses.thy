theory MCP_Analyses
  imports
    Analysis_Config
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_Analysis_Int.Int_Analyses"
    "Voblint_Analysis_Parity.Parity_Analyses"
    "Voblint_Analysis_Congruence.Congruence_Analyses"
    "Voblint_Framework.Local_Spec_Product"
    "Voblint_Framework.Check_Answer"
begin

section \<open>The state every registered analysis runs on\<close>

text \<open>
  Goblint's \<open>MCP\<close> keeps one state per activated analysis side by side. Voblint
  fixes the combined state once, with a field for every registered analysis,
  and lets the activation list choose which fields run. The fields sit in
  nested \<^typ>\<open>('a, 'b) analysis_product\<close>s, whose order, join, widening and
  narrowing are componentwise, so a field no active analysis touches stays
  what it started as and changes nothing the solver compares.

  A slot names the position of a field; the same five positions serve the
  solver's state and the published value.
\<close>

definition slot1 :: "('a, 'r) analysis_product \<Rightarrow> 'a" where
  "slot1 r = pleft r"

definition slot2 :: "('x, ('a, 'r) analysis_product) analysis_product \<Rightarrow> 'a" where
  "slot2 r = pleft (pright r)"

definition slot3 ::
  "('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product \<Rightarrow> 'a" where
  "slot3 r = pleft (pright (pright r))"

definition slot4 ::
  "('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a" where
  "slot4 r = pleft (pright (pright (pright r)))"

definition slot5 ::
  "('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a" where
  "slot5 r = pright (pright (pright (pright r)))"

definition set_slot1 :: "('a, 'r) analysis_product \<Rightarrow> 'a \<Rightarrow> ('a, 'r) analysis_product" where
  "set_slot1 r v = Product v (pright r)"

definition set_slot2 ::
  "('x, ('a, 'r) analysis_product) analysis_product \<Rightarrow> 'a
     \<Rightarrow> ('x, ('a, 'r) analysis_product) analysis_product" where
  "set_slot2 r v = Product (pleft r) (Product v (pright (pright r)))"

definition set_slot3 ::
  "('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product \<Rightarrow> 'a
     \<Rightarrow> ('x, ('y, ('a, 'r) analysis_product) analysis_product) analysis_product" where
  "set_slot3 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product v (pright (pright (pright r)))))"

definition set_slot4 ::
  "('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a
   \<Rightarrow> ('x, ('y, ('z, ('a, 'r) analysis_product) analysis_product) analysis_product)
     analysis_product" where
  "set_slot4 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
       (Product v (pright (pright (pright (pright r)))))))"

definition set_slot5 ::
  "('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product \<Rightarrow> 'a
   \<Rightarrow> ('x, ('y, ('z, ('w, 'a) analysis_product) analysis_product) analysis_product)
     analysis_product" where
  "set_slot5 r v =
     Product (pleft r) (Product (pleft (pright r)) (Product (pleft (pright (pright r)))
       (Product (pleft (pright (pright (pright r)))) v)))"

lemmas slot_defs [simp] = slot1_def slot2_def slot3_def slot4_def slot5_def
  set_slot1_def set_slot2_def set_slot3_def set_slot4_def set_slot5_def

lemma pleft_pright_bot [simp]:
  "pleft (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  "pright (\<bottom> :: ('a::order_bot, 'b::order_bot) analysis_product) = \<bottom>"
  by (simp_all add: bot_analysis_product_def)

lemma pleft_pright_mono:
  "p \<le> q \<Longrightarrow> pleft p \<le> pleft q" "p \<le> q \<Longrightarrow> pright p \<le> pright q"
  by (simp_all add: less_eq_analysis_product_def)

type_synonym mcp_st =
  "(sign exec_dg_st lifted,
    (ivl exec_dg_st lifted,
     (int_dom exec_dg_st lifted,
      (parity exec_dg_st lifted, congruence exec_dg_st lifted) analysis_product)
     analysis_product) analysis_product) analysis_product"

type_synonym mcp_val =
  "(sign abs_state lifted,
    (ivl abs_state lifted,
     (int_dom abs_state lifted,
      (parity abs_state lifted, congruence abs_state lifted) analysis_product)
     analysis_product) analysis_product) analysis_product"

subsection \<open>Each analysis on its own field\<close>

text \<open>
  An analysis runs as its executable component on its own field, through the
  lens of \<^const>\<open>lift_get\<close> and \<^const>\<open>lift_put\<close>.
\<close>

fun mcp_component_of ::
  "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_component_of \<G> p Sign_Analysis = lens_of (lift_get slot1) (lift_put set_slot1)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (sign_tf_st_for \<G>) (sign_enter_st_for \<G>))"
| "mcp_component_of \<G> p Interval_Analysis = lens_of (lift_get slot2) (lift_put set_slot2)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (ivl_tf_st_for \<G>) (ivl_enter_st_for \<G>))"
| "mcp_component_of \<G> p Int_Analysis = lens_of (lift_get slot3) (lift_put set_slot3)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (int_tf_st_for Refine_Fixpoint \<G>) (int_dom_enter_st_for Refine_Fixpoint \<G>))"
| "mcp_component_of \<G> p Parity_Analysis = lens_of (lift_get slot4) (lift_put set_slot4)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (parity_tf_st_for \<G>) (parity_enter_st_for \<G>))"
| "mcp_component_of \<G> p Congruence_Analysis = lens_of (lift_get slot5) (lift_put set_slot5)
     (exec_component \<G> (resolved_st_q_is_bot_for (declared_global_vars p))
        (congruence_tf_st_for \<G>) (congruence_enter_st_for \<G>))"

text \<open>What each field describes, read through the analysis's own readback.\<close>

fun part_gamma :: "(vname \<Rightarrow> bool) \<Rightarrow> analysis_domain \<Rightarrow> mcp_st lifted \<Rightarrow> store set" where
  "part_gamma \<G> Sign_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot1 x)))"
| "part_gamma \<G> Interval_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot2 x)))"
| "part_gamma \<G> Int_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot3 x)))"
| "part_gamma \<G> Parity_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot4 x)))"
| "part_gamma \<G> Congruence_Analysis =
     (\<lambda>x. gamma_point (map_lift (fun_of_resolved_st_q_for \<G>) (lift_get slot5 x)))"

lemma field_component_sound:
  fixes f :: "'r::{semilattice_sup, order_bot} \<Rightarrow> 'c::semilattice_sup lifted"
  assumes sound: "mcp_component_sound \<G> (\<lambda>d. gamma_point (map_lift R d)) cmp"
    and get_put: "\<And>r v. f (u r v) = v" and get_bot: "f \<bottom> = Bot"
    and mono: "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "mcp_component_sound \<G> (\<lambda>x. gamma_point (map_lift R (lift_get f x)))
           (lens_of (lift_get f) (lift_put u) cmp)"
  by (rule lens_of_sound[OF sound, where get = "lift_get f"])
     (simp_all add: lift_get_put[OF get_put get_bot] lift_get_mono[OF mono])


lemma mcp_component_of_sound:
  "mcp_component_sound (declared_global p) (part_gamma (declared_global p) a)
     (mcp_component_of (declared_global p) p a)"
  by (cases a; simp only: part_gamma.simps mcp_component_of.simps;
      rule field_component_sound[OF sign_rule.comp_sound]
        field_component_sound[OF interval_rule.comp_sound]
        field_component_sound[OF int_rule.comp_sound]
        field_component_sound[OF parity_rule.comp_sound]
        field_component_sound[OF congruence_rule.comp_sound];
      auto simp: less_eq_analysis_product_def)

lemma field_frame:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = Bot"
  shows "mcp_frame (lens_of (lift_get f1) (lift_put u1) cmp)
           (\<lambda>x. gamma_point (map_lift R (lift_get f2 x)))"
  unfolding mcp_frame_def lens_of_def by (auto simp: lift_get_put_other[OF assms])

lemma mcp_component_of_frame:
  "a \<noteq> b \<Longrightarrow> mcp_frame (mcp_component_of \<G> p a) (part_gamma \<G> b)"
  by (cases a; cases b; simp only: part_gamma.simps mcp_component_of.simps;
      simp; rule field_frame; simp)

lemma single_entry_exec_component:
  "single_entry (exec_component \<G> empty_pred tf_st enter_st)"
  by (simp add: single_entry_def exec_component_def lens_component_def)

lemma single_entry_mcp_component_of: "single_entry (mcp_component_of \<G> p a)"
  by (cases a) (auto intro!: single_entry_lens_of single_entry_exec_component lift_put_get)

subsection \<open>The active analyses, run as one\<close>

text \<open>
  The combined state is unreachable as soon as one active analysis says its
  field is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close> when one component does. The
  normalization changes no concretization: a field that describes nothing
  empties the intersection already.
\<close>

fun part_live :: "analysis_domain \<Rightarrow> mcp_st \<Rightarrow> bool" where
  "part_live Sign_Analysis r = (slot1 r \<noteq> Bot)"
| "part_live Interval_Analysis r = (slot2 r \<noteq> Bot)"
| "part_live Int_Analysis r = (slot3 r \<noteq> Bot)"
| "part_live Parity_Analysis r = (slot4 r \<noteq> Bot)"
| "part_live Congruence_Analysis r = (slot5 r \<noteq> Bot)"

definition mcp_norm :: "analysis_domain list \<Rightarrow> mcp_st lifted \<Rightarrow> mcp_st lifted" where
  "mcp_norm as x =
     (case x of Bot \<Rightarrow> Bot | Lifted r \<Rightarrow> if list_all (\<lambda>a. part_live a r) as then x else Bot)"

lemma part_gamma_Bot [simp]: "part_gamma \<G> a Bot = {}"
  by (cases a) simp_all

lemma part_gamma_dead: "\<not> part_live a r \<Longrightarrow> part_gamma \<G> a (Lifted r) = {}"
  by (cases a) simp_all

lemma mcp_gamma_norm:
  "mcp_gamma (map (part_gamma \<G>) as) (mcp_norm as x) = mcp_gamma (map (part_gamma \<G>) as) x"
  by (cases x) (auto simp: mcp_norm_def mcp_gamma_def list_all_iff dest: part_gamma_dead)

definition mcp_comp ::
  "analysis_domain list \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> mcp_st lifted mcp_component" where
  "mcp_comp as \<G> p = map_component (mcp_norm as) (mcp_combine (map (mcp_component_of \<G> p) as))"

theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "mcp_component_sound (declared_global p)
           (mcp_gamma (map (part_gamma (declared_global p)) as))
           (mcp_comp as (declared_global p) p)"
proof -
  let ?gcs = "map (\<lambda>a. (part_gamma (declared_global p) a,
                         mcp_component_of (declared_global p) p a)) as"
  have "mcp_component_sound (declared_global p) (mcp_gamma (map fst ?gcs))
          (mcp_combine (map snd ?gcs))"
    by (rule mcp_combine_sound)
       (auto simp: mcp_component_of_sound assms
         intro!: mcp_independent_map mcp_component_of_frame)
  then show ?thesis
    unfolding mcp_comp_def
    by (intro map_component_sound) (simp_all add: comp_def mcp_gamma_norm)
qed

lemma single_entry_mcp_comp: "as \<noteq> [] \<Longrightarrow> single_entry (mcp_comp as \<G> p)"
  unfolding mcp_comp_def
  by (intro single_entry_map_component single_entry_mcp_combine)
     (auto simp: single_entry_mcp_component_of)

end
