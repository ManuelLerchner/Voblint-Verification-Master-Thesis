theory Check_Report
  imports Check_Result CFG_Enumeration
begin

section \<open>Whole-program executable check report\<close>

text \<open>
  A single, domain-generic report over every compiled \<^const>\<open>EA_Check\<close> edge:
  one entry per check, at its own source node, classified by whatever
  \<open>classify\<close> function a domain supplies (\<open>sign_classify_check\<close> and its
  siblings, or \<open>abstract_check_domain.classify_check\<close> generically).
  Entries are read directly off \<^const>\<open>intra\<close> through the same deterministic
  order \<^const>\<open>cfg_intra_list\<close> already gives the TD bridge, rather than
  sorting \<^typ>\<open>pp\<close> or \<^typ>\<open>exp\<close> values by hand: a compiled \<^const>\<open>checks\<close>
  table has exactly the same \<^const>\<open>EA_Check\<close> edges as its source, by
  construction, so this report is a second view of that one representation,
  not a parallel table.

  This layer is deliberately generic in \<open>classify\<close>: it depends on neither
  \<open>Abstract_Checks\<close> nor a specific domain, only on a plain
  \<^typ>\<open>exp \<Rightarrow> 's \<Rightarrow> check_result\<close> function and its own soundness obligations
  below.
\<close>

type_synonym check_report_entry = "pp \<times> exp \<times> check_result"

definition classify_checks ::
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> check_report_entry list" where
  "classify_checks g env classify =
     map (\<lambda>(u, a, v). (u, ea_check_cond a, classify (ea_check_cond a) (env u)))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

text \<open>Membership unfolds to an \<^const>\<open>EA_Check\<close> edge at the entry's own
  source node, classified there --- the shape every soundness and
  worked-example use of \<^const>\<open>classify_checks\<close> goes through.\<close>

lemma classify_checks_mem_iff:
  assumes "finite (intra g)"
  shows "(v, c, r) \<in> set (classify_checks g env classify)
     \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g) \<and> r = classify c (env v)"
  unfolding classify_checks_def set_map set_filter
  using set_cfg_intra_list[OF assms]
  by (auto simp: image_iff split: edge_action.splits)

text \<open>
  Soundness bridge: a \<^term>\<open>Check_Proved\<close> report entry's condition genuinely
  holds at every reaching store, and a \<^term>\<open>Check_Refuted\<close> entry's condition
  genuinely fails --- given the same two facts every per-domain instance
  already proves once: a \<open>classify_check_proved\<close>/\<open>classify_check_refuted\<close>-
  shaped soundness obligation for the domain's own \<open>classify\<close>, and node-local
  collecting soundness (\<open>reach v \<le> gamma_state (env v)\<close>) for the checked
  node. Neither theorem invents new domain reasoning; both only relocate an
  existing per-node fact to every entry of the whole-program report.
  \<^term>\<open>Check_Unknown\<close> gets no counterpart, matching \<open>classify_check\<close> itself.
\<close>

theorem classify_checks_proved_sound:
  fixes gamma_state :: "'s \<Rightarrow> store set"
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Check_Proved) \<in> set (classify_checks g env classify)"
    and classify_proved: "\<And>d s. classify c d = Check_Proved \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> truthy (aval c s)"
    and node_sound: "reach v \<le> gamma_state (env v)"
  shows "\<forall>s \<in> reach v. truthy (aval c s)"
proof
  fix s assume s: "s \<in> reach v"
  have "classify c (env v) = Check_Proved"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Proved env classify] by auto
  moreover have "s \<in> gamma_state (env v)" using node_sound s by blast
  ultimately show "truthy (aval c s)" using classify_proved by blast
qed

theorem classify_checks_refuted_sound:
  fixes gamma_state :: "'s \<Rightarrow> store set"
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Check_Refuted) \<in> set (classify_checks g env classify)"
    and classify_refuted: "\<And>d s. classify c d = Check_Refuted
                              \<Longrightarrow> s \<in> gamma_state d \<Longrightarrow> \<not> truthy (aval c s)"
    and node_sound: "reach v <= gamma_state (env v)"
  shows "\<forall>s \<in> reach v. ~ truthy (aval c s)"
proof
  fix s assume s: "s : reach v"
  have "classify c (env v) = Check_Refuted"
    using mem classify_checks_mem_iff[OF fin, of v c Check_Refuted env classify] by auto
  moreover have "s : gamma_state (env v)" using node_sound s by blast
  ultimately show "~ truthy (aval c s)" using classify_refuted by blast
qed

text \<open>
  State-carrying sibling of \<^const>\<open>classify_checks\<close>: the same traversal and
  classification, with the node's own abstract state attached to each entry.
  \<^const>\<open>classify_checks\<close> stays the soundness-critical primitive every domain
  cites directly; the projection lemma below shows this report is exactly that
  one with a fourth field added, so \<open>classify_checks_proved_sound\<close> and
  \<open>classify_checks_refuted_sound\<close> reach it through the projection without
  restatement.
\<close>

definition classify_checks_with_state ::
    "cfg \<Rightarrow> (pp \<Rightarrow> 's) \<Rightarrow> (exp \<Rightarrow> 's \<Rightarrow> check_result) \<Rightarrow> (pp \<times> exp \<times> check_result \<times> 's) list" where
  "classify_checks_with_state g env classify =
     map (\<lambda>(u, c, r). (u, c, r, env u)) (classify_checks g env classify)"

lemma classify_checks_with_state_proj [simp]:
  "map (\<lambda>(u, c, r, s). (u, c, r)) (classify_checks_with_state g env classify)
     = classify_checks g env classify"
  unfolding classify_checks_with_state_def by (simp add: comp_def case_prod_beta)

end
