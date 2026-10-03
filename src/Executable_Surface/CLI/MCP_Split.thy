theory MCP_Split
  imports MCP_Analyses
begin

section \<open>The registered analyses with program globals on the shared channel\<close>

text \<open>
  The ownership-split placement asks its carrier for three operations: recombine a
  local half with a global half, and project each half back out. On the combined
  state they are defined field by field, so a carrier that splits is a type class
  closed under the constructors the combined state is built from. A pointwise field
  splits by the location each name is stored at; the relational field relates
  variables across the split and stays wholly local.
\<close>

class ownership_split = order_bot +
  fixes split_cmb :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and split_rl :: "'a \<Rightarrow> 'a"
    and split_rg :: "'a \<Rightarrow> 'a"
  assumes split_cmb_mono: "d \<le> d' \<Longrightarrow> g \<le> g' \<Longrightarrow> split_cmb d g \<le> split_cmb d' g'"
    and split_recombine: "split_cmb (split_rl x) (split_rg x) = x"
    and split_cmb_rl: "split_cmb (split_rl x) g = split_cmb x g"
    and split_rl_cmb: "split_rl (split_cmb d g) = split_rl d"

instantiation default_st :: (order_bot) ownership_split
begin

definition split_cmb_default_st :: "'a default_st \<Rightarrow> 'a default_st \<Rightarrow> 'a default_st" where
  "split_cmb_default_st = combine_default_st"

definition split_rl_default_st :: "'a default_st \<Rightarrow> 'a default_st" where
  "split_rl_default_st = restrict_local_default_st"

definition split_rg_default_st :: "'a default_st \<Rightarrow> 'a default_st" where
  "split_rg_default_st = restrict_global_default_st"

instance
proof
  fix d d' g g' :: "'a default_st"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (auto simp: split_cmb_default_st_def le_default_st_iff split: location.split)
qed (simp_all add: split_cmb_default_st_def split_rl_default_st_def split_rg_default_st_def)

end

instantiation relc :: ownership_split
begin

definition split_cmb_relc :: "relc \<Rightarrow> relc \<Rightarrow> relc" where "split_cmb_relc d g = d"
definition split_rl_relc :: "relc \<Rightarrow> relc" where "split_rl_relc d = d"
definition split_rg_relc :: "relc \<Rightarrow> relc" where "split_rg_relc d = bot"

instance
  by standard (simp_all add: split_cmb_relc_def split_rl_relc_def split_rg_relc_def)

end

instantiation analysis_product :: (ownership_split, ownership_split) ownership_split
begin

definition split_cmb_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_cmb_analysis_product d g =
     Product (split_cmb (pleft d) (pleft g)) (split_cmb (pright d) (pright g))"

definition split_rl_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_rl_analysis_product d = Product (split_rl (pleft d)) (split_rl (pright d))"

definition split_rg_analysis_product ::
  "('a, 'b) analysis_product \<Rightarrow> ('a, 'b) analysis_product" where
  "split_rg_analysis_product d = Product (split_rg (pleft d)) (split_rg (pright d))"

instance
proof
  fix d d' g g' :: "('a, 'b) analysis_product"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (simp add: split_cmb_analysis_product_def less_eq_analysis_product_def split_cmb_mono)
next
  fix x g :: "('a, 'b) analysis_product"
  show "split_cmb (split_rl x) (split_rg x) = x"
    by (cases x) (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def
        split_rg_analysis_product_def split_recombine)
  show "split_cmb (split_rl x) g = split_cmb x g"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_cmb_rl)
next
  fix d g :: "('a, 'b) analysis_product"
  show "split_rl (split_cmb d g) = split_rl d"
    by (simp add: split_cmb_analysis_product_def split_rl_analysis_product_def split_rl_cmb)
qed

end

text \<open>
  An unreachable point stays unreachable whatever global it is recombined with, and
  a reachable point recombined with a global nothing has published yet reads the
  global half at its bottom.
\<close>

instantiation lifted :: ("{ownership_split, semilattice_sup}") ownership_split
begin

definition split_cmb_lifted :: "'a lifted \<Rightarrow> 'a lifted \<Rightarrow> 'a lifted" where
  "split_cmb_lifted d g = (case d of Bot \<Rightarrow> Bot
     | Lifted a \<Rightarrow> Lifted (split_cmb a (case g of Bot \<Rightarrow> bot | Lifted b \<Rightarrow> b)))"

definition split_rl_lifted :: "'a lifted \<Rightarrow> 'a lifted" where
  "split_rl_lifted = map_lift split_rl"

definition split_rg_lifted :: "'a lifted \<Rightarrow> 'a lifted" where
  "split_rg_lifted = map_lift split_rg"

instance
proof
  fix d d' g g' :: "'a lifted"
  assume "d \<le> d'" "g \<le> g'"
  then show "split_cmb d g \<le> split_cmb d' g'"
    by (cases d; cases d'; cases g; cases g')
       (auto simp: split_cmb_lifted_def intro: split_cmb_mono)
next
  fix x g :: "'a lifted"
  show "split_cmb (split_rl x) (split_rg x) = x"
    by (cases x) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_rg_lifted_def
        split_recombine)
  show "split_cmb (split_rl x) g = split_cmb x g"
    by (cases x) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_cmb_rl)
next
  fix d g :: "'a lifted"
  show "split_rl (split_cmb d g) = split_rl d"
    by (cases d) (simp_all add: split_cmb_lifted_def split_rl_lifted_def split_rl_cmb)
qed

end

lemma split_cmb_Bot [simp]:
  "split_cmb (Bot :: 'a::{ownership_split, semilattice_sup} lifted) g = Bot"
  by (simp add: split_cmb_lifted_def)

subsection \<open>The registration\<close>

text \<open>
  The combined analysis owes the shared-globals placement exactly what it owes the
  whole-state one, plus the carrier laws above.
\<close>

lemma mcp_split_dg_analysis:
  fixes analysis_global :: 'k and global_of :: "unit \<Rightarrow> 'k"
  assumes "\<And>v ctx. seed v ctx \<noteq> analysis_global"
    and own_key: "\<And>n. global_of n = analysis_global"
  shows "dg_analysis (mcp_comp (activation as)) (mcp_emp (activation as)) mcp_rd
    (mcp_init (activation as)) analysis_global global_of seed
    (TD_side_rule_Interp_solve r)
    (TD_side_rule_Interp.solve_dom TYPE('k) TYPE((mcp_st lifted, mcp_st lifted) dg_state) r)
    \<bottom> (mcp_classify (activation as)) (mcp_gamma_v (activation as))
    (mcp_empty_v (activation as)) (TD_side_rule_Interp_solve_c r)
    (\<lambda>\<G> c. ownership_split_lift_gen split_cmb split_rg split_rl (dg_spec_of c))
    (\<lambda>\<G> d e. split_cmb d (e ())) (\<lambda>\<G>. split_rl) (\<lambda>\<G>. split_rg) (\<lambda>\<G> p. [])"
proof (rule dg_analysis_ownership_splitI[OF td_certified_solver],
    goal_cases CompSound EnterSingle CmbMono Split CmbRl RlCmb CmbBot EmptyRd EmptyVSound
    SeedNe ClProved ClRefuted BotState Init OwnKey)
  case (CompSound p)
  have eq: "mcp_gamma (map (part_gamma (declared_global p)) (activation as))
      = (\<lambda>d. gamma_lift (mcp_gamma_v (activation as)) (map_lift (mcp_rd (declared_global p)) d))"
    by (rule ext) (rule mcp_gamma_rd[OF activation_ne])
  show ?case using mcp_comp_sound[of "activation as" p] unfolding eq by simp
next
  case (EnterSingle p ci d)
  show ?case
    using single_entryD[OF single_entry_mcp_comp[OF activation_ne],
        of as "declared_global p" p
          "ls_channel (mcp_comp (activation as) (declared_global p) p) d" ci "(d, d)"]
    by (simp add: dg_pipeline.comp_entry_def)
next
  case (CmbMono \<G> d d' g g') then show ?case by (rule split_cmb_mono)
next
  case (Split \<G> x) show ?case by (rule split_recombine)
next
  case (CmbRl \<G> x g) show ?case by (rule split_cmb_rl)
next
  case (RlCmb \<G> d g) show ?case by (rule split_rl_cmb)
next
  case (CmbBot \<G> g) show ?case by simp
next
  case (EmptyRd p s) show ?case by (rule mcp_emp_rd)
next
  case EmptyVSound show ?case by (rule sound_emptiness_mcp)
next
  case (SeedNe v ctx) show ?case by (rule assms)
next
  case (ClProved e d s) then show ?case by (rule mcp_classify_proved)
next
  case (ClRefuted e d s) then show ?case by (rule mcp_classify_refuted)
next
  case BotState show ?case by (rule mcp_gamma_v_bot[OF activation_ne])
next
  case (Init p) show ?case by (rule mcp_init_sound)
next
  case (OwnKey n) show ?case by (rule own_key)
qed

text \<open>
  The three context policies again, with program globals on the shared channel.
\<close>

global_interpretation mcp_split_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    "Analysis_Global ()" Analysis_Global Activation_Seed "\<lambda>_. route_unit" "()"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, unit) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. ownership_split_lift_gen split_cmb split_rg split_rl (dg_spec_of c)"
    "\<lambda>\<G> d e. split_cmb d (e ())" "\<lambda>\<G>. split_rl" "\<lambda>\<G>. split_rg" "\<lambda>\<G> p. []"
  for as r
  by (rule mcp_split_dg_analysis) simp_all

global_interpretation mcp_split_es_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    "Analysis_Global ()" Analysis_Global Activation_Seed "mcp_formals_route (activation as)"
      mcp_root_ctx
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE((unit, mcp_ctx) global_unknown)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. ownership_split_lift_gen split_cmb split_rg split_rl (dg_spec_of c)"
    "\<lambda>\<G> d e. split_cmb d (e ())" "\<lambda>\<G>. split_rl" "\<lambda>\<G>. split_rg" "\<lambda>\<G> p. []"
  for as r
  by (rule mcp_split_dg_analysis) simp_all

global_interpretation mcp_split_cs_rule: dg_analysis
    "mcp_comp (activation as)" "mcp_emp (activation as)" mcp_rd "mcp_init (activation as)"
    Call_String_Context.Global "\<lambda>_::unit. Call_String_Context.Global"
    Call_String_Context.Seed "\<lambda>_. cs_route k" "[]"
    "TD_side_rule_Interp_solve r"
    "TD_side_rule_Interp.solve_dom TYPE(call_string_gk)
       TYPE((mcp_st lifted, mcp_st lifted) dg_state) r"
    \<bottom> "mcp_classify (activation as)" "mcp_gamma_v (activation as)"
    "mcp_empty_v (activation as)" "TD_side_rule_Interp_solve_c r"
    "\<lambda>\<G> c. ownership_split_lift_gen split_cmb split_rg split_rl (dg_spec_of c)"
    "\<lambda>\<G> d e. split_cmb d (e ())" "\<lambda>\<G>. split_rl" "\<lambda>\<G>. split_rg" "\<lambda>\<G> p. []"
  for as k r
  by (rule mcp_split_dg_analysis) simp_all

end
