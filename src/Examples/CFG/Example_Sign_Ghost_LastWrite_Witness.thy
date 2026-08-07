theory Example_Sign_Ghost_LastWrite_Witness
  imports
    "Voblint_Analysis.Sign_Ghost_LastWrite_DG"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Witnessed call-and-join example for the Sign x last-writer product\<close>

text \<open>
  A hand-built \<^const>\<open>part_post_solution\<close> for a real \<^const>\<open>compile_prog\<close> output exercising a
  branch/join and a real procedure call, exposing:
  \<^item> before either branch writes \<open>g\<close>: the ghost slot is \<^term>\<open>FVal None\<close>;
  \<^item> each branch yields a distinct \<^term>\<open>FVal (Some w)\<close>;
  \<^item> their join is \<^term>\<open>FTop\<close>;
  \<^item> the call/return path resets a fresh local's ghost slot on entry and preserves the caller's
    ghost facts across combine (both per the enter/combine semantics documented in
    \<open>Sign_Ghost_LastWrite_DG.thy\<close>);
  \<^item> \<open>hook_post_solution_collect_sound_ltr\<close> yields base-store (Sign) collecting soundness only
    --- this file does not establish, and does not claim, that the computed ghost component
    tracks \<^const>\<open>trace_last_writer\<close> globally (that is G-M3, separate future work).

  The base (Sign) component of the witness is uniformly \<^term>\<open>\<lambda>_. STop\<close> at every covered
  program point: since \<^const>\<open>STop\<close> is the top of the Sign lattice, every transfer's base output
  is trivially \<open>\<le> STop\<close>, so the witness never needs to compute a precise Sign value anywhere.
  This isolates all real proof content in the ghost (last-writer) component, which is exactly
  what the example is meant to demonstrate.

  The final section states five acceptance facts reading the ghost writer for \<open>g\<close> directly off
  \<open>gex_sigma3\<close> at the branch, join, and post-call points, so the shape above is visible as
  standalone theorems and not only inside the witness's internal algebra.
\<close>

subsection \<open>The source program and its compiled CFG\<close>

definition gex_prog5 :: imp_prog where
  "gex_prog5 = program { void p() { i := 0 } void main() { if (k < 1) { g := 1; j := 0 } else { g := 2; j := 1 }; p() } }"

definition gex_pi5 :: proc_table where "gex_pi5 = prog_table gex_prog5"

definition gex_g5 :: cfg where
  "gex_g5 = compile_prog gex_pi5 (prog_procs gex_prog5) prog_main_name (prog_main gex_prog5)"

definition gn_p_entry :: cfg_node where "gn_p_entry = FunctionEntry ''p''"
definition gn_main_entry :: cfg_node where "gn_main_entry = FunctionEntry ''main''"
definition gn0 :: cfg_node where "gn0 = Statement 0"
definition gn1 :: cfg_node where "gn1 = Statement 1"
definition gn2 :: cfg_node where "gn2 = Statement 2"
definition gn3 :: cfg_node where "gn3 = Statement 3"
definition gn4 :: cfg_node where "gn4 = Statement 4"
definition gn5 :: cfg_node where "gn5 = Statement 5"
definition gn6 :: cfg_node where "gn6 = Statement 6"
definition gn7 :: cfg_node where "gn7 = Statement 7"
definition gn8 :: cfg_node where "gn8 = Statement 8"
definition gn_p_exit :: cfg_node where "gn_p_exit = FunctionResult ''p''"
definition gn_main_exit :: cfg_node where "gn_main_exit = FunctionResult ''main''"

text \<open>
  Compiled shape (computed via \<open>by eval\<close>, not hand-built): the true branch writes \<open>g\<close> reaching
  \<open>gn4\<close>, the false branch writes \<open>g\<close> reaching \<open>gn6\<close>; both then write \<open>j\<close> (an unrelated
  variable, needed so the write to \<open>g\<close> does not land directly on the join node itself) before
  converging at the join \<open>gn7\<close>, which is also the call site to \<open>p\<close> (continuation \<open>gn8\<close>).
\<close>

lemma gex_node_defs: "gn0 = Statement 0" "gn1 = Statement 1" "gn2 = Statement 2" "gn3 = Statement 3" "gn4 = Statement 4"
  "gn5 = Statement 5" "gn6 = Statement 6" "gn7 = Statement 7" "gn8 = Statement 8"
  "gn_p_entry = FunctionEntry ''p''" "gn_main_entry = FunctionEntry ''main''"
  "gn_p_exit = FunctionResult ''p''" "gn_main_exit = FunctionResult ''main''"
  unfolding gn0_def gn1_def gn2_def gn3_def gn4_def gn5_def gn6_def gn7_def gn8_def gn_p_entry_def gn_main_entry_def gn_p_exit_def gn_main_exit_def
  by simp_all

lemma gex_intra_eval:
  "intra gex_g5 =
     {(gn_p_entry, EA_Nop, gn0), (gn0, EA_Assign ''i'' (N 0), gn1), (gn1, EA_Ret None ''p'', gn_p_exit),
      (gn_main_entry, EA_Nop, gn2),
      (gn2, EA_Assume (Less (V ''k'') (N 1)), gn3), (gn2, EA_AssumeNot (Less (V ''k'') (N 1)), gn5),
      (gn3, EA_Assign ''g'' (N 1), gn4), (gn4, EA_Assign ''j'' (N 0), gn7),
      (gn5, EA_Assign ''g'' (N 2), gn6), (gn6, EA_Assign ''j'' (N 1), gn7),
      (gn8, EA_Ret None ''main'', gn_main_exit)}"
  unfolding gex_g5_def gn_p_entry_def gn_main_entry_def gn0_def gn1_def gn2_def gn3_def gn4_def gn5_def gn6_def gn7_def gn8_def gn_p_exit_def gn_main_exit_def
  by eval

lemma gex_calls_eval: "calls gex_g5 = {(gn7, CallEdge None [] [], gn_p_entry, gn8)}"
  unfolding gex_g5_def gn7_def gn_p_entry_def gn8_def by eval

lemma gex_entry_eval: "cfg_entry gex_g5 = gn_main_entry"
  unfolding gex_g5_def gn_main_entry_def by eval

lemma gex_finI: "finite (intra gex_g5)" and gex_finC: "finite (calls gex_g5)"
  by (simp_all add: gex_intra_eval gex_calls_eval)

lemma gex_edge_preds:
  "intra_predecessor_list gex_g5 gn2 = [(gn_main_entry, EA_Nop)]"
  "intra_predecessor_list gex_g5 gn3 = [(gn2, EA_Assume (Less (V ''k'') (N 1)))]"
  "intra_predecessor_list gex_g5 gn4 = [(gn3, EA_Assign ''g'' (N 1))]"
  "intra_predecessor_list gex_g5 gn5 = [(gn2, EA_AssumeNot (Less (V ''k'') (N 1)))]"
  "intra_predecessor_list gex_g5 gn6 = [(gn5, EA_Assign ''g'' (N 2))]"
  "intra_predecessor_list gex_g5 gn0 = [(gn_p_entry, EA_Nop)]"
  "intra_predecessor_list gex_g5 gn1 = [(gn0, EA_Assign ''i'' (N 0))]"
  "intra_predecessor_list gex_g5 gn_p_exit = [(gn1, EA_Ret None ''p'')]"
  "intra_predecessor_list gex_g5 gn_main_exit = [(gn8, EA_Ret None ''main'')]"
  "return_call_action_list gex_g5 gn2 = []" "entry_call_list gex_g5 gn2 = []"
  "return_call_action_list gex_g5 gn3 = []" "entry_call_list gex_g5 gn3 = []"
  "return_call_action_list gex_g5 gn4 = []" "entry_call_list gex_g5 gn4 = []"
  "return_call_action_list gex_g5 gn5 = []" "entry_call_list gex_g5 gn5 = []"
  "return_call_action_list gex_g5 gn6 = []" "entry_call_list gex_g5 gn6 = []"
  "return_call_action_list gex_g5 gn0 = []" "entry_call_list gex_g5 gn0 = []"
  "return_call_action_list gex_g5 gn1 = []" "entry_call_list gex_g5 gn1 = []"
  "return_call_action_list gex_g5 gn_p_exit = []" "entry_call_list gex_g5 gn_p_exit = []"
  "return_call_action_list gex_g5 gn_main_exit = []" "entry_call_list gex_g5 gn_main_exit = []"
  unfolding gex_g5_def gex_node_defs by eval+

lemma gex_call_preds:
  "intra_predecessor_list gex_g5 gn_p_entry = []"
  "return_call_action_list gex_g5 gn_p_entry = []"
  "entry_call_list gex_g5 gn_p_entry = [(gn7, CallEdge None [] [])]"
  "intra_predecessor_list gex_g5 gn8 = []"
  "return_call_action_list gex_g5 gn8 = [(gn7, CallEdge None [] [], gn_p_exit)]"
  "entry_call_list gex_g5 gn8 = []"
  unfolding gex_g5_def gex_node_defs by eval+

lemma gex_main_entry_preds:
  "intra_predecessor_list gex_g5 gn_main_entry = []"
  "return_call_action_list gex_g5 gn_main_entry = []"
  "entry_call_list gex_g5 gn_main_entry = []"
  unfolding gex_g5_def gex_node_defs by eval+

subsection \<open>Node distinctness\<close>

lemma gex_node_distinct:
  "gn0 \<noteq> gn1" "gn0 \<noteq> gn2" "gn1 \<noteq> gn2" "gn2 \<noteq> gn3" "gn3 \<noteq> gn4" "gn4 \<noteq> gn5" "gn4 \<noteq> gn6" "gn4 \<noteq> gn7" "gn4 \<noteq> gn8"
  "gn5 \<noteq> gn6" "gn6 \<noteq> gn7" "gn6 \<noteq> gn8" "gn7 \<noteq> gn8" "gn2 \<noteq> gn5" "gn3 \<noteq> gn5" "gn1 \<noteq> gn7" "gn1 \<noteq> gn8"
  "gn_p_entry \<noteq> gn0" "gn_p_entry \<noteq> gn1" "gn_main_entry \<noteq> gn2" "gn_p_exit \<noteq> gn1" "gn_p_exit \<noteq> gn4" "gn_p_exit \<noteq> gn6" "gn_p_exit \<noteq> gn7" "gn_p_exit \<noteq> gn8"
  "gn_main_exit \<noteq> gn8" "gn_main_exit \<noteq> gn4" "gn_main_exit \<noteq> gn6" "gn_main_exit \<noteq> gn7" "gn_main_exit \<noteq> gn1" "gn_main_exit \<noteq> gn_p_exit"
  "gn_p_entry \<noteq> gn_main_entry" "gn_p_entry \<noteq> gn_main_exit" "gn_main_entry \<noteq> gn_p_exit"
  unfolding gn0_def gn1_def gn2_def gn3_def gn4_def gn5_def gn6_def gn7_def gn8_def gn_p_entry_def gn_main_entry_def gn_p_exit_def gn_main_exit_def
  by simp_all

lemma gex_gn2_entry_ne: "gn2 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn2_def gn_main_entry_def by simp
lemma gex_gn3_entry_ne: "gn3 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn3_def gn_main_entry_def by simp
lemma gex_gn4_entry_ne: "gn4 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn4_def gn_main_entry_def by simp
lemma gex_gn5_entry_ne: "gn5 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn5_def gn_main_entry_def by simp
lemma gex_gn6_entry_ne: "gn6 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn6_def gn_main_entry_def by simp
lemma gex_gn0_entry_ne: "gn0 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn0_def gn_main_entry_def by simp
lemma gex_gn1_entry_ne: "gn1 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn1_def gn_main_entry_def by simp
lemma gex_gn8_entry_ne: "gn8 \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn8_def gn_main_entry_def by simp
lemma gex_p_entry_entry_ne: "gn_p_entry \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn_p_entry_def gn_main_entry_def by simp
lemma gex_p_exit_entry_ne: "gn_p_exit \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn_p_exit_def gn_main_entry_def by simp
lemma gex_main_exit_entry_ne: "gn_main_exit \<noteq> cfg_entry gex_g5" unfolding gex_entry_eval gn_main_exit_def gn_main_entry_def by simp
lemma gex_gn7_not_entry: "gn7 \<noteq> cfg_entry gex_g5"
  unfolding gex_entry_eval gn7_def gn_main_entry_def by simp

lemma gex_hook_gen_gn7_pred:
  "intra_predecessor_list gex_g5 gn7 = [(gn4, EA_Assign ''j'' (N 0)), (gn6, EA_Assign ''j'' (N 1))]"
  "return_call_action_list gex_g5 gn7 = []"
  "entry_call_list gex_g5 gn7 = []"
  unfolding gex_g5_def gex_node_defs by eval+

subsection \<open>Base classifier facts (\<open>is_global\<close> is the fixed naming convention; none of this
  program's variables start with \<open>G\<close>, so everything here is local)\<close>

lemma is_global_g: "\<not> is_global ''g''" unfolding is_global_def by simp
lemma is_global_j: "\<not> is_global ''j''" unfolding is_global_def by simp
lemma is_global_i: "\<not> is_global ''i''" unfolding is_global_def by simp
lemma is_global_ret_var: "\<not> is_global ret_var" unfolding is_global_def ret_var_def by simp

lemma sign_le_STop: "(s::sign) \<le> STop"
  by (cases s) (auto simp: less_eq_sign_def)

lemma sign_abs_state_le_STop: "(sigma :: sign abs_state) \<le> (\<lambda>_. STop)"
  unfolding le_fun_def by (simp add: sign_le_STop)

lemma restrict_local_for_le_STop: "restrict_local_for is_global (X::sign abs_state) \<le> (\<lambda>_. STop)"
  using sign_abs_state_le_STop unfolding restrict_local_for_def le_fun_def by auto
lemma restrict_global_for_le_STop: "restrict_global_for is_global (X::sign abs_state) \<le> (\<lambda>_. STop)"
  using sign_abs_state_le_STop unfolding restrict_global_for_def le_fun_def by auto

subsection \<open>Ghost writer values\<close>

text \<open>\<open>gw0\<close> is the raw, unrestricted entry seed (used once, at \<open>cfg_entry\<close>'s own equation).
  \<open>gw0r\<close> is what every other program point actually sees: \<open>gw0\<close> restricted to local keys,
  since every non-entry node's value has passed through \<^const>\<open>restrict_local_for\<close> at least
  once. \<open>gw_global\<close> is the shared global unknown's stable writer value: since this program
  declares no variable classified global by \<^const>\<open>is_global\<close>, nothing ever publishes a
  non-bottom global writer fact, so the global slot stays at its restricted entry seed forever.\<close>

definition gw0 :: ghost_lw where "gw0 = sign_ghost_entry_writer"
definition gw0r :: ghost_lw where "gw0r = restrict_local_for is_global gw0"
definition gw_global :: ghost_lw where "gw_global = restrict_global_for is_global gw0"

definition gw4 :: ghost_lw where "gw4 = gw0(''g'' := FVal (Some gn4))"
definition gw6 :: ghost_lw where "gw6 = gw0(''g'' := FVal (Some gn6))"
definition gw4r :: ghost_lw where "gw4r = gw0r(''g'' := FVal (Some gn4))"
definition gw6r :: ghost_lw where "gw6r = gw0r(''g'' := FVal (Some gn6))"
definition gw7r :: ghost_lw where "gw7r = gw0r(''g'' := FTop, ''j'' := FVal (Some gn7))"
definition gwi1r :: ghost_lw where "gwi1r = gw0r(''i'' := FVal (Some gn1))"
definition gwpexit_r :: ghost_lw where "gwpexit_r = gwi1r(ret_var := FVal (Some gn_p_exit))"
definition gwmexit_r :: ghost_lw where "gwmexit_r = gw7r(ret_var := FVal (Some gn_main_exit))"

lemma gw0r_at_keys: "gw0r ''g'' = FVal None" "gw0r ''i'' = FVal None" "gw0r ''j'' = FVal None" "gw0r ret_var = FVal None"
  unfolding gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def ret_var_def
  by simp_all

text \<open>The distinction the entry seed is meant to expose: reached-but-unwritten is
  \<^term>\<open>FVal None\<close>, never the equation-unreached value \<^const>\<open>bot\<close>.\<close>
lemma sign_ghost_entry_writer_not_bot: "sign_ghost_entry_writer x \<noteq> bot"
  by (simp add: bot_flat_top_def)

subsection \<open>Reusable join/restriction algebra\<close>

lemma gw0_eq_join_global: "gw0 \<squnion> gw_global = gw0"
  unfolding gw_global_def gw0_def sign_ghost_entry_writer_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma gw0r_join_global_eq_gw0: "gw0r \<squnion> gw_global = gw0"
  unfolding gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma gw0r_restrict_join_global: "restrict_local_for is_global (gw0r \<squnion> gw_global) = gw0r"
  unfolding gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma gw0r_restrict_global_join_global: "restrict_global_for is_global (gw0r \<squnion> gw_global) = gw_global"
  unfolding gw0r_join_global_eq_gw0 unfolding gw_global_def by (rule refl)

lemma restrict_local_for_gw0r: "restrict_local_for is_global gw0r = gw0r"
  unfolding gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def
  by (auto simp: fun_eq_iff)

lemma restrict_local_for_gw4r: "restrict_local_for is_global gw4r = gw4r"
  unfolding gw4r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def
  by (auto simp: fun_eq_iff)
lemma restrict_local_for_gw6r: "restrict_local_for is_global gw6r = gw6r"
  unfolding gw6r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def
  by (auto simp: fun_eq_iff)
lemma restrict_local_for_gw7r: "restrict_local_for is_global gw7r = gw7r"
  unfolding gw7r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def
  by (auto simp: fun_eq_iff)
lemma restrict_local_for_gwi1r: "restrict_local_for is_global gwi1r = gwi1r"
  unfolding gwi1r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def
  by (auto simp: fun_eq_iff)
lemma restrict_local_for_gwpexit_r: "restrict_local_for is_global gwpexit_r = gwpexit_r"
  unfolding gwpexit_r_def gwi1r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def ret_var_def
  by (auto simp: fun_eq_iff)
lemma restrict_local_for_gwmexit_r: "restrict_local_for is_global gwmexit_r = gwmexit_r"
  unfolding gwmexit_r_def gw7r_def gw0r_def restrict_local_for_def is_global_def gw0_def sign_ghost_entry_writer_def ret_var_def
  by (auto simp: fun_eq_iff)


lemma gw4r_restrict_join_global: "restrict_local_for is_global (gw4r \<squnion> gw_global) = gw4r"
  unfolding gw4r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gw6r_restrict_join_global: "restrict_local_for is_global (gw6r \<squnion> gw_global) = gw6r"
  unfolding gw6r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gwi1r_restrict_join_global: "restrict_local_for is_global (gwi1r \<squnion> gw_global) = gwi1r"
  unfolding gwi1r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gw7r_restrict_join_global: "restrict_local_for is_global (gw7r \<squnion> gw_global) = gw7r"
  unfolding gw7r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma gw4r_restrict_global_join_global: "restrict_global_for is_global (gw4r \<squnion> gw_global) = gw_global"
  unfolding gw4r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gw6r_restrict_global_join_global: "restrict_global_for is_global (gw6r \<squnion> gw_global) = gw_global"
  unfolding gw6r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gwi1r_restrict_global_join_global: "restrict_global_for is_global (gwi1r \<squnion> gw_global) = gw_global"
  unfolding gwi1r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gw7r_restrict_global_join_global: "restrict_global_for is_global (gw7r \<squnion> gw_global) = gw_global"
  unfolding gw7r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)
lemma gwpexit_r_restrict_global_join_global: "restrict_global_for is_global (gwpexit_r \<squnion> gw_global) = gw_global"
  unfolding gwpexit_r_def gwi1r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def restrict_global_for_def is_global_def ret_var_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

lemma restrict_join_upd:
  assumes "restrict_local_for is_global (X \<squnion> gw_global) = X" and "\<not> is_global kk"
  shows "restrict_local_for is_global ((X \<squnion> gw_global)(kk := cv)) = X(kk := cv)"
proof (rule ext)
  fix x
  have h: "(if is_global x then bot else (X \<squnion> gw_global) x) = X x"
    using assms(1) unfolding restrict_local_for_def fun_eq_iff by blast
  show "restrict_local_for is_global ((X \<squnion> gw_global)(kk := cv)) x = (X(kk := cv)) x"
    unfolding restrict_local_for_def using h assms(2) by (cases "x = kk") auto
qed

lemma restrict_global_for_upd_local:
  "\<not> is_global kk \<Longrightarrow> restrict_global_for is_global (X(kk := cv::cfg_node option flat_top)) = restrict_global_for is_global X"
  unfolding restrict_global_for_def fun_eq_iff by simp

lemma gw4r_j_join: "restrict_local_for is_global ((gw4r \<squnion> gw_global)(''j'' := FVal (Some gn7))) = gw4r(''j'' := FVal (Some gn7))"
  by (rule restrict_join_upd[OF gw4r_restrict_join_global is_global_j])
lemma gw6r_j_join: "restrict_local_for is_global ((gw6r \<squnion> gw_global)(''j'' := FVal (Some gn7))) = gw6r(''j'' := FVal (Some gn7))"
  by (rule restrict_join_upd[OF gw6r_restrict_join_global is_global_j])
lemma gw7r_is_join: "gw4r(''j'' := FVal (Some gn7)) \<squnion> gw6r(''j'' := FVal (Some gn7)) = gw7r"
  unfolding gw4r_def gw6r_def gw7r_def gw0r_def gw0_def sign_ghost_entry_writer_def restrict_local_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def gex_node_defs)

lemma ghost_enter_step_gw7r: "ghost_enter_step (gw7r \<squnion> gw_global) = gw0"
  unfolding ghost_enter_step_def gw7r_def gw0r_def gw_global_def gw0_def sign_ghost_entry_writer_def
    restrict_local_for_def restrict_global_for_def is_global_def
  by (auto simp: fun_eq_iff sup_flat_top_def less_eq_flat_top_def bot_flat_top_def)

subsection \<open>The witness \<open>sigma\<close>\<close>

definition s0d :: sign_ghost_dl where "s0d = DG (\<lambda>_. STop) gw0"
definition s0g_val2 :: sign_ghost_dl where "s0g_val2 = DG (\<lambda>_. STop) gw_global"

definition gex_local :: "ghost_lw \<Rightarrow> (sign_ghost_dl, sign_ghost_dl) dg_state" where
  "gex_local w = DG (DG (\<lambda>_. STop) w) bot"
definition gex_global_val2 :: "(sign_ghost_dl, sign_ghost_dl) dg_state" where
  "gex_global_val2 = DG bot s0g_val2"

definition gex_sigma3 :: "(cfg_node \<times> unit + unit) \<Rightarrow> (sign_ghost_dl, sign_ghost_dl) dg_state" where
  "gex_sigma3 z = (case z of
     Inr () \<Rightarrow> gex_global_val2
   | Inl (v, ()) \<Rightarrow>
       (if v = gn_main_entry then gex_local gw0
        else if v = gn4 then gex_local gw4r
        else if v = gn6 then gex_local gw6r
        else if v = gn7 then gex_local gw7r
        else if v = gn8 then gex_local gw7r
        else if v = gn1 then gex_local gwi1r
        else if v = gn_p_exit then gex_local gwpexit_r
        else if v = gn_main_exit then gex_local gwmexit_r
        else gex_local gw0r))"

lemma gex_hookD3_main_entry: "dg_hook_D gex_sigma3 gn_main_entry = DG (\<lambda>_. STop) gw0"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_gn3_mem: "gn3 \<in> {gn2, gn3, gn5, gn_p_entry, gn0}" by simp
lemma gex_gn5_mem: "gn5 \<in> {gn2, gn3, gn5, gn_p_entry, gn0}" by simp
lemma gex_p_entry_mem: "gn_p_entry \<in> {gn2, gn3, gn5, gn_p_entry, gn0}" by simp
lemma gex_gn0_mem: "gn0 \<in> {gn2, gn3, gn5, gn_p_entry, gn0}" by simp
lemma gex_hookD3_default:
  "v \<in> {gn2, gn3, gn5, gn_p_entry, gn0} \<Longrightarrow> dg_hook_D gex_sigma3 v = DG (\<lambda>_. STop) gw0r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by auto
lemma gex_hookD3_gn4: "dg_hook_D gex_sigma3 gn4 = DG (\<lambda>_. STop) gw4r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_gn6: "dg_hook_D gex_sigma3 gn6 = DG (\<lambda>_. STop) gw6r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_gn7: "dg_hook_D gex_sigma3 gn7 = DG (\<lambda>_. STop) gw7r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_gn8: "dg_hook_D gex_sigma3 gn8 = DG (\<lambda>_. STop) gw7r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_gn1: "dg_hook_D gex_sigma3 gn1 = DG (\<lambda>_. STop) gwi1r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_p_exit: "dg_hook_D gex_sigma3 gn_p_exit = DG (\<lambda>_. STop) gwpexit_r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookD3_main_exit: "dg_hook_D gex_sigma3 gn_main_exit = DG (\<lambda>_. STop) gwmexit_r"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def gex_node_defs by simp
lemma gex_hookG3: "dg_hook_G gex_sigma3 = DG (\<lambda>_. STop) gw_global"
  unfolding dg_hook_G_def gex_sigma3_def gex_global_val2_def s0g_val2_def by (simp split: unit.split)
lemma gex_hookG3_raw: "globs (gex_sigma3 (Inr ())) = DG (\<lambda>_. STop) gw_global"
  using gex_hookG3 unfolding dg_hook_G_def by simp
lemma gex_sigma3_Inr: "gex_sigma3 (Inr ()) = DG bot (DG (\<lambda>_. STop) gw_global)"
  unfolding gex_sigma3_def gex_global_val2_def s0g_val2_def by (simp split: unit.split)
lemma gex_sigma3_Inl_shape: "gex_sigma3 (Inl (v, ())) = DG (dg_hook_D gex_sigma3 v) bot"
  unfolding dg_hook_D_def gex_sigma3_def gex_local_def by simp
lemma gex_hookD3_main_entry_raw: "locals (gex_sigma3 (Inl (gn_main_entry, ()))) = DG (\<lambda>_. STop) gw0"
  using gex_hookD3_main_entry unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn2_raw: "locals (gex_sigma3 (Inl (gn2, ()))) = DG (\<lambda>_. STop) gw0r"
  using gex_hookD3_default[of gn2] unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn3_raw: "locals (gex_sigma3 (Inl (gn3, ()))) = DG (\<lambda>_. STop) gw0r"
  using gex_hookD3_default[OF gex_gn3_mem] unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn5_raw: "locals (gex_sigma3 (Inl (gn5, ()))) = DG (\<lambda>_. STop) gw0r"
  using gex_hookD3_default[OF gex_gn5_mem] unfolding dg_hook_D_def by simp
lemma gex_sigma3_p_entry_raw: "locals (gex_sigma3 (Inl (gn_p_entry, ()))) = DG (\<lambda>_. STop) gw0r"
  using gex_hookD3_default[OF gex_p_entry_mem] unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn0_raw: "locals (gex_sigma3 (Inl (gn0, ()))) = DG (\<lambda>_. STop) gw0r"
  using gex_hookD3_default[OF gex_gn0_mem] unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn1_raw: "locals (gex_sigma3 (Inl (gn1, ()))) = DG (\<lambda>_. STop) gwi1r"
  using gex_hookD3_gn1 unfolding dg_hook_D_def by simp
lemma gex_sigma3_gn8_raw: "locals (gex_sigma3 (Inl (gn8, ()))) = DG (\<lambda>_. STop) gw7r"
  using gex_hookD3_gn8 unfolding dg_hook_D_def by simp

lemma sg_value_bot: "sg_value (bot :: sign_ghost_dl) = bot" by (simp add: bot_dg_state_def)
lemma sg_writer_bot: "sg_writer (bot :: sign_ghost_dl) = bot" by (simp add: bot_dg_state_def)

subsection \<open>Generic reduction: only the global publication needs checking\<close>

lemma gex_se_sides_generic:
  fixes a v :: cfg_node and sigma :: "(cfg_node \<times> unit + unit) \<Rightarrow> (sign_ghost_dl, sign_ghost_dl) dg_state"
  assumes "sides_of_rhs (sign_ghost_edge_tree a act v) sigma (Inr ()) \<le> sigma (Inr ())"
  shows "sides_of_rhs (sign_ghost_edge_tree a act v) sigma \<le> sigma"
proof (rule le_funI)
  fix k show "sides_of_rhs (sign_ghost_edge_tree a act v) sigma k \<le> sigma k"
    using assms by (cases k) (simp_all add: sides_sign_ghost_edge_tree_Inl)
qed

lemma gex_sides_fun_single_edge:
  assumes not_entry: "v \<noteq> cfg_entry gex_g5"
    and pred: "intra_predecessor_list gex_g5 v = [(u, a)]"
    and no_combine: "return_call_action_list gex_g5 v = []"
    and no_enter: "entry_call_list gex_g5 v = []"
  shows "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (v, ())) sigma
           = sides_of_rhs (sign_ghost_edge_tree u a v) sigma"
  unfolding sign_ghost_dg.hook_gen_def
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def not_entry pred no_combine no_enter
      Let_def sides_of_rhs_seqcomp fun_eq_iff)

lemma sides_sign_ghost_enter_tree_Inl: "sides_of_rhs (sign_ghost_enter_tree cc ca p) sigma (Inl w) = bot"
  unfolding sign_ghost_enter_tree_def
  by (cases ca) (simp add: dg_edge_tree_def map_gtree.simps map_ltree.simps sides_of_rhs.simps Let_def)

lemma sides_sign_ghost_combine_tree_Inl: "sides_of_rhs (sign_ghost_combine_tree caller ca ex k) sigma (Inl w) = bot"
  unfolding sign_ghost_combine_tree_def
  by (cases ca) (simp add: dg_combine_tree_def map_gtree.simps map_ltree.simps sides_of_rhs.simps Let_def)

lemma sides_sign_ghost_enter_tree_Inr_locals: "locals (sides_of_rhs (sign_ghost_enter_tree cc ca p) sigma (Inr ())) = bot"
  unfolding sign_ghost_enter_tree_def
  by (cases ca) (simp add: dg_edge_tree_def map_gtree.simps map_ltree.simps sides_of_rhs.simps Let_def)

lemma sides_sign_ghost_combine_tree_Inr_locals: "locals (sides_of_rhs (sign_ghost_combine_tree caller ca ex k) sigma (Inr ())) = bot"
  unfolding sign_ghost_combine_tree_def
  by (cases ca) (simp add: dg_combine_tree_def map_gtree.simps map_ltree.simps sides_of_rhs.simps Let_def)

lemma gex_se_sides_generic_enter:
  fixes cc p :: cfg_node and ca :: call_action
  assumes "sides_of_rhs (sign_ghost_enter_tree cc ca p) sigma (Inr ()) \<le> sigma (Inr ())"
  shows "sides_of_rhs (sign_ghost_enter_tree cc ca p) sigma \<le> sigma"
proof (rule le_funI)
  fix k show "sides_of_rhs (sign_ghost_enter_tree cc ca p) sigma k \<le> sigma k"
    using assms by (cases k) (simp_all add: sides_sign_ghost_enter_tree_Inl)
qed

lemma gex_se_sides_generic_combine:
  fixes caller ex k :: cfg_node and ca :: call_action
  assumes "sides_of_rhs (sign_ghost_combine_tree caller ca ex k) sigma (Inr ()) \<le> sigma (Inr ())"
  shows "sides_of_rhs (sign_ghost_combine_tree caller ca ex k) sigma \<le> sigma"
proof (rule le_funI)
  fix j show "sides_of_rhs (sign_ghost_combine_tree caller ca ex k) sigma j \<le> sigma j"
    using assms by (cases j) (simp_all add: sides_sign_ghost_combine_tree_Inl)
qed

lemma gex_sides_fun_single_enter:
  assumes not_entry: "v \<noteq> cfg_entry gex_g5"
    and no_edge: "intra_predecessor_list gex_g5 v = []"
    and no_combine: "return_call_action_list gex_g5 v = []"
    and pred: "entry_call_list gex_g5 v = [(caller, action)]"
  shows "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (v, ())) sigma
           = sides_of_rhs (sign_ghost_enter_tree caller action v) sigma"
  unfolding sign_ghost_dg.hook_gen_def
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def not_entry no_edge no_combine pred
      Let_def sides_of_rhs_seqcomp fun_eq_iff)

lemma gex_sides_fun_single_combine:
  assumes not_entry: "v \<noteq> cfg_entry gex_g5"
    and no_edge: "intra_predecessor_list gex_g5 v = []"
    and pred: "return_call_action_list gex_g5 v = [(caller, action, callee_exit)]"
    and no_enter: "entry_call_list gex_g5 v = []"
  shows "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (v, ())) sigma
           = sides_of_rhs (sign_ghost_combine_tree caller action callee_exit v) sigma"
  unfolding sign_ghost_dg.hook_gen_def
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def not_entry no_edge pred no_enter
      Let_def sides_of_rhs_seqcomp fun_eq_iff)

subsection \<open>Dependency sets (all 13 covered unknowns)\<close>

lemma gex_dep_main_entry: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn_main_entry, ()) = {}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def gex_entry_eval
  by (simp add: gex_main_entry_preds Let_def dep_aux.simps)
lemma gex_dep_gn2: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn2, ()) = {(gn_main_entry, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn2_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn3: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn3, ()) = {(gn2, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn3_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn4: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn4, ()) = {(gn3, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn4_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn5: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn5, ()) = {(gn2, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn5_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn6: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn6, ()) = {(gn5, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn6_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn7: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn7, ()) = {(gn4, ()), (gn6, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (auto simp: gex_hook_gen_gn7_pred gex_gn7_not_entry Let_def dep_aux.simps dep_aux_seqcomp sign_ghost_edge_tree_def)
lemma gex_dep_gn0: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn0, ()) = {(gn_p_entry, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn0_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_gn1: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn1, ()) = {(gn0, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_gn1_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_p_exit: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn_p_exit, ()) = {(gn1, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_p_exit_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_main_exit: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn_main_exit, ()) = {(gn8, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_edge_preds gex_main_exit_entry_ne Let_def dep_aux.simps sign_ghost_edge_tree_def)
lemma gex_dep_p_entry: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn_p_entry, ()) = {(gn7, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (simp add: gex_call_preds gex_p_entry_entry_ne Let_def dep_aux.simps sign_ghost_enter_tree_def
      map_gtree.simps map_ltree.simps dg_edge_tree_def)
lemma gex_dep_gn8: "dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 (gn8, ()) = {(gn7, ()), (gn_p_exit, ())}"
  unfolding dep\<^sub>L_def dep_def sign_ghost_dg.hook_gen_def side_cfg_T_eff_keyed_seed_trees_def
  by (auto simp: gex_call_preds gex_gn8_entry_ne Let_def dep_aux.simps sign_ghost_combine_tree_def
      map_gtree.simps map_ltree.simps dg_combine_tree_def)

subsection \<open>Per-node \<open>se_constraint_holds\<close>\<close>

lemma gex_se_gn2: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn2, ())) gex_sigma3 (gn2, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn2_entry_ne gex_edge_preds(1) gex_edge_preds(10,11) refl]
    unfolding traverse_sign_ghost_edge_tree gex_hookD3_main_entry gex_sigma3_Inl_shape gex_hookD3_default[OF insertI1] gex_hookG3_raw
    by (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps gw0_eq_join_global gw0r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn2_entry_ne gex_edge_preds(1) gex_edge_preds(10,11)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_hookD3_main_entry_raw gex_sigma3_Inr
    by (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps gw_global_def[symmetric] gw0_eq_join_global)
  done

lemma gex_se_gn3: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn3, ())) gex_sigma3 (gn3, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn3_entry_ne gex_edge_preds(2) gex_edge_preds(12,13) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_default[OF gex_gn3_mem] gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn2_raw[unfolded dg_hook_D_def]
    by (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps gw0r_restrict_join_global)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn3_entry_ne gex_edge_preds(2) gex_edge_preds(12,13)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_gn2_raw gex_sigma3_Inr
    unfolding dg_hook_D_def
    by (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps gw0r_restrict_global_join_global)
  done

lemma gex_se_gn5: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn5, ())) gex_sigma3 (gn5, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn5_entry_ne gex_edge_preds(4) gex_edge_preds(16,17) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_default[OF gex_gn5_mem] gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn2_raw[unfolded dg_hook_D_def]
    by (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps gw0r_restrict_join_global)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn5_entry_ne gex_edge_preds(4) gex_edge_preds(16,17)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_gn2_raw gex_sigma3_Inr
    unfolding dg_hook_D_def
    by (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps gw0r_restrict_global_join_global)
  done

lemma gex_se_gn4: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn4, ())) gex_sigma3 (gn4, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn4_entry_ne gex_edge_preds(3) gex_edge_preds(14,15) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_gn4 gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn3_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps)
    by (simp add: restrict_join_upd[OF gw0r_restrict_join_global is_global_g] gw4r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn4_entry_ne gex_edge_preds(3) gex_edge_preds(14,15)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_gn3_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps)
    by (simp add: restrict_global_for_upd_local[OF is_global_g] gw0r_restrict_global_join_global)
  done

lemma gex_se_gn6: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn6, ())) gex_sigma3 (gn6, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn6_entry_ne gex_edge_preds(5) gex_edge_preds(18,19) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_gn6 gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn5_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps)
    by (simp add: restrict_join_upd[OF gw0r_restrict_join_global is_global_g] gw6r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn6_entry_ne gex_edge_preds(5) gex_edge_preds(18,19)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_gn5_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps)
    by (simp add: restrict_global_for_upd_local[OF is_global_g] gw0r_restrict_global_join_global)
  done

lemma gex_se_gn0: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn0, ())) gex_sigma3 (gn0, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn0_entry_ne gex_edge_preds(6) gex_edge_preds(20,21) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_default[OF gex_gn0_mem] gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_p_entry_raw[unfolded dg_hook_D_def]
    by (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps gw0r_restrict_join_global)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn0_entry_ne gex_edge_preds(6) gex_edge_preds(20,21)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_p_entry_raw[unfolded dg_hook_D_def]
    by (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps gw0r_restrict_global_join_global)
  done

lemma gex_se_gn1: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn1, ())) gex_sigma3 (gn1, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_gn1_entry_ne gex_edge_preds(7) gex_edge_preds(22,23) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_gn1 gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn0_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps)
    by (simp add: restrict_join_upd[OF gw0r_restrict_join_global is_global_i] gwi1r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_gn1_entry_ne gex_edge_preds(7) gex_edge_preds(22,23)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_gn0_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps)
    by (simp add: restrict_global_for_upd_local[OF is_global_i] gw0r_restrict_global_join_global)
  done

lemma gex_se_p_exit: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn_p_exit, ())) gex_sigma3 (gn_p_exit, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_p_exit_entry_ne gex_edge_preds(8) gex_edge_preds(24,25) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_p_exit gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn1_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps)
    by (simp add: restrict_join_upd[OF gwi1r_restrict_join_global is_global_ret_var] gwpexit_r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_p_exit_entry_ne gex_edge_preds(8) gex_edge_preds(24,25)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_gn1_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps)
    by (simp add: restrict_global_for_upd_local[OF is_global_ret_var] gwi1r_restrict_global_join_global)
  done

lemma gex_se_main_exit: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn_main_exit, ())) gex_sigma3 (gn_main_exit, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_edge(1)[OF gex_main_exit_entry_ne gex_edge_preds(9) gex_edge_preds(26,27) refl]
    unfolding traverse_sign_ghost_edge_tree gex_sigma3_Inl_shape gex_hookD3_main_exit gex_hookG3_raw
    unfolding dg_hook_D_def gex_sigma3_gn8_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_local restrict_local_for_le_STop
        sg_writer_edge_local ghost_step_def edge_write_var.simps)
    by (simp add: restrict_join_upd[OF gw7r_restrict_join_global is_global_ret_var] gwmexit_r_def)
  subgoal
    unfolding gex_sides_fun_single_edge[OF gex_main_exit_entry_ne gex_edge_preds(9) gex_edge_preds(26,27)]
    apply (rule gex_se_sides_generic)
    unfolding sides_sign_ghost_edge_tree_Inr gex_sigma3_Inr
    unfolding dg_hook_D_def gex_sigma3_gn8_raw[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_edge_global restrict_global_for_le_STop
        sg_writer_edge_global ghost_step_def edge_write_var.simps)
    by (simp add: restrict_global_for_upd_local[OF is_global_ret_var] gw7r_restrict_global_join_global)
  done

text \<open>The join at \<open>gn7\<close>: two intra predecessors, so \<open>hook_gen_single_edge\<close> does not apply.
  The closed forms are derived directly from \<open>side_cfg_T_eff_keyed_seed_trees_def\<close> and
  \<open>side_acc_dg\<close>'s two-element fold, isolated once as \<open>gex_gn7_eq\<close>/\<open>gex_gn7_sides_fun\<close> so the
  final proof does not re-unfold the generator.\<close>

lemma gex_gn7_eq:
  "eq (sign_ghost_dg.hook_gen gex_g5 bot (DG (\<lambda>_. STop) gw0) s0g) (gn7, ()) sigma =
     DG (sign_ghost_edge_local (EA_Assign ''j'' (N 0)) gn7 (dg_hook_D sigma gn4) (dg_hook_G sigma)
         \<squnion> sign_ghost_edge_local (EA_Assign ''j'' (N 1)) gn7 (dg_hook_D sigma gn6) (dg_hook_G sigma)) bot"
  unfolding sign_ghost_dg.eq_hook_gen sign_ghost_dg.hook_acc_def sign_ghost_dg.hook_trees_def
    gex_hook_gen_gn7_pred
  by (simp add: gex_gn7_not_entry traverse_sign_ghost_edge_tree dg_hook_D_def dg_hook_G_def)

lemma gex_gn7_sides_fun: "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn7, ())) gex_sigma3 =
  sides_of_rhs (sign_ghost_edge_tree gn4 (EA_Assign ''j'' (N 0)) gn7) gex_sigma3
    \<squnion> sides_of_rhs (sign_ghost_edge_tree gn6 (EA_Assign ''j'' (N 1)) gn7) gex_sigma3"
  unfolding sign_ghost_dg.hook_gen_def
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def gex_hook_gen_gn7_pred gex_gn7_not_entry
      Let_def sides_of_rhs_seqcomp fun_eq_iff)

lemma gex_se_gn7_local: "eq (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) (gn7, ()) gex_sigma3 \<le> gex_sigma3 (Inl (gn7, ()))"
  unfolding s0d_def gex_gn7_eq gex_sigma3_Inl_shape gex_hookD3_gn7 gex_hookD3_gn4 gex_hookD3_gn6 gex_hookG3
  apply (simp add: less_eq_dg_state_def sg_value_sup sg_writer_sup sg_value_edge_local restrict_local_for_le_STop sup.bounded_iff)
  apply (simp add: sg_writer_edge_local ghost_step_def edge_write_var.simps)
  by (metis gw4r_j_join gw6r_j_join gw7r_is_join sup_ge1 sup_ge2)

lemma gex_se_gn7_sides_Inr: "globs (sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn7, ())) gex_sigma3 (Inr ())) \<le> globs (gex_sigma3 (Inr ()))"
  unfolding gex_gn7_sides_fun
  apply (simp only: sup_fun_def)
  unfolding sides_sign_ghost_edge_tree_Inr dg_hook_D_def[symmetric] gex_hookD3_gn4 gex_hookD3_gn6 gex_hookG3_raw gex_sigma3_Inr
  apply (simp add: sup_dg_state_def)
  by (simp add: less_eq_dg_state_def sg_writer_sup sg_writer_edge_global ghost_step_def edge_write_var.simps
      restrict_global_for_upd_local[OF is_global_j] gw4r_restrict_global_join_global gw6r_restrict_global_join_global
      sg_value_sup sg_value_edge_global restrict_global_for_le_STop sup.bounded_iff)

lemma gex_se_gn7_sides_Inr_locals: "locals (sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn7, ())) gex_sigma3 (Inr ())) = bot"
  unfolding gex_gn7_sides_fun
  by (simp add: sup_fun_def sides_sign_ghost_edge_tree_Inr sup_dg_state_def)

lemma gex_se_gn7_sides_Inr_full: "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn7, ())) gex_sigma3 (Inr ()) \<le> gex_sigma3 (Inr ())"
  unfolding less_eq_dg_state_def
  apply (rule conjI)
  subgoal by (simp add: gex_se_gn7_sides_Inr_locals sg_value_bot sg_writer_bot)
  subgoal using gex_se_gn7_sides_Inr[unfolded less_eq_dg_state_def] by blast
  done

lemma gex_se_gn7: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn7, ())) gex_sigma3 (gn7, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal by (rule gex_se_gn7_local)
  subgoal
    apply (rule le_funI)
    subgoal for k
      apply (cases k)
      subgoal by (simp add: gex_gn7_sides_fun sides_sign_ghost_edge_tree_Inl)
      subgoal by (simp add: gex_se_gn7_sides_Inr_full)
      done
    done
  done

subsection \<open>The ENTER case at \<open>gn_p_entry\<close>\<close>

lemma gex_se_p_entry: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn_p_entry, ())) gex_sigma3 (gn_p_entry, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_enter(1)[OF gex_p_entry_entry_ne gex_call_preds(1) gex_call_preds(2) gex_call_preds(3) refl]
    unfolding traverse_sign_ghost_enter_tree gex_sigma3_Inl_shape gex_hookD3_default[OF gex_p_entry_mem] gex_hookG3_raw
    unfolding dg_hook_D_def gex_hookD3_gn7[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_enter_snd restrict_local_for_le_STop sg_writer_enter_snd)
    by (simp add: ghost_enter_step_gw7r gw0r_def)
  subgoal
    unfolding gex_sides_fun_single_enter[OF gex_p_entry_entry_ne gex_call_preds(1) gex_call_preds(2) gex_call_preds(3)]
    apply (rule gex_se_sides_generic_enter)
    unfolding gex_sigma3_Inr less_eq_dg_state_def
    unfolding sides_sign_ghost_enter_tree_Inr sides_sign_ghost_enter_tree_Inr_locals
    unfolding gex_hookD3_gn7[unfolded dg_hook_D_def] gex_hookG3_raw
    apply (simp add: sg_value_enter_fst restrict_global_for_le_STop
        sg_writer_enter_fst ghost_enter_step_gw7r gw0_eq_join_global)
    by (simp add: gw_global_def)
  done

subsection \<open>The COMBINE case at \<open>gn8\<close>\<close>

lemma gex_se_gn8: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn8, ())) gex_sigma3 (gn8, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding sign_ghost_dg.hook_gen_single_combine(1)[OF gex_gn8_entry_ne gex_call_preds(4) gex_call_preds(5) gex_call_preds(6) refl]
    unfolding traverse_sign_ghost_combine_tree gex_sigma3_Inl_shape gex_hookD3_gn8 gex_hookG3_raw
    unfolding dg_hook_D_def gex_hookD3_gn7[unfolded dg_hook_D_def] gex_hookD3_p_exit[unfolded dg_hook_D_def]
    apply (simp add: less_eq_dg_state_def sg_value_combine_snd restrict_local_for_le_STop sg_writer_combine_snd)
    apply (simp add: combine_collect_abs_None combine_abs_for_eq_restrict)
    by (simp add: gw7r_restrict_join_global)
  subgoal
    unfolding gex_sides_fun_single_combine[OF gex_gn8_entry_ne gex_call_preds(4) gex_call_preds(5) gex_call_preds(6)]
    apply (rule gex_se_sides_generic_combine)
    unfolding gex_sigma3_Inr less_eq_dg_state_def
    unfolding sides_sign_ghost_combine_tree_Inr sides_sign_ghost_combine_tree_Inr_locals
    unfolding gex_hookD3_gn7[unfolded dg_hook_D_def] gex_hookD3_p_exit[unfolded dg_hook_D_def] gex_hookG3_raw
    apply (simp add: sg_value_combine_fst restrict_global_for_le_STop sg_writer_combine_fst)
    apply (simp add: combine_collect_abs_None combine_abs_for_eq_restrict)
    by (simp add: gwpexit_r_restrict_global_join_global)
  done

subsection \<open>The entry case at \<open>gn_main_entry\<close>\<close>

lemma gex_sides_fun_entry:
  "sides_of_rhs (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (cfg_entry gex_g5, ())) sigma
     = (\<lambda>j. if j = Inr () then DG bot s0g_val2 else bot)"
  unfolding sign_ghost_dg.hook_gen_def gex_entry_eval
  by (simp add: side_cfg_T_eff_keyed_seed_trees_def gex_main_entry_preds gex_entry_eval Let_def
      sides_of_rhs_seqcomp fun_eq_iff)

lemma gex_se_main_entry: "se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 (gn_main_entry, ())) gex_sigma3 (gn_main_entry, ())"
  unfolding se_constraint_holds_def
  apply (intro conjI)
  subgoal
    unfolding gex_entry_eval[symmetric]
    unfolding sign_ghost_dg.hook_gen_entry(1)[OF
        gex_main_entry_preds(1)[unfolded gex_entry_eval[symmetric]]
        gex_main_entry_preds(2)[unfolded gex_entry_eval[symmetric]]
        gex_main_entry_preds(3)[unfolded gex_entry_eval[symmetric]] refl]
    unfolding gex_entry_eval gex_sigma3_Inl_shape gex_hookD3_main_entry
    by (simp add: s0d_def)
  subgoal
    unfolding gex_entry_eval[symmetric]
    unfolding gex_sides_fun_entry
    unfolding gex_entry_eval
    by (simp add: le_fun_def s0g_val2_def less_eq_dg_state_def gex_sigma3_Inr
        bot_dg_state_def sg_value_bot sg_writer_bot)
  done

subsection \<open>Assembling the post-solution: all 13 covered unknowns\<close>

definition gex_vars :: "(cfg_node \<times> unit) set" where
  "gex_vars = {(gn_main_entry, ()), (gn0, ()), (gn1, ()), (gn2, ()), (gn3, ()), (gn4, ()),
    (gn5, ()), (gn6, ()), (gn7, ()), (gn8, ()), (gn_p_entry, ()), (gn_p_exit, ()), (gn_main_exit, ())}"

lemma gex_ball:
  "\<forall>u \<in> gex_vars. dep\<^sub>L (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) gex_sigma3 u \<subseteq> gex_vars \<and>
     se_constraint_holds (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2 u) gex_sigma3 u"
  unfolding gex_vars_def
  by (auto simp: gex_dep_main_entry gex_dep_gn0 gex_dep_gn1 gex_dep_gn2 gex_dep_gn3 gex_dep_gn4
      gex_dep_gn5 gex_dep_gn6 gex_dep_gn7 gex_dep_gn8 gex_dep_p_entry gex_dep_p_exit gex_dep_main_exit
      gex_se_main_entry gex_se_gn0 gex_se_gn1 gex_se_gn2 gex_se_gn3 gex_se_gn4 gex_se_gn5 gex_se_gn6
      gex_se_gn7 gex_se_gn8 gex_se_p_entry gex_se_p_exit gex_se_main_exit)

lemma gex_part_post_solution:
  "part_post_solution (sign_ghost_dg.hook_gen gex_g5 bot s0d s0g_val2) (gn_main_exit, ()) gex_sigma3 gex_vars"
  by (rule sign_ghost_dg.part_post_solution_of_ball[OF _ gex_ball]) (simp add: gex_vars_def)

subsection \<open>Base-store collecting soundness at every covered program point\<close>

lemma gex_ltr_collect_sound:
  assumes sound0: "S0 \<subseteq> sign_ghost_gamma s0d s0g_val2"
  shows "ltr_collect is_global gex_g5 S0 v \<subseteq> dg_hook_gamma sign_ghost_gamma gex_sigma3 v"
  apply (rule sign_ghost_dg_ltr.hook_post_solution_collect_sound_ltr[OF gex_part_post_solution])
  subgoal unfolding gex_entry_eval gex_vars_def by simp
  subgoal unfolding gex_intra_eval gex_vars_def by auto
  subgoal unfolding gex_calls_eval gn_p_entry_def gex_vars_def by auto
  subgoal unfolding gex_calls_eval gex_vars_def by auto
  subgoal by (rule gex_finI)
  subgoal by (rule gex_finC)
  subgoal by (rule sound0)
  done

subsection \<open>The witnessed story: five acceptance facts\<close>

text \<open>What \<^const>\<open>gex_sigma3\<close> actually says about \<open>g\<close>'s last writer at the five
  program points that matter, read off \<open>dg_hook_D\<close> directly. These are restatements
  of the \<open>gw*\<close> definitions above, not new content --- the payoff is that they read as
  a five-line story rather than being buried inside the witness's internal algebra.\<close>

lemma gex_ghost_g_before_branch: "sg_writer (dg_hook_D gex_sigma3 gn2) ''g'' = FVal None"
  unfolding dg_hook_D_def gex_sigma3_gn2_raw[unfolded dg_hook_D_def] by (simp add: gw0r_at_keys)

lemma gex_ghost_g_true_branch: "sg_writer (dg_hook_D gex_sigma3 gn4) ''g'' = FVal (Some gn4)"
  unfolding gex_hookD3_gn4 by (simp add: gw4r_def)

lemma gex_ghost_g_false_branch: "sg_writer (dg_hook_D gex_sigma3 gn6) ''g'' = FVal (Some gn6)"
  unfolding gex_hookD3_gn6 by (simp add: gw6r_def)

lemma gex_ghost_g_join: "sg_writer (dg_hook_D gex_sigma3 gn7) ''g'' = FTop"
  unfolding gex_hookD3_gn7 by (simp add: gw7r_def)

lemma gex_ghost_g_after_call_return: "sg_writer (dg_hook_D gex_sigma3 gn8) ''g'' = FTop"
  unfolding gex_hookD3_gn8 by (simp add: gw7r_def)

end
