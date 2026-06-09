section \<open>Example: TD\_IP Sign Analysis on a Single Global Increment Call\<close>

theory Example_Proc_Global
  imports TD_IP_Soundness CFG_Collect_IP_Adeq
begin

text \<open>
  M1 slice 4 witness: @{const inc_pi} with a single call to procedure p.
  Operational semantics via @{const pruns_to_ip}; soundness via @{const td_analyse_ip}.
\<close>

definition proc_global_s0 :: "sign abs_state" where
  "proc_global_s0 = (\<lambda>_. STop)"

lemma proc_global_s0_gamma:
  "s \<in> sign_domain.gamma_state proc_global_s0"
  unfolding proc_global_s0_def sign_domain.gamma_state_def
  by (simp add: gamma_sign.simps)

lemma compile_prog_inc_finite:
  "finite (edges (compile_prog inc_pi [''p''] (PCall ''p'')))"
  using compile_prog_inc_edges by (simp add: finite_insert)

lemma compile_prog_inc_finite_combines:
  "finite (combines (compile_prog inc_pi [''p''] (PCall ''p'')))"
  using compile_prog_inc_combines by (simp add: finite_insert)

lemma inc_g_finite_edges:
  "finite (edges inc_g)"
  by (simp add: compile_prog_inc_structure finite_insert)

lemma inc_g_finite_combines:
  "finite (combines inc_g)"
  by (simp add: compile_prog_inc_structure finite_insert)

lemma make_rhs_tree_ip_inc_g_cong:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and v :: pp
  shows "make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) tf join_abs bot_abs s0 v
       = make_rhs_tree_ip inc_g tf join_abs bot_abs s0 v"
proof (rule make_rhs_tree_ip_cong)
  show "cfg_entry (compile_prog inc_pi [''p''] (PCall ''p'')) = cfg_entry inc_g"
    using compile_prog_inc_entry compile_prog_inc_structure by simp
  show "edges (compile_prog inc_pi [''p''] (PCall ''p'')) = edges inc_g"
    using compile_prog_inc_edges compile_prog_inc_structure by simp
  show "combines (compile_prog inc_pi [''p''] (PCall ''p'')) = combines inc_g"
    using compile_prog_inc_combines compile_prog_inc_structure by simp
  show "finite (edges (compile_prog inc_pi [''p''] (PCall ''p'')))"
    by (rule compile_prog_inc_finite)
  show "finite (combines (compile_prog inc_pi [''p''] (PCall ''p'')))"
    by (rule compile_prog_inc_finite_combines)
qed

lemma make_rhs_tree_ip_inc_g_fn_cong:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
  shows "make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) tf join_abs bot_abs s0
       = make_rhs_tree_ip inc_g tf join_abs bot_abs s0"
  by (rule ext, rule make_rhs_tree_ip_inc_g_cong)

lemma inc_g_predecessor_list_3:
  "predecessor_list inc_g 3 = []"
  by (simp add: predecessor_list_def cfg_edges_list_def compile_prog_inc_structure
       inc_g_finite_edges)

lemma inc_g_combine_predecessor_list_3:
  "combine_predecessor_list inc_g 3 = [(2, Suc 0)]"
  by (simp add: combine_predecessor_list_def cfg_combines_list_def
       compile_prog_inc_structure inc_g_finite_combines)

lemma inc_g_predecessor_list_1:
  "predecessor_list inc_g 1 = [(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)))]"
  by (simp add: predecessor_list_def cfg_edges_list_def compile_prog_inc_structure
       inc_g_finite_edges)

lemma inc_g_predecessor_list_Suc0:
  "predecessor_list inc_g (Suc 0) = [(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)))]"
  using inc_g_predecessor_list_1 by simp

lemma inc_g_combine_predecessor_list_1:
  "combine_predecessor_list inc_g 1 = []"
  by (simp add: combine_predecessor_list_def cfg_combines_list_def
       compile_prog_inc_structure inc_g_finite_combines)

lemma inc_g_combine_predecessor_list_Suc0:
  "combine_predecessor_list inc_g (Suc 0) = []"
  using inc_g_combine_predecessor_list_1 by simp

lemma inc_g_make_rhs_tree_3:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
  shows "make_rhs_tree_ip inc_g tf join_abs bot_abs s0 3 =
    ip_rhs_tree tf join_abs combine_abs bot_abs [] [(2, Suc 0)]"
  unfolding make_rhs_tree_ip_def Let_def
  by (simp add: inc_g_predecessor_list_3 inc_g_combine_predecessor_list_3
       compile_prog_inc_structure(1))

lemma inc_g_dep_2_at_3:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and \<sigma>
  shows "2 \<in> dep (make_rhs_tree_ip inc_g tf join_abs bot_abs s0) \<sigma> 3"
  unfolding dep_def inc_g_make_rhs_tree_3 by (simp add: dep_aux.simps)

lemma inc_g_dep_1_at_3:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and \<sigma>
  shows "1 \<in> dep (make_rhs_tree_ip inc_g tf join_abs bot_abs s0) \<sigma> 3"
  unfolding dep_def inc_g_make_rhs_tree_3 by (simp add: dep_aux.simps)

lemma inc_g_make_rhs_tree_1:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state"
  shows "make_rhs_tree_ip inc_g tf join_abs bot_abs s0 1 =
    ip_rhs_tree tf join_abs combine_abs bot_abs
      [(0, EA_Assign ''Gx'' (Plus (V ''Gx'') (N 1)))] []"
  unfolding make_rhs_tree_ip_def Let_def
  by (simp add: inc_g_predecessor_list_Suc0 inc_g_combine_predecessor_list_Suc0
       compile_prog_inc_structure(1) ip_rhs_tree.simps apply_tf.simps)

lemma inc_g_dep_0_at_1:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and \<sigma>
  shows "0 \<in> dep (make_rhs_tree_ip inc_g tf join_abs bot_abs s0) \<sigma> 1"
  unfolding dep_def inc_g_make_rhs_tree_1 by (simp add: dep_aux.simps)

lemma inc_g_reach_at_exit:
  fixes tf :: "'a::bounded_semilattice_sup_bot domain_transfer"
    and join_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state"
    and bot_abs s0 :: "'a abs_state" and \<sigma>
  defines "T \<equiv> make_rhs_tree_ip inc_g tf join_abs bot_abs s0"
  assumes "w \<in> {0, 1, 2, 3}"
  shows "w \<in> reach T \<sigma> 3"
proof -
  have r3: "3 \<in> reach T \<sigma> 3" by (simp add: reach.base)
  have dep2: "2 \<in> dep T \<sigma> 3" unfolding T_def by (fact inc_g_dep_2_at_3)
  have r2: "2 \<in> reach T \<sigma> 3" by (rule reach.step[OF r3 dep2])
  have dep1: "1 \<in> dep T \<sigma> 3" unfolding T_def by (fact inc_g_dep_1_at_3)
  have r1: "1 \<in> reach T \<sigma> 3" by (rule reach.step[OF r3 dep1])
  have dep0: "0 \<in> dep T \<sigma> 1" unfolding T_def by (fact inc_g_dep_0_at_1)
  have r0: "0 \<in> reach T \<sigma> 3" by (rule reach.step[OF r1 dep0])
  show ?thesis using assms r0 r1 r2 r3 by auto
qed

lemma proc_global_combine_reach:
  fixes \<sigma> :: "(pp, sign abs_state) map"
  assumes uce: "(c, ex, w) \<in> combines (compile_prog inc_pi [''p''] (PCall ''p''))"
  shows "w \<in> reach (make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) sign_tf (\<squnion>) bot proc_global_s0) \<sigma>
     (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
proof -
  have w_eq: "w = cfg_exit (compile_prog inc_pi [''p''] (PCall ''p''))"
    using uce compile_prog_inc_combines compile_prog_inc_exit by auto
  have w_set: "w \<in> {0, 1, 2, 3}" by (simp add: w_eq compile_prog_inc_exit)
  show ?thesis
    using inc_g_reach_at_exit[OF w_set, of sign_tf "(\<squnion>)" bot proc_global_s0 \<sigma>]
    unfolding make_rhs_tree_ip_inc_g_fn_cong compile_prog_inc_exit by simp
qed

lemma proc_global_edge_reach:
  fixes \<sigma> :: "(pp, sign abs_state) map"
  assumes ed: "(u, a, w) \<in> edges (compile_prog inc_pi [''p''] (PCall ''p''))"
  shows "w \<in> reach (make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) sign_tf (\<squnion>) bot proc_global_s0) \<sigma>
     (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
proof -
  have w_set: "w \<in> {0, 1, 2, 3}"
    using ed compile_prog_inc_edges compile_prog_inc_exit compile_prog_inc_structure
    by auto
  show ?thesis
    using inc_g_reach_at_exit[OF w_set, of sign_tf "(\<squnion>)" bot proc_global_s0 \<sigma>]
    unfolding make_rhs_tree_ip_inc_g_fn_cong compile_prog_inc_exit by simp
qed

lemma proc_global_entry_reach:
  fixes \<sigma> :: "(pp, sign abs_state) map"
  shows "cfg_entry (compile_prog inc_pi [''p''] (PCall ''p''))
     \<in> reach (make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) sign_tf (\<squnion>) bot proc_global_s0) \<sigma>
       (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
  using inc_g_reach_at_exit[of _ sign_tf "(\<squnion>)" bot proc_global_s0 \<sigma>]
  unfolding make_rhs_tree_ip_inc_g_fn_cong compile_prog_inc_entry compile_prog_inc_exit
  by simp

theorem proc_global_sign_analysis:
  fixes s t :: store
  assumes runs: "pruns_to_ip inc_pi [''p''] (PCall ''p'') s t"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree_ip (compile_prog inc_pi [''p''] (PCall ''p'')) sign_tf (\<squnion>) bot
         proc_global_s0)
       (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
  shows "t \<in> sign_domain.gamma_state
       (td_analyse_ip inc_pi [''p''] (PCall ''p'') sign_tf (\<squnion>) bot proc_global_s0
         (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p''))))"
proof -
  have collect_exit:
    "t \<in> cfg_collect_ip (compile_prog inc_pi [''p''] (PCall ''p'')) {s}
       (cfg_exit (compile_prog inc_pi [''p''] (PCall ''p'')))"
    using runs unfolding pruns_to_ip_def
    by (metis singleton_store_def)
  show ?thesis
    by (rule ip_sign_analysis_sound[OF proc_global_s0_gamma collect_exit
          compile_prog_inc_finite compile_prog_inc_finite_combines td_solve_dom
          proc_global_edge_reach proc_global_combine_reach proc_global_entry_reach])
qed

end
