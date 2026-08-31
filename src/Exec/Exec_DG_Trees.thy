theory Exec_DG_Trees
  imports
    Exec_DG_Refines
begin

section \<open>Executable D/G strategy trees and their traversal\<close>

text \<open>
  The commutation of a single executable tree's traversal with the readback: the D/G edge
  and combine trees have closed-form traversals, so \<open>fun_of_dg_st_for\<close> commutes with a
  traversal precisely when the analysis step commutes componentwise. Everything here is
  about one tree at a time; the fold over a whole node's tree list is the next layer up.
\<close>
subsection \<open>Per-tree traversal commutation\<close>

text \<open>
  The D/G edge and combine trees have closed-form traversals
  (\<open>Voblint_Core.DG_Framework\<close>): the local Answer carries \<open>snd (step \<dots>)\<close>
  and no global, so \<open>fun_of_dg_st_for\<close> commutes with the traversal precisely when
  the analysis step commutes componentwise.
\<close>


lemma traverse_dg_edge_tree_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g)
                     = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (dg_edge_tree step_st u) \<sigma>_st)
           = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "snd (step_abs (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl u)))) (fun_of_exec_dg_st_for gs (globs (\<sigma>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (snd (step_st (locals (\<sigma>_st (Inl u))) (globs (\<sigma>_st (Inr ())))))"
    using H[of "locals (\<sigma>_st (Inl u))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_edge_tree fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_bot bot_fun_def)
qed

lemma traverse_wrapped_edge_commute_for:
  assumes H: "\<And>d g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (step_st d g)
                     = step_abs (fun_of_exec_dg_st_for gs d) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_st u))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_edge_tree step_abs u))) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_for gs (traverse_rhs (dg_edge_tree step_st u) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_edge_tree step_abs u) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_edge_tree_commute_for)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

subsection \<open>Wrapped-tree commutation and the accumulator fold\<close>

text \<open>
  The generator re-keys each tree with \<open>map_gtree\<close> / \<open>map_ltree\<close> to place
  local unknowns at \<open>(pp, c)\<close> and global unknowns at \<open>gkey c\<close>.  Those relabellings
  are transparent to \<open>fun_of_dg_st_for\<close>: it acts on values, they act on unknown
  keys, and the per-tree commutation is stated for an arbitrary valuation.
\<close>


text \<open>Generic mirror of \<open>traverse_wrapped_combine_commute\<close> over an arbitrary storage
  classifier \<open>gs\<close>, built on \<open>traverse_dg_combine_tree_commute_for\<close> below. (The
  \<open>side_acc_dg\<close> fold has its own generic mirror, \<open>side_acc_dg_commute_for\<close>, further
  down alongside \<open>sides_side_rhs_fold_dg_commute_for\<close>.)\<close>

lemma traverse_dg_combine_tree_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (dg_combine_tree comb_st dst cc ex) \<sigma>_st)
           = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "snd (comb_abs dst (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl cc)))) (fun_of_exec_dg_st_for gs (locals (\<sigma>_st (Inl ex))))
              (fun_of_exec_dg_st_for gs (globs (\<sigma>_st (Inr ())))))
        = fun_of_exec_dg_st_for gs (snd (comb_st dst (locals (\<sigma>_st (Inl cc))) (locals (\<sigma>_st (Inl ex)))
              (globs (\<sigma>_st (Inr ())))))"
    using H[of dst "locals (\<sigma>_st (Inl cc))" "locals (\<sigma>_st (Inl ex))" "globs (\<sigma>_st (Inr ()))"]
    by (metis map_prod_simp snd_conv surj_pair)
  thus ?thesis
    by (simp add: traverse_dg_combine_tree fun_of_exec_dg_st_for_def fun_of_resolved_st_q_for_bot bot_fun_def)
qed

lemma traverse_wrapped_combine_commute_for:
  assumes H: "\<And>dst dc de g. map_prod (fun_of_exec_dg_st_for gs) (fun_of_exec_dg_st_for gs) (comb_st dst dc de g)
                        = comb_abs dst (fun_of_exec_dg_st_for gs dc) (fun_of_exec_dg_st_for gs de) (fun_of_exec_dg_st_for gs g)"
  shows "fun_of_dg_st_for gs (traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_st dst cc ex))) \<sigma>_st)
       = traverse_rhs (map_gtree gk (map_ltree lk (dg_combine_tree comb_abs dst cc ex))) (fun_of_dg_st_for gs \<circ> \<sigma>_st)"
proof -
  have "fun_of_dg_st_for gs (traverse_rhs (dg_combine_tree comb_st dst cc ex) (\<lambda>z. \<sigma>_st (map_sum lk gk z)))
        = traverse_rhs (dg_combine_tree comb_abs dst cc ex) (fun_of_dg_st_for gs \<circ> (\<lambda>z. \<sigma>_st (map_sum lk gk z)))"
    using H by (rule traverse_dg_combine_tree_commute_for)
  thus ?thesis
    by (simp add: traverse_rhs_map_gtree traverse_rhs_map_ltree sum.map_comp comp_def o_def)
qed

end
