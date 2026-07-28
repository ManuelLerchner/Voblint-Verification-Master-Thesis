theory TD_Side_Eff_Ctx_Shared
  imports TD_Side_Tree
begin

section \<open>Shared context-pull helpers\<close>

text \<open>
  Shared support for the context-indexed keyed and digest proofs.  The context pullback
  keeps the local slot at a fixed context and preserves all global slots.  The two
  slot-bot invariants state that the inappropriate half of each slot is \<^term>\<open>bot\<close>.
\<close>

subsection \<open>The context pullback\<close>

definition pull_ctx ::
  "'c \<Rightarrow> (pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
       \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state)"
where
  "pull_ctx ctx \<sigma> = \<sigma> \<circ> map_sum (\<lambda>w. (w, ctx)) id"

lemma pull_ctx_Inl: "pull_ctx ctx \<sigma> (Inl u) = \<sigma> (Inl (u, ctx))"
  by (simp add: pull_ctx_def)

lemma pull_ctx_Inr: "pull_ctx ctx \<sigma> (Inr g) = \<sigma> (Inr g)"
  by (simp add: pull_ctx_def)

subsection \<open>Slot invariants\<close>

definition inr_slot_locals_bot_ctx ::
  "(pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> bool"
where
  "inr_slot_locals_bot_ctx \<sigma> =
     (\<forall>g. \<forall>x. \<not> is_global x \<longrightarrow> \<sigma> (Inr g) x = bot)"

lemma inr_slot_locals_bot_pull_ctx:
  "inr_slot_locals_bot_ctx \<sigma> \<Longrightarrow> inr_slot_locals_bot (pull_ctx ctx \<sigma>)"
  by (simp add: inr_slot_locals_bot_ctx_def inr_slot_locals_bot_def pull_ctx_Inr)



lemma sides_fold_le_side_cfg_T_eff_ctx:
  shows "sides_of_rhs (fold_rhs_trees
           (if v = cfg_entry g then bot0 \<squnion> restrict_local s0 else bot0)
           (map (\<lambda>(u, a). map_ltree (\<lambda>w. (w, ctx)) (apply_etf etf a u))
                (intra_predecessor_list g v)
            @ map (\<lambda>(cl, fs, as). map_ltree (\<lambda>w. (w, ctx)) (etf_enter etf fs as cl))
                (entry_seed_list g v)
            @ map (\<lambda>(cc, dst, ex). cmb ctx dst cc ex) (return_call_list g v)))
           \<sigma> (Inr gg)
         \<le> sides_of_rhs (side_cfg_T_eff_ctx cmb g etf bot0 s0 gseed (v, ctx))
             \<sigma> (Inr gg)"
  unfolding side_cfg_T_eff_ctx_def
  by (cases "v = cfg_entry g") (auto simp: Let_def fun_upd_def)

end
