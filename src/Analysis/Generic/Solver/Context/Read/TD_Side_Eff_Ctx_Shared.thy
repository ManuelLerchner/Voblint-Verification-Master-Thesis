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

definition inl_slot_globals_bot_ctx ::
  "(pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state) \<Rightarrow> bool"
where
  "inl_slot_globals_bot_ctx \<sigma> =
     (\<forall>v. \<forall>x. is_global x \<longrightarrow> \<sigma> (Inl v) x = bot)"

subsection \<open>Fold lemmas for the context-side builder\<close>

lemma sides_le_side_rhs_fold_ctx:
  fixes \<sigma> :: "pp \<times> 'c + 'g \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state"
  shows "t \<in> set ts \<Longrightarrow>
         sides_of_rhs t \<sigma> (Inr gg)
           \<le> sides_of_rhs (side_rhs_fold_ctx acc ts) \<sigma> (Inr gg)"
proof (induction ts arbitrary: acc)
  case Nil thus ?case by simp
next
  case (Cons t' ts)
  from Cons.prems consider (hd) "t = t'" | (tl) "t \<in> set ts" by auto
  then show ?case
  proof cases
    case hd
    show ?thesis unfolding hd side_rhs_fold_ctx.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule sup_ge1)
  next
    case tl
    have ih: "sides_of_rhs t \<sigma> (Inr gg)
            \<le> sides_of_rhs
                 (side_rhs_fold_ctx (acc \<squnion> traverse_rhs t' \<sigma>) ts) \<sigma> (Inr gg)"
      by (rule Cons.IH[OF tl])
    show ?thesis unfolding side_rhs_fold_ctx.simps
      by (simp only: sides_of_rhs_seqcomp_at) (rule le_supI2[OF ih])
  qed
qed

lemma sides_fold_le_side_cfg_T_eff_ctx:
  shows "sides_of_rhs (side_rhs_fold_ctx
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
