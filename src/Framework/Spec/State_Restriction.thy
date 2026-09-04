theory State_Restriction
  imports "Voblint_VIMP.VIMP_Globals" "Voblint_Domain.Nonrelational_State"
    "Voblint_Domain.Reachability_Lift"
begin

section \<open>Local/global restriction of abstract states\<close>

text \<open>
  A variable classifier selects one half of an abstract state and replaces the
  other with \<^const>\<open>bot\<close>. Both restrictions specialize the generic
  \<^const>\<open>combine_env\<close> selector. Their join recovers the original state;
  they preserve joins, are idempotent, and annihilate each other.
\<close>

definition restrict_local_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local_for gs sigma = combine_env gs sigma bot"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for gs sigma = combine_env gs bot sigma"

lemma restrict_local_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_local_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_local_for gs sigma2"
  unfolding restrict_local_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_global_for gs (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_global_for gs sigma2"
  unfolding restrict_global_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_local_for_le:
  "restrict_local_for gs (sigma :: 'a::bounded_semilattice_sup_bot abs_state) \<le> sigma"
  unfolding restrict_local_for_def le_fun_def by auto

lemma restrict_global_for_le:
  "restrict_global_for gs (sigma :: 'a::bounded_semilattice_sup_bot abs_state) \<le> sigma"
  unfolding restrict_global_for_def le_fun_def by auto

lemma map_lift_restrict_global_for_le:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) x \<le> x"
  by (cases x) (simp_all add: restrict_global_for_le)

lemma restrict_local_for_join [simp]:
  "restrict_local_for gs (A \<squnion> B) = restrict_local_for gs A \<squnion> restrict_local_for gs B"
  unfolding restrict_local_for_def sup_fun_def by (rule ext) simp

lemma restrict_global_for_join [simp]:
  "restrict_global_for gs (A \<squnion> B) = restrict_global_for gs A \<squnion> restrict_global_for gs B"
  unfolding restrict_global_for_def sup_fun_def by (rule ext) simp

lemma restrict_local_for_idem [simp]:
  "restrict_local_for gs (restrict_local_for gs A) = restrict_local_for gs A"
  unfolding restrict_local_for_def by (rule ext) simp

lemma restrict_global_for_idem [simp]:
  "restrict_global_for gs (restrict_global_for gs A) = restrict_global_for gs A"
  unfolding restrict_global_for_def by (rule ext) simp

lemma map_lift_restrict_global_for_idem [simp]:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for gs) (map_lift (restrict_global_for gs) x)
           = map_lift (restrict_global_for gs) x"
  unfolding map_lift_comp o_def by simp

lemma restrict_local_for_restrict_global_for_bot [simp]:
  "restrict_local_for gs (restrict_global_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_global_for_restrict_local_for_bot [simp]:
  "restrict_global_for gs (restrict_local_for gs A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_global_join [simp]:
  "restrict_local_for gs \<sigma> \<squnion> restrict_global_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_global_for_local_join [simp]:
  "restrict_global_for gs \<sigma> \<squnion> restrict_local_for gs \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

text \<open>
  The selector equals the join of its disjoint local and global projections.
  This bridge lets state proofs use the restriction algebra without unfolding
  \<^const>\<open>combine_env\<close>.
\<close>

lemma combine_env_for_eq_restrictions:
  "combine_env gs sc se =
     restrict_local_for gs sc \<squnion> restrict_global_for gs se"
  unfolding combine_env_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp

subsection \<open>Lifted restrictions\<close>

text \<open>The lifted rules transport the same join homomorphisms to reachable states.\<close>

lemma map_lift_restrict_local_for_join [simp]:
  "map_lift (restrict_local_for gs) (a \<squnion> b)
     = map_lift (restrict_local_for gs) a \<squnion> map_lift (restrict_local_for gs) b"
  by (rule map_lift_sup) simp

lemma map_lift_restrict_global_for_join [simp]:
  "map_lift (restrict_global_for gs) (a \<squnion> b)
     = map_lift (restrict_global_for gs) a \<squnion> map_lift (restrict_global_for gs) b"
  by (rule map_lift_sup) simp

subsection \<open>Splitting and rejoining\<close>

text \<open>Routing a state's two halves back through \<^const>\<open>combine_env\<close> recovers it
  exactly: each half is already bottom outside the names it owns.\<close>

lemma combine_env_restrict_id [simp]:
  "combine_env gs (restrict_local_for gs sigma) (restrict_global_for gs sigma) = sigma"
  by (simp add: combine_env_for_eq_restrictions)

end
