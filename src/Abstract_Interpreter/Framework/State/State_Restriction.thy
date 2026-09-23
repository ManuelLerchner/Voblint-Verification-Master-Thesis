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
  "restrict_local_for \<G> sigma = combine_env \<G> sigma bot"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for \<G> sigma = combine_env \<G> bot sigma"

lemma restrict_local_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_local_for \<G> (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_local_for \<G> sigma2"
  unfolding restrict_local_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_global_for_mono:
  "sigma1 \<le> sigma2 \<Longrightarrow>
     restrict_global_for \<G> (sigma1 :: 'a::bounded_semilattice_sup_bot abs_state)
       \<le> restrict_global_for \<G> sigma2"
  unfolding restrict_global_for_def le_fun_def
  by (auto dest: le_funD)

lemma restrict_local_for_join [simp]:
  "restrict_local_for \<G> (A \<squnion> B) = restrict_local_for \<G> A \<squnion> restrict_local_for \<G> B"
  unfolding restrict_local_for_def sup_fun_def by (rule ext) simp

lemma restrict_global_for_join [simp]:
  "restrict_global_for \<G> (A \<squnion> B) = restrict_global_for \<G> A \<squnion> restrict_global_for \<G> B"
  unfolding restrict_global_for_def sup_fun_def by (rule ext) simp

lemma restrict_local_for_idem [simp]:
  "restrict_local_for \<G> (restrict_local_for \<G> A) = restrict_local_for \<G> A"
  unfolding restrict_local_for_def by (rule ext) simp

lemma restrict_global_for_idem [simp]:
  "restrict_global_for \<G> (restrict_global_for \<G> A) = restrict_global_for \<G> A"
  unfolding restrict_global_for_def by (rule ext) simp

lemma map_lift_restrict_global_for_idem [simp]:
  fixes x :: "'a::bounded_semilattice_sup_bot abs_state lifted"
  shows "map_lift (restrict_global_for \<G>) (map_lift (restrict_global_for \<G>) x)
           = map_lift (restrict_global_for \<G>) x"
  unfolding map_lift_comp o_def by simp

lemma restrict_local_for_restrict_global_for_bot [simp]:
  "restrict_local_for \<G> (restrict_global_for \<G> A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_global_for_restrict_local_for_bot [simp]:
  "restrict_global_for \<G> (restrict_local_for \<G> A) = bot"
  unfolding restrict_local_for_def restrict_global_for_def by (rule ext) simp

lemma restrict_local_for_global_join [simp]:
  "restrict_local_for \<G> \<sigma> \<squnion> restrict_global_for \<G> \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

lemma restrict_global_for_local_join [simp]:
  "restrict_global_for \<G> \<sigma> \<squnion> restrict_local_for \<G> \<sigma> = \<sigma>"
  unfolding restrict_local_for_def restrict_global_for_def sup_fun_def
  by (rule ext) simp

text \<open>
  The selector equals the join of its disjoint local and global projections.
  This bridge lets state proofs use the restriction algebra without unfolding
  \<^const>\<open>combine_env\<close>.
\<close>

lemma combine_env_for_eq_restrictions:
  "combine_env \<G> sc se =
     restrict_local_for \<G> sc \<squnion> restrict_global_for \<G> se"
  unfolding combine_env_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp

subsection \<open>Lifted restrictions\<close>

text \<open>The lifted rules transport the same join homomorphisms to reachable states.\<close>

lemma map_lift_restrict_local_for_join [simp]:
  "map_lift (restrict_local_for \<G>) (a \<squnion> b)
     = map_lift (restrict_local_for \<G>) a \<squnion> map_lift (restrict_local_for \<G>) b"
  by (rule map_lift_sup) simp

lemma map_lift_restrict_global_for_join [simp]:
  "map_lift (restrict_global_for \<G>) (a \<squnion> b)
     = map_lift (restrict_global_for \<G>) a \<squnion> map_lift (restrict_global_for \<G>) b"
  by (rule map_lift_sup) simp

subsection \<open>Splitting and rejoining\<close>

text \<open>Routing a state's two halves back through \<^const>\<open>combine_env\<close> recovers it
  exactly: each half is already bottom outside the names it owns.\<close>

lemma combine_env_restrict_id [simp]:
  "combine_env \<G> (restrict_local_for \<G> sigma) (restrict_global_for \<G> sigma) = sigma"
  by (simp add: combine_env_for_eq_restrictions)

subsection \<open>Reading one selected name\<close>

text \<open>The two pointwise equations, so a proof about a single variable never has
  to unfold \<^const>\<open>combine_env\<close>. The nesting law is what lets a combine step
  read a returned value straight out of the callee exit: every call site owns
  \<open>ret_var\<close> as its own compiler-internal name and never a user-declared global
  (\<open>reserved_ret_var\<close>), so routing it through \<^const>\<open>combine_env\<close> a second
  time would change nothing.\<close>

lemma combine_env_local_eq [simp]:
  "\<not> \<G> x \<Longrightarrow> combine_env \<G> sc se x = sc x"
  by (simp add: combine_env_def)

lemma combine_env_global_eq [simp]:
  "\<G> x \<Longrightarrow> combine_env \<G> sc se x = se x"
  by (simp add: combine_env_def)

lemma combine_env_combine_env_left [simp]:
  "combine_env \<G> (combine_env \<G> dc g) (combine_env \<G> de g) = combine_env \<G> dc g"
  by (auto simp: combine_env_def)

end
