theory State_Restriction
  imports Transfer_Interface "Voblint_Domain.Split_State"
begin

section \<open>Local/global restriction of abstract states\<close>

text \<open>
  The locals/globals split on abstract states. \<open>restrict_local_for\<close> and
  \<open>restrict_global_for\<close> each keep one component and set the other to
  \<open>bot\<close>, so their join recovers the original state. They are join
  homomorphisms, idempotent, and annihilate each other; the resulting \<open>simp\<close>
  rules normalize any split/reassembly expression without a dedicated
  lemma. \<^const>\<open>combine_env\<close> reduces to that algebra, and the paired
  representation of @{theory Voblint_Domain.Split_State} is exactly this
  decomposition.
\<close>

definition restrict_local_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_local_for gs \<sigma> = (\<lambda>x. if gs x then bot else \<sigma> x)"

definition restrict_global_for ::
  "(vname => bool) => 'a::bounded_semilattice_sup_bot abs_state => 'a abs_state" where
  "restrict_global_for gs \<sigma> = (\<lambda>x. if gs x then \<sigma> x else bot)"

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

lemma restrict_global_for_le:
  "restrict_global_for gs (sigma :: 'a::bounded_semilattice_sup_bot abs_state) \<le> sigma"
  unfolding restrict_global_for_def le_fun_def by (auto simp: bot_least)

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
  by (cases x) simp_all

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

text \<open>\<^const>\<open>combine_env\<close>'s primitive definition is a single if-then-else lambda;
  this reduces it to the \<^const>\<open>restrict_local_for\<close>/\<^const>\<open>restrict_global_for\<close>
  algebra so proofs never need to unfold \<open>combine_env_def\<close> and re-derive the split by
  hand.\<close>
lemma combine_env_for_eq_restrict:
  "combine_env gs sc se =
     restrict_local_for gs sc \<squnion> restrict_global_for gs se"
  unfolding combine_env_def restrict_local_for_def restrict_global_for_def
    sup_fun_def
  by (rule ext) simp


subsection \<open>Split-state bridge\<close>

text \<open>
  The split representation of \<open>Split_State\<close> packages exactly this
  \<^const>\<open>restrict_local_for\<close> / \<^const>\<open>restrict_global_for\<close> decomposition; the
  \<open>map_lift\<close> siblings below are its lifted-carrier counterparts.
\<close>

lemma map_lift_restrict_local_for_join [simp]:
  "map_lift (restrict_local_for gs) (a \<squnion> b)
     = map_lift (restrict_local_for gs) a \<squnion> map_lift (restrict_local_for gs) b"
  by (cases a; cases b) simp_all

lemma map_lift_restrict_global_for_join [simp]:
  "map_lift (restrict_global_for gs) (a \<squnion> b)
     = map_lift (restrict_global_for gs) a \<squnion> map_lift (restrict_global_for gs) b"
  by (cases a; cases b) simp_all

end
