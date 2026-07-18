section \<open>Example: backward guard refinement vs identity assume\<close>

theory Example_Guard_Refinement
  imports "Voblint_Analysis.Interval_Domain"
begin

hide_const (open) Update_rules.N

text \<open>
  Backward analysis is sound without being useful: the pre-migration identity
  assume transfer already satisfied @{term tf_assume}.  The payoff is
  \emph{precision}.  This theory exhibits the gap on a single guard and one
  loop-body step --- the same pattern that makes the bounded-loop example
  (@{file "Example_Interval_Loop_Coverage.thy"}) stabilise at @{text "[0,20]"}.
  Sign cannot express either bound; interval backward filtering on
  @{text "x < n"} is where the difference shows up.
\<close>

subsection \<open>Setup: loop-head abstract state and identity baseline\<close>

definition sigma_x :: "ivl \<Rightarrow> ivl abs_state" where
  "sigma_x iv = (\<lambda>_. Ivl MinInf PlusInf)(''x'' := iv)"

abbreviation "sigma_loop_head \<equiv> sigma_x (Ivl (Fin 0) (Fin 20))"

text \<open>
  Pre-migration assume: leave the abstract state unchanged (still sound, but
  imprecise).
\<close>
definition assume_ivl_identity :: "bexp \<Rightarrow> ivl abs_state \<Rightarrow> ivl abs_state" where
  "assume_ivl_identity _ sigma = sigma"

subsection \<open>One guard: @{text "x < 20"} narrows the upper bound\<close>

lemma refine_x_lt_20:
  "assume_ivl (Less (V ''x'') (N 20)) sigma_loop_head ''x'' = Ivl (Fin 0) (Fin 19)"
  unfolding sigma_x_def
  by (simp add: assume_ivl_def)

lemma identity_x_lt_20:
  "assume_ivl_identity (Less (V ''x'') (N 20)) sigma_loop_head ''x'' =
   Ivl (Fin 0) (Fin 20)"
  by (simp add: assume_ivl_identity_def sigma_x_def)

text \<open>
  The refined interval is strictly tighter: @{text 20} is possible before the
  guard but excluded on the then-branch.
\<close>
lemma refine_excludes_20:
  "20 \<in> gamma_ivl (Ivl (Fin 0) (Fin 20))"
  "20 \<notin> gamma_ivl (Ivl (Fin 0) (Fin 19))"
  by simp_all

value "assume_ivl (Less (V ''x'') (N 20)) sigma_loop_head ''x''"
value "assume_ivl_identity (Less (V ''x'') (N 20)) sigma_loop_head ''x''"

subsection \<open>One body step: @{text "x := x + 1"} after the guard\<close>

definition body_after_refined :: "ivl abs_state" where
  "body_after_refined =
     assign_ivl ''x'' (Plus (V ''x'') (N 1))
       (assume_ivl (Less (V ''x'') (N 20)) sigma_loop_head)"

definition body_after_identity :: "ivl abs_state" where
  "body_after_identity =
     assign_ivl ''x'' (Plus (V ''x'') (N 1))
       (assume_ivl_identity (Less (V ''x'') (N 20)) sigma_loop_head)"

lemma body_step_refined:
  "body_after_refined ''x'' = Ivl (Fin 1) (Fin 20)"
  unfolding body_after_refined_def sigma_x_def
  by (simp add: assign_ivl_def assume_ivl_def normalize_ivl_def)

lemma body_step_identity:
  "body_after_identity ''x'' = Ivl (Fin 1) (Fin 21)"
  unfolding body_after_identity_def sigma_x_def assume_ivl_identity_def
  by (simp add: assign_ivl_def normalize_ivl_def)

text \<open>
  Joining the initial @{text "[0,0]"} with the body exit is where the gap
  compounds: backward analysis yields the tight loop-head interval; identity
  assume drifts upward and never closes at @{text "[0,20]"} without widening.
\<close>
lemma loop_join_refined:
  "sigma_x (Ivl (Fin 0) (Fin 0)) ''x'' \<squnion> body_after_refined ''x'' = Ivl (Fin 0) (Fin 20)"
  unfolding body_after_refined_def sigma_x_def
  by (simp add: sup_ivl_def assign_ivl_def assume_ivl_def normalize_ivl_def)

lemma loop_join_identity:
  "sigma_x (Ivl (Fin 0) (Fin 0)) ''x'' \<squnion> body_after_identity ''x'' = Ivl (Fin 0) (Fin 21)"
  unfolding body_after_identity_def sigma_x_def assume_ivl_identity_def
  by (simp add: sup_ivl_def assign_ivl_def normalize_ivl_def)

lemma backward_analysis_strictly_tighter:
  "Ivl (Fin 0) (Fin 20) \<le> Ivl (Fin 0) (Fin 21)"
  "Ivl (Fin 0) (Fin 21) \<le> Ivl (Fin 0) (Fin 20) \<longleftrightarrow> False"
  by (simp_all add: less_eq_ivl_def)

value "sigma_x (Ivl (Fin 0) (Fin 0)) ''x'' \<squnion> body_after_refined ''x''"
value "sigma_x (Ivl (Fin 0) (Fin 0)) ''x'' \<squnion> body_after_identity ''x''"

end
