theory Transfer_Algebra
  imports "Voblint_CFG.CFG_Transfer" "Voblint_Domain.Nonrelational_State"
begin

section \<open>The abstract-state algebra a whole-state transfer computes in\<close>

text \<open>
  A Base-style analysis carries one pointwise abstract state per program point: a
  map from variable names to abstract values. This theory fixes the operations its
  transfer functions are assembled from -- how a call resets the callee frame and
  binds its formals, how a return merges caller against callee and publishes the
  result value -- together with their soundness and monotonicity against
  \<open>gamma_state\<close>.

  It defines no interface. What an analysis supplies to the framework is a
  \<open>gdg_spec\<close>: one manager-native transfer per edge action, taking the manager and
  returning a program. This theory is the algebra those transfers compute in,
  stated once so that no whole-state domain re-proves it.

  Most of the operations themselves live lower still, in the language session,
  because they are generic in the state's codomain and the concrete semantics
  runs the very same constants: \<^const>\<open>combine_env\<close>, \<^const>\<open>enter_frame\<close>,
  \<^const>\<open>bind_formals\<close>, \<^const>\<open>combine_assign\<close> and \<^const>\<open>enter_binding\<close> are
  all shared. What is genuinely new here is their meaning against a
  concretization, which is the first point at which the domain session and the
  CFG session are both in scope.
\<close>


subsection \<open>The structural environment combine\<close>

lemma combine_env_mono:
  fixes sc1 sc2 se1 se2 :: "('k, 'a::order) gabs_state"
  assumes "sc1 \<le> sc2" and "se1 \<le> se2"
  shows "combine_env \<G> sc1 se1 \<le> combine_env \<G> sc2 se2"
  using assms by (auto simp: combine_env_def le_fun_def)

text \<open>
  Soundness of the abstract combine: combining a caller store (sound for sc) with
  a callee-exit store (sound for se) yields a store sound for \<open>combine_env \<G> sc se\<close>.
  A pure \<open>numeric_domain\<close> fact -- independent of any transfer function -- reused by
  both the interprocedural constraint-system soundness and the effectful pipeline.
  \<open>combine_env\<close> is the fixed structural merge the Base call boundary uses; an
  analysis that wants a different one overrides its specification's own
  environment stage instead.
\<close>
lemma combine_env_sound [intro]:
  fixes dc de :: "('k, 'a::numeric_domain) gabs_state"
  assumes sc: "s \<in> \<gamma> dc" and se: "t \<in> \<gamma> de"
  shows "combine_env \<G> s t \<in> \<gamma> (combine_env \<G> dc de)"
  using assms by (auto simp: gamma_state_def le_fun_def)

subsection \<open>Generic soundness and monotonicity helpers\<close>

text \<open>The two facts a call boundary keeps re-deriving: writing one variable, and binding a
  list of formals, each preserve soundness and monotonicity.  They are stated for an
  arbitrary domain and no transfer function, so every analysis picks them up rather than
  proving its own copy.\<close>
lemma gamma_state_upd [intro]:
  fixes d :: "('k, 'a::numeric_domain) gabs_state"
  assumes s: "s \<in> \<gamma> d" and v: "v \<in> \<gamma> a"
  shows "s(x := v) \<in> \<gamma> (d(x := a))"
  using s v unfolding gamma_state_def by auto

text \<open>
  Binding formals preserves soundness: pointwise-sound actual values bound to the
  same formals yield a sound entry state.
\<close>
lemma bind_formals_sound [intro]:
  fixes d :: "('k, 'a::numeric_domain) gabs_state"
  assumes s: "s \<in> \<gamma> d"
    and vals: "list_all2 (\<lambda>v a. v \<in> \<gamma> a) vs avs"
  shows "bind_formals xs vs s \<in> \<gamma> (bind_formals xs avs d)"
  using assms apply (induction xs arbitrary: vs avs s d)
  subgoal
    by simp
  subgoal for _ _ vs avs
    by (cases vs; cases avs) (auto simp: gamma_state_upd)
  done

lemma bind_formals_mono:
  fixes d1 d2 :: "('k, 'a::order) gabs_state"
  assumes base: "d1 \<le> d2"
    and vals: "list_all2 (\<le>) avs1 avs2"
  shows "bind_formals xs avs1 d1 \<le> bind_formals xs avs2 d2"
  using assms apply (induction xs arbitrary: avs1 avs2 d1 d2)
  subgoal
    by simp
  subgoal for _ _ avs1 avs2
    by (cases avs1; cases avs2) (auto simp add: le_fun_def)
  done

subsection \<open>Procedure entry: binding formals and resetting the frame\<close>

text \<open>
  Procedure entry itself is not defined here. \<^const>\<open>enter_frame\<close> and
  \<^const>\<open>enter_binding\<close> (\<^theory>\<open>Voblint_VIMP.VIMP_Proc\<close>) are already generic in
  the state's codomain, and the concrete semantics is \<^const>\<open>enter_binding\<close> at
  the reset value \<open>0\<close> and the language's evaluator
  (\<^const>\<open>cfg_transfer_sem.gcall_enter\<close>). An abstract domain runs the same constant at its own
  \<open>top\<close> and its own evaluator, so the two can never drift apart: there is one
  definition and two instances of it.

  What this theory adds is the pair of facts that relate those two instances --
  the concrete entered store lands in the concretization of the abstract one, and
  the abstract one is monotone. Neither is expressible below here, because
  \<^const>\<open>gamma_state\<close> lives in the domain session and \<^const>\<open>enter_binding\<close> in
  the language session.
\<close>

lemma enter_frame_sound [intro]:
  fixes reset_val :: "'a::numeric_domain"
  assumes sv: "s \<in> \<gamma> d" and reset_full: "\<gamma> reset_val = UNIV"
  shows "enter_state \<G> s \<in> \<gamma> (enter_frame \<G> reset_val d)"
  unfolding gamma_state_def enter_state_def
  using gamma_stateD[OF sv] reset_full by auto

lemma enter_frame_mono:
  fixes reset_val :: "'a::order"
  assumes "d1 \<le> d2"
  shows "enter_frame \<G> reset_val d1 \<le> enter_frame \<G> reset_val d2"
  by (simp add: assms le_funD le_funI)

text \<open>
  \<^const>\<open>bind_formals\<close>'s own soundness and monotonicity are relational in the
  actual values, but that is not the shape a domain owns: an evaluator's
  soundness and monotonicity are pointwise in one actual. This turns the one into
  the other, so the entry lemmas below can take the fact a caller already has and
  nobody builds a \<^const>\<open>list_all2\<close> by hand.
\<close>

lemma list_all2_map_mapI [intro]:
  assumes "\<And>x. x \<in> set xs \<Longrightarrow> R (f x) (g x)"
  shows "list_all2 R (map f xs) (map g xs)"
  using assms by (induction xs) auto

lemma enter_binding_sound_list_all2 [intro]:
  fixes reset_val :: "'a::numeric_domain"
  assumes sv: "s \<in> \<gamma> d" and reset_full: "\<gamma> reset_val = UNIV"
    and vals: "list_all2 (\<lambda>v a. v \<in> \<gamma> a)
                 (map (\<lambda>e. ev e s) es) (map (\<lambda>e. aval_abs e d) es)"
  shows "enter_binding \<G> 0 ev xs es s
           \<in> \<gamma> (enter_binding \<G> reset_val aval_abs xs es d)"
  unfolding enter_binding_def enter_state_def[symmetric]
  by (rule bind_formals_sound[OF enter_frame_sound[OF sv reset_full] vals])

lemma enter_binding_sound [intro]:
  fixes reset_val :: "'a::numeric_domain"
  assumes sv: "s \<in> \<gamma> d" and reset_full: "\<gamma> reset_val = UNIV"
    and eval: "\<And>e. e \<in> set es \<Longrightarrow> ev e s \<in> \<gamma> (aval_abs e d)"
  shows "enter_binding \<G> 0 ev xs es s
           \<in> \<gamma> (enter_binding \<G> reset_val aval_abs xs es d)"
proof (rule enter_binding_sound_list_all2[OF sv reset_full])
  show "list_all2 (\<lambda>v a. v \<in> \<gamma> a)
          (map (\<lambda>e. ev e s) es) (map (\<lambda>e. aval_abs e d) es)"
    by (rule list_all2_map_mapI) (rule eval)
qed

lemma enter_binding_mono:
  fixes reset_val :: "'a::order" and d1 d2 :: "('k, 'a) gabs_state"
  assumes state_le: "d1 \<le> d2"
    and eval_mono: "\<And>e. e \<in> set es \<Longrightarrow> aval_abs e d1 \<le> aval_abs e d2"
  shows "enter_binding \<G> reset_val aval_abs xs es d1
           \<le> enter_binding \<G> reset_val aval_abs xs es d2"
  unfolding enter_binding_def
proof (rule bind_formals_mono[OF enter_frame_mono[OF state_le]])
  show "list_all2 (\<le>) (map (\<lambda>e. aval_abs e d1) es) (map (\<lambda>e. aval_abs e d2) es)"
    by (rule list_all2_map_mapI) (rule eval_mono)
qed

text \<open>
  A call site reads the formals and actuals off \<^typ>\<open>call_info\<close> rather than
  passing them separately, but that projection stays at the call site: a domain
  writes \<open>enter_binding \<G> top ev (ci_formals ci) (ci_args ci)\<close>, exactly as the
  return side writes \<open>combine_assign (ci_dst ci)\<close>. No constant here wraps it.

  The caller's own continuation is not computed here either. Goblint's
  \<open>Spec.enter\<close> answers caller/callee pairs and \<open>constraints.ml\<close> hands the caller
  half on to \<open>combine_env\<close>; a specification's entry field answers the same
  pairs, so a domain that wants to drop caller facts a callee could invalidate
  --- Goblint's \<open>varEq\<close> filters its caller state by taint --- returns the
  filtered state as the continuation half of its own alternatives. Nothing in
  this algebra chooses that half: the operations below are what a whole-state
  domain computes each half \<^emph>\<open>with\<close>.
\<close>

subsection \<open>The structural return combine\<close>

text \<open>The return-value write is a single-slot update, hence monotone in both the
  written value and the state it writes into.  Any combine built over it inherits
  monotonicity from this one fact.\<close>

lemma combine_assign_mono:
  fixes s1 s2 :: "('k, 'a::order) gabs_state"
  assumes v: "v1 \<le> v2" and s: "s1 \<le> s2"
  shows "combine_assign dst v1 s1 \<le> combine_assign dst v2 s2"
  using assms by (cases dst) (auto simp: le_fun_def)

end
