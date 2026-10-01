theory DG_Result_Construction
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.DG_Analysis_Adapter"
    "Voblint_Framework.Routed_Call_Programs"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Exec.Exec_Result_Abs"
    "Voblint_Exec.Exec_DG_State"
    "Voblint_Exec.Default_St_Reachability"
begin

section \<open>What a solved D/G system publishes\<close>

text \<open>
  Every analysis, at every context policy and every solver discipline, turns the
  solver's answer -- a covered key set and a map from unknowns to \<open>dg_state\<close>s over
  its carrier -- into an \<^type>\<open>analysis_result\<close> table of the locals. This
  theory states that construction once, over an arbitrary solved pair, so an
  analysis's result table is one application rather than a rewritten body.

  Publishing a local unknown means two steps in sequence.
  \<^const>\<open>canonicalize_lift\<close> collapses a stored \<^const>\<open>Lifted\<close> payload that
  describes no store to \<^const>\<open>Bot\<close>, so a dead point reads as dead; the publication
  map \<open>rd\<close> then turns the carrier into the value the table publishes. Coverage is
  separate from deadness: a key the solver never visited is absent from the
  table, and \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Bot\<close> for it without any
  claim about the program.
\<close>

text \<open>
  \<open>sol\<close> is the already-solved pair, not the solve function. Passing the pair keeps
  one solve per table in generated code -- the argument is evaluated once and the
  per-point closure captures it -- which is why no analysis needs a separate
  \<open>[code]\<close> equation with an explicit \<open>let\<close>.
\<close>

definition dg_result_for ::
    "('s \<Rightarrow> 'v) \<Rightarrow> ('s \<Rightarrow> bool)
     \<Rightarrow> (pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 'g) dg_state)
     \<Rightarrow> ('c, 'v) analysis_result" where
  "dg_result_for rd emp sol =
     Analysis_Result (fst sol)
       (\<lambda>v ctx. map_lift rd (canonicalize_lift emp (dg_local (snd sol (Inl (v, ctx))))))"

lemma result_unknowns_dg_result_for [simp]:
  "result_unknowns (dg_result_for rd emp sol) = fst sol"
  unfolding dg_result_for_def by simp

text \<open>
  The one fact every soundness bridge needs about the table: a covered key reads
  back the normalized local unknown, an uncovered one answers \<^const>\<open>Bot\<close>.
\<close>

lemma lookup_context_dg_result_for [simp]:
  "lookup_context (dg_result_for rd emp sol) v ctx
     = (if (v, ctx) \<in> fst sol
        then map_lift rd (canonicalize_lift emp (dg_local (snd sol (Inl (v, ctx)))))
        else Bot)"
  unfolding dg_result_for_def lookup_context_def by simp

text \<open>
  Normalizing before publication agrees with normalizing after it whenever the
  two emptiness tests agree, so a soundness bridge stated after publication
  applies to the table built before it.
\<close>

lemma map_lift_canonicalize_lift:
  assumes "\<And>s. emp s = empty\<^sub>V (rd s)"
  shows "map_lift rd (canonicalize_lift emp d) = canonicalize_lift empty\<^sub>V (map_lift rd d)"
  by (cases d) (simp_all add: assms normalize_lift_def)

lemma lookup_context_dg_result_for_projected:
  assumes "\<And>s. emp s = empty\<^sub>V (rd s)"
  shows "lookup_context (dg_result_for rd emp sol) v ctx =
    (if (v, ctx) \<in> fst sol
     then canonicalize_lift empty\<^sub>V (map_lift rd (dg_local (snd sol (Inl (v, ctx)))))
     else Bot)"
  using map_lift_canonicalize_lift[of emp "empty\<^sub>V" rd] assms by simp

text \<open>Collapsing a payload that denotes nothing to \<^const>\<open>Bot\<close> does not change
  what the value denotes.\<close>

lemma gamma_lift_canonicalize_lift:
  assumes "\<And>v. empty\<^sub>V v \<Longrightarrow> gm v = {}"
  shows "gamma_lift gm (canonicalize_lift empty\<^sub>V x) = gamma_lift gm x"
  by (cases x) (simp_all add: normalize_lift_def assms)

end
