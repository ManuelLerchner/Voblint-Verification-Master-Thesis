theory DG_Result_Construction
  imports
    "Voblint_Framework.DG_Analysis_Adapter"
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Exec.Exec_DG_State"
begin

section \<open>What a solved D/G system publishes\<close>

text \<open>
  Every analysis, at every context policy and every solver discipline, turns the
  solver's answer -- a covered key set and a map from unknowns to \<open>dg_state\<close>s over
  its carrier -- into an \<^type>\<open>solved_table\<close> table of the locals. This
  theory states that construction once, over an arbitrary solved pair, so an
  analysis's result table is one application rather than a rewritten body.

  Publishing a local unknown means two steps in sequence.
  \<^const>\<open>canonicalize_lift\<close> collapses a stored \<^const>\<open>Lifted\<close> payload that
  describes no store to \<^const>\<open>Bot\<close>, so a dead point reads as dead; the publication
  map \<open>rd\<close> then turns the carrier into the value the table publishes. Coverage is
  separate from deadness: a key the solver never visited is absent from the
  table, and \<^const>\<open>lookup_table\<close> answers \<^const>\<open>Bot\<close> for it without any
  claim about the program.
\<close>

text \<open>
  \<open>sol\<close> is the already-solved pair, not the solve function. Passing the pair keeps
  one solve per table in generated code -- the argument is evaluated once and the
  per-point closure captures it -- which is why no analysis needs a separate
  \<open>[code]\<close> equation with an explicit \<open>let\<close>.

  What a point publishes is read off its local unknown together with the solved
  global environment, each name read at its key \<open>Inr (gk n)\<close>: \<open>rc\<close> recombines
  the local half with that environment into the state the point describes. An analysis that keeps every variable in the local half passes a
  recombination that ignores the global.
\<close>

definition dg_result_for ::
    "('s \<Rightarrow> 'v) \<Rightarrow> ('s \<Rightarrow> bool) \<Rightarrow> ('s lifted \<Rightarrow> ('n \<Rightarrow> 'g) \<Rightarrow> 's lifted) \<Rightarrow> ('n \<Rightarrow> 'k)
     \<Rightarrow> (pp \<times> 'c) set \<times> (pp \<times> 'c + 'k \<Rightarrow> ('s lifted, 'g) dg_state)
     \<Rightarrow> ('c, 'v) solved_table" where
  "dg_result_for rd emp rc gk sol =
     Solved_Table (fst sol)
       (\<lambda>v ctx. map_lift rd (canonicalize_lift emp
          (rc (dg_local (snd sol (Inl (v, ctx)))) (genv gk (snd sol)))))"

lemma covered_keys_dg_result_for [simp]:
  "covered_keys (dg_result_for rd emp rc gk sol) = fst sol"
  unfolding dg_result_for_def by simp

text \<open>
  The one fact every soundness bridge needs about the table: a covered key reads
  back the normalized recombined state, an uncovered one answers \<^const>\<open>Bot\<close>.
\<close>

lemma lookup_table_dg_result_for [simp]:
  "lookup_table (dg_result_for rd emp rc gk sol) v ctx
     = (if (v, ctx) \<in> fst sol
        then map_lift rd (canonicalize_lift emp
               (rc (dg_local (snd sol (Inl (v, ctx)))) (genv gk (snd sol))))
        else Bot)"
  unfolding dg_result_for_def lookup_table_def by simp

text \<open>
  Normalizing before publication agrees with normalizing after it whenever the
  two emptiness tests agree, so a soundness bridge stated after publication
  applies to the table built before it.
\<close>

lemma map_lift_canonicalize_lift:
  assumes "\<And>s. emp s = empty\<^sub>V (rd s)"
  shows "map_lift rd (canonicalize_lift emp d) = canonicalize_lift empty\<^sub>V (map_lift rd d)"
  by (cases d) (simp_all add: assms normalize_lift_def)

text \<open>Collapsing a payload that denotes nothing to \<^const>\<open>Bot\<close> does not change
  what the value denotes.\<close>

lemma gamma_lift_canonicalize_lift:
  assumes "\<And>v. empty\<^sub>V v \<Longrightarrow> gm v = {}"
  shows "gamma_lift gm (canonicalize_lift empty\<^sub>V x) = gamma_lift gm x"
  by (cases x) (simp_all add: normalize_lift_def assms)

end
