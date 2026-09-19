theory DG_Result_Construction
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.DG_Analysis_Adapter"
    "Voblint_Framework.Routed_Call_Programs"
    "Voblint_Framework.CFG_Enumeration"
    "Voblint_VIMP.VIMP_Program"
    "Voblint_Exec.Exec_Result_Readback"
    "Voblint_Exec.Exec_DG_State"
    "Voblint_Exec.Exec_St_Reachability"
begin

section \<open>What a solved D/G system publishes\<close>

text \<open>
  Every domain, at every context policy and every solver discipline, turns the
  solver's answer -- a covered key set and a map from unknowns to \<open>dg_state\<close>s over
  the executable carrier -- into an \<^type>\<open>analysis_result\<close> table of the locals.
  This theory states that construction once, over an arbitrary solved pair, so a
  domain's result table is one application rather than a rewritten body.

  Reading a local unknown back means two normalizations in sequence.
  \<^const>\<open>canonicalize_lift\<close> collapses a stored \<^const>\<open>Lifted\<close> payload that is
  bottom in every declared slot to \<^const>\<open>Bot\<close>, so a dead point reads as dead;
  \<^const>\<open>readback_result_value\<close> then projects the association-list carrier to
  the function-valued state the soundness theorems are stated over. Coverage is
  separate from deadness: a key the solver never visited is absent from the
  table, and \<^const>\<open>lookup_context\<close> answers \<^const>\<open>Bot\<close> for it without any
  claim about the program.
\<close>

text \<open>
  \<open>sol\<close> is the already-solved pair, not the solve function. Passing the pair keeps
  one solve per table in generated code -- the argument is evaluated once and the
  per-point closure captures it -- which is why no domain needs a separate
  \<open>[code]\<close> equation with an explicit \<open>let\<close> any more.
\<close>

definition dg_result_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname list
     \<Rightarrow> (pp \<times> 'c) set
          \<times> (pp \<times> 'c + 'k
               \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)
     \<Rightarrow> ('c, 'a abs_state) analysis_result" where
  "dg_result_for gs gl sol =
     Analysis_Result (fst sol)
       (\<lambda>v ctx. readback_result_value gs
                  (canonicalize_lift (resolved_st_q_is_bot_for gl)
                    (locals (snd sol (Inl (v, ctx))))))"

lemma result_keys_dg_result_for [simp]:
  "result_keys (dg_result_for gs gl sol) = fst sol"
  unfolding dg_result_for_def by simp

text \<open>
  The one fact every soundness bridge needs about the table: a covered key reads
  back the normalized local unknown, an uncovered one answers \<^const>\<open>Bot\<close>.
\<close>

lemma lookup_context_dg_result_for [simp]:
  "lookup_context (dg_result_for gs gl sol) v ctx
     = (if (v, ctx) \<in> fst sol
        then readback_result_value gs
               (canonicalize_lift (resolved_st_q_is_bot_for gl)
                 (locals (snd sol (Inl (v, ctx)))))
        else Bot)"
  unfolding dg_result_for_def lookup_context_def by simp

text \<open>
  Soundness bridges normalize after projecting to the function-valued state. The
  following commutation fact keeps that representation argument in one place; each
  adapter interpretation still supplies the assumptions that connect its result
  table to collecting semantics.
\<close>

lemma readback_canonicalize_lift_eq:
  assumes "\<And>s. empty_pred s = is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "readback_result_value gs (canonicalize_lift empty_pred d)
       = canonicalize_lift is_empty_state (map_lift (fun_of_resolved_st_q_for gs) d)"
  by (cases d) (simp_all add: assms normalize_lift_def)

lemma lookup_context_dg_result_for_projected:
  fixes sol :: "(pp \<times> 'c) set
    \<times> (pp \<times> 'c + 'k \<Rightarrow>
      ('a::executable_domain exec_dg_st lifted,
       'a exec_dg_st lifted) dg_state)"
  assumes exact:
    "\<And>s :: 'a::executable_domain exec_dg_st.
      resolved_st_q_is_bot_for gl s =
      is_empty_state (fun_of_resolved_st_q_for gs s)"
  shows "lookup_context (dg_result_for gs gl sol) v ctx =
    (if (v, ctx) \<in> fst sol
     then canonicalize_lift is_empty_state
       (map_lift (fun_of_resolved_st_q_for gs)
         (locals (snd sol (Inl (v, ctx)))))
     else Bot)"
proof -
  have commute:
    "readback_result_value gs
        (canonicalize_lift (resolved_st_q_is_bot_for gl) d) =
      canonicalize_lift is_empty_state
        (map_lift (fun_of_resolved_st_q_for gs) d)"
    for d :: "'a exec_dg_st lifted"
    by (rule readback_canonicalize_lift_eq[OF exact])
  show ?thesis
  proof (cases "(v, ctx) \<in> fst sol")
    case False
    then show ?thesis unfolding lookup_context_dg_result_for by simp
  next
    case True
    have commute_at:
      "readback_result_value gs
          (canonicalize_lift (resolved_st_q_is_bot_for gl)
            (locals (snd sol (Inl (v, ctx))))) =
        canonicalize_lift is_empty_state
          (map_lift (fun_of_resolved_st_q_for gs)
            (locals (snd sol (Inl (v, ctx)))))"
    proof (cases "locals (snd sol (Inl (v, ctx)))")
      case Bot
      then show ?thesis by simp
    next
      case (Lifted s)
      have eq: "resolved_st_q_is_bot_for gl s =
          is_empty_state (fun_of_resolved_st_q_for gs s)"
        by (rule exact[of s])
      show ?thesis unfolding Lifted using eq by (simp add: normalize_lift_def)
    qed
    with True show ?thesis unfolding lookup_context_dg_result_for by simp
  qed
qed

end
