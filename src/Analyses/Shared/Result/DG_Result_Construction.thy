theory DG_Result_Construction
  imports
    "Voblint_Framework.Analysis_Result"
    "Voblint_Framework.DG_Analysis_Adapter"
    "Voblint_Framework.Seed_Global_Keys"
    "Voblint_Exec.Exec_Result_Readback"
    "Voblint_Exec.Exec_DG_State"
    "Voblint_Exec.Exec_St_Reachability"
begin

section \<open>What a solved D/G system publishes\<close>

text \<open>
  Every domain, at every context policy and every solver discipline, turns the
  solver's answer -- a covered key set and a map from unknowns to \<open>dg_state\<close>s over
  the executable carrier -- into the same two things: an \<^type>\<open>analysis_result\<close>
  table of the locals, and the list of global unknowns beside it. This theory
  states both constructions once, over an arbitrary solved pair, so a domain's
  result table is one application rather than a rewritten body.

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

text \<open>
  The whole-state reader of a solve whose local unknown already carries the entire
  abstract state: no key set, no canonicalization, just the projected state at a unit
  context point, with an unreached (\<^const>\<open>Bot\<close>) unknown read as \<^const>\<open>bot\<close>. It
  differs from \<^const>\<open>dg_result_for\<close> in skipping \<^const>\<open>canonicalize_lift\<close>, so a
  witness-bottom \<^const>\<open>Lifted\<close> payload reads back as its (empty) state rather than
  as \<^const>\<open>bot\<close>; the routes that use it publish no soundness theorem and serve
  executable witnesses only. Stated over \<open>sigma\<close> alone so an instance applied to the
  solved map, point-free in \<open>v\<close>, solves once and reads many times.
\<close>

definition dg_env_for ::
    "(vname \<Rightarrow> bool)
     \<Rightarrow> (pp \<times> unit + 'k \<Rightarrow> (('a::order_bot) exec_dg_st lifted, 'g) dg_state)
     \<Rightarrow> pp \<Rightarrow> 'a abs_state" where
  "dg_env_for gs sigma v =
     (case map_lift (fun_of_exec_dg_st_for gs) (locals (sigma (Inl (v, ())))) of
        Bot \<Rightarrow> bot | Lifted s \<Rightarrow> s)"

definition dg_globals_for ::
    "(vname \<Rightarrow> bool) \<Rightarrow> vname list
     \<Rightarrow> (pp \<times> 'c + 'k \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state)
     \<Rightarrow> ('k \<times> String.literal
          \<times> (('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state \<Rightarrow> 'a exec_dg_st lifted)) list
     \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list" where
  "dg_globals_for gs gl sigma keys =
     map (\<lambda>(k, label, payload).
            (label,
             readback_result_value gs
               (canonicalize_lift (resolved_st_q_is_bot_for gl) (payload (sigma (Inr k))))))
         keys"

text \<open>
  Both halves of one routed unit-context solve: the locals table every check report
  already reads, and the globals beside it. \<open>solve\<close> is a parameter because which
  solver discipline produced the pair is an application-site choice, so each
  domain's instance is a partial application rather than another copy of this body.

  Binding \<open>sol\<close> once is what keeps a report that shows both halves from solving twice.
\<close>

definition ctx_solved_for ::
    "((vname \<Rightarrow> bool) \<Rightarrow> imp_prog
        \<Rightarrow> (pp \<times> unit) set
             \<times> (pp \<times> unit + 'k
                  \<Rightarrow> ('a::executable_domain exec_dg_st lifted, 'a exec_dg_st lifted) dg_state))
     \<Rightarrow> (imp_prog
          \<Rightarrow> ('k \<times> String.literal
                \<times> (('a exec_dg_st lifted, 'a exec_dg_st lifted) dg_state
                     \<Rightarrow> 'a exec_dg_st lifted)) list)
     \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> imp_prog
     \<Rightarrow> (unit, 'a abs_state) analysis_result
          \<times> (String.literal \<times> 'a abs_state lifted) list" where
  "ctx_solved_for solve keys gs p =
     (let sol = solve gs p; gl = declared_global_vars p
      in (dg_result_for gs gl sol, dg_globals_for gs gl (snd sol) (keys p)))"

text \<open>The locals half is the domain's own result table, so publishing the globals
  beside it adds a column and changes no verdict.\<close>

lemma fst_ctx_solved_for:
  "fst (ctx_solved_for solve keys gs p)
     = dg_result_for gs (declared_global_vars p) (solve gs p)"
  by (simp add: ctx_solved_for_def Let_def)

end
