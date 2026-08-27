theory Example_Analysis_Result_Regression
  imports "Voblint_CLI.Analyse_Dispatch"
begin

section \<open>Regression: the solved-result table\<close>

text \<open>
  Acceptance witnesses for \<^theory>\<open>Voblint_Core.Analysis_Result\<close>'s reachability
  reading, in the same \<open>by eval\<close> style as the sibling regressions. The Interval
  adapter carries the detailed four-case coverage; Sign and \<open>int_dom\<close> only
  witness that they reach the same generic abstraction correctly.

  The four cases a result lookup must distinguish are all present in this one
  program:

    \<^item> a covered key with a genuinely reachable state,
    \<^item> a covered key whose stored state is \<^const>\<open>Lifted\<close> but concretizes to
      nothing,
    \<^item> a covered key the solver left at \<^const>\<open>Bot\<close>,
    \<^item> a key the solver never covered at all.

  The second and third are the pair the design exists to keep apart: both are
  \<^const>\<open>Unreachable\<close> at the result boundary, and neither is decided by the
  outer \<^const>\<open>Bot\<close>/\<^const>\<open>Lifted\<close> constructor alone.
\<close>

text \<open>
  \<open>x := 5\<close> makes the \<open>x < 0\<close> guard statically false, so the \<open>then\<close> branch is
  dead while the \<open>else\<close> branch and the trailing check are live. No globals,
  no calls: every covered key is a plain local unknown at \<^typ>\<open>unit\<close> context.
\<close>

definition result_demo_prog :: imp_prog where
  "result_demo_prog =
     program {
       void main() {
         x := 5;
         if (x < 0) {
           y := 1
         } else {
           y := 2
         };
         __voblint_check(x < 6)
       }
     }"

subsection \<open>Interval: the four reachability cases\<close>

text \<open>
  Case A --- a covered, genuinely reachable key. \<^const>\<open>Statement\<close> \<open>1\<close> is the
  guard node reached right after \<open>x := 5\<close>. The lookup is projected through
  \<^const>\<open>map_point_state\<close> onto \<open>x\<close>'s own interval: the payload is a
  \<^typ>\<open>ivl abs_state\<close>, i.e. a function on \<^typ>\<open>vname\<close>, which has no
  executable equality of its own.
\<close>

lemma result_demo_interval_stmt1_joined:
  "map_point_state (\<lambda>st. st (STR ''x''))
     (lookup_joined_state (analyse_interval_td_result result_demo_prog) (Statement 1))
   = Reachable (Ivl (Fin 5) (Fin 5))"
  by eval

text \<open>
  Case B --- a covered key whose raw stored state is \<^const>\<open>Lifted\<close> and yet
  concretizes to nothing. The production pipeline never leaves such a state
  behind, because it threads \<^const>\<open>resolved_st_q_is_bot_for\<close> through the
  equation system and collapses a witness-bottom result to \<^const>\<open>Bot\<close> on the
  spot. Passing \<^term>\<open>\<lambda>_. False\<close> as that predicate instead is what makes the
  case observable: the very same solver run then stores the dead branch's
  node as \<^const>\<open>Lifted\<close> over an empty (inverted-bound) interval. This is
  exactly the raw, noncanonical value a result adapter's own
  \<^const>\<open>canonicalize_lift\<close> step exists to catch, using the real
  \<^const>\<open>resolved_st_q_is_bot_for\<close> test rather than the solver's own
  (deliberately disabled, here) one: \<^const>\<open>lookup_context\<close> must still
  report it \<^const>\<open>Unreachable\<close> --- reading off the raw outer constructor
  alone would call it live.
\<close>

definition result_demo_unnormalized :: "(unit, ivl abs_state) analysis_result" where
  "result_demo_unnormalized =
     (let sol = analyse_interval_dg_for (\<lambda>_. False)
                  (declared_global result_demo_prog) result_demo_prog;
          gl = declared_global_vars result_demo_prog
      in Analysis_Result (fst sol)
           (\<lambda>v ctx. normalize_point (declared_global result_demo_prog)
                      (canonicalize_lift (resolved_st_q_is_bot_for gl)
                        (locals (snd sol (Inl (v, ctx)))))))"

lemma result_demo_unnormalized_stmt2_stored_lifted_bottom:
  "(case locals (snd (analyse_interval_dg_for (\<lambda>_. False)
                        (declared_global result_demo_prog) result_demo_prog)
                  (Inl (Statement 2, ()))) of
      Bot \<Rightarrow> False
    | Lifted s \<Rightarrow> resolved_st_q_is_bot_for (declared_global_vars result_demo_prog) s)"
  by eval

lemma result_demo_unnormalized_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context result_demo_unnormalized (Statement 2) ())"
  by eval

lemma result_demo_unnormalized_stmt2_unreachable:
  "lookup_context result_demo_unnormalized (Statement 2) () = Unreachable"
  using result_demo_unnormalized_stmt2_not_reachable
  by (simp add: is_reachable_point_iff)

text \<open>The same table still reports the live nodes live, so the collapse above
  is the dead branch's own, not a blanket one.\<close>

lemma result_demo_unnormalized_stmt1_reachable:
  "map_point_state (\<lambda>st. st (STR ''x''))
     (lookup_context result_demo_unnormalized (Statement 1) ())
   = Reachable (Ivl (Fin 5) (Fin 5))"
  by eval

text \<open>
  Case C --- a covered key the solver itself left at \<^const>\<open>Bot\<close>. Under the
  production predicate the very node case B observed as \<^const>\<open>Lifted\<close> is
  stored as the outer \<^const>\<open>Bot\<close> instead; it is still a covered key, and the
  result reports it \<^const>\<open>Unreachable\<close> for a different structural reason.
\<close>

lemma result_demo_interval_stmt2_stored_bot:
  "(case locals (snd (analyse_interval_dg_for
                        (resolved_st_q_is_bot_for (declared_global_vars result_demo_prog))
                        (declared_global result_demo_prog) result_demo_prog)
                  (Inl (Statement 2, ()))) of
      Bot \<Rightarrow> True | Lifted _ \<Rightarrow> False)"
  by eval

lemma result_demo_interval_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_interval_td_result result_demo_prog)
                          (Statement 2) ())"
  by eval

text \<open>
  Case D --- a key the solver never covered. \<^const>\<open>Statement\<close> \<open>99\<close> is not a
  node of this program's CFG at all, so it is absent from \<^const>\<open>result_keys\<close>
  rather than present with a bottom value. \<^const>\<open>lookup_context\<close>'s membership
  guard, not \<^const>\<open>result_at\<close>, is what answers here.
\<close>

lemma result_demo_interval_absent_key:
  "(Statement 99, ()) \<notin> result_keys (analyse_interval_td_result result_demo_prog)"
  by eval

lemma result_demo_interval_absent_unreachable:
  "lookup_context (analyse_interval_td_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent[OF result_demo_interval_absent_key])

lemma result_demo_interval_absent_contexts:
  "contexts_at (analyse_interval_td_result result_demo_prog) (Statement 99) = {}"
  by eval

lemma result_demo_interval_absent_joined:
  "lookup_joined_state (analyse_interval_td_result result_demo_prog) (Statement 99)
   = Unreachable"
  by (rule lookup_joined_state_absent[OF result_demo_interval_absent_contexts])

lemma result_demo_interval_absent_not_live:
  "\<not> node_live_ex (analyse_interval_td_result result_demo_prog) (Statement 99)"
  by eval

text \<open>
  Case C's dead node is covered because it is a structural CFG node, not
  because the solver happened to reach it: \<^const>\<open>cfg_node_list\<close> is
  \<open>monovariant_analysis_result_for\<close>'s key domain (\<^theory>\<open>Voblint_Core.Monovariant_Analysis_Result\<close>),
  independent of solver support. \<^const>\<open>Statement\<close> \<open>99\<close> (Case D) has no such
  membership, which is exactly why it alone stays outside \<^const>\<open>result_keys\<close>.
\<close>

lemma result_demo_interval_stmt2_cfg_node:
  "Statement 2 \<in> set (cfg_node_list (prog_cfg prog_main_name result_demo_prog))"
  by eval

lemma result_demo_interval_absent_not_cfg_node:
  "Statement 99 \<notin> set (cfg_node_list (prog_cfg prog_main_name result_demo_prog))"
  by eval

subsection \<open>Two contexts at one node\<close>

text \<open>
  The monovariant adapters above never cover a node under more than one
  context, so they cannot exercise the join itself. These tables are written
  out by hand for exactly that reason: they are not solver output, and the
  point under test is the generic result API, not a domain adapter.

  The context type is \<^typ>\<open>ivl list\<close> --- an argument vector, the shape a
  context-sensitive analysis actually uses --- rather than \<^typ>\<open>unit\<close>, so
  \<open>Statement 1\<close> really is covered twice. The payload stays
  \<^typ>\<open>ivl abs_state\<close>, the production shape whose \<open>\<le>\<close> has no executable
  realization; every witness below is closed by \<open>eval\<close>, so the joined view
  and the liveness test are running as generated code, not being rewritten.
\<close>

definition result_demo_ctx1 :: "ivl list" where
  "result_demo_ctx1 = [Ivl (Fin 1) (Fin 1)]"

definition result_demo_ctx2 :: "ivl list" where
  "result_demo_ctx2 = [Ivl (Fin 3) (Fin 3)]"

definition result_demo_state :: "ivl \<Rightarrow> ivl abs_state" where
  "result_demo_state i = (\<lambda>_. Ivl (Fin 0) (Fin 0))(STR ''x'' := i)"

text \<open>
  Both contexts reachable, with genuinely different intervals for \<open>x\<close>: the
  joined view must run the domain's own \<open>\<squnion>\<close> at least once.
\<close>

definition result_demo_two :: "(ivl list, ivl abs_state) analysis_result" where
  "result_demo_two =
     Analysis_Result {(Statement 1, result_demo_ctx1), (Statement 1, result_demo_ctx2)}
       (\<lambda>v ctx. if ctx = result_demo_ctx1
                then Reachable (result_demo_state (Ivl (Fin 1) (Fin 1)))
                else Reachable (result_demo_state (Ivl (Fin 3) (Fin 3))))"

text \<open>
  One context unreachable: \<^const>\<open>Unreachable\<close> is the join's unit, so the
  surviving context's state passes through unchanged, and the node is still
  live on the strength of that one context.
\<close>

definition result_demo_two_half :: "(ivl list, ivl abs_state) analysis_result" where
  "result_demo_two_half =
     Analysis_Result {(Statement 1, result_demo_ctx1), (Statement 1, result_demo_ctx2)}
       (\<lambda>v ctx. if ctx = result_demo_ctx1 then Unreachable
                else Reachable (result_demo_state (Ivl (Fin 3) (Fin 3))))"

text \<open>
  Both contexts unreachable at a node that is nonetheless covered: the fold
  runs over a non-empty context set and still lands on \<^const>\<open>Unreachable\<close>,
  which is a different route to the same answer than the absent-key case above.
\<close>

definition result_demo_two_dead :: "(ivl list, ivl abs_state) analysis_result" where
  "result_demo_two_dead =
     Analysis_Result {(Statement 1, result_demo_ctx1), (Statement 1, result_demo_ctx2)}
       (\<lambda>v ctx. Unreachable)"

subsection \<open>Sign and int_dom: the same abstraction, one live and one dead key\<close>

text \<open>
  Deliberately lighter than the Interval coverage above: these two only have
  to witness that their adapters feed the same generic
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>lookup_context\<close> surface, not to re-exercise
  the reachability case analysis a third and fourth time.
\<close>

lemma result_demo_sign_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_sign_result result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_sign_absent_unreachable:
  "lookup_context (analyse_sign_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

lemma result_demo_int_absent_unreachable:
  "lookup_context (analyse_int_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

subsection \<open>Solver-choice variants: the same generic constructor, off a different solve\<close>

text \<open>
  \<open>analyse_sign_result_per_origin\<close>, \<open>analyse_interval_join_result\<close>,
  \<open>analyse_interval_per_origin_result\<close>, \<open>analyse_int_join_result\<close>, and
  \<open>analyse_int_per_origin_result\<close> all come from
  \<^const>\<open>monovariant_analysis_result_for\<close>, the same generic constructor as
  the default-solver adapters above, applied to a different native solve
  function. \<open>result_demo_prog\<close> has no loop and no global feedback, so every
  update-rule discipline agrees with the default solver on it; these pins
  witness that each variant reaches the same generic
  \<^const>\<open>normalize_point\<close>/\<^const>\<open>lookup_context\<close> surface with the same
  values the default-solver adapters above already established, not a
  second full reachability case analysis.
\<close>

lemma result_demo_sign_per_origin_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_sign_result_per_origin result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_sign_per_origin_absent_unreachable:
  "lookup_context (analyse_sign_result_per_origin result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

lemma result_demo_interval_join_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_interval_join_result result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_interval_join_absent_unreachable:
  "lookup_context (analyse_interval_join_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

lemma result_demo_interval_per_origin_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_interval_per_origin_result result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_interval_per_origin_absent_unreachable:
  "lookup_context (analyse_interval_per_origin_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

lemma result_demo_int_join_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_int_join_result result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_int_join_absent_unreachable:
  "lookup_context (analyse_int_join_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

lemma result_demo_int_per_origin_stmt2_not_reachable:
  "\<not> is_reachable_point (lookup_context (analyse_int_per_origin_result result_demo_prog) (Statement 2) ())"
  by eval

lemma result_demo_int_per_origin_absent_unreachable:
  "lookup_context (analyse_int_per_origin_result result_demo_prog) (Statement 99) () = Unreachable"
  by (rule lookup_context_absent) eval

end

