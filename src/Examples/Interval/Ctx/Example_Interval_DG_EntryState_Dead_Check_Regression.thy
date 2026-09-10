theory Example_Interval_DG_EntryState_Dead_Check_Regression
  imports
    "Voblint_Analysis_Interval.Interval_Analyses"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: dead checks under entry-state context sensitivity\<close>

text \<open>
  Acceptance witnesses for the contextual check report. Three programs cover
  the three shapes a check node can take once contexts are kept apart:

    \<^item> every covered context is unreachable, so the check is \<^const>\<open>Dead\<close> and
      no verdict may be reported for it at all;
    \<^item> some contexts are unreachable and one is not, so the dead ones drop out
      of the join and the live one's verdict survives;
    \<^item> two live contexts decide the same condition differently, so the join
      collapses to \<^term>\<open>Decided Check_Unknown\<close>.

  The first is the case a solver-level reading gets wrong: an unreachable
  point's stored abstract state is bottom, bottom satisfies every condition
  vacuously, and the check then reports \<^const>\<open>Check_Proved\<close> for code no
  execution reaches. \<^const>\<open>classify_point\<close> declines to classify against
  \<^const>\<open>Bot\<close> at all, which is what these witnesses pin.
\<close>

subsection \<open>Reading one check's contextual observations\<close>

text \<open>The projection is one entry per source check, so selecting a check node
  selects at most one entry; a node with no check has no observations.\<close>

definition observations_at ::
    "(pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list \<Rightarrow> pp
       \<Rightarrow> (ivl list \<times> contextual_verdict) set" where
  "observations_at rs v =
     (case filter (\<lambda>(u, cnd, vs). u = v) rs of [] \<Rightarrow> {} | e # _ \<Rightarrow> snd (snd e))"

subsection \<open>A check no execution reaches\<close>

text \<open>\<open>x\<close> is exactly \<open>5\<close>, so the \<open>x < 2\<close> branch is unreachable and its check
  is covered under one context, \<open>[]\<close>, which is dead there.\<close>

definition dead_check_prog :: imp_prog where
  "dead_check_prog = program {
     void main() {
       x := 5;
       if (x < 2) {
         __voblint_check(x == 99)
       } else {
         __voblint_check(x == 5)
       }
     }
   }"

definition mixed_ctx_prog :: imp_prog where
  "mixed_ctx_prog = program {
     void f(n) {
       if (n < 2) {
         __voblint_check(n == 1);
         return 1
       } else {
         r := f(n - 1);
         return n * r
       }
     }
     void main() {
       a := f(3);
       __voblint_check(a == 6)
     }
   }"

definition disagree_prog :: imp_prog where
  "disagree_prog = program {
     void g(n) {
       __voblint_check(n < 3);
       return n
     }
     void main() {
       a := g(1);
       b := g(5)
     }
   }"

abbreviation dead_check_projection ::
    "(pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "dead_check_projection \<equiv> entry_state_check_projection dead_check_prog"

text \<open>The unreachable branch's check is covered -- the solver reached the node
  under the caller's own context -- and dead there. Both facts matter: this is
  not the never-covered case a membership guard would answer, it is a covered
  key whose stored state concretizes to nothing.\<close>

lemma dead_check_observations:
  "observations_at dead_check_projection (Statement 2) = {([], Dead)}"
  by eval

lemma dead_check_is_dead:
  "check_dead (observations_at dead_check_projection (Statement 2))"
  by eval

lemma dead_check_aggregate_dead:
  "aggregate_verdicts (snd ` observations_at dead_check_projection (Statement 2)) = Dead"
  by eval

text \<open>The reachable sibling branch in the same program is unaffected, so the
  dead case is not suppressing live checks.\<close>

lemma dead_check_live_sibling:
  "observations_at dead_check_projection (Statement 3) = {([], Decided Check_Proved)}"
  by eval

lemma dead_check_analyse_interval_entry_state:
  "analyse_interval_entry_state dead_check_prog =
     [(Statement 2, exp.Eq (V (STR ''x'')) (exp.N 99), Dead),
      (Statement 3, exp.Eq (V (STR ''x'')) (exp.N 5), Decided Check_Proved)]"
  by eval

subsection \<open>A check dead in some activations and live in another\<close>

text \<open>
  \<^const>\<open>mixed_ctx_prog\<close>'s base-case check sits inside \<open>f\<close>'s \<open>n < 2\<close> branch,
  which is structurally unreachable in every \<open>n >= 2\<close> activation and taken in
  the innermost one. The node therefore carries dead and live observations at
  once, and the source-level verdict must come from the live one alone.
\<close>

abbreviation mixed_ctx_projection ::
    "(pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "mixed_ctx_projection \<equiv> entry_state_check_projection mixed_ctx_prog"

text \<open>Three contexts reach the base-case check: the two outer activations
  (\<open>n = 3\<close>, \<open>n = 2\<close>) where the branch is dead, and the innermost one (\<open>n = 1\<close>)
  where it is taken. The innermost activation's own recursive call would enter
  with an empty interval, but a \<^const>\<open>bot\<close> entry is dropped at the call
  boundary, so no context is seeded for it and it contributes no observation.\<close>

lemma mixed_ctx_observations:
  "observations_at mixed_ctx_projection (Statement 1) =
     {([Ivl (Fin 1) (Fin 1)], Decided Check_Proved),
      ([Ivl (Fin 2) (Fin 2)], Dead),
      ([Ivl (Fin 3) (Fin 3)], Dead)}"
  by eval

lemma mixed_ctx_not_dead:
  "\<not> check_dead (observations_at mixed_ctx_projection (Statement 1))"
  by eval

text \<open>The aggregate is the live context's own verdict. Joining the dead
  contexts in as \<^typ>\<open>check_result\<close> values instead would have to pick some
  value for them, and every choice is wrong: \<^const>\<open>Check_Proved\<close> would
  reassert the fabricated verdict, \<^const>\<open>Check_Unknown\<close> would destroy the
  live context's decision.\<close>

lemma mixed_ctx_aggregate_from_live_context:
  "aggregate_verdicts (snd ` observations_at mixed_ctx_projection (Statement 1))
     = Decided Check_Proved"
  by eval

lemma mixed_ctx_analyse_interval_entry_state:
  "analyse_interval_entry_state mixed_ctx_prog =
     [(Statement 1, exp.Eq (V (STR ''n'')) (exp.N 1), Decided Check_Proved),
      (Statement 7, exp.Eq (V (STR ''a'')) (exp.N 6), Decided Check_Proved)]"
  by eval

subsection \<open>Two live contexts that disagree\<close>

text \<open>\<open>g\<close> is called at \<open>1\<close> and at \<open>5\<close>, so its single check is exactly decided
  in each activation and decided differently. The per-context projection keeps
  both decisions; only the aggregate collapses.\<close>

abbreviation disagree_projection ::
    "(pp \<times> exp \<times> (ivl list \<times> contextual_verdict) set) list" where
  "disagree_projection \<equiv> entry_state_check_projection disagree_prog"

lemma disagree_observations_retained:
  "observations_at disagree_projection (Statement 0) =
     {([Ivl (Fin 1) (Fin 1)], Decided Check_Proved),
      ([Ivl (Fin 5) (Fin 5)], Decided Check_Refuted)}"
  by eval

lemma disagree_aggregate_unknown:
  "aggregate_verdicts (snd ` observations_at disagree_projection (Statement 0))
     = Decided Check_Unknown"
  by eval

lemma disagree_analyse_interval_entry_state:
  "analyse_interval_entry_state disagree_prog =
     [(Statement 0, Less (V (STR ''n'')) (exp.N 3), Decided Check_Unknown)]"
  by eval

end
