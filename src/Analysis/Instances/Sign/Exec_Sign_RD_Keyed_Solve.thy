theory Exec_Sign_RD_Keyed_Solve
  imports Exec_Sign_RD_Keyed_Run Exec_Sign_Run
begin

section \<open>Reaching-definition global reads: executable solver run (sign)\<close>

text \<open>
  The executable counterpart of \<open>Exec_Sign_RD_Keyed_Run\<close>.  There the def-site-keyed
  post-solution \<^const>\<open>rd_sig\<close> is exhibited by hand and \<open>CMP_SOUND\<close> is discharged
  against it.  Here the same flat callee-writes abstraction (\<section>7/\<section>8) is written as a
  genuine side-effecting equation system whose global writes are routed to
  \<^emph>\<open>definition-site\<close> slots \<^term>\<open>Inr DS1\<close> / \<^term>\<open>Inr DS3\<close>, and handed to the vendored
  \<^const>\<open>TD_side_always_join_Interp_solve\<close>.  The solver computes the def-site routing;
  the separated slots are read back by the code generator, and the
  reaching-definition read (\<^const>\<open>glob_env_cmp\<close> filtered by the reaching set) recovers
  the point-sensitive value under a \<^emph>\<open>single call-only context\<close> --- \<^const>\<open>SZero\<close> at the
  call, \<^const>\<open>SPos\<close> at the return, where the context-blind join-all merges to
  \<^const>\<open>SNonNeg\<close>.
\<close>

subsection \<open>The def-site-keyed side-effecting equation system\<close>

text \<open>
  Program points of the flat program: \<open>RMain\<close> assigns \<open>G := 0\<close> (its own def-site
  \<^const>\<open>DS1\<close>) then calls \<open>f\<close>; \<open>RF\<close> is \<open>f\<close>'s body \<open>G := 1\<close> (def-site \<^const>\<open>DS3\<close>).  Each
  global write side-effects its result to its own def-site slot, so the solver keeps
  the two definitions apart with no join at publication.
\<close>
datatype rdpp = RMain | RF

fun rd_eqs :: "rdpp \<Rightarrow> (rdpp, def_site, sign st) strategy_tree" where
  "rd_eqs RMain =
     (let g0 = update_st (bot :: sign st) ''G'' SZero
      in Side DS1 g0 (QueryL RF (\<lambda>_. Answer g0)))"
| "rd_eqs RF =
     (let g1 = update_st (bot :: sign st) ''G'' SPos
      in Side DS3 g1 (Answer g1))"

definition rd_solution :: "rdpp set \<times> (rdpp + def_site \<Rightarrow> sign st)" where
  "rd_solution = TD_side_always_join_Interp_solve rd_eqs RMain"

subsection \<open>The solver computes separated def-site slots\<close>

lemma slot_DS1: "lookup_st (snd rd_solution (Inr DS1)) ''G'' = SZero"
  unfolding rd_solution_def by eval

lemma slot_DS3: "lookup_st (snd rd_solution (Inr DS3)) ''G'' = SPos"
  unfolding rd_solution_def by eval

lemma slot_join_all:
  "lookup_st (snd rd_solution (Inr DS1) \<squnion> snd rd_solution (Inr DS3)) ''G'' = SNonNeg"
  unfolding rd_solution_def by eval

subsection \<open>The precision payoff, sealed by the solver\<close>

theorem rd_slots_strictly_separate:
  "lookup_st (snd rd_solution (Inr DS1)) ''G'' = SZero
   \<and> lookup_st (snd rd_solution (Inr DS3)) ''G'' = SPos
   \<and> lookup_st (snd rd_solution (Inr DS1) \<squnion> snd rd_solution (Inr DS3)) ''G'' = SNonNeg
   \<and> lookup_st (snd rd_solution (Inr DS1)) ''G''
       < lookup_st (snd rd_solution (Inr DS1) \<squnion> snd rd_solution (Inr DS3)) ''G''
   \<and> lookup_st (snd rd_solution (Inr DS3)) ''G''
       < lookup_st (snd rd_solution (Inr DS1) \<squnion> snd rd_solution (Inr DS3)) ''G''"
  unfolding rd_solution_def by eval

subsection \<open>The reaching-definition read recovers the point-sensitive value\<close>

text \<open>
  The def-site-filtered global read on the \<^emph>\<open>solved\<close> environment: a reader whose
  reaching set is \<^term>\<open>{DS1}\<close> recovers \<^const>\<open>SZero\<close> (the caller's write), one whose
  set is \<^term>\<open>{DS3}\<close> recovers \<^const>\<open>SPos\<close> (the callee's write).  This is
  \<^const>\<open>glob_env_cmp\<close> under \<^const>\<open>rd_compatible\<close> --- the executable half of
  \<^const>\<open>rd_obs\<close> --- run on the solver's own output, keying globals by def-site while
  the context stays call-only.
\<close>

definition rd_env :: "rdpp + def_site \<Rightarrow> sign abs_state" where
  "rd_env = (\<lambda>k. fun_of_st (snd rd_solution k))"

lemma read_reach_DS1:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G'' = SZero"
  unfolding rd_env_def rd_solution_def rd_compatible_def by eval

lemma read_reach_DS3:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G'' = SPos"
  unfolding rd_env_def rd_solution_def rd_compatible_def by eval

lemma read_join_all:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1, DS3} g) () rd_env ''G'' = SNonNeg"
  unfolding rd_env_def rd_solution_def rd_compatible_def by eval

text \<open>
  Sealed by the solver: the two reaching-definition reads separate the call and the
  return under one call-only context, while the context-blind (all-def-sites) read
  merges them.  The soundness of these reads --- that the reaching set at a point
  over-approximates the concrete definitions reaching it --- is discharged in
  \<open>Exec_Sign_RD_Keyed_Run\<close> (\<open>CMP_SOUND_inst\<close>, \<open>rd_collect_sound_witness\<close>).
\<close>
theorem rd_reads_point_sensitive:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G'' = SZero
   \<and> glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G'' = SPos
   \<and> glob_env_cmp (\<lambda>_ g. rd_compatible {DS1, DS3} g) () rd_env ''G'' = SNonNeg
   \<and> glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G''
       < glob_env_cmp (\<lambda>_ g. rd_compatible {DS1, DS3} g) () rd_env ''G''"
  unfolding rd_env_def rd_solution_def rd_compatible_def by eval

subsection \<open>The executable read agrees with the sound witness\<close>

text \<open>
  The link between this executable run and the soundness proof of
  \<open>Exec_Sign_RD_Keyed_Run\<close>: the reaching-definition read computed on the solver's
  output coincides with the read the soundness witness covers.  Reading the reaching
  set \<^term>\<open>{DS1}\<close> on the solved environment gives what \<^const>\<open>rd_obs\<close> gives at the
  call node \<^term>\<open>4::nat\<close> of the hand witness (\<^const>\<open>SZero\<close>); reading \<^term>\<open>{DS3}\<close>
  gives the return-node read (\<^const>\<open>SPos\<close>).  So the solver-computed analysis and the
  provably-sound analysis agree on the example: the executable result is the one whose
  soundness \<open>rd_collect_sound_witness\<close> certifies.
\<close>
theorem exec_read_agrees_with_sound_witness:
  "glob_env_cmp (\<lambda>_ g. rd_compatible {DS1} g) () rd_env ''G'' = rd_obs rd_reach rd_sig ((4::nat), ()) ''G''
   \<and> glob_env_cmp (\<lambda>_ g. rd_compatible {DS3} g) () rd_env ''G'' = rd_obs rd_reach rd_sig ((6::nat), ()) ''G''"
  by (simp add: read_reach_DS1 read_reach_DS3 read_call4 read_return6)

end
