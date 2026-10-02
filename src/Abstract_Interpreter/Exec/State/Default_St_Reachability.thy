theory Default_St_Reachability
  imports Default_St_Transfer "Voblint_Domain.Nonrelational_Reachability"
begin

unbundle default_st_syntax

text \<open>A lifted state reads back pointwise under the lift.\<close>

adhoc_overloading readback == "\<lambda>\<G>. map_lift (default_st_to_fun \<G>)"

section \<open>Executable dead-code detection\<close>

text \<open>
  A nonrelational state denotes the product of its variables' value sets, so a
  single bottom component makes the whole state denote nothing. Deciding that
  by inspecting every variable is not executable -- there are infinitely many
  names -- so this theory builds a finite test and proves it says exactly what
  the infinite one does.

  The finite test has three witness sources: the local default, which covers
  every name no entry mentions; an explicitly stored entry that is bottom in
  the dictionary the classifier selects for its name; and a scan of the
  program's declared globals, which covers the side where no fresh-name
  argument is available. The middle one needs the classifier, since an entry
  stored in the other dictionary says nothing about the function the state
  represents. Above that sits the lifted view, where a whole unreachable state
  collapses to \<^const>\<open>Bot\<close> and an update that writes a bottom value collapses
  to it incrementally, without re-testing the rest of the state.
\<close>

subsection \<open>Raw witness test\<close>

text \<open>
  Bottom detection is the one carrier operation that consults \<open>\<G>\<close>, and the
  reason is the mismatch between two readings of the same state. The quotient
  \<^typ>\<open>'a default_st\<close> identifies two states exactly when their lookups agree
  at \<^emph>\<open>every\<close> location, whereas \<^const>\<open>default_st_rep_to_fun\<close> reads each
  name in the one dictionary \<open>\<G>\<close> selects for it. An entry for a name in the
  other dictionary is therefore visible to equality and invisible to the
  concretization, and a test that must agree with \<^const>\<open>is_empty_state\<close> on the
  represented function has to skip it. Every other operation on the carrier --
  lookup, update, order, join, widening, narrowing -- treats all locations
  alike and needs no classifier.

  The test below is sufficient but not yet exact, and takes three disjuncts:
  the local default already bottom, which covers every name no entry mentions;
  or a local entry, for a name \<open>\<G>\<close> leaves local, that is bottom; or a global
  entry, for a name \<open>\<G>\<close> calls global, that is bottom. The global default is
  deliberately not checked. A real program's classifier calls only finitely
  many names global, so no argument independent of the entry list can produce a
  fresh global escaping it, the way a fresh local always exists. Only the entry
  branch can safely observe a global; the exact test in the next subsection
  closes that gap by enumerating the declared globals outright.
\<close>

fun default_st_rep_is_bot ::
  "(vname => bool) => ('a::executable_domain) default_st_rep => bool" where
  "default_st_rep_is_bot \<G> ((dl, ls), (dg, gs)) \<longleftrightarrow>
     is_empty dl \<or>
     (\<exists>x \<in> set (map fst ls). \<not> \<G> x \<and> is_empty (default_dict_get (dl, ls) x)) \<or>
     (\<exists>x \<in> set (map fst gs). \<G> x \<and> is_empty (default_dict_get (dg, gs) x))"

text \<open>
  Soundness needs \<open>\<G>\<close> to leave infinitely many vnames local, so that some local
  witness always escapes any given (finite) entry list -- true for any
  @{term declared_global} of a real program, which only ever declares finitely
  many globals while @{typ vname} is infinite.
\<close>
lemma default_st_rep_is_bot_sound:
  assumes bot: "default_st_rep_is_bot \<G> s"
    and infinite_local: "infinite {x. \<not> \<G> x}"
  shows "is_empty_state (default_st_rep_to_fun \<G> s)"
proof -
  obtain l g where s_eq: "s = (l, g)" by (cases s)
  obtain dl ls where l_eq: "l = (dl, ls)" by (cases l)
  obtain dg gs where g_eq: "g = (dg, gs)" by (cases g)
  have local_lookup: "default_st_rep_to_fun \<G> s x = default_dict_get l x"
    if "\<not> \<G> x" for x
    using that unfolding default_st_rep_to_fun_def location_of_def s_eq by simp
  have global_lookup: "default_st_rep_to_fun \<G> s x = default_dict_get g x"
    if "\<G> x" for x
    using that unfolding default_st_rep_to_fun_def location_of_def s_eq by simp
  from bot consider
      (local_default) "is_empty dl"
    | (local_entry) x where "\<not> \<G> x" "is_empty (default_dict_get l x)"
    | (global_entry) x where "\<G> x" "is_empty (default_dict_get g x)"
    unfolding s_eq l_eq g_eq by auto
  then show ?thesis
  proof cases
    case local_default
    from infinite_local obtain x :: vname
      where x_local: "x \<in> {x. \<not> \<G> x}"
        and fresh: "x \<notin> set (map fst ls)"
      by (rule obtain_fresh_vname)
    from fresh have "map_of ls x = None"
      by (simp add: map_of_resolved_none_iff)
    then have "default_dict_get l x = dl"
      unfolding l_eq by simp
    with local_default x_local have "is_empty (default_st_rep_to_fun \<G> s x)"
      by (simp add: local_lookup)
    then show ?thesis by (rule is_empty_stateI)
  next
    case (local_entry x)
    then have "is_empty (default_st_rep_to_fun \<G> s x)"
      by (simp add: local_lookup)
    then show ?thesis by (rule is_empty_stateI)
  next
    case (global_entry x)
    then have "is_empty (default_st_rep_to_fun \<G> s x)"
      by (simp add: global_lookup)
    then show ?thesis by (rule is_empty_stateI)
  qed
qed

text \<open>
  \<^const>\<open>default_st_rep_is_bot\<close> deliberately leaves the global default unchecked
  because an opaque classifier gives no way to enumerate the (finite) globally
  classified vnames. A concrete program's classifier is always backed by an
  explicit finite list (@{term declared_global_vars}), and enumerating exactly
  that list closes the gap: every globally classified vname is checked
  directly, so the global branch needs no entry witness. This makes the
  combined check an exact (not merely sound) characterization of
  @{const is_empty_state}, with no side condition on \<open>\<G>\<close> beyond \<open>globals\<close>
  actually listing its true set -- unlike @{thm default_st_rep_is_bot_sound},
  which still needs infinitely many locals to exist.
\<close>

subsection \<open>Exact test for the declared globals\<close>

text \<open>
  In these names \<open>rep\<close> marks a test on representations and \<open>for\<close> a test exact for an
  explicit list of declared globals. The classifier-only test
  \<^const>\<open>default_st_rep_is_bot\<close> has no quotient counterpart: it ignores the global
  default, so extensionally equal representatives can disagree on it.
\<close>

definition default_st_rep_is_bot_for ::
  "vname list => (vname => bool) => ('a::executable_domain) default_st_rep => bool" where
  "default_st_rep_is_bot_for globals \<G> s =
     ((\<exists>x \<in> set globals. is_empty (default_st_rep_get s (location_of \<G> x))) \<or>
      default_st_rep_is_bot \<G> s)"

lemma default_st_rep_is_bot_for_iff:
  fixes s :: "'a::executable_domain default_st_rep"
  assumes globals: "\<And>x. \<G> x = (x \<in> set globals)"
  shows "default_st_rep_is_bot_for globals \<G> s \<longleftrightarrow> is_empty_state (default_st_rep_to_fun \<G> s)"
proof -
  have infinite_local: "infinite {x::vname. \<not> \<G> x}"
  proof
    assume fin: "finite {x::vname. \<not> \<G> x}"
    have "finite (UNIV :: vname set)"
    proof -
      have univ: "(UNIV :: vname set) = {x. \<not> \<G> x} \<union> set globals"
        using globals by auto
      have "finite ({x. \<not> \<G> x} \<union> set globals)" using fin by simp
      then show ?thesis unfolding univ .
    qed
    then show False using infinite_literal by simp
  qed
  show ?thesis
  proof
    assume "default_st_rep_is_bot_for globals \<G> s"
    then show "is_empty_state (default_st_rep_to_fun \<G> s)"
      unfolding default_st_rep_is_bot_for_def
    proof (elim disjE)
      assume "\<exists>x \<in> set globals. is_empty (default_st_rep_get s (location_of \<G> x))"
      then obtain x where "is_empty (default_st_rep_get s (location_of \<G> x))" by blast
      then have "is_empty (default_st_rep_to_fun \<G> s x)"
        unfolding default_st_rep_to_fun_def by simp
      then show ?thesis by (rule is_empty_stateI)
    next
      assume bot: "default_st_rep_is_bot \<G> s"
      show ?thesis by (rule default_st_rep_is_bot_sound[OF bot infinite_local])
    qed
  next
    assume "is_empty_state (default_st_rep_to_fun \<G> s)"
    then obtain x where x: "is_empty (default_st_rep_to_fun \<G> s x)" by (rule is_empty_stateE)
    show "default_st_rep_is_bot_for globals \<G> s"
    proof (cases "\<G> x")
      case True
      then have "x \<in> set globals" using globals by simp
      moreover have "default_st_rep_to_fun \<G> s x = default_st_rep_get s (location_of \<G> x)"
        unfolding default_st_rep_to_fun_def by (rule refl)
      ultimately have "\<exists>y \<in> set globals. is_empty (default_st_rep_get s (location_of \<G> y))"
        using x by auto
      then show ?thesis unfolding default_st_rep_is_bot_for_def by (rule disjI1)
    next
      case False
      note local_x = False
      obtain l g where s_eq: "s = (l, g)" by (cases s)
      obtain dl ls where l_eq: "l = (dl, ls)" by (cases l)
      obtain dg gs where g_eq: "g = (dg, gs)" by (cases g)
      have empty: "is_empty (default_dict_get l x)"
        using x local_x unfolding default_st_rep_to_fun_def location_of_def s_eq by simp
      have "default_st_rep_is_bot \<G> s"
      proof (cases "x \<in> set (map fst ls)")
        case True
        with empty local_x
        have "\<exists>y \<in> set (map fst ls). \<not> \<G> y \<and> is_empty (default_dict_get (dl, ls) y)"
          unfolding l_eq by blast
        then show ?thesis unfolding s_eq l_eq g_eq by simp
      next
        case False
        then have "map_of ls x = None"
          by (simp add: map_of_resolved_none_iff)
        with empty have "is_empty dl" unfolding l_eq by simp
        then show ?thesis unfolding s_eq l_eq g_eq by simp
      qed
      then show ?thesis unfolding default_st_rep_is_bot_for_def by (rule disjI2)
    qed
  qed
qed


subsection \<open>Lifting the exact test to the quotient\<close>

text \<open>
  \<^const>\<open>default_st_rep_is_bot_for\<close> takes \<open>\<G>\<close> as a free parameter, which makes it
  \<^const>\<open>eq_default_st_rep\<close>-respectful only when \<open>\<G>\<close> agrees with \<open>globals\<close>: a
  mismatched pair can pick out a witness through one representative's
  dictionary entries that another, extensionally equal, representative encodes
  via its defaults instead. Every real caller supplies the matching pair, so fixing
  \<open>\<G>\<close> to \<open>\<lambda>x. x \<in> set globals\<close> internally loses nothing and restores
  unconditional respectfulness -- which is what makes
  \<open>default_st_is_bot_for\<close> below liftable to the quotient at all.

  With that pair fixed, respectfulness is a corollary of exactness rather than
  a separate argument: extensionally equal representatives project to the same
  state, and @{thm [source] default_st_rep_is_bot_for_iff} says the test is
  exactly \<^const>\<open>is_empty_state\<close> of that projection.
\<close>

lemma eq_default_st_rep_is_bot_for:
  assumes eq: "eq_default_st_rep s t"
  shows "default_st_rep_is_bot_for globals (\<lambda>x. x \<in> set globals) s
       = default_st_rep_is_bot_for globals (\<lambda>x. x \<in> set globals) t"
proof -
  have iff: "default_st_rep_is_bot_for globals (\<lambda>x. x \<in> set globals) u
      = is_empty_state (default_st_rep_to_fun (\<lambda>x. x \<in> set globals) u)"
    for u :: "'a default_st_rep"
    by (rule default_st_rep_is_bot_for_iff) simp
  have "default_st_rep_to_fun (\<lambda>x. x \<in> set globals) s
          = default_st_rep_to_fun (\<lambda>x. x \<in> set globals) t"
    unfolding default_st_rep_to_fun_def
    by (rule ext) (rule eq_default_st_repD[OF eq])
  then show ?thesis unfolding iff by simp
qed

text \<open>
  The exact check transported to the quotient through \<^const>\<open>rep_default_st\<close>.
  This is the predicate the executable side trees are built against: unlike
  \<^const>\<open>is_empty_state\<close> composed with \<^const>\<open>default_st_to_fun\<close>, it has
  a genuine \<open>[code]\<close> equation, because it never quantifies over all of
  \<^typ>\<open>vname\<close>.

  It takes \<open>globals\<close> alone and rebuilds \<open>\<G>\<close> from it internally, rather than
  accepting a caller-supplied classifier. That is what makes
  @{thm [source] eq_default_st_rep_is_bot_for} apply unconditionally, and so what
  makes the definition liftable at all. Nothing is lost: every real caller
  already recomputes the same \<open>\<G>\<close> from the same list at the call site.
\<close>

lift_definition default_st_is_bot_for ::
  "vname list => ('a::executable_domain) default_st => bool"
  is "\<lambda>globals s. default_st_rep_is_bot_for globals (\<lambda>x. x \<in> set globals) s"
  by (rule eq_default_st_rep_is_bot_for)

lemma default_st_is_bot_for_iff:
  fixes s :: "'a::executable_domain default_st"
  assumes globals: "\<And>x. \<G> x = (x \<in> set globals)"
  shows "default_st_is_bot_for globals s \<longleftrightarrow> is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s)"
proof -
  have gs_eq: "(\<lambda>x. x \<in> set globals) = \<G>"
    using globals by (simp add: fun_eq_iff)
  show ?thesis
    unfolding default_st_is_bot_for.rep_eq gs_eq
    by (simp add: default_st_rep_is_bot_for_iff[OF globals]
      default_st_to_fun_rep)
qed

text \<open>
  The same test read through the carrier's concretization: a state passes it
  exactly when it describes no store.
\<close>

lemma default_st_is_bot_for_gamma_iff:
  fixes s :: "'a::numeric_domain default_st"
  assumes globals: "\<And>x. \<G> x = (x \<in> set globals)"
  shows "default_st_is_bot_for globals s \<longleftrightarrow> default_st_gamma \<G> s = {}"
  by (simp add: default_st_is_bot_for_iff[OF globals] default_st_gamma_def
      is_empty_state_iff_gamma_state_empty)

subsection \<open>The stores a lifted carrier state describes\<close>

text \<open>
  Reachability adds no new concretization: a lifted carrier state is read
  through \<^const>\<open>gamma_lift\<close> over \<^const>\<open>default_st_gamma\<close>, as a lifted
  pointwise state is read through \<^const>\<open>gamma_lift\<close> over
  \<^const>\<open>gamma_state\<close>. The second lemma relates the two through the
  represented function.
\<close>

lemma gamma_lift_default_st_gamma_mono:
  fixes x y :: "'a::numeric_domain default_st lifted"
  shows "x \<le> y \<Longrightarrow> gamma_lift (default_st_gamma \<G>) x \<subseteq> gamma_lift (default_st_gamma \<G>) y"
  by (rule gamma_lift_mono[OF default_st_gamma_mono])

lemma gamma_lift_default_st_gamma_to_fun:
  "gamma_lift (default_st_gamma \<G>) = (\<lambda>d. \<lbrakk>map_lift \<rho>\<^bsub>\<G>\<^esub> d\<rbrakk>\<^sub>\<bottom>)"
  by (rule ext) (simp add: gamma_lift_def default_st_gamma_def split: lifted.split)


subsection \<open>Incremental dead-code tracking\<close>


definition live_default_st ::
  "(vname => bool) => ('a::executable_domain) default_st => bool"
where
  "live_default_st \<G> s = (~ is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s))"

lemma live_default_stD:
  assumes "live_default_st \<G> s"
  shows "~ is_empty (\<rho>\<^bsub>\<G>\<^esub> s x)"
  using assms unfolding live_default_st_def is_empty_state_def by blast

text \<open>
  \<open>is_empty_state\<close> on \<open>\<rho>\<^bsub>\<G>\<^esub> s\<close> is an infinite existential over
  \<open>vname\<close>, not executable on a quotient value.  \<open>default_st_set_lift\<close> tracks it
  incrementally instead: given a @{const live_default_st} input and the single
  freshly computed element, the result is witness-bottom iff that element is
  \<open>is_empty\<close> -- every other location is provably unchanged
  (@{thm default_st_to_fun_set}), so it cannot newly become bottom.  This
  mirrors Goblint's per-analysis \<open>Deadcode\<close> raise while staying generic: it lives at
  the shared update primitive, not in each domain's own transfer code.
\<close>

definition default_st_set_lift ::
  "('a::executable_domain) default_st lifted => location => 'a => 'a default_st lifted"
where
  "default_st_set_lift x loc a = do {
     s <- x;
     if is_empty a then Bot else Lifted s\<langle>loc := a\<rangle>
   }"

lemma default_st_set_lift_Bot [simp]:
  "default_st_set_lift Bot loc a = Bot"
  unfolding default_st_set_lift_def by simp

lemma default_st_set_lift_Lifted:
  "default_st_set_lift (Lifted s) loc a =
     (if is_empty a then Bot else Lifted s\<langle>loc := a\<rangle>)"
  unfolding default_st_set_lift_def by simp

text \<open>
  The completeness theorem the location-scoped check relies on: from a live input,
  the lifted update exactly tracks the spec-level normalized result.  Only the
  freshly written variable's element needs checking -- every other variable's
  \<open>abs_state\<close> component provably survives unchanged
  (@{thm default_st_to_fun_set}), so it cannot be the source of a new
  witness-bottom.
\<close>
lemma default_st_set_lift_correct:
  fixes s :: "'a::executable_domain default_st"
  assumes live: "live_default_st \<G> s"
  shows "map_lift \<rho>\<^bsub>\<G>\<^esub>
           (default_st_set_lift (Lifted s) (location_of \<G> x) a) =
         normalize_lift is_empty_state ((\<rho>\<^bsub>\<G>\<^esub> s)(x := a))"
proof -
  from live have live': "\<not> is_empty_state (\<rho>\<^bsub>\<G>\<^esub> s)"
    unfolding live_default_st_def by simp
  have upd: "is_empty_state ((\<rho>\<^bsub>\<G>\<^esub> s)(x := a)) = is_empty a"
    by (rule is_empty_state_fun_upd_iff[OF live'])
  show ?thesis
    by (cases "is_empty a")
      (simp_all add: default_st_set_lift_Lifted upd)
qed

unbundle no default_st_syntax

end
