theory Exec_St_Reachability
  imports Exec_St_Transfer "Voblint_Domain.Nonrelational_Reachability"
begin

section \<open>Executable dead-code detection\<close>

text \<open>
  A nonrelational state denotes the product of its variables' value sets, so a
  single bottom component makes the whole state denote nothing. Deciding that
  by inspecting every variable is not executable -- there are infinitely many
  names -- so this theory builds a finite test and proves it says exactly what
  the infinite one does.

  The finite test has three witness sources: the local default, which covers
  every name no entry mentions; an explicitly stored entry that is bottom at a
  location the classifier would itself produce for that name; and a scan of the
  program's declared globals, which covers the side where no fresh-name
  argument is available. The middle one needs the canonicality filter, since an
  entry stored under the tag the classifier does not select for its name says
  nothing about the readback. Above that sits
  the lifted view, where a whole unreachable state collapses to \<^const>\<open>Bot\<close>
  and an update that writes a bottom value collapses to it incrementally,
  without re-testing the rest of the state.
\<close>

subsection \<open>Raw witness test\<close>

text \<open>
  Bottom detection is the one carrier operation that consults \<open>gs\<close>, and the
  reason is the mismatch between two readings of the same state. The quotient
  \<^typ>\<open>'a resolved_st_q\<close> identifies two states exactly when their lookups agree
  at \<^emph>\<open>every\<close> location, whereas \<^const>\<open>fun_of_resolved_st_for\<close> reads back only
  the one location \<open>gs\<close> selects for each name. An entry stored under the other
  tagging of a name is therefore visible to equality and invisible to the
  concretization, and a test that must agree with \<^const>\<open>is_empty_state\<close> on the
  readback has to skip it. \<open>canonical_location\<close> names that filter. Every other
  operation on the carrier -- lookup, update, order, join, widening, narrowing
  -- treats all locations alike and needs no classifier.

  The test below is sufficient but not yet exact, and takes two disjuncts: the
  local default already bottom, which covers every name no entry mentions; or
  an entry that is bottom at a canonical location. The global default is
  deliberately not checked. A real program's classifier calls only finitely
  many names global, so no argument independent of the entry list can produce a
  fresh global escaping it, the way a fresh local always exists. Only the entry
  branch can safely observe a global; the exact test in the next subsection
  closes that gap by enumerating the declared globals outright.
\<close>

definition canonical_location ::
  "(vname => bool) => location => bool" where
  "canonical_location gs loc \<longleftrightarrow> location_of gs (location_vname loc) = loc"

lemma canonical_location_location_of [simp]:
  "canonical_location gs (location_of gs x)"
  by (simp add: canonical_location_def location_of_def)

lemma canonical_location_Local [simp]:
  "canonical_location gs (Local_Location x) \<longleftrightarrow> \<not> gs x"
  by (auto simp: canonical_location_def location_of_def)

lemma canonical_location_Global [simp]:
  "canonical_location gs (Global_Location x) \<longleftrightarrow> gs x"
  by (auto simp: canonical_location_def location_of_def)

definition resolved_st_is_bot ::
  "(vname => bool) => ('a::executable_domain) resolved_st => bool" where
  "resolved_st_is_bot gs s =
     (case s of (dl, dg, ps) =>
       is_empty dl \<or>
       (\<exists>loc \<in> set (map fst ps). is_empty (lookup_resolved_st s loc)
          \<and> canonical_location gs loc))"

text \<open>
  The two ways the test can hold, as rules rather than as a disjunction the
  reader has to unfold. The introduction rule for the default side is cheap
  enough to tag; the elimination rule is not tagged, because its second case
  hands back a location and letting \<open>auto\<close> search for one everywhere a
  \<^const>\<open>resolved_st_is_bot\<close> hypothesis appears is a poor trade.
\<close>

lemma resolved_st_is_bot_defaultI [intro]:
  assumes "is_empty (fst s)"
  shows "resolved_st_is_bot gs s"
  using assms by (cases s) (simp add: resolved_st_is_bot_def)

lemma resolved_st_is_botE:
  assumes "resolved_st_is_bot gs (dl, dg, ps)"
  obtains (default) "is_empty dl"
    | (override) loc where "loc \<in> set (map fst ps)"
        "is_empty (lookup_resolved_st (dl, dg, ps) loc)"
        "canonical_location gs loc"
  using assms by (auto simp: resolved_st_is_bot_def)

text \<open>
  Soundness needs gs to leave infinitely many vnames local, so that some local
  witness always escapes any given (finite) override list -- true for any
  @{term declared_global} of a real program, which only ever declares finitely
  many globals while @{typ vname} is infinite.
\<close>
lemma resolved_st_is_bot_sound:
  assumes bot: "resolved_st_is_bot gs s"
    and infinite_local: "infinite {x. \<not> gs x}"
  shows "is_empty_state (fun_of_resolved_st_for gs s)"
proof -
  obtain dl dg ps where s_eq: "s = (dl, dg, ps)" by (cases s)
  from bot consider
      (dl) "is_empty dl"
    | (ps) loc where "loc \<in> set (map fst ps)" "is_empty (lookup_resolved_st s loc)"
        "location_of gs (location_vname loc) = loc"
    unfolding s_eq
    by (elim resolved_st_is_botE) (simp_all add: canonical_location_def)
  then show ?thesis
  proof cases
    case dl
    from infinite_local obtain x :: vname
      where x_local: "x \<in> {x. \<not> gs x}"
        and local_ps: "Local_Location x \<notin> set (map fst ps)"
        and "Global_Location x \<notin> set (map fst ps)"
      by (rule obtain_fresh_location)
    from x_local have not_gs: "\<not> gs x" by simp
    have mo_l: "map_of ps (Local_Location x) = None"
      using local_ps by (simp add: map_of_resolved_none_iff)
    have "lookup_resolved_st s (Local_Location x) = dl"
      unfolding s_eq by (simp add: mo_l)
    then have "is_empty (fun_of_resolved_st_for gs s x)"
      unfolding fun_of_resolved_st_for_def location_of_def
      using dl not_gs by simp
    then show ?thesis by (rule is_empty_stateI)
  next
    case ps
    let ?x = "location_vname loc"
    have loc_eq: "location_of gs ?x = loc" by (rule ps(3))
    have "fun_of_resolved_st_for gs s ?x = lookup_resolved_st s loc"
      unfolding fun_of_resolved_st_for_def loc_eq by (rule refl)
    then have "is_empty (fun_of_resolved_st_for gs s ?x)"
      using ps(2) by simp
    then show ?thesis by (rule is_empty_stateI)
  qed
qed

text \<open>
  \<^const>\<open>resolved_st_is_bot\<close> deliberately leaves the global default unchecked
  because an opaque classifier gives no way to enumerate the (finite) globally
  classified vnames. A concrete program's classifier is always backed by an
  explicit finite list (@{term declared_global_vars}), and enumerating exactly
  that list closes the gap: every globally classified vname is checked
  directly, so the global branch needs no override witness. This makes the
  combined check an exact (not merely sound) characterization of
  @{const is_empty_state}, with no side condition on \<open>gs\<close> beyond \<open>globals\<close>
  actually listing its true set -- unlike @{thm resolved_st_is_bot_sound},
  which still needs infinitely many locals to exist.
\<close>

subsection \<open>Exact test for the declared globals\<close>

definition resolved_st_is_bot_for ::
  "vname list => (vname => bool) => ('a::executable_domain) resolved_st => bool" where
  "resolved_st_is_bot_for globals gs s =
     ((\<exists>x \<in> set globals. is_empty (lookup_resolved_st s (location_of gs x))) \<or>
      resolved_st_is_bot gs s)"

lemma resolved_st_is_bot_for_iff:
  fixes s :: "'a::executable_domain resolved_st"
  assumes globals: "\<And>x. gs x = (x \<in> set globals)"
  shows "resolved_st_is_bot_for globals gs s \<longleftrightarrow> is_empty_state (fun_of_resolved_st_for gs s)"
proof -
  have infinite_local: "infinite {x::vname. \<not> gs x}"
  proof
    assume fin: "finite {x::vname. \<not> gs x}"
    have "finite (UNIV :: vname set)"
    proof -
      have univ: "(UNIV :: vname set) = {x. \<not> gs x} \<union> set globals"
        using globals by auto
      have "finite ({x. \<not> gs x} \<union> set globals)" using fin by simp
      then show ?thesis unfolding univ .
    qed
    then show False using infinite_literal by simp
  qed
  show ?thesis
  proof
    assume "resolved_st_is_bot_for globals gs s"
    then show "is_empty_state (fun_of_resolved_st_for gs s)"
      unfolding resolved_st_is_bot_for_def
    proof (elim disjE)
      assume "\<exists>x \<in> set globals. is_empty (lookup_resolved_st s (location_of gs x))"
      then obtain x where "is_empty (lookup_resolved_st s (location_of gs x))" by blast
      then have "is_empty (fun_of_resolved_st_for gs s x)"
        unfolding fun_of_resolved_st_for_def by simp
      then show ?thesis by (rule is_empty_stateI)
    next
      assume bot: "resolved_st_is_bot gs s"
      show ?thesis by (rule resolved_st_is_bot_sound[OF bot infinite_local])
    qed
  next
    assume "is_empty_state (fun_of_resolved_st_for gs s)"
    then obtain x where x: "is_empty (fun_of_resolved_st_for gs s x)" by (rule is_empty_stateE)
    show "resolved_st_is_bot_for globals gs s"
    proof (cases "gs x")
      case True
      then have "x \<in> set globals" using globals by simp
      moreover have "fun_of_resolved_st_for gs s x = lookup_resolved_st s (location_of gs x)"
        unfolding fun_of_resolved_st_for_def by (rule refl)
      ultimately have "\<exists>y \<in> set globals. is_empty (lookup_resolved_st s (location_of gs y))"
        using x by auto
      then show ?thesis unfolding resolved_st_is_bot_for_def by (rule disjI1)
    next
      case False
      have loc_eq: "location_of gs x = Local_Location x"
        using False unfolding location_of_def by simp
      have lookup_eq: "lookup_resolved_st s (Local_Location x) = fun_of_resolved_st_for gs s x"
        unfolding fun_of_resolved_st_for_def loc_eq by (rule refl)
      obtain dl dg ps where s_eq: "s = (dl, dg, ps)" by (cases s)
      have "resolved_st_is_bot gs s"
      proof (cases "Local_Location x \<in> set (map fst ps)")
        case True
        have loc_vname_eq: "location_of gs (location_vname (Local_Location x)) = Local_Location x"
          using loc_eq by simp
        show ?thesis
          unfolding resolved_st_is_bot_def canonical_location_def
          using True lookup_eq x loc_vname_eq s_eq
          by (metis (mono_tags, lifting) case_prod_conv)
      next
        case False
        then have mo: "map_of ps (Local_Location x) = None"
          by (simp add: map_of_resolved_none_iff)
        have "lookup_resolved_st s (Local_Location x) = dl"
          unfolding s_eq using mo by simp
        with lookup_eq x have "is_empty dl" by simp
        then show ?thesis
          unfolding resolved_st_is_bot_def canonical_location_def using s_eq by auto
      qed
      then show ?thesis unfolding resolved_st_is_bot_for_def by (rule disjI2)
    qed
  qed
qed


subsection \<open>Lifting the exact test to the quotient\<close>

text \<open>
  \<^const>\<open>resolved_st_is_bot_for\<close> takes \<open>gs\<close> as a free parameter, which makes it
  \<^const>\<open>eq_resolved_st\<close>-respectful only when \<open>gs\<close> agrees with \<open>globals\<close>: a
  mismatched pair can pick out a witness through one representative's override
  list that another, extensionally equal, representative encodes via its
  defaults instead. Every real caller supplies the matching pair, so fixing
  \<open>gs\<close> to \<open>\<lambda>x. x \<in> set globals\<close> internally loses nothing and restores
  unconditional respectfulness -- which is what makes
  \<open>resolved_st_q_is_bot_for\<close> below liftable to the quotient at all.

  With that pair fixed, respectfulness is a corollary of exactness rather than
  a separate argument: extensionally equal representatives project to the same
  state, and @{thm [source] resolved_st_is_bot_for_iff} says the test is
  exactly \<^const>\<open>is_empty_state\<close> of that projection.
\<close>

lemma eq_resolved_st_is_bot_for:
  assumes eq: "eq_resolved_st s t"
  shows "resolved_st_is_bot_for globals (\<lambda>x. x \<in> set globals) s
       = resolved_st_is_bot_for globals (\<lambda>x. x \<in> set globals) t"
proof -
  have iff: "resolved_st_is_bot_for globals (\<lambda>x. x \<in> set globals) u
      = is_empty_state (fun_of_resolved_st_for (\<lambda>x. x \<in> set globals) u)" for u
    by (rule resolved_st_is_bot_for_iff) simp
  have "fun_of_resolved_st_for (\<lambda>x. x \<in> set globals) s
          = fun_of_resolved_st_for (\<lambda>x. x \<in> set globals) t"
    unfolding fun_of_resolved_st_for_def
    by (rule ext) (rule eq_resolved_stD[OF eq])
  then show ?thesis unfolding iff by simp
qed

text \<open>
  The exact check transported to the quotient through \<^const>\<open>rep_resolved_st\<close>.
  This is the predicate the executable side trees are built against: unlike
  \<^const>\<open>is_empty_state\<close> composed with \<^const>\<open>fun_of_resolved_st_q_for\<close>, it has
  a genuine \<open>[code]\<close> equation, because it never quantifies over all of
  \<^typ>\<open>vname\<close>.

  It takes \<open>globals\<close> alone and rebuilds \<open>gs\<close> from it internally, rather than
  accepting a caller-supplied classifier. That is what makes
  @{thm [source] eq_resolved_st_is_bot_for} apply unconditionally, and so what
  makes the definition liftable at all. Nothing is lost: every real caller
  already recomputes the same \<open>gs\<close> from the same list at the call site.
\<close>

lift_definition resolved_st_q_is_bot_for ::
  "vname list => ('a::executable_domain) resolved_st_q => bool"
  is "\<lambda>globals s. resolved_st_is_bot_for globals (\<lambda>x. x \<in> set globals) s"
  by (rule eq_resolved_st_is_bot_for)

lemma resolved_st_q_is_bot_for_alt:
  "resolved_st_q_is_bot_for globals s =
     resolved_st_is_bot_for globals (\<lambda>x. x \<in> set globals) (rep_resolved_st s)"
  by (rule resolved_st_q_is_bot_for.rep_eq)

lemma resolved_st_q_is_bot_for_iff:
  fixes s :: "'a::executable_domain resolved_st_q"
  assumes globals: "\<And>x. gs x = (x \<in> set globals)"
  shows "resolved_st_q_is_bot_for globals s \<longleftrightarrow> is_empty_state (fun_of_resolved_st_q_for gs s)"
proof -
  have gs_eq: "(\<lambda>x. x \<in> set globals) = gs"
    using globals by (simp add: fun_eq_iff)
  show ?thesis
    unfolding resolved_st_q_is_bot_for_alt gs_eq
    by (simp add: resolved_st_is_bot_for_iff[OF globals]
      fun_of_resolved_st_q_for_rep)
qed



subsection \<open>Incremental dead-code tracking\<close>


definition live_resolved_st_q ::
  "(vname => bool) => ('a::executable_domain) resolved_st_q => bool"
where
  "live_resolved_st_q gs s = (~ is_empty_state (fun_of_resolved_st_q_for gs s))"

lemma live_resolved_st_qD:
  assumes "live_resolved_st_q gs s"
  shows "~ is_empty (fun_of_resolved_st_q_for gs s x)"
  using assms unfolding live_resolved_st_q_def is_empty_state_def by blast

text \<open>
  \<open>is_empty_state\<close> on \<open>fun_of_resolved_st_q_for gs s\<close> is an infinite existential over
  \<open>vname\<close>, not executable on a quotient value.  \<open>update_resolved_st_q_lift\<close> tracks it
  incrementally instead: given a @{const live_resolved_st_q} input and the single
  freshly computed element, the result is witness-bottom iff that element is
  \<open>is_empty\<close> -- every other location is provably unchanged
  (@{thm fun_of_resolved_st_q_for_update}), so it cannot newly become bottom.  This
  mirrors Goblint's per-analysis \<open>Deadcode\<close> raise while staying generic: it lives at
  the shared update primitive, not in each domain's own transfer code.
\<close>

definition update_resolved_st_q_lift ::
  "('a::executable_domain) resolved_st_q lifted => location => 'a => 'a resolved_st_q lifted"
where
  "update_resolved_st_q_lift x loc a = do {
     s <- x;
     if is_empty a then Bot else Lifted (update_resolved_st_q s loc a)
   }"

lemma update_resolved_st_q_lift_Bot [simp]:
  "update_resolved_st_q_lift Bot loc a = Bot"
  unfolding update_resolved_st_q_lift_def by simp

lemma update_resolved_st_q_lift_Lifted:
  "update_resolved_st_q_lift (Lifted s) loc a =
     (if is_empty a then Bot else Lifted (update_resolved_st_q s loc a))"
  unfolding update_resolved_st_q_lift_def by simp

text \<open>
  The completeness theorem the location-scoped check relies on: from a live input,
  the lifted update exactly tracks the spec-level normalized result.  Only the
  freshly written variable's element needs checking -- every other variable's
  \<open>abs_state\<close> component provably survives unchanged
  (@{thm fun_of_resolved_st_q_for_update}), so it cannot be the source of a new
  witness-bottom.
\<close>
lemma update_resolved_st_q_lift_correct:
  fixes s :: "'a::executable_domain resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (update_resolved_st_q_lift (Lifted s) (location_of gs x) a) =
         normalize_lift is_empty_state ((fun_of_resolved_st_q_for gs s)(x := a))"
proof -
  from live have live': "\<not> is_empty_state (fun_of_resolved_st_q_for gs s)"
    unfolding live_resolved_st_q_def by simp
  have upd: "is_empty_state ((fun_of_resolved_st_q_for gs s)(x := a)) = is_empty a"
    by (rule is_empty_state_fun_upd_iff[OF live'])
  show ?thesis
    by (cases "is_empty a")
      (simp_all add: update_resolved_st_q_lift_Lifted upd)
qed

end
