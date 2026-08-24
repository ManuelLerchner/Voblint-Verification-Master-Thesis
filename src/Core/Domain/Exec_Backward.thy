  theory Exec_Backward
  imports Exec_St
begin

section \<open>Generic executable mirror of backward filtering\<close>

text \<open>
  Every interpretation of @{locale backward_domain} gets an executable
  @{typ "'a resolved_st_q"} mirror of its @{text afilter} / @{text bfilter}
  for free, parameterized by an explicit location classifier \<open>gs\<close>:
  \<open>afilter_st\<close> / \<open>bfilter_st\<close> and their commutation with the abstract
  filters through @{const fun_of_resolved_st_q_for}, proved once here so no
  domain needs to repeat the induction by hand. A concrete domain
  names its own specialization via the \<open>defines\<close> clause of its existing
  \<open>backward_domain\<close> interpretation (see \<open>Sign_Backward\<close>,
  \<open>Interval_Backward\<close>); no per-domain proof is needed.
\<close>

text \<open>
  The finite set of variables an expression can refine, used by the lifted
  compound-boolean join below to bound its bottom check to a decidable,
  finite probe instead of a whole-state scan.
\<close>

fun footprint_exp :: "exp => vname list" where
    "footprint_exp (N n) = []"
  | "footprint_exp (V x) = [x]"
  | "footprint_exp (Plus e1 e2) = footprint_exp e1 @ footprint_exp e2"
  | "footprint_exp (Minus e1 e2) = footprint_exp e1 @ footprint_exp e2"
  | "footprint_exp (Times e1 e2) = footprint_exp e1 @ footprint_exp e2"
  | "footprint_exp (Less e1 e2) = footprint_exp e1 @ footprint_exp e2"
  | "footprint_exp (Eq e1 e2) = footprint_exp e1 @ footprint_exp e2"
  | "footprint_exp (Not b) = footprint_exp b"
  | "footprint_exp (And b1 b2) = footprint_exp b1 @ footprint_exp b2"
  | "footprint_exp (Or b1 b2) = footprint_exp b1 @ footprint_exp b2"

text \<open>
  \<open>probe_exp\<close> is what the lifted layer actually tests for witness-bottom: the
  expression's own footprint, plus one location outside every expression's
  footprint. The extra point is what makes the test complete rather than
  merely sound. A gated join whose gates ruled both disjuncts out is bottom
  at every location, including ones the expression never mentions, and a
  footprint-scoped probe cannot see that when the expression mentions no
  variable at all. Probing one more location costs nothing in every other
  case, since a live state is bottom at no location.
\<close>

definition probe_exp :: "exp => vname list" where
  "probe_exp e = STR '''' # footprint_exp e"

context backward_domain
begin

fun afilter_st ::
  "(vname => bool) => exp => 'a => 'a resolved_st_q => 'a resolved_st_q"
where
    "afilter_st gs (V x) a s =
       update_resolved_st_q s (location_of gs x)
         (intersect a (fun_of_resolved_st_q_for gs s x))"
  | "afilter_st gs (Plus e1 e2) a s =
       (let (a1, a2) = inv_plus a
              (aval_abs e1 (fun_of_resolved_st_q_for gs s))
              (aval_abs e2 (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e1 a1 (afilter_st gs e2 a2 s))"
  | "afilter_st gs (Minus e1 e2) a s =
       (let (a1, a2) = inv_minus a
              (aval_abs e1 (fun_of_resolved_st_q_for gs s))
              (aval_abs e2 (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e1 a1 (afilter_st gs e2 a2 s))"
  | "afilter_st gs (Times e1 e2) a s =
       (let (a1, a2) = inv_times a
              (aval_abs e1 (fun_of_resolved_st_q_for gs s))
              (aval_abs e2 (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e1 a1 (afilter_st gs e2 a2 s))"
  | "afilter_st gs _ a s = s"

fun bfilter_st ::
  "(vname => bool) => exp => bool => 'a resolved_st_q => 'a resolved_st_q"
where
    "bfilter_st gs (Less e1 e2) res s =
       (let (a1, a2) = inv_less res
              (aval_abs e1 (fun_of_resolved_st_q_for gs s))
              (aval_abs e2 (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e1 a1 (afilter_st gs e2 a2 s))"
  | "bfilter_st gs (Not b) res s = bfilter_st gs b (\<not> res) s"
  | "bfilter_st gs (And b1 b2) True s =
       bfilter_st gs b1 True (bfilter_st gs b2 True s)"
  | "bfilter_st gs (And b1 b2) False s =
       (if feasible b1 False (fun_of_resolved_st_q_for gs s) then bfilter_st gs b1 False s else bot)
       \<squnion> (if feasible b2 False (fun_of_resolved_st_q_for gs s) then bfilter_st gs b2 False s else bot)"
  | "bfilter_st gs (Or b1 b2) True s =
       (if feasible b1 True (fun_of_resolved_st_q_for gs s) then bfilter_st gs b1 True s else bot)
       \<squnion> (if feasible b2 True (fun_of_resolved_st_q_for gs s) then bfilter_st gs b2 True s else bot)"
  | "bfilter_st gs (Or b1 b2) False s =
       bfilter_st gs b1 False (bfilter_st gs b2 False s)"
  | "bfilter_st gs (Eq e1 e2) res s =
       (let (a1, a2) = inv_eq res
              (aval_abs e1 (fun_of_resolved_st_q_for gs s))
              (aval_abs e2 (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e1 a1 (afilter_st gs e2 a2 s))"
  | "bfilter_st gs e res s =
       (let (a1, a2) = inv_eq (\<not> res)
              (aval_abs e (fun_of_resolved_st_q_for gs s))
              (aval_abs (N 0) (fun_of_resolved_st_q_for gs s))
        in afilter_st gs e a1 s)"

text \<open>
  \<open>afilter_st_lift\<close>/\<open>bfilter_st_lift\<close> mirror \<open>afilter_st\<close>/\<open>bfilter_st\<close>'s own recursion
  exactly, but thread a \<open>resolved_st_q lifted\<close> value through it: a \<open>Bot\<close> input never
  reaches a further narrowing step, and a leaf whose freshly narrowed element is
  \<open>is_bot\<close> collapses to \<open>Bot\<close> via @{const update_resolved_st_q_lift}.  The compound
  cases either sequence two single-variable narrows (never re-checking a location
  the other branch already settled) or join two gated branches via \<open>\<squnion>\<close>.  Joining
  two live branches can never produce a witness-bottom result, since \<open>is_bot\<close> is
  downward closed (@{thm is_bot_mono}) and each branch's own value is a lower bound
  of the join; a branch whose gate ruled its polarity out contributes \<open>bot\<close>
  instead, so the join is witness-bottom exactly when both gates ruled out --
  which the lift's join cases test directly, ahead of the footprint probe.  No
  per-domain code is needed: this is generic in the @{locale backward_domain}
  operations, exactly like \<open>afilter_st\<close>/\<open>bfilter_st\<close> themselves.
\<close>

fun afilter_st_lift ::
  "(vname => bool) => exp => 'a => 'a resolved_st_q lifted => 'a resolved_st_q lifted"
where
    "afilter_st_lift gs (V x) a x_lift = do {
       s <- x_lift;
       update_resolved_st_q_lift (Lifted s) (location_of gs x)
         (intersect a (fun_of_resolved_st_q_for gs s x))
     }"
  | "afilter_st_lift gs (Plus e1 e2) a x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_plus a
             (aval_abs e1 (fun_of_resolved_st_q_for gs s))
             (aval_abs e2 (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))
     }"
  | "afilter_st_lift gs (Minus e1 e2) a x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_minus a
             (aval_abs e1 (fun_of_resolved_st_q_for gs s))
             (aval_abs e2 (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))
     }"
  | "afilter_st_lift gs (Times e1 e2) a x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_times a
             (aval_abs e1 (fun_of_resolved_st_q_for gs s))
             (aval_abs e2 (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))
     }"
    | "afilter_st_lift gs _ a x_lift = x_lift"

lemma afilter_st_lift_Bot [simp]: "afilter_st_lift gs e a Bot = Bot"
  by (induction e) simp_all

lemma afilter_st_commute:
  "fun_of_resolved_st_q_for gs (afilter_st gs e a s) =
     afilter e a (fun_of_resolved_st_q_for gs s)"
proof (induction e arbitrary: a s)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  show ?case by (simp add: Plus.IH split: prod.splits)
next
  case (Minus e1 e2)
  show ?case by (simp add: Minus.IH split: prod.splits)
next
  case (Times e1 e2)
  show ?case by (simp add: Times.IH split: prod.splits)
next
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
next
  case (Not e) then show ?case by simp
next
  case (And e1 e2) then show ?case by simp
next
  case (Or e1 e2) then show ?case by simp
qed

lemma bfilter_st_commute:
  "fun_of_resolved_st_q_for gs (bfilter_st gs b res s) =
     bfilter b res (fun_of_resolved_st_q_for gs s)"
proof (induction b arbitrary: res s)
  case (N n)
  then show ?case unfolding bfilter_st.simps bfilter.simps Let_def case_prod_beta
    using afilter_st_commute by simp
next
  case (V x)
  then show ?case unfolding bfilter_st.simps bfilter.simps Let_def case_prod_beta
    using afilter_st_commute by simp
next
  case (Plus e1 e2)
  then show ?case
    by (simp add: bfilter_st.simps bfilter.simps Let_def case_prod_beta afilter_st_commute)
next
  case (Minus e1 e2)
  then show ?case
    by (simp add: bfilter_st.simps bfilter.simps Let_def case_prod_beta afilter_st_commute)
next
  case (Times e1 e2)
  then show ?case
    by (simp add: bfilter_st.simps bfilter.simps Let_def case_prod_beta afilter_st_commute)
next
  case (Not b)
  then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: And.IH)
  next
    case False
    then show ?thesis by (simp add: And.IH bot_fun_def)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: Or.IH bot_fun_def)
  next
    case False
    then show ?thesis by (simp add: Or.IH)
  qed
next
  case (Less e1 e2)
  then show ?case by (simp add: afilter_st_commute split: prod.splits)
next
  case (Eq e1 e2)
  then show ?case by (simp add: afilter_st_commute split: prod.splits)
qed

text \<open>
  \<open>branch_st\<close> is \<open>branch\<close>'s executable \<open>resolved_st_q\<close> mirror: the same
  forward \<open>feasible\<close> gate ahead of \<open>bfilter_st\<close>, short-circuiting to the
  global \<open>bot\<close> \<open>resolved_st_q\<close> exactly where \<open>branch\<close> short-circuits to
  \<open>bot\<close>. \<open>fun_of_resolved_st_q_for_bot\<close> (\<open>Exec_St\<close>) is what makes this land
  on the right value: reading back the \<open>resolved_st_q\<close> \<open>bot\<close> instance gives
  exactly the pointwise-\<open>bot\<close> function \<open>branch\<close>'s own \<open>bot\<close> case produces, so
  \<open>branch_st_commute\<close> follows directly from \<open>branch_unfold\<close> -- \<open>branch\<close>'s
  plain-state case split, recovered as a lemma now that \<open>branch_lifted\<close> is the
  primitive definition -- and \<open>bfilter_st_commute\<close>, with no new induction.

  It is also the operator \<open>bfilter_st\<close>'s two join cases apply per disjunct, so
  those cases read back as \<open>branch\<close>-per-disjunct joins on the spec side
  (\<open>bfilter_st_And_False_branch\<close>, \<open>bfilter_st_Or_True_branch\<close> below).
\<close>

definition branch_st ::
  "(vname => bool) => exp => bool => 'a resolved_st_q => 'a resolved_st_q"
where
  "branch_st gs e pol s =
     (if feasible e pol (fun_of_resolved_st_q_for gs s) then bfilter_st gs e pol s else bot)"

lemma branch_st_commute:
  "fun_of_resolved_st_q_for gs (branch_st gs e pol s) =
     branch e pol (fun_of_resolved_st_q_for gs s)"
  unfolding branch_st_def branch_unfold
  by (simp add: bfilter_st_commute fun_of_resolved_st_q_for_bot)

lemma bfilter_st_And_False_branch:
  "bfilter_st gs (And b1 b2) False s = branch_st gs b1 False s \<squnion> branch_st gs b2 False s"
  by (simp add: branch_st_def)

lemma bfilter_st_Or_True_branch:
  "bfilter_st gs (Or b1 b2) True s = branch_st gs b1 True s \<squnion> branch_st gs b2 True s"
  by (simp add: branch_st_def)

text \<open>
  Locality: \<open>afilter_st\<close> never touches a location outside its own finite
  @{const footprint_exp}. \<open>bfilter_st\<close>'s counterpart is weaker -- a gated
  join whose gates ruled both disjuncts out is bottom everywhere -- and needs
  reductiveness to state, so it sits with the lifted layer in
  @{locale backward_domain_refined} below.
\<close>

lemma afilter_st_locality:
  "x \<notin> set (footprint_exp e) \<Longrightarrow>
     fun_of_resolved_st_q_for gs (afilter_st gs e a s) x = fun_of_resolved_st_q_for gs s x"
proof (induction e arbitrary: a s)
  case (N n)
  then show ?case by simp
next
  case (V y)
  then show ?case by simp
next
  case (Plus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  show ?case
    unfolding afilter_st.simps Let_def case_prod_beta
    using Plus.IH(1)[OF x1] Plus.IH(2)[OF x2] by simp
next
  case (Minus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  show ?case
    unfolding afilter_st.simps Let_def case_prod_beta
    using Minus.IH(1)[OF x1] Minus.IH(2)[OF x2] by simp
next
  case (Times e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  show ?case
    unfolding afilter_st.simps Let_def case_prod_beta
    using Times.IH(1)[OF x1] Times.IH(2)[OF x2] by simp
next
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
next
  case (Not e) then show ?case by simp
next
  case (And e1 e2) then show ?case by simp
next
  case (Or e1 e2) then show ?case by simp
qed


text \<open>
  \<open>bfilter_st_lift\<close> mirrors \<open>bfilter_st\<close>'s recursion for the sequential cases
  (\<open>Not\<close>/\<open>And True\<close>/\<open>Or False\<close>/\<open>Less\<close>/\<open>Eq\<close>) exactly like \<open>afilter_st_lift\<close>.
  The compound-join cases (\<open>And False\<close>/\<open>Or True\<close>) cannot be built the same
  way: spec-level \<open>bfilter\<close> joins its two gated branch results with plain
  pointwise \<open>\<squnion>\<close> (needed so \<open>bfilter_sign\<close>/\<open>bfilter_ivl\<close> stay
  code-generatable -- \<open>is_bot_state\<close> is not executable, since \<open>vname\<close> is not a
  finite type), and that plain join can leave a live result even when both
  branches independently narrowed to a witness-bottom at different locations.
  Recursively lifting each branch first (collapsing to \<open>Bot\<close> before the join)
  would answer a different, more precise question than spec's own \<open>\<squnion>\<close>
  actually computes. Instead the join cases run the raw \<open>bfilter_st\<close>
  computation (exactly mirroring spec) and then decide witness-bottom with one
  finite probe over @{const probe_exp}.
\<close>

fun bfilter_st_lift ::
  "(vname => bool) => exp => bool => 'a resolved_st_q lifted => 'a resolved_st_q lifted"
where
    "bfilter_st_lift gs (Less e1 e2) res x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_less res
             (aval_abs e1 (fun_of_resolved_st_q_for gs s))
             (aval_abs e2 (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))
     }"
  | "bfilter_st_lift gs (Not b) res x_lift = bfilter_st_lift gs b (\<not> res) x_lift"
  | "bfilter_st_lift gs (And b1 b2) True x_lift =
       bfilter_st_lift gs b1 True (bfilter_st_lift gs b2 True x_lift)"
  | "bfilter_st_lift gs (And b1 b2) False x_lift = do {
       s <- x_lift;
       if list_ex (%x. is_bot (fun_of_resolved_st_q_for gs
              (bfilter_st gs (And b1 b2) False s) x))
            (probe_exp (And b1 b2))
       then Bot
       else Lifted (bfilter_st gs (And b1 b2) False s)
     }"
  | "bfilter_st_lift gs (Or b1 b2) True x_lift = do {
       s <- x_lift;
       if list_ex (%x. is_bot (fun_of_resolved_st_q_for gs
              (bfilter_st gs (Or b1 b2) True s) x))
            (probe_exp (Or b1 b2))
       then Bot
       else Lifted (bfilter_st gs (Or b1 b2) True s)
     }"
  | "bfilter_st_lift gs (Or b1 b2) False x_lift =
       bfilter_st_lift gs b1 False (bfilter_st_lift gs b2 False x_lift)"
  | "bfilter_st_lift gs (Eq e1 e2) res x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_eq res
             (aval_abs e1 (fun_of_resolved_st_q_for gs s))
             (aval_abs e2 (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))
     }"
  | "bfilter_st_lift gs e res x_lift = do {
       s <- x_lift;
       let (a1, a2) = inv_eq (\<not> res)
             (aval_abs e (fun_of_resolved_st_q_for gs s))
             (aval_abs (N 0) (fun_of_resolved_st_q_for gs s));
       afilter_st_lift gs e a1 (Lifted s)
     }"

lemma bfilter_st_lift_Bot [simp]: "bfilter_st_lift gs b res Bot = Bot"
proof (induction b arbitrary: res)
  case (N n)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus e1 e2)
  then show ?case by simp
next
  case (Minus e1 e2)
  then show ?case by simp
next
  case (Times e1 e2)
  then show ?case by simp
next
  case (Not b)
  then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: And.IH)
  next
    case False
    then show ?thesis by (simp add: And.IH)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: Or.IH)
  next
    case False
    then show ?thesis by (simp add: Or.IH)
  qed
next
  case (Less e1 e2)
  then show ?case by simp
next
  case (Eq e1 e2)
  then show ?case by simp
qed

end

context backward_domain_refined
begin

text \<open>
  Exec/spec correspondence for the lift, exact rather than a one-sided
  soundness bound: a live input's lifted transfer, interpreted, equals the
  spec-level transfer normalized to canonical bottom. Two composition shapes
  recur through the induction:

    - Sequential (\<open>Plus\<close>/\<open>Minus\<close>/\<open>Times\<close>, \<open>Not\<close>, \<open>And True\<close>, \<open>Or False\<close>,
      \<open>Less\<close>/\<open>Eq\<close>'s two-narrow chain): \<open>afilter_reductive\<close> /
      \<open>bfilter_reductive\<close> guarantee a later step can never revive a
      location an earlier step already narrowed to \<open>is_bot\<close>, so once the
      inner step goes \<open>Bot\<close> the outer step does too, without recomputation.

    - Compound join (\<open>And False\<close>/\<open>Or True\<close>): handled directly by
      @{const bfilter_st_lift}'s own footprint-scoped definition, not by a
      recursive sub-lift, since spec's join is plain pointwise \<open>\<squnion>\<close> (kept
      executable) rather than a canonicalizing one.
\<close>

text \<open>
  Locality: \<open>bfilter_st\<close> touches no location outside its own finite
  @{const footprint_exp} -- with one escape. A gated join whose gates ruled
  both disjuncts out is \<open>bot\<close> everywhere, and so changes locations the
  expression never mentions. The disjunction below states exactly that, and
  is why the lifted join case probes one location beyond the two footprints:
  a join that went entirely \<open>bot\<close> is invisible to a footprint-scoped probe
  when neither disjunct mentions a variable.
\<close>

lemma bfilter_st_bot:
  assumes "fun_of_resolved_st_q_for gs s = \<bottom>"
  shows "fun_of_resolved_st_q_for gs (bfilter_st gs b res s) = \<bottom>"
proof -
  have "fun_of_resolved_st_q_for gs (bfilter_st gs b res s)
          = bfilter b res (fun_of_resolved_st_q_for gs s)"
    by (rule bfilter_st_commute)
  also have "... \<le> fun_of_resolved_st_q_for gs s" by (rule bfilter_reductive)
  finally show ?thesis using assms by (simp add: le_bot)
qed

lemma bfilter_st_locality:
  "x \<notin> set (footprint_exp b) \<Longrightarrow>
     fun_of_resolved_st_q_for gs (bfilter_st gs b res s) x = fun_of_resolved_st_q_for gs s x
     \<or> fun_of_resolved_st_q_for gs (bfilter_st gs b res s) = \<bottom>"
proof (induction b arbitrary: res s)
  case (N n)
  then show ?case
    unfolding bfilter_st.simps Let_def case_prod_beta using afilter_st_locality by simp
next
  case (V y)
  then show ?case
    unfolding bfilter_st.simps Let_def case_prod_beta using afilter_st_locality by simp
next
  case (Plus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta
                  afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Minus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta
                  afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Times e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta
                  afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Not b)
  then show ?case by (simp add: Not.IH)
next
  case (And b1 b2)
  then have x1: "x \<notin> set (footprint_exp b1)" and x2: "x \<notin> set (footprint_exp b2)" by simp_all
  show ?case
  proof (cases res)
    case True
    from And.IH(2)[OF x2, where res = True and s = s] show ?thesis
    proof
      assume h2: "fun_of_resolved_st_q_for gs (bfilter_st gs b2 True s) x
                    = fun_of_resolved_st_q_for gs s x"
      from And.IH(1)[OF x1, where res = True and s = "bfilter_st gs b2 True s"]
      show ?thesis using h2 True by auto
    next
      assume h2: "fun_of_resolved_st_q_for gs (bfilter_st gs b2 True s) = \<bottom>"
      then have "fun_of_resolved_st_q_for gs (bfilter_st gs b1 True (bfilter_st gs b2 True s)) = \<bottom>"
        by (rule bfilter_st_bot)
      then show ?thesis using True by simp
    qed
  next
    case False
    have g1: "fun_of_resolved_st_q_for gs
                (if feasible b1 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b1 False s else bot) x
                 = fun_of_resolved_st_q_for gs s x
              \<or> fun_of_resolved_st_q_for gs
                (if feasible b1 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b1 False s else bot) = \<bottom>"
      using And.IH(1)[OF x1, where res = False and s = s]
      by (cases "feasible b1 False (fun_of_resolved_st_q_for gs s)")
         (simp_all add: fun_of_resolved_st_q_for_bot bot_fun_def)
    have g2: "fun_of_resolved_st_q_for gs
                (if feasible b2 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b2 False s else bot) x
                 = fun_of_resolved_st_q_for gs s x
              \<or> fun_of_resolved_st_q_for gs
                (if feasible b2 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b2 False s else bot) = \<bottom>"
      using And.IH(2)[OF x2, where res = False and s = s]
      by (cases "feasible b2 False (fun_of_resolved_st_q_for gs s)")
         (simp_all add: fun_of_resolved_st_q_for_bot bot_fun_def)
    show ?thesis using False g1 g2 by (auto simp: sup_fun_def)
  qed
next
  case (Or b1 b2)
  then have x1: "x \<notin> set (footprint_exp b1)" and x2: "x \<notin> set (footprint_exp b2)" by simp_all
  show ?case
  proof (cases res)
    case True
    have g1: "fun_of_resolved_st_q_for gs
                (if feasible b1 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b1 True s else bot) x
                 = fun_of_resolved_st_q_for gs s x
              \<or> fun_of_resolved_st_q_for gs
                (if feasible b1 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b1 True s else bot) = \<bottom>"
      using Or.IH(1)[OF x1, where res = True and s = s]
      by (cases "feasible b1 True (fun_of_resolved_st_q_for gs s)")
         (simp_all add: fun_of_resolved_st_q_for_bot bot_fun_def)
    have g2: "fun_of_resolved_st_q_for gs
                (if feasible b2 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b2 True s else bot) x
                 = fun_of_resolved_st_q_for gs s x
              \<or> fun_of_resolved_st_q_for gs
                (if feasible b2 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st gs b2 True s else bot) = \<bottom>"
      using Or.IH(2)[OF x2, where res = True and s = s]
      by (cases "feasible b2 True (fun_of_resolved_st_q_for gs s)")
         (simp_all add: fun_of_resolved_st_q_for_bot bot_fun_def)
    show ?thesis using True g1 g2 by (auto simp: sup_fun_def)
  next
    case False
    from Or.IH(2)[OF x2, where res = False and s = s] show ?thesis
    proof
      assume h2: "fun_of_resolved_st_q_for gs (bfilter_st gs b2 False s) x
                    = fun_of_resolved_st_q_for gs s x"
      from Or.IH(1)[OF x1, where res = False and s = "bfilter_st gs b2 False s"]
      show ?thesis using h2 False by auto
    next
      assume h2: "fun_of_resolved_st_q_for gs (bfilter_st gs b2 False s) = \<bottom>"
      then have "fun_of_resolved_st_q_for gs (bfilter_st gs b1 False (bfilter_st gs b2 False s)) = \<bottom>"
        by (rule bfilter_st_bot)
      then show ?thesis using False by simp
    qed
  qed
next
  case (Less e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  show ?case
    unfolding bfilter_st.simps Let_def case_prod_beta
    using afilter_st_locality[OF x1] afilter_st_locality[OF x2] by simp
next
  case (Eq e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  show ?case
    unfolding bfilter_st.simps Let_def case_prod_beta
    using afilter_st_locality[OF x1] afilter_st_locality[OF x2] by simp
qed

lemma afilter_lift_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
    and IH1: "!!s'. live_resolved_st_q gs s' ==>
                map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e1 a1 (Lifted s')) =
                normalize_lift is_bot_state (afilter e1 a1 (fun_of_resolved_st_q_for gs s'))"
    and IH2: "map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e2 a2 (Lifted s)) =
                normalize_lift is_bot_state (afilter e2 a2 (fun_of_resolved_st_q_for gs s))"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))) =
         normalize_lift is_bot_state (afilter e1 a1 (afilter e2 a2 (fun_of_resolved_st_q_for gs s)))"
proof (cases "is_bot_state (afilter e2 a2 (fun_of_resolved_st_q_for gs s))")
  case True
  then have bot2: "afilter_st_lift gs e2 a2 (Lifted s) = Bot"
    using IH2 by (cases "afilter_st_lift gs e2 a2 (Lifted s)") simp_all
  have "is_bot_state (afilter e1 a1 (afilter e2 a2 (fun_of_resolved_st_q_for gs s)))"
    using is_bot_state_mono[OF afilter_reductive True] .
  with bot2 show ?thesis by simp
next
  case False
  then obtain t where t: "afilter_st_lift gs e2 a2 (Lifted s) = Lifted t"
    using IH2 by (cases "afilter_st_lift gs e2 a2 (Lifted s)") simp_all
  have ft: "fun_of_resolved_st_q_for gs t = afilter e2 a2 (fun_of_resolved_st_q_for gs s)"
    using IH2 t False by simp
  have live_t: "live_resolved_st_q gs t"
    unfolding live_resolved_st_q_def ft using False by simp
  show ?thesis
    unfolding t using IH1[OF live_t] ft by simp
qed

lemma bfilter_lift_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
    and IH1: "!!s'. live_resolved_st_q gs s' ==>
                map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b1 res (Lifted s')) =
                normalize_lift is_bot_state (bfilter b1 res (fun_of_resolved_st_q_for gs s'))"
    and IH2: "map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b2 res (Lifted s)) =
                normalize_lift is_bot_state (bfilter b2 res (fun_of_resolved_st_q_for gs s))"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (bfilter_st_lift gs b1 res (bfilter_st_lift gs b2 res (Lifted s))) =
         normalize_lift is_bot_state (bfilter b1 res (bfilter b2 res (fun_of_resolved_st_q_for gs s)))"
proof (cases "is_bot_state (bfilter b2 res (fun_of_resolved_st_q_for gs s))")
  case True
  then have bot2: "bfilter_st_lift gs b2 res (Lifted s) = Bot"
    using IH2 by (cases "bfilter_st_lift gs b2 res (Lifted s)") simp_all
  have "is_bot_state (bfilter b1 res (bfilter b2 res (fun_of_resolved_st_q_for gs s)))"
    using is_bot_state_mono[OF bfilter_reductive True] .
  with bot2 show ?thesis by simp
next
  case False
  then obtain t where t: "bfilter_st_lift gs b2 res (Lifted s) = Lifted t"
    using IH2 by (cases "bfilter_st_lift gs b2 res (Lifted s)") simp_all
  have ft: "fun_of_resolved_st_q_for gs t = bfilter b2 res (fun_of_resolved_st_q_for gs s)"
    using IH2 t False by simp
  have live_t: "live_resolved_st_q gs t"
    unfolding live_resolved_st_q_def ft using False by simp
  show ?thesis
    unfolding t using IH1[OF live_t] ft by simp
qed

lemma lift_probe_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (if list_ex (\<lambda>x. is_bot (fun_of_resolved_st_q_for gs (bfilter_st gs b res s) x))
                 (probe_exp b)
            then Bot
            else Lifted (bfilter_st gs b res s))
         = normalize_lift is_bot_state (bfilter b res (fun_of_resolved_st_q_for gs s))"
proof -
  define t where "t = bfilter_st gs b res s"
  have ft: "fun_of_resolved_st_q_for gs t = bfilter b res (fun_of_resolved_st_q_for gs s)"
    unfolding t_def by (rule bfilter_st_commute)
  have bot_is_bot: "is_bot (bot :: 'a)" by (simp add: is_bot_correct gamma_bot)
  have iff: "is_bot_state (fun_of_resolved_st_q_for gs t) \<longleftrightarrow>
      list_ex (\<lambda>x. is_bot (fun_of_resolved_st_q_for gs t x)) (probe_exp b)"
  proof
    assume "is_bot_state (fun_of_resolved_st_q_for gs t)"
    then obtain x where x: "is_bot (fun_of_resolved_st_q_for gs t x)" by (rule is_bot_stateE)
    show "list_ex (\<lambda>x. is_bot (fun_of_resolved_st_q_for gs t x)) (probe_exp b)"
    proof (cases "x \<in> set (footprint_exp b)")
      case True
      then show ?thesis using x by (auto simp: probe_exp_def list_ex_iff)
    next
      case outside: False
      have "fun_of_resolved_st_q_for gs t x = fun_of_resolved_st_q_for gs s x
              \<or> fun_of_resolved_st_q_for gs t = \<bottom>"
        unfolding t_def by (rule bfilter_st_locality[OF outside])
      then show ?thesis
      proof
        assume "fun_of_resolved_st_q_for gs t x = fun_of_resolved_st_q_for gs s x"
        with x have "is_bot (fun_of_resolved_st_q_for gs s x)" by simp
        with live_resolved_st_qE[OF live] show ?thesis by blast
      next
        assume "fun_of_resolved_st_q_for gs t = \<bottom>"
        then have "is_bot (fun_of_resolved_st_q_for gs t (STR ''''))"
          using bot_is_bot by (simp add: bot_fun_def)
        then show ?thesis by (simp add: probe_exp_def)
      qed
    qed
  next
    assume "list_ex (\<lambda>x. is_bot (fun_of_resolved_st_q_for gs t x)) (probe_exp b)"
    then show "is_bot_state (fun_of_resolved_st_q_for gs t)"
      by (auto simp: list_ex_iff intro: is_bot_stateI)
  qed
  show ?thesis
    unfolding t_def[symmetric]
    using iff ft by (cases "is_bot_state (fun_of_resolved_st_q_for gs t)") simp_all
qed

lemma afilter_st_lift_correct:
  fixes s :: "'a resolved_st_q"
  assumes "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e a (Lifted s)) =
         normalize_lift is_bot_state (afilter e a (fun_of_resolved_st_q_for gs s))"
using assms proof (induction e arbitrary: a s)
  case (N n)
  then show ?case by (simp add: live_resolved_st_q_def)
next
    case (V x)
  show ?case
    unfolding afilter_st_lift.simps bind_lift_Lifted afilter.simps
    by (rule update_resolved_st_q_lift_correct[OF V.prems])
next
  case (Plus e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Plus_unfold bind_lift_Lifted Let_def case_prod_beta
    using afilter_lift_step[OF Plus.prems Plus.IH(1) Plus.IH(2)[OF Plus.prems]]
    by simp
next
  case (Minus e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Minus_unfold bind_lift_Lifted Let_def case_prod_beta
    using afilter_lift_step[OF Minus.prems Minus.IH(1) Minus.IH(2)[OF Minus.prems]]
    by simp
next
  case (Times e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Times_unfold bind_lift_Lifted Let_def case_prod_beta
    using afilter_lift_step[OF Times.prems Times.IH(1) Times.IH(2)[OF Times.prems]]
    by simp
next
  case (Less e1 e2) then show ?case by (simp add: live_resolved_st_q_def)
next
  case (Eq e1 e2) then show ?case by (simp add: live_resolved_st_q_def)
next
  case (Not e) then show ?case by (simp add: live_resolved_st_q_def)
next
  case (And e1 e2) then show ?case by (simp add: live_resolved_st_q_def)
next
  case (Or e1 e2) then show ?case by (simp add: live_resolved_st_q_def)
qed

lemma bfilter_st_lift_correct:
  fixes s :: "'a resolved_st_q"
  assumes "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b res (Lifted s)) =
         normalize_lift is_bot_state (bfilter b res (fun_of_resolved_st_q_for gs s))"
using assms proof (induction b arbitrary: res s)
  case (N n)
  show ?case
    using N.prems
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_Lifted
        afilter_st_lift_correct[OF N.prems] live_resolved_st_q_def)
next
  case (V x)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_Lifted
        update_resolved_st_q_lift_correct[OF V.prems] fun_upd_def)
next
  case (Plus e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_Lifted
        afilter_lift_step[OF Plus.prems afilter_st_lift_correct afilter_st_lift_correct[OF Plus.prems]])
next
  case (Minus e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_Lifted
        afilter_lift_step[OF Minus.prems afilter_st_lift_correct afilter_st_lift_correct[OF Minus.prems]])
next
  case (Times e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_Lifted
        afilter_lift_step[OF Times.prems afilter_st_lift_correct afilter_st_lift_correct[OF Times.prems]])
next
  case (Not b)
  then show ?case by (simp add: Not.IH)
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis
      using bfilter_lift_step[OF And.prems And.IH(1) And.IH(2)[OF And.prems]]
      by simp
  next
    case False
    have r: "res = False" using False by simp
    show ?thesis
      unfolding r bfilter_st_lift.simps bind_lift_Lifted
      by (rule lift_probe_step[OF And.prems])
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have r: "res = True" using True by simp
    show ?thesis
      unfolding r bfilter_st_lift.simps bind_lift_Lifted
      by (rule lift_probe_step[OF Or.prems])
  next
    case False
    then show ?thesis
      using bfilter_lift_step[OF Or.prems Or.IH(1) Or.IH(2)[OF Or.prems]]
      by simp
  qed
next
  case (Less e1 e2)
  show ?case
    unfolding bfilter_st_lift.simps bfilter_Less_unfold bind_lift_Lifted Let_def case_prod_beta
    using afilter_lift_step[OF Less.prems afilter_st_lift_correct afilter_st_lift_correct[OF Less.prems]]
    by simp
next
  case (Eq e1 e2)
  show ?case
    unfolding bfilter_st_lift.simps bfilter_Eq_unfold bind_lift_Lifted Let_def case_prod_beta
    using afilter_lift_step[OF Eq.prems afilter_st_lift_correct afilter_st_lift_correct[OF Eq.prems]]
    by simp
qed

end

end

