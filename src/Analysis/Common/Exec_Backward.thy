  theory Exec_Backward
    imports "Voblint_Exec.Exec_St" "Voblint_Domain.Backward_Domain_Refined"
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
  \<open>is_empty\<close> collapses to \<open>Bot\<close> via @{const update_resolved_st_q_lift}.  The compound
  cases either sequence two single-variable narrows (never re-checking a location
  the other branch already settled) or join two gated branches via \<open>\<squnion>\<close>.  Joining
  two live branches can never produce a witness-bottom result, since \<open>is_empty\<close> is
  downward closed (@{thm is_empty_antimono}) and each branch's own value is a lower bound
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
  \<open>bfilter_st_lift\<close> mirrors \<open>bfilter_lifted\<close>'s recursion one constructor at a
  time, exactly as \<open>bfilter_st\<close> mirrors plain \<open>bfilter\<close>: the sequential cases
  (\<open>Not\<close>/\<open>And True\<close>/\<open>Or False\<close>/\<open>Less\<close>/\<open>Eq\<close>) chain two narrowing steps, and the
  compound-join cases (\<open>And False\<close>/\<open>Or True\<close>) gate each arm to structural
  \<open>Bot\<close> via @{const feasible} and join at the lifted level, ahead of the
  join rather than after it. This is what \<open>bfilter\<close>'s own join (kept plain and
  pointwise so \<open>bfilter_sign\<close>/\<open>bfilter_ivl\<close> stay code-generatable) cannot
  afford: a witness-bottom arm collapses to \<open>Bot\<close> here regardless of what the
  other arm's unrefined locations look like, so \<open>Bot \<squnion> x = x\<close> discards it
  exactly, with no whole-expression probe needed afterward.
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
       (if feasible b1 False (fun_of_resolved_st_q_for gs s)
        then bfilter_st_lift gs b1 False (Lifted s) else Bot)
       \<squnion> (if feasible b2 False (fun_of_resolved_st_q_for gs s)
          then bfilter_st_lift gs b2 False (Lifted s) else Bot)
     }"
  | "bfilter_st_lift gs (Or b1 b2) True x_lift = do {
       s <- x_lift;
       (if feasible b1 True (fun_of_resolved_st_q_for gs s)
        then bfilter_st_lift gs b1 True (Lifted s) else Bot)
       \<squnion> (if feasible b2 True (fun_of_resolved_st_q_for gs s)
          then bfilter_st_lift gs b2 True (Lifted s) else Bot)
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
  case (N n) then show ?case by simp
next
  case (V x) then show ?case by simp
next
  case (Plus e1 e2) then show ?case by simp
next
  case (Minus e1 e2) then show ?case by simp
next
  case (Times e1 e2) then show ?case by simp
next
  case (Not b) then show ?case by simp
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
  case (Less e1 e2) then show ?case by simp
next
  case (Eq e1 e2) then show ?case by simp
qed

end

context backward_domain_refined
begin

lemma afilter_lift_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
    and IH1: "!!s'. live_resolved_st_q gs s' ==>
                map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e1 a1 (Lifted s')) =
                normalize_lift is_empty_state (afilter e1 a1 (fun_of_resolved_st_q_for gs s'))"
    and IH2: "map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e2 a2 (Lifted s)) =
                normalize_lift is_empty_state (afilter e2 a2 (fun_of_resolved_st_q_for gs s))"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (afilter_st_lift gs e1 a1 (afilter_st_lift gs e2 a2 (Lifted s))) =
         normalize_lift is_empty_state (afilter e1 a1 (afilter e2 a2 (fun_of_resolved_st_q_for gs s)))"
proof (cases "is_empty_state (afilter e2 a2 (fun_of_resolved_st_q_for gs s))")
  case True
  then have bot2: "afilter_st_lift gs e2 a2 (Lifted s) = Bot"
    using IH2 by (cases "afilter_st_lift gs e2 a2 (Lifted s)") simp_all
  have "is_empty_state (afilter e1 a1 (afilter e2 a2 (fun_of_resolved_st_q_for gs s)))"
    using is_empty_state_antimono[OF afilter_reductive True] .
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

text \<open>
  \<open>bfilter_lift_bind_step\<close> composes two sequential lifted narrowing steps
  (\<open>And True\<close>, \<open>Or False\<close>): if the inner step already went \<open>Bot\<close>, the outer
  step is never reached and the composite is \<open>Bot\<close> too; otherwise it recurses
  on the inner step's live witness. This is @{const bind_lift}'s own
  associativity, specialized to the executable/lifted correspondence.
\<close>

lemma bfilter_lift_bind_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
    and IH1: "!!s'. live_resolved_st_q gs s' ==>
                map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b1 res (Lifted s')) =
                bfilter_lifted b1 res (fun_of_resolved_st_q_for gs s')"
    and IH2: "map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b2 res (Lifted s)) =
                bfilter_lifted b2 res (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (bfilter_st_lift gs b1 res (bfilter_st_lift gs b2 res (Lifted s))) =
         bind_lift (bfilter_lifted b2 res (fun_of_resolved_st_q_for gs s)) (bfilter_lifted b1 res)"
proof (cases "bfilter_st_lift gs b2 res (Lifted s)")
  case Bot
  then show ?thesis using IH2 by simp
next
  case (Lifted t)
  have eq: "Lifted (fun_of_resolved_st_q_for gs t) = bfilter_lifted b2 res (fun_of_resolved_st_q_for gs s)"
    using IH2 Lifted by simp
  have live_t: "live_resolved_st_q gs t"
  proof -
    have "normalized_lift is_empty_state (Lifted (fun_of_resolved_st_q_for gs t))"
      using bfilter_lifted_normalized[of b2 res "fun_of_resolved_st_q_for gs s"] eq by simp
    then show ?thesis by (simp add: live_resolved_st_q_def)
  qed
    show ?thesis
    unfolding Lifted using IH1[OF live_t] eq[symmetric] by simp
qed

text \<open>
  \<open>bfilter_lift_gate_step\<close> is the executable/lifted correspondence for a
  single gated disjunct, feeding @{const feasible} the same read-back state
  \<open>bfilter_lifted\<close>'s own gate reads: a feasible disjunct recurses, an
  infeasible one contributes \<open>Bot\<close> on both sides.
\<close>

lemma bfilter_lift_gate_step:
  fixes s :: "'a resolved_st_q"
  assumes IH: "map_lift (fun_of_resolved_st_q_for gs) (bfilter_st_lift gs b pol (Lifted s)) =
                 bfilter_lifted b pol (fun_of_resolved_st_q_for gs s)"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (if feasible b pol (fun_of_resolved_st_q_for gs s)
            then bfilter_st_lift gs b pol (Lifted s) else Bot)
         = (if feasible b pol (fun_of_resolved_st_q_for gs s)
            then bfilter_lifted b pol (fun_of_resolved_st_q_for gs s) else Bot)"
  by (cases "feasible b pol (fun_of_resolved_st_q_for gs s)") (simp_all add: IH)



lemma afilter_st_lift_correct:
  fixes s :: "'a resolved_st_q"
  assumes "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs) (afilter_st_lift gs e a (Lifted s)) =
         normalize_lift is_empty_state (afilter e a (fun_of_resolved_st_q_for gs s))"
using assms proof (induction e arbitrary: a s)
  case (N n)
  then show ?case by (simp add: live_resolved_st_q_def)
next
    case (V x)
  show ?case
    unfolding afilter_st_lift.simps bind_lift_left_identity afilter.simps
    by (rule update_resolved_st_q_lift_correct[OF V.prems])
next
  case (Plus e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Plus_unfold bind_lift_left_identity Let_def case_prod_beta
    using afilter_lift_step[OF Plus.prems Plus.IH(1) Plus.IH(2)[OF Plus.prems]]
    by simp
next
  case (Minus e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Minus_unfold bind_lift_left_identity Let_def case_prod_beta
    using afilter_lift_step[OF Minus.prems Minus.IH(1) Minus.IH(2)[OF Minus.prems]]
    by simp
next
  case (Times e1 e2)
  show ?case
    unfolding afilter_st_lift.simps afilter_Times_unfold bind_lift_left_identity Let_def case_prod_beta
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
         bfilter_lifted b res (fun_of_resolved_st_q_for gs s)"
using assms proof (induction b arbitrary: res s)
  case (N n)
  show ?case
    using N.prems
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        afilter_st_lift_correct[OF N.prems] live_resolved_st_q_def)
next
  case (V x)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        update_resolved_st_q_lift_correct[OF V.prems] fun_upd_def)
next
  case (Plus e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        afilter_lift_step[OF Plus.prems afilter_st_lift_correct afilter_st_lift_correct[OF Plus.prems]])
next
  case (Minus e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        afilter_lift_step[OF Minus.prems afilter_st_lift_correct afilter_st_lift_correct[OF Minus.prems]])
next
  case (Times e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
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
      using bfilter_lift_bind_step[OF And.prems And.IH(1) And.IH(2)[OF And.prems]]
      by simp
  next
    case False
    have g1: "map_lift (fun_of_resolved_st_q_for gs)
                (if feasible b1 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st_lift gs b1 False (Lifted s) else Bot)
              = (if feasible b1 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_lifted b1 False (fun_of_resolved_st_q_for gs s) else Bot)"
      by (rule bfilter_lift_gate_step[OF And.IH(1)[OF And.prems]])
    have g2: "map_lift (fun_of_resolved_st_q_for gs)
                (if feasible b2 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_st_lift gs b2 False (Lifted s) else Bot)
              = (if feasible b2 False (fun_of_resolved_st_q_for gs s)
                 then bfilter_lifted b2 False (fun_of_resolved_st_q_for gs s) else Bot)"
      by (rule bfilter_lift_gate_step[OF And.IH(2)[OF And.prems]])
    show ?thesis
      using False
      by (simp add: bind_lift_left_identity map_lift_sup[OF fun_of_resolved_st_q_for_sup] g1 g2)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    have g1: "map_lift (fun_of_resolved_st_q_for gs)
                (if feasible b1 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st_lift gs b1 True (Lifted s) else Bot)
              = (if feasible b1 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_lifted b1 True (fun_of_resolved_st_q_for gs s) else Bot)"
      by (rule bfilter_lift_gate_step[OF Or.IH(1)[OF Or.prems]])
    have g2: "map_lift (fun_of_resolved_st_q_for gs)
                (if feasible b2 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_st_lift gs b2 True (Lifted s) else Bot)
              = (if feasible b2 True (fun_of_resolved_st_q_for gs s)
                 then bfilter_lifted b2 True (fun_of_resolved_st_q_for gs s) else Bot)"
      by (rule bfilter_lift_gate_step[OF Or.IH(2)[OF Or.prems]])
    show ?thesis
      using True
      by (simp add: bind_lift_left_identity map_lift_sup[OF fun_of_resolved_st_q_for_sup] g1 g2)
  next
    case False
    then show ?thesis
      using bfilter_lift_bind_step[OF Or.prems Or.IH(1) Or.IH(2)[OF Or.prems]]
      by simp
  qed
next
    case (Less e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        afilter_lift_step[OF Less.prems afilter_st_lift_correct afilter_st_lift_correct[OF Less.prems]])
next
  case (Eq e1 e2)
  show ?case
    by (simp add: bfilter_st_lift.simps bfilter.simps Let_def case_prod_beta bind_lift_left_identity
        afilter_lift_step[OF Eq.prems afilter_st_lift_correct afilter_st_lift_correct[OF Eq.prems]])
qed

end

end

