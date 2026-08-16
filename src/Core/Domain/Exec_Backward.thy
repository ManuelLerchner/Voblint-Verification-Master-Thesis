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
       bfilter_st gs b1 False s \<squnion> bfilter_st gs b2 False s"
  | "bfilter_st gs (Or b1 b2) True s =
       bfilter_st gs b1 True s \<squnion> bfilter_st gs b2 True s"
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
  the other branch already settled) or join two branches via \<open>\<squnion>\<close> -- and joining two
  live branches can never produce a witness-bottom result, since \<open>is_bot\<close> is
  downward closed (@{thm is_bot_mono}) and each branch's own value is a lower bound
  of the join. No per-domain code is needed: this is generic in the
  @{locale backward_domain} operations, exactly like \<open>afilter_st\<close>/\<open>bfilter_st\<close>
  themselves.
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
  then show ?case by (simp add: afilter_st_commute split: prod.splits)
next
  case (Eq e1 e2)
  then show ?case by (simp add: afilter_st_commute split: prod.splits)
qed

text \<open>
  Locality: \<open>afilter_st\<close>/\<open>bfilter_st\<close> never touch a location outside their own
  finite @{const footprint_exp}/@{const footprint_exp}. This is what lets the
  lifted compound-boolean join below decide witness-bottom for its raw \<open>\<squnion>\<close>
  result from a live input by probing only that finite footprint, rather than
  the whole (infinite) state.
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

lemma bfilter_st_locality:
  "x \<notin> set (footprint_exp b) \<Longrightarrow>
     fun_of_resolved_st_q_for gs (bfilter_st gs b res s) x = fun_of_resolved_st_q_for gs s x"
proof (induction b arbitrary: res s)
  case (N n)
  then show ?case unfolding bfilter_st.simps Let_def case_prod_beta using afilter_st_locality by simp
next
  case (V y)
  then show ?case unfolding bfilter_st.simps Let_def case_prod_beta using afilter_st_locality by simp
next
  case (Plus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Minus e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Times e1 e2)
  then have x1: "x \<notin> set (footprint_exp e1)" and x2: "x \<notin> set (footprint_exp e2)" by simp_all
  then show ?case
    by (simp add: bfilter_st.simps Let_def case_prod_beta afilter_st_locality[OF x1] afilter_st_locality[OF x2])
next
  case (Not b)
  then show ?case by (simp add: Not.IH)
next
    case (And b1 b2)
  then have x1: "x \<notin> set (footprint_exp b1)" and x2: "x \<notin> set (footprint_exp b2)" by simp_all
  show ?case
  proof (cases res)
    case True
    show ?thesis
      using And.IH(1)[OF x1] And.IH(2)[OF x2] True by simp
  next
    case False
    show ?thesis
      using And.IH(1)[OF x1] And.IH(2)[OF x2] False by simp
  qed
next
  case (Or b1 b2)
  then have x1: "x \<notin> set (footprint_exp b1)" and x2: "x \<notin> set (footprint_exp b2)" by simp_all
  show ?case
  proof (cases res)
    case True
    show ?thesis
      using Or.IH(1)[OF x1] Or.IH(2)[OF x2] True by simp
  next
    case False
    show ?thesis
      using Or.IH(1)[OF x1] Or.IH(2)[OF x2] False by simp
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

text \<open>
  \<open>bfilter_st_lift\<close> mirrors \<open>bfilter_st\<close>'s recursion for the sequential cases
  (\<open>Not\<close>/\<open>And True\<close>/\<open>Or False\<close>/\<open>Less\<close>/\<open>Eq\<close>) exactly like \<open>afilter_st_lift\<close>. The
  compound-join cases (\<open>And False\<close>/\<open>Or True\<close>) cannot be built the same way:
  spec-level \<open>bfilter\<close> joins its two branch results with plain pointwise \<open>\<squnion>\<close>
  (needed so \<open>bfilter_sign\<close>/\<open>bfilter_ivl\<close> stay code-generatable -- \<open>is_bot_state\<close>
  is not executable, since \<open>vname\<close> is not a finite type), and that plain join
  can leave a live result even when both branches independently narrowed to a
  witness-bottom at different locations. Recursively lifting each branch first
  (collapsing to \<open>Bot\<close> before the join) would answer a different, more precise
  question than spec's own \<open>\<squnion>\<close> actually computes. Instead, the join cases run
  the raw \<open>bfilter_st\<close> computation (exactly mirroring spec) and then decide
  witness-bottom with one finite probe over the two branches' combined
  @{const footprint_exp}, sound by @{thm bfilter_st_locality} against a live
  input.
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
              (bfilter_st gs b1 False s \<squnion> bfilter_st gs b2 False s) x))
            (footprint_exp b1 @ footprint_exp b2)
       then Bot
       else Lifted (bfilter_st gs b1 False s \<squnion> bfilter_st gs b2 False s)
     }"
  | "bfilter_st_lift gs (Or b1 b2) True x_lift = do {
       s <- x_lift;
       if list_ex (%x. is_bot (fun_of_resolved_st_q_for gs
              (bfilter_st gs b1 True s \<squnion> bfilter_st gs b2 True s) x))
            (footprint_exp b1 @ footprint_exp b2)
       then Bot
       else Lifted (bfilter_st gs b1 True s \<squnion> bfilter_st gs b2 True s)
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

lemma bfilter_lift_join_step:
  fixes s :: "'a resolved_st_q"
  assumes live: "live_resolved_st_q gs s"
  shows "map_lift (fun_of_resolved_st_q_for gs)
           (if list_ex (%x. is_bot (fun_of_resolved_st_q_for gs
                  (bfilter_st gs b1 res s \<squnion> bfilter_st gs b2 res s) x))
                (footprint_exp b1 @ footprint_exp b2)
            then Bot
            else Lifted (bfilter_st gs b1 res s \<squnion> bfilter_st gs b2 res s)) =
         normalize_lift is_bot_state
           (bfilter b1 res (fun_of_resolved_st_q_for gs s) \<squnion> bfilter b2 res (fun_of_resolved_st_q_for gs s))"
proof -
  define t where "t = bfilter_st gs b1 res s \<squnion> bfilter_st gs b2 res s"
  have ft: "fun_of_resolved_st_q_for gs t =
      bfilter b1 res (fun_of_resolved_st_q_for gs s) \<squnion> bfilter b2 res (fun_of_resolved_st_q_for gs s)"
    unfolding t_def by (simp add: bfilter_st_commute)
  have iff: "is_bot_state (fun_of_resolved_st_q_for gs t) \<longleftrightarrow>
      list_ex (%x. is_bot (fun_of_resolved_st_q_for gs t x)) (footprint_exp b1 @ footprint_exp b2)"
  proof
    assume "is_bot_state (fun_of_resolved_st_q_for gs t)"
    then obtain x where x: "is_bot (fun_of_resolved_st_q_for gs t x)" by (rule is_bot_stateE)
    have "x \<in> set (footprint_exp b1) \<union> set (footprint_exp b2)"
    proof (rule ccontr)
      assume "x \<notin> set (footprint_exp b1) \<union> set (footprint_exp b2)"
      then have nx1: "x \<notin> set (footprint_exp b1)" and nx2: "x \<notin> set (footprint_exp b2)" by auto
      have "fun_of_resolved_st_q_for gs t x = fun_of_resolved_st_q_for gs s x"
        unfolding t_def
        using bfilter_st_locality[OF nx1] bfilter_st_locality[OF nx2]
        by simp
      with x have "is_bot (fun_of_resolved_st_q_for gs s x)" by simp
      with live_resolved_st_qE[OF live] show False by blast
    qed
    then show "list_ex (%x. is_bot (fun_of_resolved_st_q_for gs t x)) (footprint_exp b1 @ footprint_exp b2)"
      using x by (auto simp: list_ex_iff)
  next
    assume "list_ex (%x. is_bot (fun_of_resolved_st_q_for gs t x)) (footprint_exp b1 @ footprint_exp b2)"
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
    then show ?thesis
      unfolding bfilter_st_lift.simps False bfilter.simps
      using bfilter_lift_join_step[OF And.prems]
      by (simp add: sup_fun_def)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis
      unfolding bfilter_st_lift.simps True bfilter.simps
      using bfilter_lift_join_step[OF Or.prems]
      by (simp add: sup_fun_def)
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

