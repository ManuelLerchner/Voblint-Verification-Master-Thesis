theory Exec_St_Transfer
  imports Exec_St_Algebra "Voblint_Framework.Transfer_Algebra"
begin

section \<open>Refinement to variable-indexed states\<close>

text \<open>
  Everything so far is stated about locations. A program, though, talks about
  variable names, and which names are global is a property of the program, not
  of the carrier. \<open>location_of\<close> is that classifier applied: it turns a name
  into the location holding its value, and \<open>fun_of_resolved_st_for\<close> reads a
  whole state back as the function \<^typ>\<open>'a abs_state\<close> that soundness is stated
  over.

  The rest of the theory is the operations a call and a return need --
  assignment, formal binding, restriction to one side of the ownership split,
  frame entry, and the caller/callee combination -- each paired with the
  equation saying that performing it on the carrier and then reading back
  agrees with performing its counterpart on the read-back function. Those
  equations are the interface every soundness proof downstream actually uses.
\<close>

subsection \<open>Location classification and projection\<close>

definition location_of ::
  "(vname => bool) => vname => location" where
  "location_of gs x =
     (if gs x then Global_Location x else Local_Location x)"

text \<open>
  Both tags carry the vname they classify, so a classified location determines
  its own name and two names collide only when they are equal.  Proofs about
  \<^const>\<open>location_of\<close> therefore need no case split on \<^term>\<open>gs x\<close> against
  \<^term>\<open>gs y\<close>.
\<close>

lemma location_vname_location_of [simp]:
  "location_vname (location_of gs x) = x"
  by (simp add: location_of_def)

lemma location_of_eq_iff [simp]:
  "location_of gs x = location_of gs y \<longleftrightarrow> x = y"
  by (auto simp: location_of_def)

text \<open>
  Deliberately no \<open>[simp]\<close> rule matching \<^term>\<open>location_of gs x = Local_Location y\<close>
  against a constructor. Such a rule reads well in isolation, but proofs here
  derive facts of exactly that shape and then use them as rewrites for
  \<^const>\<open>location_of\<close>; a simp rule on the same left-hand side collapses the
  equation to its classification side and takes the rewrite away.
\<close>

definition fun_of_resolved_st_for ::
  "(vname => bool) => ('a::bot) resolved_st => vname => 'a" where
  "fun_of_resolved_st_for gs s x =
     lookup_resolved_st s (location_of gs x)"

lemma fun_of_resolved_st_for_update_location [simp]:
  "fun_of_resolved_st_for gs
      (update_resolved_st s (location_of gs x) a) =
   (fun_of_resolved_st_for gs s)(x := a)"
proof (rule ext)
  fix y
  show "fun_of_resolved_st_for gs
      (update_resolved_st s (location_of gs x) a) y =
    ((fun_of_resolved_st_for gs s)(x := a)) y"
    unfolding fun_of_resolved_st_for_def    by (cases "x = y"; cases "gs x"; cases "gs y";
        simp_all add: location_of_def)
qed


lemma map_of_filter_fst:
  fixes P :: "location => bool"
    and xs :: "(location \<times> 'a) list"
    and k :: location
  shows "map_of (filter (\<lambda>p. P (fst p)) xs) k =
     (if P k then map_of xs k else None)"
  by (induction xs) auto

definition fun_of_resolved_st_q_for ::
  "(vname => bool) => ('a::bot) resolved_st_q => vname => 'a"
where
  "fun_of_resolved_st_q_for gs s x =
     lookup_resolved_st_q s (location_of gs x)"


lemma fun_of_resolved_st_q_for_bot [simp]:
  "fun_of_resolved_st_q_for gs (bot :: ('a::order_bot) resolved_st_q) = bot"
  by (rule ext) (simp add: fun_of_resolved_st_q_for_def)

text \<open>
  The quotient-level projection agrees with the raw one at \<open>s\<close>'s own chosen
  representative -- so any raw-level fact about @{const fun_of_resolved_st_for}
  transports directly to @{const fun_of_resolved_st_q_for} through
  @{const rep_resolved_st}, with no separate quotient-respectfulness argument
  needed: @{const rep_resolved_st} is a genuine function of \<open>s\<close>, so anything
  defined through it is automatically well-defined on the quotient.
\<close>

lemma fun_of_resolved_st_q_for_rep:
  "fun_of_resolved_st_q_for gs s = fun_of_resolved_st_for gs (rep_resolved_st s)"
  unfolding fun_of_resolved_st_q_for_def fun_of_resolved_st_for_def
  by (rule ext) (simp add: lookup_rep_resolved_st_q)

lemma fun_of_resolved_st_q_for_mono:
  assumes "s \<le> t"
  shows "fun_of_resolved_st_q_for gs s \<le> fun_of_resolved_st_q_for gs t"
  using assms
  unfolding fun_of_resolved_st_q_for_def le_fun_def
  by (simp add: le_resolved_st_q_iff)


text \<open>
  Each quotient-level refinement equation is its raw counterpart transported
  along the quotient: unfolding the projection leaves a goal in
  \<^const>\<open>lookup_resolved_st_q\<close>, \<open>transfer\<close> lowers it to
  \<^const>\<open>lookup_resolved_st\<close>, and the raw lemma -- read at the same unfolded
  shape -- closes it. An operation returning the quotient has no \<open>rep_eq\<close> to
  unfold instead, since its representative is fixed only up to
  \<^const>\<open>eq_resolved_st\<close>.
\<close>


subsection \<open>Assignment and formal binding\<close>

definition combine_assign_resolved ::
  "(vname => bool) => vname option => 'a => ('a::bot) resolved_st
   => 'a resolved_st"
where
  "combine_assign_resolved gs dst v s =
     (case dst of None => s
      | Some x => update_resolved_st s (location_of gs x) v)"

lemma eq_resolved_st_combine_assign:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (combine_assign_resolved gs dst v s)
      (combine_assign_resolved gs dst v t)"
  by (unfold combine_assign_resolved_def; cases dst;
      simp_all add: assms eq_resolved_st_update)

lift_definition combine_assign_resolved_q ::
  "(vname => bool) => vname option => 'a => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is combine_assign_resolved
  by (rule eq_resolved_st_combine_assign)

lemma lookup_combine_assign_resolved_q [simp]:
  "lookup_resolved_st_q (combine_assign_resolved_q gs dst v s) loc =
     (case dst of
        None => lookup_resolved_st_q s loc
      | Some x =>
          if location_of gs x = loc then v
          else lookup_resolved_st_q s loc)"
  by transfer (auto simp add:combine_assign_resolved_def split:option.splits)

lemma fun_of_resolved_st_for_combine_assign [simp]:
  "fun_of_resolved_st_for gs
      (combine_assign_resolved gs dst v s) =
   combine_assign dst v (fun_of_resolved_st_for gs s)"
by (cases dst)
   (simp_all add: combine_assign_resolved_def)

lemma fun_of_resolved_st_q_for_combine_assign [simp]:
  "fun_of_resolved_st_q_for gs
      (combine_assign_resolved_q gs dst v s) =
   combine_assign dst v (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer
     (rule fun_of_resolved_st_for_combine_assign[unfolded fun_of_resolved_st_for_def])

definition bind_formals_resolved ::
  "(vname => bool) => vname list => 'a list => ('a::bot) resolved_st
   => 'a resolved_st"
where
  "bind_formals_resolved gs xs avs s =
     fold (\<lambda>(x, a) t. update_resolved_st t (location_of gs x) a)
       (zip xs avs) s"

lemma eq_resolved_st_fold_update:
  "eq_resolved_st s t \<Longrightarrow>
     eq_resolved_st
       (fold (\<lambda>(x, a) t. update_resolved_st t (location_of gs x) a) ps s)
       (fold (\<lambda>(x, a) t. update_resolved_st t (location_of gs x) a) ps t)"
proof (induction ps arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case
    by (cases p) (simp_all add: eq_resolved_st_update)
qed

lemma eq_resolved_st_bind_formals:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (bind_formals_resolved gs xs avs s)
      (bind_formals_resolved gs xs avs t)"
  unfolding bind_formals_resolved_def
  using assms by (rule eq_resolved_st_fold_update)

lift_definition bind_formals_resolved_q ::
  "(vname => bool) => vname list => 'a list => ('a::bot) resolved_st_q
   => 'a resolved_st_q"
  is bind_formals_resolved
  by (rule eq_resolved_st_bind_formals)

text \<open>A single-formal call binds exactly one location, so its reduction is a
  plain \<^const>\<open>update_resolved_st_q\<close>. An instance with a
  one-argument procedure call cites this directly instead of unfolding
  \<^const>\<open>bind_formals_resolved_q\<close>'s fold.\<close>

lemma bind_formals_resolved_q_singleton:
  "bind_formals_resolved_q gs [x] [a] s = update_resolved_st_q s (location_of gs x) a"
  by transfer (simp add: bind_formals_resolved_def eq_resolved_st_def)

lemma fun_of_resolved_st_for_fold_update:
  "fun_of_resolved_st_for gs
      (fold (\<lambda>(x, a) t. update_resolved_st t (location_of gs x) a) ps s) =
   fold (\<lambda>(x, a) t. t(x := a)) ps
      (fun_of_resolved_st_for gs s)"
by (induction ps arbitrary: s)
   (simp_all split: prod.splits)

lemma fun_of_resolved_st_for_bind_formals [simp]:
  "fun_of_resolved_st_for gs
      (bind_formals_resolved gs xs avs s) =
   bind_formals xs avs (fun_of_resolved_st_for gs s)"
unfolding bind_formals_resolved_def
by (rule fun_of_resolved_st_for_fold_update)

lemma fun_of_resolved_st_q_for_bind_formals [simp]:
  "fun_of_resolved_st_q_for gs
      (bind_formals_resolved_q gs xs avs s) =
   bind_formals xs avs (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer
     (rule fun_of_resolved_st_for_bind_formals[unfolded fun_of_resolved_st_for_def])

lemma fun_of_resolved_st_q_for_update [simp]:
  "fun_of_resolved_st_q_for gs
      (update_resolved_st_q s (location_of gs x) a) =
   (fun_of_resolved_st_q_for gs s)(x := a)"
proof (rule ext)
  fix y
  show "fun_of_resolved_st_q_for gs
      (update_resolved_st_q s (location_of gs x) a) y =
    ((fun_of_resolved_st_q_for gs s)(x := a)) y"
    unfolding fun_of_resolved_st_q_for_def
    by (cases "x = y"; cases "gs x"; cases "gs y";
        simp_all add: location_of_def)
qed



subsection \<open>Ownership restriction and combination\<close>

fun location_is_local :: "location => bool" where
  "location_is_local (Local_Location x) = True"
| "location_is_local (Global_Location x) = False"

fun location_is_global :: "location => bool" where
  "location_is_global (Local_Location x) = False"
| "location_is_global (Global_Location x) = True"

definition restrict_local_resolved ::
  "('a::bot) resolved_st => 'a resolved_st" where
  "restrict_local_resolved s =
     (case s of (dl, dg, ps) =>
       (dl, bot, filter (\<lambda>p. location_is_local (fst p)) ps))"

definition restrict_global_resolved ::
  "('a::bot) resolved_st => 'a resolved_st" where
  "restrict_global_resolved s =
     (case s of (dl, dg, ps) =>
       (bot, dg, filter (\<lambda>p. location_is_global (fst p)) ps))"


lemma lookup_restrict_local_resolved:
  "lookup_resolved_st (restrict_local_resolved s) loc =
     (case loc of
        Local_Location x => lookup_resolved_st s loc
      | Global_Location x => bot)"
  by (cases s; cases loc)
     (simp_all add: restrict_local_resolved_def map_of_filter_fst
       split: location.splits option.splits)

lemma lookup_restrict_global_resolved:
  "lookup_resolved_st (restrict_global_resolved s) loc =
     (case loc of
        Local_Location x => bot
      | Global_Location x => lookup_resolved_st s loc)"
  by (cases s; cases loc)
     (simp_all add: restrict_global_resolved_def map_of_filter_fst
       split: location.splits option.splits)

lemma eq_resolved_st_restrict_local:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (restrict_local_resolved s)
      (restrict_local_resolved t)"
  by (rule eq_resolved_stI)
     (simp add: lookup_restrict_local_resolved eq_resolved_stD[OF assms]
       split: location.split)

lemma eq_resolved_st_restrict_global:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (restrict_global_resolved s)
      (restrict_global_resolved t)"
  by (rule eq_resolved_stI)
     (simp add: lookup_restrict_global_resolved eq_resolved_stD[OF assms]
       split: location.split)

lift_definition restrict_local_resolved_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q"
  is restrict_local_resolved
  by (rule eq_resolved_st_restrict_local)

lift_definition restrict_global_resolved_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q"
  is restrict_global_resolved
  by (rule eq_resolved_st_restrict_global)

text \<open>
  \<^const>\<open>restrict_local_resolved_q\<close>/\<^const>\<open>restrict_global_resolved_q\<close>
  preserve the caller's semantic default over the (potentially infinite)
  location space: the kept side carries over its input's own per-location
  default verbatim (\<^term>\<open>dl\<close>/\<^term>\<open>dg\<close>, which need not be \<^term>\<open>bot\<close>), and
  only the dropped side is forced to \<^term>\<open>bot\<close>. A scope-parametric
  projection over a bounded materialized support would disagree with this
  pair outside its bound, so the pair is stated over the full location
  space and preserves the default by construction.
\<close>

lemma lookup_restrict_local_resolved_q [simp]:
  "lookup_resolved_st_q (restrict_local_resolved_q s) loc =
     (case loc of
        Local_Location x => lookup_resolved_st_q s loc
      | Global_Location x => bot)"
  by transfer (rule lookup_restrict_local_resolved)

lemma lookup_restrict_global_resolved_q [simp]:
  "lookup_resolved_st_q (restrict_global_resolved_q s) loc =
     (case loc of
        Local_Location x => bot
      | Global_Location x => lookup_resolved_st_q s loc)"
  by transfer (rule lookup_restrict_global_resolved)

lemma fun_of_resolved_st_q_for_restrict_local [simp]:
  "fun_of_resolved_st_q_for gs (restrict_local_resolved_q s) x =
     (if gs x then bot else fun_of_resolved_st_q_for gs s x)"
  unfolding fun_of_resolved_st_q_for_def location_of_def
  by (cases "gs x") simp_all

lemma fun_of_resolved_st_q_for_restrict_global [simp]:
  "fun_of_resolved_st_q_for gs (restrict_global_resolved_q s) x =
     (if gs x then fun_of_resolved_st_q_for gs s x else bot)"
  unfolding fun_of_resolved_st_q_for_def location_of_def
  by (cases "gs x") simp_all

definition combine_resolved_st ::
  "('a::bot) resolved_st => 'a resolved_st => 'a resolved_st"
where
  "combine_resolved_st sc se =
     (case sc of (dlc, dgc, psc) =>
      case se of (dle, dge, pse) =>
        (dlc, dge,
         filter (\<lambda>p. location_is_local (fst p)) psc @
         filter (\<lambda>p. location_is_global (fst p)) pse))"

lemma lookup_combine_resolved_st [simp]:
  "lookup_resolved_st (combine_resolved_st sc se) loc =
   (case loc of
      Local_Location x => lookup_resolved_st sc loc
    | Global_Location x => lookup_resolved_st se loc)"
by (cases sc; cases se; cases loc)
     (simp_all add: combine_resolved_st_def map_add_def map_of_filter_fst
       split: option.splits)

lemma eq_resolved_st_combine:
  assumes "eq_resolved_st sc1 sc2"
    and "eq_resolved_st se1 se2"
  shows "eq_resolved_st (combine_resolved_st sc1 se1)
      (combine_resolved_st sc2 se2)"
  by (rule eq_resolved_stI)
     (simp add: eq_resolved_stD[OF assms(1)] eq_resolved_stD[OF assms(2)]
       split: location.split)

lift_definition combine_resolved_st_q ::
  "('a::bot) resolved_st_q => 'a resolved_st_q => 'a resolved_st_q"
  is combine_resolved_st
  by (rule eq_resolved_st_combine)

lemma lookup_combine_resolved_st_q [simp]:
  "lookup_resolved_st_q (combine_resolved_st_q sc se) loc =
     (case loc of
        Local_Location x => lookup_resolved_st_q sc loc
      | Global_Location x => lookup_resolved_st_q se loc)"
  by transfer (rule lookup_combine_resolved_st)


lemma fun_of_resolved_st_for_combine_resolved [simp]:
  "fun_of_resolved_st_for gs (combine_resolved_st sc se) =
   combine_env gs (fun_of_resolved_st_for gs sc)
     (fun_of_resolved_st_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (combine_resolved_st sc se) x =
      combine_env gs (fun_of_resolved_st_for gs sc)
        (fun_of_resolved_st_for gs se) x"
    unfolding fun_of_resolved_st_for_def combine_env_def location_of_def
    by (cases "gs x") simp_all
qed

lemma fun_of_resolved_st_q_for_combine [simp]:
  "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) =
   combine_env gs (fun_of_resolved_st_q_for gs sc)
     (fun_of_resolved_st_q_for gs se)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_q_for gs (combine_resolved_st_q sc se) x =
      combine_env gs (fun_of_resolved_st_q_for gs sc)
        (fun_of_resolved_st_q_for gs se) x"
    unfolding fun_of_resolved_st_q_for_def combine_env_def location_of_def
    by (cases "gs x") simp_all
qed


lemma fun_of_resolved_st_q_for_sup [simp]:
  "fun_of_resolved_st_q_for gs (s \<squnion> t) =
   fun_of_resolved_st_q_for gs s \<squnion> fun_of_resolved_st_q_for gs t"
  by (rule ext) (simp add: fun_of_resolved_st_q_for_def sup_fun_def)


subsection \<open>Frame entry\<close>

definition enter_frame_D_resolved ::
  "'a => ('a::bot) resolved_st => 'a resolved_st"
where
  "enter_frame_D_resolved top_val s =
     (case s of (dl, dg, ps) =>
       (top_val, dg, filter (\<lambda>p. location_is_global (fst p)) ps))"

lemma lookup_enter_frame_D_resolved [simp]:
  "lookup_resolved_st (enter_frame_D_resolved top_val s) loc =
   (case loc of
      Local_Location x => top_val
    | Global_Location x => lookup_resolved_st s loc)"
by (cases s; cases loc)
     (simp_all add: enter_frame_D_resolved_def map_of_filter_fst
       split: option.splits)

lemma eq_resolved_st_enter_frame_D:
  assumes "eq_resolved_st s t"
  shows "eq_resolved_st (enter_frame_D_resolved top_val s)
      (enter_frame_D_resolved top_val t)"
  by (rule eq_resolved_stI)
     (simp add: eq_resolved_stD[OF assms] split: location.split)

lift_definition enter_frame_D_resolved_q ::
  "'a => ('a::bot) resolved_st_q => 'a resolved_st_q"
  is enter_frame_D_resolved
  by (rule eq_resolved_st_enter_frame_D)

lemma lookup_enter_frame_D_resolved_q [simp]:
  "lookup_resolved_st_q (enter_frame_D_resolved_q top_val s) loc =
     (case loc of
        Local_Location x => top_val
      | Global_Location x => lookup_resolved_st_q s loc)"
  by transfer (rule lookup_enter_frame_D_resolved)

lemma fun_of_resolved_st_for_enter_frame [simp]:
  "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) =
   enter_frame gs top_val (fun_of_resolved_st_for gs s)"
proof (rule ext)
  fix x
  show "fun_of_resolved_st_for gs (enter_frame_D_resolved top_val s) x =
      enter_frame gs top_val (fun_of_resolved_st_for gs s) x"
    unfolding enter_frame_def fun_of_resolved_st_for_def location_of_def
    by (cases "gs x") simp_all
qed

lemma fun_of_resolved_st_q_for_enter_frame [simp]:
  "fun_of_resolved_st_q_for gs
      (enter_frame_D_resolved_q top_val s) =
   enter_frame gs top_val (fun_of_resolved_st_q_for gs s)"
  unfolding fun_of_resolved_st_q_for_def
  by transfer
     (rule fun_of_resolved_st_for_enter_frame[unfolded fun_of_resolved_st_for_def])


subsection \<open>Executable restriction and combination laws\<close>

text \<open>
  Algebraic identities of the carrier itself: no abstract state, no
  concretization, no classifier. They say that combining and then projecting
  recovers the projected side, and that the two projections recombine by join.
  Executable trees use them to split and rebuild a routed state.
\<close>

lemma combine_resolved_st_q_eq_restrict_sup:
  "combine_resolved_st_q A B =
     restrict_local_resolved_q A \<squnion> restrict_global_resolved_q B"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma restrict_local_resolved_q_combine_resolved_st_q [simp]:
  "restrict_local_resolved_q (combine_resolved_st_q A B) =
     restrict_local_resolved_q A"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma restrict_global_resolved_q_combine_resolved_st_q [simp]:
  "restrict_global_resolved_q (combine_resolved_st_q A B) =
     restrict_global_resolved_q B"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma restrict_local_resolved_q_split [simp]:
  "restrict_local_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_local_resolved_q A"
  by (rule resolved_st_q_eqI) (simp split: location.split)

lemma restrict_global_resolved_q_split [simp]:
  "restrict_global_resolved_q (restrict_local_resolved_q A \<squnion>
      restrict_global_resolved_q B) = restrict_global_resolved_q B"
  by (rule resolved_st_q_eqI) (simp split: location.split)

end
