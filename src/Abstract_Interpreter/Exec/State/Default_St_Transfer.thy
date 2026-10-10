theory Default_St_Transfer
  imports Default_St_Algebra "Voblint_Framework.Transfer_Algebra"
begin

unbundle default_st_carrier_syntax

section \<open>Refinement to variable-indexed states\<close>

text \<open>
  Everything so far is stated about locations. A program, though, talks about
  variable names, and which names are global is a property of the program, not
  of the carrier. \<open>location_of\<close> is that classifier applied: it turns a name
  into the location holding its value, and \<open>default_st_rep_to_fun\<close> maps a
  whole state to the function \<^typ>\<open>'a abs_state\<close> it represents, the form
  soundness is stated over.

  The rest of the theory is the operations a call and a return need --
  assignment, formal binding, restriction to one side of the ownership split,
  frame entry, and the caller/callee combination -- each paired with the
  equation saying that performing it on the carrier and then taking the
  represented function agrees with performing its counterpart on that
  function. Those equations are the interface every soundness proof downstream
  actually uses.
\<close>

subsection \<open>Location classification and projection\<close>

definition location_of ::
  "(vname => bool) => vname => location" where
  "location_of \<G> x =
     (if \<G> x then Global_Location x else Local_Location x)"

text \<open>
  Both tags carry the vname they classify, so a classified location determines
  its own name and two names collide only when they are equal.  Proofs about
  \<^const>\<open>location_of\<close> therefore need no case split on \<^term>\<open>\<G> x\<close> against
  \<^term>\<open>\<G> y\<close>.
\<close>

lemma location_vname_location_of [simp]:
  "location_vname (location_of \<G> x) = x"
  by (simp add: location_of_def)

lemma location_of_eq_iff [simp]:
  "location_of \<G> x = location_of \<G> y \<longleftrightarrow> x = y"
  by (auto simp: location_of_def)

text \<open>
  Deliberately no \<open>[simp]\<close> rule matching \<^term>\<open>location_of \<G> x = Local_Location y\<close>
  against a constructor. Such a rule reads well in isolation, but proofs here
  derive facts of exactly that shape and then use them as rewrites for
  \<^const>\<open>location_of\<close>; a simp rule on the same left-hand side collapses the
  equation to its classification side and takes the rewrite away.
\<close>

definition default_st_rep_to_fun ::
  "(vname => bool) => ('a::bot) default_st_rep => vname => 'a" where
  "default_st_rep_to_fun \<G> s x =
     default_st_rep_get s (location_of \<G> x)"

lemma default_st_rep_to_fun_set_location [simp]:
  "default_st_rep_to_fun \<G>
      (default_st_rep_set s (location_of \<G> x) a) =
   (default_st_rep_to_fun \<G> s)(x := a)"
proof (rule ext)
  fix y
  show "default_st_rep_to_fun \<G>
      (default_st_rep_set s (location_of \<G> x) a) y =
    ((default_st_rep_to_fun \<G> s)(x := a)) y"
    unfolding default_st_rep_to_fun_def    by (cases "x = y"; cases "\<G> x"; cases "\<G> y";
        simp_all add: location_of_def)
qed


definition default_st_to_fun ::
  "(vname => bool) => ('a::bot) default_st => vname => 'a"
where
  "default_st_to_fun \<G> s x =
     s\<langle>location_of \<G> x\<rangle>"

text \<open>
  The function a state represents is its \<^const>\<open>readback\<close>, written
  \<open>\<rho>\<^bsub>\<G>\<^esub> s\<close>; a lifted state reads back pointwise under the lift.
  The notation joins the carrier notation in the opt-in bundle
  \<open>default_st_syntax\<close>: vendored theories bind \<open>\<rho>\<close> as a
  variable, so it must never be global.
\<close>

adhoc_overloading readback == default_st_to_fun

bundle default_st_syntax
begin
unbundle default_st_carrier_syntax
notation readback ("\<rho>\<^bsub>_\<^esub>")
end

unbundle default_st_syntax

lemma default_st_to_fun_bot [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (bot :: ('a::order_bot) default_st) = bot"
  by (rule ext) (simp add: default_st_to_fun_def)

text \<open>
  The state a run starts in gives every local one value and every global
  another: C initializes a declared global to zero and leaves a local
  unconstrained. Each domain's C-initial state is this construction at its own
  abstraction of zero and its whole-value element, so the equation for its
  function is one lemma rather than one per domain. The two empty dictionaries
  are abstracted directly rather than lifted, because a domain whose value type
  is itself a typedef would otherwise descend through both quotients.
\<close>

definition initial_default_st :: "'a::bot => 'a => 'a default_st" where
  "initial_default_st local_value global_value =
     \<llangle>(local_value, []), (global_value, [])\<rrangle>"

lemma default_st_get_initial [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (initial_default_st local_value global_value) x =
   (if \<G> x then global_value else local_value)"
  unfolding default_st_to_fun_def initial_default_st_def
  by (auto simp: location_of_def split: if_splits)

lemma default_st_to_fun_initial:
  "\<rho>\<^bsub>\<G>\<^esub> (initial_default_st local_value global_value) =
   (\<lambda>x. if \<G> x then global_value else local_value)"
  by (rule ext) simp

text \<open>
  The quotient-level projection agrees with the raw one at \<open>s\<close>'s own chosen
  representative -- so any raw-level fact about @{const default_st_rep_to_fun}
  transports directly to @{const default_st_to_fun} through
  @{const rep_default_st}, with no separate quotient-respectfulness argument
  needed: @{const rep_default_st} is a genuine function of \<open>s\<close>, so anything
  defined through it is automatically well-defined on the quotient.
\<close>

lemma default_st_to_fun_rep:
  "\<rho>\<^bsub>\<G>\<^esub> s = default_st_rep_to_fun \<G> (rep_default_st s)"
  unfolding default_st_to_fun_def default_st_rep_to_fun_def
  by (rule ext) (simp add: default_st_get_rep)

lemma default_st_to_fun_mono:
  assumes "s \<le> t"
  shows "\<rho>\<^bsub>\<G>\<^esub> s \<le> \<rho>\<^bsub>\<G>\<^esub> t"
  using assms
  unfolding default_st_to_fun_def le_fun_def
  by (simp add: le_default_st_iff)


text \<open>
  Each quotient-level refinement equation is its raw counterpart transported
  along the quotient: unfolding the projection leaves a goal in
  \<^const>\<open>default_st_get\<close>, \<open>transfer\<close> lowers it to
  \<^const>\<open>default_st_rep_get\<close>, and the raw lemma -- read at the same unfolded
  shape -- closes it. An operation returning the quotient has no \<open>rep_eq\<close> to
  unfold instead, since its representative is fixed only up to
  \<^const>\<open>eq_default_st_rep\<close>.
\<close>


subsection \<open>Assignment and formal binding\<close>

definition combine_assign_default_st_rep ::
  "(vname => bool) => vname option => 'a => ('a::bot) default_st_rep
   => 'a default_st_rep"
where
  "combine_assign_default_st_rep \<G> dst v s =
     (case dst of None => s
      | Some x => default_st_rep_set s (location_of \<G> x) v)"

lemma eq_default_st_rep_combine_assign:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (combine_assign_default_st_rep \<G> dst v s)
      (combine_assign_default_st_rep \<G> dst v t)"
  by (unfold combine_assign_default_st_rep_def; cases dst;
      simp_all add: assms eq_default_st_rep_set)

lift_definition combine_assign_default_st ::
  "(vname => bool) => vname option => 'a => ('a::bot) default_st
   => 'a default_st"
  is combine_assign_default_st_rep
  by (rule eq_default_st_rep_combine_assign)

lemma default_st_get_combine_assign [simp]:
  "(combine_assign_default_st \<G> dst v s)\<langle>loc\<rangle> =
     (case dst of
        None => s\<langle>loc\<rangle>
      | Some x => if location_of \<G> x = loc then v else s\<langle>loc\<rangle>)"
  by transfer (auto simp add:combine_assign_default_st_rep_def split:option.splits)

lemma default_st_rep_to_fun_combine_assign [simp]:
  "default_st_rep_to_fun \<G>
      (combine_assign_default_st_rep \<G> dst v s) =
   combine_assign dst v (default_st_rep_to_fun \<G> s)"
  by (cases dst)
     (simp_all add: combine_assign_default_st_rep_def)

lemma default_st_to_fun_combine_assign [simp]:
  "\<rho>\<^bsub>\<G>\<^esub>
      (combine_assign_default_st \<G> dst v s) =
   combine_assign dst v (\<rho>\<^bsub>\<G>\<^esub> s)"
  unfolding default_st_to_fun_def
  by transfer
     (rule default_st_rep_to_fun_combine_assign[unfolded default_st_rep_to_fun_def])

definition bind_formals_default_st_rep ::
  "(vname => bool) => vname list => 'a list => ('a::bot) default_st_rep
   => 'a default_st_rep"
where
  "bind_formals_default_st_rep \<G> xs avs s =
     fold (\<lambda>(x, a) t. default_st_rep_set t (location_of \<G> x) a)
       (zip xs avs) s"

lemma eq_default_st_rep_fold_set:
  "eq_default_st_rep s t \<Longrightarrow>
     eq_default_st_rep
       (fold (\<lambda>(x, a) t. default_st_rep_set t (location_of \<G> x) a) ps s)
       (fold (\<lambda>(x, a) t. default_st_rep_set t (location_of \<G> x) a) ps t)"
proof (induction ps arbitrary: s t)
  case Nil
  then show ?case by simp
next
  case (Cons p ps)
  then show ?case
    by (cases p) (simp_all add: eq_default_st_rep_set)
qed

lemma eq_default_st_rep_bind_formals:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (bind_formals_default_st_rep \<G> xs avs s)
      (bind_formals_default_st_rep \<G> xs avs t)"
  unfolding bind_formals_default_st_rep_def
  using assms by (rule eq_default_st_rep_fold_set)

lift_definition bind_formals_default_st ::
  "(vname => bool) => vname list => 'a list => ('a::bot) default_st
   => 'a default_st"
  is bind_formals_default_st_rep
  by (rule eq_default_st_rep_bind_formals)

text \<open>A single-formal call binds exactly one location, so its reduction is a
  plain \<^const>\<open>default_st_set\<close>. An instance with a
  one-argument procedure call cites this directly instead of unfolding
  \<^const>\<open>bind_formals_default_st\<close>'s fold.\<close>

lemma bind_formals_default_st_singleton:
  "bind_formals_default_st \<G> [x] [a] s = s\<langle>location_of \<G> x := a\<rangle>"
  by transfer (simp add: bind_formals_default_st_rep_def eq_default_st_rep_def)

lemma default_st_rep_to_fun_fold_set:
  "default_st_rep_to_fun \<G>
      (fold (\<lambda>(x, a) t. default_st_rep_set t (location_of \<G> x) a) ps s) =
   fold (\<lambda>(x, a) t. t(x := a)) ps
      (default_st_rep_to_fun \<G> s)"
  by (induction ps arbitrary: s)
     (simp_all split: prod.splits)

lemma default_st_rep_to_fun_bind_formals [simp]:
  "default_st_rep_to_fun \<G>
      (bind_formals_default_st_rep \<G> xs avs s) =
   bind_formals xs avs (default_st_rep_to_fun \<G> s)"
  unfolding bind_formals_default_st_rep_def
  by (rule default_st_rep_to_fun_fold_set)

lemma default_st_to_fun_bind_formals [simp]:
  "\<rho>\<^bsub>\<G>\<^esub>
      (bind_formals_default_st \<G> xs avs s) =
   bind_formals xs avs (\<rho>\<^bsub>\<G>\<^esub> s)"
  unfolding default_st_to_fun_def
  by transfer
     (rule default_st_rep_to_fun_bind_formals[unfolded default_st_rep_to_fun_def])

lemma default_st_to_fun_set [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> s\<langle>location_of \<G> x := a\<rangle> =
   (\<rho>\<^bsub>\<G>\<^esub> s)(x := a)"
proof (rule ext)
  fix y
  show "\<rho>\<^bsub>\<G>\<^esub> s\<langle>location_of \<G> x := a\<rangle> y =
    ((\<rho>\<^bsub>\<G>\<^esub> s)(x := a)) y"
    unfolding default_st_to_fun_def
    by (cases "x = y"; cases "\<G> x"; cases "\<G> y";
        simp_all add: location_of_def)
qed


subsection \<open>Ownership restriction and combination\<close>

text \<open>
  Each dictionary holds one partition, so the ownership operations below move
  whole dictionaries: a restriction keeps one and empties the other to
  \<open>bot\<close>, and the combination takes the caller's local dictionary and the
  callee's global one.
\<close>

definition restrict_local_default_st_rep ::
  "('a::bot) default_st_rep => 'a default_st_rep" where
  "restrict_local_default_st_rep s = (fst s, (bot, []))"

definition restrict_global_default_st_rep ::
  "('a::bot) default_st_rep => 'a default_st_rep" where
  "restrict_global_default_st_rep s = ((bot, []), snd s)"


lemma default_st_rep_get_restrict_local:
  "default_st_rep_get (restrict_local_default_st_rep s) loc =
     (case loc of
        Local_Location x => default_st_rep_get s loc
      | Global_Location x => bot)"
  by (cases s; cases loc) (simp_all add: restrict_local_default_st_rep_def)

lemma default_st_rep_get_restrict_global:
  "default_st_rep_get (restrict_global_default_st_rep s) loc =
     (case loc of
        Local_Location x => bot
      | Global_Location x => default_st_rep_get s loc)"
  by (cases s; cases loc) (simp_all add: restrict_global_default_st_rep_def)

lemma eq_default_st_rep_restrict_local:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (restrict_local_default_st_rep s)
      (restrict_local_default_st_rep t)"
  by (rule eq_default_st_repI)
     (simp add: default_st_rep_get_restrict_local eq_default_st_repD[OF assms]
       split: location.split)

lemma eq_default_st_rep_restrict_global:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (restrict_global_default_st_rep s)
      (restrict_global_default_st_rep t)"
  by (rule eq_default_st_repI)
     (simp add: default_st_rep_get_restrict_global eq_default_st_repD[OF assms]
       split: location.split)

lift_definition restrict_local_default_st ::
  "('a::bot) default_st => 'a default_st"
  is restrict_local_default_st_rep
  by (rule eq_default_st_rep_restrict_local)

lift_definition restrict_global_default_st ::
  "('a::bot) default_st => 'a default_st"
  is restrict_global_default_st_rep
  by (rule eq_default_st_rep_restrict_global)

text \<open>
  \<^const>\<open>restrict_local_default_st\<close>/\<^const>\<open>restrict_global_default_st\<close>
  preserve the caller's semantic default over the (potentially infinite)
  location space: the kept side carries over its input's own dictionary
  verbatim, whose default need not be \<^term>\<open>bot\<close>, and only the dropped side
  is replaced by the empty dictionary over \<^term>\<open>bot\<close>. A scope-parametric
  projection over a bounded materialized support would disagree with this
  pair outside its bound, so the pair is stated over the full location
  space and preserves the default by construction.
\<close>

lemma default_st_get_restrict_local [simp]:
  "(restrict_local_default_st s)\<langle>loc\<rangle> =
     (case loc of
        Local_Location x => s\<langle>loc\<rangle>
      | Global_Location x => bot)"
  by transfer (rule default_st_rep_get_restrict_local)

lemma default_st_get_restrict_global [simp]:
  "(restrict_global_default_st s)\<langle>loc\<rangle> =
     (case loc of
        Local_Location x => bot
      | Global_Location x => s\<langle>loc\<rangle>)"
  by transfer (rule default_st_rep_get_restrict_global)

lemma default_st_to_fun_restrict_local [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (restrict_local_default_st s) x =
     (if \<G> x then bot else \<rho>\<^bsub>\<G>\<^esub> s x)"
  unfolding default_st_to_fun_def location_of_def
  by (cases "\<G> x") simp_all

lemma default_st_to_fun_restrict_global [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (restrict_global_default_st s) x =
     (if \<G> x then \<rho>\<^bsub>\<G>\<^esub> s x else bot)"
  unfolding default_st_to_fun_def location_of_def
  by (cases "\<G> x") simp_all

definition combine_default_st_rep ::
  "('a::bot) default_st_rep => 'a default_st_rep => 'a default_st_rep"
where
  "combine_default_st_rep sc se = (fst sc, snd se)"

lemma default_st_rep_get_combine [simp]:
  "default_st_rep_get (combine_default_st_rep sc se) loc =
   (case loc of
      Local_Location x => default_st_rep_get sc loc
    | Global_Location x => default_st_rep_get se loc)"
  by (cases sc; cases se; cases loc) (simp_all add: combine_default_st_rep_def)

lemma eq_default_st_rep_combine:
  assumes "eq_default_st_rep sc1 sc2"
    and "eq_default_st_rep se1 se2"
  shows "eq_default_st_rep (combine_default_st_rep sc1 se1)
      (combine_default_st_rep sc2 se2)"
  by (rule eq_default_st_repI)
     (simp add: eq_default_st_repD[OF assms(1)] eq_default_st_repD[OF assms(2)]
       split: location.split)

lift_definition combine_default_st ::
  "('a::bot) default_st => 'a default_st => 'a default_st"
  is combine_default_st_rep
  by (rule eq_default_st_rep_combine)

lemma default_st_get_combine [simp]:
  "(combine_default_st sc se)\<langle>loc\<rangle> =
     (case loc of
        Local_Location x => sc\<langle>loc\<rangle>
      | Global_Location x => se\<langle>loc\<rangle>)"
  by transfer (rule default_st_rep_get_combine)


lemma default_st_rep_to_fun_combine [simp]:
  "default_st_rep_to_fun \<G> (combine_default_st_rep sc se) =
   combine_env \<G> (default_st_rep_to_fun \<G> sc)
     (default_st_rep_to_fun \<G> se)"
proof (rule ext)
  fix x
  show "default_st_rep_to_fun \<G> (combine_default_st_rep sc se) x =
      combine_env \<G> (default_st_rep_to_fun \<G> sc)
        (default_st_rep_to_fun \<G> se) x"
    unfolding default_st_rep_to_fun_def combine_env_def location_of_def
    by (cases "\<G> x") simp_all
qed

lemma default_st_to_fun_combine [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (combine_default_st sc se) =
   combine_env \<G> (\<rho>\<^bsub>\<G>\<^esub> sc)
     (\<rho>\<^bsub>\<G>\<^esub> se)"
proof (rule ext)
  fix x
  show "\<rho>\<^bsub>\<G>\<^esub> (combine_default_st sc se) x =
      combine_env \<G> (\<rho>\<^bsub>\<G>\<^esub> sc)
        (\<rho>\<^bsub>\<G>\<^esub> se) x"
    unfolding default_st_to_fun_def combine_env_def location_of_def
    by (cases "\<G> x") simp_all
qed


lemma default_st_to_fun_sup [simp]:
  "\<rho>\<^bsub>\<G>\<^esub> (s \<squnion> t) =
   \<rho>\<^bsub>\<G>\<^esub> s \<squnion> \<rho>\<^bsub>\<G>\<^esub> t"
  by (rule ext) (simp add: default_st_to_fun_def sup_fun_def)


subsection \<open>Frame entry\<close>

text \<open>
  Entering a frame sets every local to \<open>top_val\<close> and keeps the globals;
  the lemmas carry this through the quotient and the readback.
\<close>

definition enter_frame_D_default_st_rep ::
  "'a => ('a::bot) default_st_rep => 'a default_st_rep"
where
  "enter_frame_D_default_st_rep top_val s = ((top_val, []), snd s)"

lemma default_st_rep_get_enter_frame_D [simp]:
  "default_st_rep_get (enter_frame_D_default_st_rep top_val s) loc =
   (case loc of
      Local_Location x => top_val
    | Global_Location x => default_st_rep_get s loc)"
  by (cases s; cases loc) (simp_all add: enter_frame_D_default_st_rep_def)

lemma eq_default_st_rep_enter_frame_D:
  assumes "eq_default_st_rep s t"
  shows "eq_default_st_rep (enter_frame_D_default_st_rep top_val s)
      (enter_frame_D_default_st_rep top_val t)"
  by (rule eq_default_st_repI)
     (simp add: eq_default_st_repD[OF assms] split: location.split)

lift_definition enter_frame_D_default_st ::
  "'a => ('a::bot) default_st => 'a default_st"
  is enter_frame_D_default_st_rep
  by (rule eq_default_st_rep_enter_frame_D)

lemma default_st_get_enter_frame_D [simp]:
  "(enter_frame_D_default_st top_val s)\<langle>loc\<rangle> =
     (case loc of
        Local_Location x => top_val
      | Global_Location x => s\<langle>loc\<rangle>)"
  by transfer (rule default_st_rep_get_enter_frame_D)

lemma default_st_rep_to_fun_enter_frame [simp]:
  "default_st_rep_to_fun \<G> (enter_frame_D_default_st_rep top_val s) =
   enter_frame \<G> top_val (default_st_rep_to_fun \<G> s)"
proof (rule ext)
  fix x
  show "default_st_rep_to_fun \<G> (enter_frame_D_default_st_rep top_val s) x =
      enter_frame \<G> top_val (default_st_rep_to_fun \<G> s) x"
    unfolding enter_frame_def default_st_rep_to_fun_def location_of_def
    by (cases "\<G> x") simp_all
qed

lemma default_st_to_fun_enter_frame [simp]:
  "\<rho>\<^bsub>\<G>\<^esub>
      (enter_frame_D_default_st top_val s) =
   enter_frame \<G> top_val (\<rho>\<^bsub>\<G>\<^esub> s)"
  unfolding default_st_to_fun_def
  by transfer
     (rule default_st_rep_to_fun_enter_frame[unfolded default_st_rep_to_fun_def])


subsection \<open>Executable restriction and combination laws\<close>

text \<open>
  Algebraic identities of the carrier itself: no abstract state, no
  concretization, no classifier. They say that combining and then projecting
  recovers the projected side, and that the two projections recombine by join.
  Executable trees use them to split and rebuild a routed state.
\<close>

lemma combine_default_st_eq_restrict_sup:
  "combine_default_st A B =
     restrict_local_default_st A \<squnion> restrict_global_default_st B"
  by (rule default_st_eqI) (simp split: location.split)

lemma restrict_local_default_st_combine [simp]:
  "restrict_local_default_st (combine_default_st A B) =
     restrict_local_default_st A"
  by (rule default_st_eqI) (simp split: location.split)

lemma restrict_global_default_st_combine [simp]:
  "restrict_global_default_st (combine_default_st A B) =
     restrict_global_default_st B"
  by (rule default_st_eqI) (simp split: location.split)

lemma restrict_local_default_st_split [simp]:
  "restrict_local_default_st (restrict_local_default_st A \<squnion>
      restrict_global_default_st B) = restrict_local_default_st A"
  by (rule default_st_eqI) (simp split: location.split)

lemma restrict_global_default_st_split [simp]:
  "restrict_global_default_st (restrict_local_default_st A \<squnion>
      restrict_global_default_st B) = restrict_global_default_st B"
  by (rule default_st_eqI) (simp split: location.split)

text \<open>
  Combining reads only the local half of its first argument and the global half
  of its second, so a state recombines from its own two projections.
\<close>

lemma combine_default_st_restrict_split [simp]:
  "combine_default_st (restrict_local_default_st x) (restrict_global_default_st x) = x"
  by (rule default_st_eqI) (simp split: location.split)

lemma combine_default_st_restrict_local_left [simp]:
  "combine_default_st (restrict_local_default_st x) y = combine_default_st x y"
  by (rule default_st_eqI) (simp split: location.split)

lemma combine_default_st_self_restrict_global [simp]:
  "combine_default_st x (restrict_global_default_st x) = x"
  by (rule default_st_eqI) (simp split: location.split)

subsection \<open>The stores a carrier state describes\<close>

text \<open>
  A carrier state denotes the stores its function denotes. This is the one
  concretization the carrier offers to semantic statements; the represented
  function itself stays a refinement device, used to relate carrier operations
  to their counterparts on \<^typ>\<open>'a abs_state\<close>. Only the classifier
  \<open>\<G>\<close> is needed besides the state, because it decides which location holds each
  name's value. A context that fixes \<open>\<G>\<close> may register
  \<open>default_st_gamma \<G>\<close> under \<open>\<gamma> _\<close> with \<open>adhoc_overloading\<close>.
\<close>

definition default_st_gamma ::
  "(vname => bool) => ('a::numeric_domain) default_st => store set" where
  "default_st_gamma \<G> s = \<gamma> (\<rho>\<^bsub>\<G>\<^esub> s)"

lemma default_st_gamma_mono:
  "s \<le> t \<Longrightarrow> default_st_gamma \<G> s \<subseteq> default_st_gamma \<G> t"
  unfolding default_st_gamma_def by (intro gamma_state_mono default_st_to_fun_mono)

lemma default_st_gamma_bot [simp]: "default_st_gamma \<G> bot = {}"
  by (simp add: default_st_gamma_def)

lemma default_st_gamma_initial:
  "default_st_gamma \<G> (initial_default_st local_value global_value) =
   \<gamma> (\<lambda>x. if \<G> x then global_value else local_value)"
  by (simp add: default_st_gamma_def default_st_to_fun_initial)

unbundle no default_st_syntax

end
