theory MCP_Spec
  imports "Voblint_Framework.DG_Spec_Sound" "Voblint_Domain.Reachability_Lift"
begin

text \<open>The soundness of a component is stated against the concrete semantics of the
  language it runs on.\<close>

locale mcp_sem = cfg_transfer_sem ev rv conv glob
  for ev :: "'e \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> int" and rv :: 'vr
    and conv :: "'vr option \<Rightarrow> int \<Rightarrow> int" and glob :: "'vr \<Rightarrow> bool"

section \<open>Many cooperating analyses over one state\<close>

text \<open>
  Goblint's \<open>MCP\<close> runs every activated analysis on its own part of one
  combined state (\<open>mCP.ml\<close> at \<open>0dc12d355\<close>). Voblint keeps the combined state
  as one type \<open>'s\<close>, a record with a field per registered analysis, and a
  component as operations on the whole record that touch only its own field.
  The activation list chooses which components run; the fields of inactive
  analyses are never read.

  Every operation of a component receives the query channel of the manager
  Goblint hands it, \<open>man.ask\<close>, as a function \<^typ>\<open>channel\<close> from queries to
  answers: its query handler (\<open>S.query man q\<close>), its edge transfers, its entry
  (\<open>S.enter man\<close>) and both stages of its return. The return stages also receive
  the callee's channel, which Goblint's normal-call transfer in \<open>constraints.ml\<close>
  passes as \<open>f_ask\<close>.
  A handler may therefore ask further queries while it answers, and the channel
  that answers them is the one \<open>ask_rec\<close> below closes over the combined
  state, as Goblint's \<open>MCP.query'\<close> does.

  The channel is a pure function of the state it describes. A component
  therefore neither reads nor publishes globals: the combined state covers
  analyses whose operations are local, and effectful analyses run as
  specifications of their own (\<^const>\<open>dgs_query\<close> is the effectful handler).

  A component holds only what runs. What its states describe, a set of stores,
  is not executable and is supplied beside it wherever soundness is stated,
  as \<^class>\<open>numeric_domain\<close> keeps \<open>gamma\<close> out of \<^class>\<open>executable_domain\<close>.
\<close>

record ('vr,'e,'s) glocal_spec =
  ls_query :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel"
  ls_skip :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 's"
  ls_assign :: "'e gchannel \<Rightarrow> 'vr \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's"
  ls_special :: "'e gchannel \<Rightarrow> 'e gspecial_call \<Rightarrow> 'vr \<Rightarrow> 's \<Rightarrow> 's"
  ls_branch :: "'e gchannel \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's"
  ls_body :: "'e gchannel \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_return :: "'e gchannel \<Rightarrow> 'e option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's"
  ls_event :: "'e gchannel \<Rightarrow> 'e ganalysis_event \<Rightarrow> 's \<Rightarrow> 's"
  ls_enter :: "'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list"
  ls_combine_env :: "'e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"
  ls_combine_assign :: "'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's"

type_synonym 's local_spec = "(vname, exp, 's) glocal_spec"

text \<open>
  The edge transfers are separate fields, one per kind of edge, as Goblint's
  \<open>Spec\<close> has \<open>skip\<close>, \<open>assign\<close>, \<open>special\<close>, \<open>branch\<close>, \<open>body\<close>, \<open>return\<close> and
  \<open>event\<close>. A component that overrides one of them updates that field alone. The
  step on an arbitrary edge is derived from them.
\<close>

definition ls_step :: "('vr,'e,'s) glocal_spec \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gedge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "ls_step c ch = local_spec_step (ls_skip c ch) (ls_assign c ch) (ls_special c ch)
     (ls_branch c ch) (ls_body c ch) (ls_return c ch) (ls_event c ch)"

lemma ls_step_simps [simp]:
  "ls_step c ch EA_Nop = ls_skip c ch"
  "ls_step c ch (EA_Assign x e) = ls_assign c ch x e"
  "ls_step c ch (EA_Special sc x) = ls_special c ch sc x"
  "ls_step c ch (EA_Assume b) = ls_branch c ch b True"
  "ls_step c ch (EA_AssumeNot b) = ls_branch c ch b False"
  "ls_step c ch (EA_Body p) = ls_body c ch p"
  "ls_step c ch (EA_Ret r p) = ls_return c ch r p"
  "ls_step c ch (EA_Check l cnd) = ls_event c ch (Check_Event l cnd)"
  by (simp_all add: ls_step_def)

lemma ls_step_event_action [simp]: "ls_step c ch (event_action e) = ls_event c ch e"
  by (cases e) simp

lemma ls_step_update_other [simp]:
  "ls_step (c\<lparr>ls_query := h\<rparr>) = ls_step c"
  "ls_step (c\<lparr>ls_enter := e\<rparr>) = ls_step c"
  "ls_step (c\<lparr>ls_combine_env := ce\<rparr>) = ls_step c"
  "ls_step (c\<lparr>ls_combine_assign := ca\<rparr>) = ls_step c"
  by (simp_all add: ls_step_def fun_eq_iff)

text \<open>
  A component whose edge transfers are one function of the edge, such as a
  lens onto a field or a fold over several components, is built from that
  function: each field is the function at its kind of edge.
\<close>

definition make_local_spec ::
  "('e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel) \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gedge_action \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list)
   \<Rightarrow> ('e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('vr,'e,'s) glocal_spec" where
  "make_local_spec qry st en ce ca = \<lparr>
     ls_query = qry,
     ls_skip = (\<lambda>ch. st ch EA_Nop),
     ls_assign = (\<lambda>ch x e. st ch (EA_Assign x e)),
     ls_special = (\<lambda>ch sc x. st ch (EA_Special sc x)),
     ls_branch = (\<lambda>ch b pol. st ch (if pol then EA_Assume b else EA_AssumeNot b)),
     ls_body = (\<lambda>ch p. st ch (EA_Body p)),
     ls_return = (\<lambda>ch r p. st ch (EA_Ret r p)),
     ls_event = (\<lambda>ch ev. st ch (event_action ev)),
     ls_enter = en, ls_combine_env = ce, ls_combine_assign = ca \<rparr>"

lemma make_local_spec_sel [simp]:
  "ls_query (make_local_spec qry st en ce ca) = qry"
  "ls_step (make_local_spec qry st en ce ca) = st"
  "ls_enter (make_local_spec qry st en ce ca) = en"
  "ls_combine_env (make_local_spec qry st en ce ca) = ce"
  "ls_combine_assign (make_local_spec qry st en ce ca) = ca"
proof -
  have "ls_step (make_local_spec qry st en ce ca) ch a = st ch a" for ch a
  proof (cases a)
    case (EA_Check l cnd)
    then show ?thesis by (simp add: make_local_spec_def ls_step_def)
  qed (simp_all add: make_local_spec_def ls_step_def)
  then show "ls_step (make_local_spec qry st en ce ca) = st" by (simp add: fun_eq_iff)
qed (simp_all add: make_local_spec_def)

text \<open>
  The return runs in the two stages of Goblint's \<open>combine_env\<close> and
  \<open>combine_assign\<close>, which both receive the callee's channel. Only the first
  receives the caller's: Goblint's \<open>combine_assign\<close> asks about the state
  \<open>combine_env\<close> produced, which describes no concrete store on its own here,
  since soundness and independence speak only about the composite.
\<close>

abbreviation ls_combine ::
  "('vr,'e,'s) glocal_spec \<Rightarrow> 'e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "ls_combine c ch ch' ci x de \<equiv> ls_combine_assign c ch' ci (ls_combine_env c ch ch' ci x de) de"

text \<open>
  A local specification is sound for a concretization \<open>gamma\<close> when each operation covers the
  concrete behaviour, whatever the other fields of the record hold. Every
  operation is proved against every channel that holds at the stores it is
  asked about, so its proof cannot depend on who answers: the caller's store for a
  step, an entry, a query and the first stage of a return, and the callee's exit
  store for the callee's channel.
\<close>

context mcp_sem
begin

definition gsound_local_spec ::
  "('s::order \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('vr,'e,'s) glocal_spec \<Rightarrow> bool" where
  "gsound_local_spec gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> (\<forall>ch a x. gedge_collect a (gm x \<inter> Collect (geval_query.channel_holds ev ch))
                  \<subseteq> gm (ls_step c ch a x))
     \<and> (\<forall>ch s ci p. s \<in> gm (fst p) \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          (\<exists>q \<in> set (ls_enter c ch ci p). s \<in> gm (fst q)
             \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                 \<in> gm (snd q)))
     \<and> (\<forall>ch ch' s t ci x de. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          t \<in> gm de \<longrightarrow> geval_query.channel_holds ev ch' t \<longrightarrow>
          gcombine_collect (ci_dst ci) s t \<in> gm (ls_combine c ch ch' ci x de))
     \<and> (\<forall>ch s x q. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
          geval_holds ev q (ls_query c ch x q) s)"

text \<open>
  The step obligation splits into one law per kind of edge, each about the
  field that handles it: the store the edge produces lies in what the field
  returns, for every store and channel that hold before. A component proves the
  laws of the fields it defines, and a field it replaces needs only its own law
  again (\<open>sound_local_spec_update\<close>).
\<close>

definition gsound_skip :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_skip gm f \<longleftrightarrow>
     (\<forall>ch x s. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> s \<in> gm (f ch x))"

definition gsound_assign ::
  "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 'vr \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_assign gm f \<longleftrightarrow>
     (\<forall>ch x s y e. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> s(y := conv (Some y) (ev e s)) \<in> gm (f ch y e x))"

definition gsound_special ::
  "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 'e gspecial_call \<Rightarrow> 'vr \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_special gm f \<longleftrightarrow>
     (\<forall>ch x s sc y t. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> t \<in> gspecial_step sc y s
        \<longrightarrow> t \<in> gm (f ch sc y x))"

definition gsound_branch :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_branch gm f \<longleftrightarrow>
     (\<forall>ch x s b pol. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> truthy (ev b s) = pol
        \<longrightarrow> s \<in> gm (f ch b pol x))"

definition gsound_body :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_body gm f \<longleftrightarrow>
     (\<forall>ch x s p. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> s \<in> gm (f ch p x))"

definition gsound_return ::
  "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 'e option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_return gm f \<longleftrightarrow>
     (\<forall>ch x s r p. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s
        \<longrightarrow> s(rv := (case r of None \<Rightarrow> s rv | Some a \<Rightarrow> ev a s)) \<in> gm (f ch r p x))"

definition gsound_event :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 'e ganalysis_event \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_event gm f \<longleftrightarrow>
     (\<forall>ch x s evt. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> s \<in> gm (f ch evt x))"

text \<open>
  The laws of the other fields. The handler's answers hold at every store its
  state describes. An entry covers the caller's store and the store the call
  enters by one of its pairs. The two return stages carry one law together,
  because only their composition describes a concrete store.
\<close>

definition gsound_query :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> ('e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel) \<Rightarrow> bool" where
  "gsound_query gm h \<longleftrightarrow>
     (\<forall>ch s x q. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow> geval_holds ev q (h ch x q) s)"

definition gsound_enter ::
  "('s \<Rightarrow> ('vr \<Rightarrow> int) set)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list) \<Rightarrow> bool" where
  "gsound_enter gm en \<longleftrightarrow>
     (\<forall>ch s ci p. s \<in> gm (fst p) \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
        (\<exists>q \<in> set (en ch ci p). s \<in> gm (fst q)
           \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> gm (snd q)))"

definition gsound_combine ::
  "('s \<Rightarrow> ('vr \<Rightarrow> int) set)
   \<Rightarrow> ('e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> bool" where
  "gsound_combine gm ce ca \<longleftrightarrow>
     (\<forall>ch ch' s t ci x de. s \<in> gm x \<longrightarrow> geval_query.channel_holds ev ch s \<longrightarrow>
        t \<in> gm de \<longrightarrow> geval_query.channel_holds ev ch' t \<longrightarrow>
        gcombine_collect (ci_dst ci) s t \<in> gm (ca ch' ci (ce ch ch' ci x de) de))"

theorem ls_step_sound_iff:
  "(\<forall>ch a x. gedge_collect a (gm x \<inter> Collect (geval_query.channel_holds ev ch)) \<subseteq> gm (ls_step c ch a x))
   \<longleftrightarrow> gsound_skip gm (ls_skip c) \<and> gsound_assign gm (ls_assign c) \<and> gsound_special gm (ls_special c)
     \<and> gsound_branch gm (ls_branch c) \<and> gsound_body gm (ls_body c)
     \<and> gsound_return gm (ls_return c) \<and> gsound_event gm (ls_event c)"
  (is "?step \<longleftrightarrow> ?fields")
proof
  assume step: ?step
  have at: "t \<in> gm (ls_step c ch act x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" "t \<in> gedge_step act s" for ch act x s t
    using step that unfolding gedge_collect_def by blast
  have skip: "s \<in> gm (ls_skip c ch x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" for ch x s
  proof -
    have "s \<in> gm (ls_step c ch EA_Nop x)" by (rule at[OF that]) simp
    then show ?thesis by simp
  qed
  have assign: "s(y := conv (Some y) (ev e s)) \<in> gm (ls_assign c ch y e x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" for ch x s y e
  proof -
    have "s(y := conv (Some y) (ev e s)) \<in> gm (ls_step c ch (EA_Assign y e) x)"
      by (rule at[OF that]) simp
    then show ?thesis by simp
  qed
  have body: "s \<in> gm (ls_body c ch p x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" for ch x s p
  proof -
    have "s \<in> gm (ls_step c ch (EA_Body p) x)" by (rule at[OF that]) simp
    then show ?thesis by simp
  qed
  have ret: "s(rv := (case r of None \<Rightarrow> s rv | Some a \<Rightarrow> ev a s)) \<in> gm (ls_return c ch r p x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" for ch x s r p
  proof -
    have "s(rv := (case r of None \<Rightarrow> s rv | Some a \<Rightarrow> ev a s)) \<in> gm (ls_step c ch (EA_Ret r p) x)"
      by (rule at[OF that]) simp
    then show ?thesis by simp
  qed
  have pol: "s \<in> gm (ls_branch c ch b pol x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" "truthy (ev b s) = pol" for ch b pol x s
  proof (cases pol)
    case True
    have "s \<in> gm (ls_step c ch (EA_Assume b) x)"
      by (rule at[OF that(1,2)]) (use that(3) True in simp)
    then show ?thesis using True by simp
  next
    case False
    have "s \<in> gm (ls_step c ch (EA_AssumeNot b) x)"
      by (rule at[OF that(1,2)]) (use that(3) False in simp)
    then show ?thesis using False by simp
  qed
  have ev: "s \<in> gm (ls_event c ch evt x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" for ch evt x s
  proof (cases evt)
    case (Check_Event l e)
    have "s \<in> gm (ls_step c ch (EA_Check l e) x)" by (rule at[OF that]) simp
    then show ?thesis using Check_Event by simp
  qed
  have special: "t \<in> gm (ls_special c ch sc y x)"
    if "s \<in> gm x" "geval_query.channel_holds ev ch s" "t \<in> gspecial_step sc y s" for ch x s sc y t
  proof -
    have "t \<in> gm (ls_step c ch (EA_Special sc y) x)"
      by (rule at[OF that(1,2)]) (simp only: gedge_step.simps that(3))
    then show ?thesis by (simp only: ls_step_simps)
  qed
  show ?fields
    unfolding gsound_skip_def gsound_assign_def gsound_special_def gsound_branch_def gsound_body_def
      gsound_return_def gsound_event_def
    by (intro conjI allI impI; (rule skip assign special pol body ret ev; assumption))
next
  assume F: ?fields
  show ?step
  proof (intro allI subsetI)
    fix ch a x t
    assume "t \<in> gedge_collect a (gm x \<inter> Collect (geval_query.channel_holds ev ch))"
    then obtain s where s: "s \<in> gm x" "geval_query.channel_holds ev ch s" "t \<in> gedge_step a s"
      unfolding gedge_collect_def by blast
    show "t \<in> gm (ls_step c ch a x)"
    proof (cases a)
      case (EA_Special sc y)
      have "t \<in> gspecial_step sc y s" using s(3) EA_Special by (simp only: gedge_step.simps)
      then show ?thesis
        using F s(1,2) EA_Special unfolding gsound_special_def by (simp only: ls_step_simps)
    next
      case (EA_Assume b)
      then have "t = s" "truthy (ev b s) = True" using s(3) by (simp_all split: if_splits)
      then show ?thesis
        using F s(1,2) EA_Assume unfolding gsound_branch_def by (simp only: ls_step_simps)
    next
      case (EA_AssumeNot b)
      then have "t = s" "truthy (ev b s) = False" using s(3) by (simp_all split: if_splits)
      then show ?thesis
        using F s(1,2) EA_AssumeNot unfolding gsound_branch_def by (simp only: ls_step_simps)
    qed (use F s in \<open>auto simp: gsound_skip_def gsound_assign_def gsound_body_def gsound_return_def
                     gsound_event_def\<close>)
  qed
qed

text \<open>
  The certificate is exactly the conjunction of a monotone concretization and
  one law per field, the two return stages sharing one law. A local
  specification is therefore built, taken apart and changed field by field.
\<close>

theorem sound_local_spec_iff:
  "gsound_local_spec gm c \<longleftrightarrow>
     (\<forall>x y. x \<le> y \<longrightarrow> gm x \<subseteq> gm y)
     \<and> gsound_query gm (ls_query c)
     \<and> gsound_skip gm (ls_skip c) \<and> gsound_assign gm (ls_assign c)
     \<and> gsound_special gm (ls_special c) \<and> gsound_branch gm (ls_branch c)
     \<and> gsound_body gm (ls_body c) \<and> gsound_return gm (ls_return c)
     \<and> gsound_event gm (ls_event c)
     \<and> gsound_enter gm (ls_enter c)
     \<and> gsound_combine gm (ls_combine_env c) (ls_combine_assign c)"
  unfolding gsound_local_spec_def ls_step_sound_iff gsound_query_def gsound_enter_def
    gsound_combine_def
  by (intro iffI; elim conjE; intro conjI; assumption)

lemma sound_local_specI:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> gm x \<subseteq> gm y"
    and "gsound_query gm (ls_query c)"
    and "gsound_skip gm (ls_skip c)" and "gsound_assign gm (ls_assign c)"
    and "gsound_special gm (ls_special c)" and "gsound_branch gm (ls_branch c)"
    and "gsound_body gm (ls_body c)" and "gsound_return gm (ls_return c)"
    and "gsound_event gm (ls_event c)"
    and "gsound_enter gm (ls_enter c)"
    and "gsound_combine gm (ls_combine_env c) (ls_combine_assign c)"
  shows "gsound_local_spec gm c"
  using assms unfolding sound_local_spec_iff by blast

lemma sound_local_specD:
  assumes "gsound_local_spec gm c"
  shows sound_local_spec_monoD: "x \<le> y \<Longrightarrow> gm x \<subseteq> gm y"
    and sound_local_spec_queryD: "gsound_query gm (ls_query c)"
    and sound_local_spec_skipD: "gsound_skip gm (ls_skip c)"
    and sound_local_spec_assignD: "gsound_assign gm (ls_assign c)"
    and sound_local_spec_specialD: "gsound_special gm (ls_special c)"
    and sound_local_spec_branchD: "gsound_branch gm (ls_branch c)"
    and sound_local_spec_bodyD: "gsound_body gm (ls_body c)"
    and sound_local_spec_returnD: "gsound_return gm (ls_return c)"
    and sound_local_spec_eventD: "gsound_event gm (ls_event c)"
    and sound_local_spec_enterD: "gsound_enter gm (ls_enter c)"
    and sound_local_spec_combineD:
      "gsound_combine gm (ls_combine_env c) (ls_combine_assign c)"
  using assms unfolding sound_local_spec_iff by blast+

text \<open>
  A sound local specification stays sound when one field is replaced by one
  satisfying that field's law. A return stage is replaced together with the law
  of the composed return it forms with the other stage.
\<close>

lemma sound_local_spec_update:
  assumes "gsound_local_spec gm c"
  shows sound_local_spec_update_query:
      "gsound_query gm h \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_query := h\<rparr>)"
    and sound_local_spec_update_skip:
      "gsound_skip gm sk \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_skip := sk\<rparr>)"
    and sound_local_spec_update_assign:
      "gsound_assign gm asn \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_assign := asn\<rparr>)"
    and sound_local_spec_update_special:
      "gsound_special gm sp \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_special := sp\<rparr>)"
    and sound_local_spec_update_branch:
      "gsound_branch gm br \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_branch := br\<rparr>)"
    and sound_local_spec_update_body:
      "gsound_body gm bd \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_body := bd\<rparr>)"
    and sound_local_spec_update_return:
      "gsound_return gm rt \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_return := rt\<rparr>)"
    and sound_local_spec_update_event:
      "gsound_event gm evt \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_event := evt\<rparr>)"
    and sound_local_spec_update_enter:
      "gsound_enter gm en \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_enter := en\<rparr>)"
    and sound_local_spec_update_combine_env:
      "gsound_combine gm ce (ls_combine_assign c)
       \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_combine_env := ce\<rparr>)"
    and sound_local_spec_update_combine_assign:
      "gsound_combine gm (ls_combine_env c) ca
       \<Longrightarrow> gsound_local_spec gm (c\<lparr>ls_combine_assign := ca\<rparr>)"
  using assms unfolding sound_local_spec_iff by simp_all

end

subsection \<open>Conservative defaults\<close>

text \<open>
  A field whose concrete counterpart leaves the store unchanged has a default
  that decides nothing: the handler answers \<open>\<top>\<close>, and skip, body, event and
  branch keep the state. Each is sound for every concretization. Assign,
  special, return, entry and the second return stage change the store or the
  frame, so no default is sound for every concretization and an analysis
  supplies them. The first return stage defaults to the caller's state; it has
  no law of its own, only the composed return does.
\<close>

definition query_unknown :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel" where
  "query_unknown ch x = \<top>"

definition skip_identity :: "'e gchannel \<Rightarrow> 's \<Rightarrow> 's" where
  "skip_identity ch x = x"

definition body_identity :: "'e gchannel \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's" where
  "body_identity ch p x = x"

definition event_identity :: "'e gchannel \<Rightarrow> 'e ganalysis_event \<Rightarrow> 's \<Rightarrow> 's" where
  "event_identity ch ev x = x"

definition branch_identity :: "'e gchannel \<Rightarrow> 'e \<Rightarrow> bool \<Rightarrow> 's \<Rightarrow> 's" where
  "branch_identity ch b pol x = x"

definition combine_env_identity :: "'e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "combine_env_identity ch ch' ci x de = x"

context mcp_sem
begin

lemma sound_query_unknown: "gsound_query gm query_unknown"
  by (simp add: gsound_query_def query_unknown_def)

lemma sound_skip_identity: "gsound_skip gm skip_identity"
  by (simp add: gsound_skip_def skip_identity_def)

lemma sound_body_identity: "gsound_body gm body_identity"
  by (simp add: gsound_body_def body_identity_def)

lemma sound_event_identity: "gsound_event gm event_identity"
  by (simp add: gsound_event_def event_identity_def)

lemma sound_branch_identity: "gsound_branch gm branch_identity"
  by (simp add: gsound_branch_def branch_identity_def)

lemma sound_combine_env_identity:
  "gsound_combine gm combine_env_identity ca \<longleftrightarrow>
     (\<forall>ch' s t ci x de. s \<in> gm x \<longrightarrow> t \<in> gm de \<longrightarrow> geval_query.channel_holds ev ch' t \<longrightarrow>
        gcombine_collect (ci_dst ci) s t \<in> gm (ca ch' ci x de))"
  unfolding gsound_combine_def combine_env_identity_def
  using geval_query.channel_holds_top by blast

end

text \<open>
  A local specification that supplies only the five operations without a
  default. An analysis starts from it and overrides the fields it decides more
  precisely; each override needs only its own law again
  (\<open>sound_local_spec_update\<close>).
\<close>

definition conservative_local_spec ::
  "('e gchannel \<Rightarrow> 'vr \<Rightarrow> 'e \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> 'e gspecial_call \<Rightarrow> 'vr \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> 'e option \<Rightarrow> pname \<Rightarrow> 's \<Rightarrow> 's)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> ('s \<times> 's) list)
   \<Rightarrow> ('e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('vr,'e,'s) glocal_spec" where
  "conservative_local_spec asn sp rt en ca = \<lparr>
     ls_query = query_unknown, ls_skip = skip_identity, ls_assign = asn,
     ls_special = sp, ls_branch = branch_identity, ls_body = body_identity,
     ls_return = rt, ls_event = event_identity, ls_enter = en,
     ls_combine_env = combine_env_identity, ls_combine_assign = ca \<rparr>"

context mcp_sem
begin

theorem sound_conservative_local_spec:
  assumes "\<And>x y. x \<le> y \<Longrightarrow> gm x \<subseteq> gm y"
    and "gsound_assign gm asn" and "gsound_special gm sp" and "gsound_return gm rt"
    and "gsound_enter gm en" and "gsound_combine gm combine_env_identity ca"
  shows "gsound_local_spec gm (conservative_local_spec asn sp rt en ca)"
  by (rule sound_local_specI)
     (simp_all add: conservative_local_spec_def assms sound_query_unknown sound_skip_identity
        sound_body_identity sound_event_identity sound_branch_identity)
end

text \<open>
  A component leaves a concretization alone when none of its operations
  changes what that concretization says. For components that each own one
  field of a record this is the lens law that updating one field leaves the
  others.
\<close>

definition mcp_frame :: "('vr,'e,'s) glocal_spec \<Rightarrow> ('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<Rightarrow> bool" where
  "mcp_frame c gm \<longleftrightarrow>
     (\<forall>ch a x. gm (ls_step c ch a x) = gm x)
     \<and> (\<forall>ch ci p q. q \<in> set (ls_enter c ch ci p) \<longrightarrow>
          gm (fst q) = gm (fst p) \<and> gm (snd q) = gm (snd p))
     \<and> (\<forall>ch ch' ci x de. gm (ls_combine c ch ch' ci x de) = gm x)"

text \<open>
  Cooperating analyses come as pairs of a concretization and a component.
  They are independent when each leaves the others' concretizations alone.
\<close>

type_synonym ('vr,'e,'s) gcertified_component = "('s \<Rightarrow> ('vr \<Rightarrow> int) set) \<times> ('vr,'e,'s) glocal_spec"
type_synonym 's certified_component = "(vname, exp, 's) gcertified_component"

fun mcp_independent :: "('vr,'e,'s) gcertified_component list \<Rightarrow> bool" where
  "mcp_independent [] \<longleftrightarrow> True"
| "mcp_independent ((g, c) # gcs) \<longleftrightarrow>
     (\<forall>(g', c') \<in> set gcs. mcp_frame c g' \<and> mcp_frame c' g) \<and> mcp_independent gcs"

section \<open>The query channel\<close>

text \<open>
  A handler answers a query given the channel through which it may ask further
  ones. \<open>ask_rec\<close> closes that recursion over one state, as Goblint's
  \<open>MCP.query'\<close> does: a query already being asked answers \<open>\<top>\<close> instead of
  recursing, and every other query is answered by the handler under a channel
  that remembers it. The depth bound plays the role it plays in
  \<^const>\<open>ask_with\<close>: queries range over an infinite type, so cycle detection
  alone does not make the recursion total, and exhausting the bound aborts the
  generated program. Logically the fallback is \<open>\<top>\<close>, so the bound plays no part
  in soundness. Goblint also caches answers per transfer; that changes only how
  often a handler runs.
\<close>

fun ask_rec :: "('e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel) \<Rightarrow> nat \<Rightarrow> 'e gquery set \<Rightarrow> 's \<Rightarrow> 'e gchannel" where
  "ask_rec H 0 asked x q =
     Code.abort (STR ''query recursion exceeded query_depth'') (\<lambda>_. \<top>)"
| "ask_rec H (Suc n) asked x q =
     (if q \<in> asked then \<top> else H (ask_rec H n (insert q asked) x) x q)"

text \<open>
  A handler that answers soundly under every sound channel makes the closed
  channel sound: by induction on the depth, each level's channel holds, so the
  handler's answer under it holds.
\<close>

context mcp_sem
begin

lemma ask_rec_sound:
  assumes "\<And>ch q. geval_query.channel_holds ev ch s \<Longrightarrow> geval_holds ev q (H ch x q) s"
  shows "geval_query.channel_holds ev (ask_rec H n asked x) s"
proof (induction n arbitrary: asked)
  case 0
  then show ?case by (simp add: geval_query.channel_holds_def)
next
  case (Suc n)
  then show ?case
    using assms by (auto simp: geval_query.channel_holds_def)
qed

end

definition ls_channel :: "('vr,'e,'s) glocal_spec \<Rightarrow> 's \<Rightarrow> 'e gchannel" where
  "ls_channel c x = ask_rec (ls_query c) query_depth {} x"

context mcp_sem
begin

lemma ls_channel_sound:
  assumes "gsound_local_spec \<gamma>\<^sub>c c" and "s \<in> \<gamma>\<^sub>c x"
  shows "geval_query.channel_holds ev (ls_channel c x) s"
  unfolding ls_channel_def
  by (rule ask_rec_sound) (use assms in \<open>simp add: gsound_local_spec_def\<close>)

end

lemma ls_channel_const: "ls_query c = (\<lambda>ch x. h x) \<Longrightarrow> ls_channel c = h"
  by (simp add: ls_channel_def query_depth_def fun_eq_iff eval_nat_numeral)

section \<open>The combined operations\<close>

text \<open>
  The combined operations run the active components in turn. Soundness needs
  only \<^const>\<open>mcp_frame\<close>: a component keeps what the other components'
  states describe, not their representation, so the soundness proof says
  nothing about the order of the fold. A component that updates only its own
  field of a product does leave the other fields unchanged, and for those the
  order does not matter; Goblint runs every component on the predecessor's
  part of the state, which is the same computation. Every component gets the
  same channel, as every Goblint component gets the same \<open>man.ask\<close>.
\<close>

definition mcp_step :: "('vr,'e,'s) glocal_spec list \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gedge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_step cs ch a x = fold (\<lambda>c y. ls_step c ch a y) cs x"

definition mcp_en_from ::
  "('vr,'e,'s) glocal_spec list \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<times> 's \<Rightarrow> 's enter_result list" where
  "mcp_en_from cs ch ci p = fold (\<lambda>c ps. concat (map (ls_enter c ch ci) ps)) cs [p]"

definition mcp_comb ::
  "('vr,'e,'s) glocal_spec list \<Rightarrow> 'e gchannel \<Rightarrow> 'e gchannel \<Rightarrow> ('vr,'e) gcall_info \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 's" where
  "mcp_comb cs ch ch' ci x de = fold (\<lambda>c y. ls_combine c ch ch' ci y de) cs x"

text \<open>
  The combined handler meets every component's answer, each given the same
  channel, as \<open>MCP.query'\<close> meets the results of all analyses.
\<close>

definition mcp_qry :: "('vr,'e,'s) glocal_spec list \<Rightarrow> 'e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel" where
  "mcp_qry cs ch x q = fold (\<lambda>c r. r \<sqinter> ls_query c ch x q) cs \<top>"

definition mcp_gamma :: "('s \<Rightarrow> ('vr \<Rightarrow> int) set) list \<Rightarrow> 's \<Rightarrow> ('vr \<Rightarrow> int) set" where
  "mcp_gamma \<Gamma> x = (\<Inter>\<gamma>\<^sub>i \<in> set \<Gamma>. \<gamma>\<^sub>i x)"

section \<open>Soundness of the combination\<close>

text \<open>
  The combined state is sound for the intersection \<open>mcp_gamma\<close> of the
  components' concretizations. Step, combine, entry and query folds each stay
  sound because a component leaves the others' concretizations unchanged.
\<close>

lemma mcp_gamma_Cons [simp]: "mcp_gamma (g # gs) x = g x \<inter> mcp_gamma gs x"
  by (simp add: mcp_gamma_def)

lemma mcp_gamma_Nil [simp]: "mcp_gamma [] x = UNIV"
  by (simp add: mcp_gamma_def)

text \<open>Components a fold runs leave an independent concretization as it was.\<close>

lemma gamma_fold_step:
  "(\<forall>c \<in> set cs. mcp_frame c g) \<Longrightarrow> g (fold (\<lambda>c y. ls_step c ch a y) cs x) = g x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma gamma_fold_comb:
  "(\<forall>c \<in> set cs. mcp_frame c g) \<Longrightarrow> g (fold (\<lambda>c y. ls_combine c ch ch' ci y de) cs x) = g x"
  by (induction cs arbitrary: x) (simp_all add: mcp_frame_def)

lemma mcp_gamma_frame:
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (ls_step c ch a x) = mcp_gamma gs x"
  "(\<forall>g \<in> set gs. mcp_frame c g) \<Longrightarrow> mcp_gamma gs (ls_combine c ch ch' ci x de) = mcp_gamma gs x"
  by (auto simp: mcp_gamma_def mcp_frame_def intro!: INF_cong)

lemma mcp_independent_Cons_frames:
  assumes "mcp_independent ((g, c) # gcs)"
  shows "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
  using assms by auto

context mcp_sem
begin

lemma mcp_step_sound:
  assumes "\<forall>(g, c) \<in> set gcs. gsound_local_spec g c" and "mcp_independent gcs"
  shows "gedge_collect a (mcp_gamma (map fst gcs) x \<inter> Collect (geval_query.channel_holds ev ch))
           \<subseteq> mcp_gamma (map fst gcs) (mcp_step (map snd gcs) ch a x)"
  using assms
proof (induction gcs arbitrary: x)
  case Nil
  then show ?case by (simp add: mcp_step_def)
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  let ?O = "Collect (geval_query.channel_holds ev ch)"
  let ?x1 = "ls_step c ch a x"
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  have own: "gedge_collect a (g x \<inter> ?O) \<subseteq> g ?x1"
    using Cons.prems(1) unfolding gc by (simp add: gsound_local_spec_def)
  have own_kept: "g (mcp_step (map snd gcs) ch a ?x1) = g ?x1"
    unfolding mcp_step_def by (rule gamma_fold_step) (use frames in auto)
  have rest: "gedge_collect a (mcp_gamma (map fst gcs) ?x1 \<inter> ?O)
      \<subseteq> mcp_gamma (map fst gcs) (mcp_step (map snd gcs) ch a ?x1)"
    by (rule Cons.IH) (use Cons.prems(1) frames in auto)
  have rest_eq: "mcp_gamma (map fst gcs) ?x1 = mcp_gamma (map fst gcs) x"
    by (rule mcp_gamma_frame(1)) (use frames in auto)
  have "gedge_collect a (mcp_gamma (map fst (gc # gcs)) x \<inter> ?O)
          \<subseteq> gedge_collect a (g x \<inter> ?O) \<inter> gedge_collect a (mcp_gamma (map fst gcs) ?x1 \<inter> ?O)"
    unfolding gc by (intro Int_greatest edge_collect_mono) (auto simp: rest_eq)
  also have "\<dots> \<subseteq> mcp_gamma (map fst (gc # gcs)) (mcp_step (map snd (gc # gcs)) ch a x)"
    using own own_kept rest unfolding gc by (auto simp: mcp_step_def)
  finally show ?case .
qed

lemma mcp_comb_sound:
  assumes "\<forall>(g, c) \<in> set gcs. gsound_local_spec g c" and "mcp_independent gcs"
    and "s \<in> mcp_gamma (map fst gcs) x" and "geval_query.channel_holds ev ch s"
    and "t \<in> mcp_gamma (map fst gcs) de" and "geval_query.channel_holds ev ch' t"
  shows "gcombine_collect (ci_dst ci) s t
           \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) ch ch' ci x de)"
  using assms
proof (induction gcs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  let ?x1 = "ls_combine c ch ch' ci x de"
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  have own: "gcombine_collect (ci_dst ci) s t \<in> g ?x1"
    using Cons.prems(1,3-6) unfolding gc by (simp add: gsound_local_spec_def)
  have own_kept: "g (mcp_comb (map snd gcs) ch ch' ci ?x1 de) = g ?x1"
    unfolding mcp_comb_def by (rule gamma_fold_comb) (use frames in auto)
  have rest_eq: "mcp_gamma (map fst gcs) ?x1 = mcp_gamma (map fst gcs) x"
    by (rule mcp_gamma_frame(2)) (use frames in auto)
  have rest: "gcombine_collect (ci_dst ci) s t
      \<in> mcp_gamma (map fst gcs) (mcp_comb (map snd gcs) ch ch' ci ?x1 de)"
    by (rule Cons.IH) (use Cons.prems frames rest_eq gc in auto)
  show ?case
    using own own_kept rest unfolding gc by (simp add: mcp_comb_def)
qed

text \<open>
  Entry threads a list of pairs through the components. The invariant carries
  the concretizations of the components already run (\<open>ds\<close>), whose fields are
  set in both halves, and the components still to run (\<open>gcs\<close>), whose fields
  are still the caller's.
\<close>

lemma mcp_en_fold_sound:
  assumes "\<forall>(g, c) \<in> set gcs. gsound_local_spec g c" and "mcp_independent gcs"
    and "\<forall>c \<in> snd ` set gcs. \<forall>d \<in> set ds. mcp_frame c d"
    and "\<exists>p \<in> set ps. s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma ds (fst p)
                       \<and> E \<in> mcp_gamma ds (snd p)"
    and A: "geval_query.channel_holds ev ch s"
    and E: "E = gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s"
  shows "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (ls_enter c ch ci) ps)) (map snd gcs) ps).
           s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma ds (fst p)
           \<and> E \<in> mcp_gamma (map fst gcs) (snd p) \<and> E \<in> mcp_gamma ds (snd p)"
  using assms(1-4)
proof (induction gcs arbitrary: ps ds)
  case Nil
  then show ?case by simp
next
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  have frames: "\<forall>g' \<in> fst ` set gcs. mcp_frame c g'" "\<forall>c' \<in> snd ` set gcs. mcp_frame c' g"
    "mcp_independent gcs"
    using mcp_independent_Cons_frames[OF Cons.prems(2)[unfolded gc]] by simp_all
  obtain p where p: "p \<in> set ps" "s \<in> g (fst p)" "s \<in> mcp_gamma (map fst gcs) (fst p)"
      "s \<in> mcp_gamma ds (fst p)" "E \<in> mcp_gamma ds (snd p)"
    using Cons.prems(4) unfolding gc by auto
  have "gsound_local_spec g c" using Cons.prems(1) unfolding gc by simp
  then obtain q where q: "q \<in> set (ls_enter c ch ci p)" "s \<in> g (fst q)" "E \<in> g (snd q)"
    using p(2) A unfolding E gsound_local_spec_def by meson
  have keep: "d (fst q) = d (fst p) \<and> d (snd q) = d (snd p)"
    if "d \<in> fst ` set gcs \<union> set ds" for d
  proof -
    have "mcp_frame c d" using that frames(1) Cons.prems(3) unfolding gc by auto
    then show ?thesis using q(1) unfolding mcp_frame_def by blast
  qed
  have q_in: "q \<in> set (concat (map (ls_enter c ch ci) ps))"
    using p(1) q(1) by auto
  have "\<exists>p \<in> set (fold (\<lambda>c ps. concat (map (ls_enter c ch ci) ps)) (map snd gcs)
                 (concat (map (ls_enter c ch ci) ps))).
          s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma (g # ds) (fst p)
          \<and> E \<in> mcp_gamma (map fst gcs) (snd p) \<and> E \<in> mcp_gamma (g # ds) (snd p)"
  proof (rule Cons.IH)
    show "\<forall>(g, c) \<in> set gcs. gsound_local_spec g c" using Cons.prems(1) by simp
    show "mcp_independent gcs" by (fact frames(3))
    show "\<forall>c' \<in> snd ` set gcs. \<forall>d \<in> set (g # ds). mcp_frame c' d"
      using frames(2) Cons.prems(3) unfolding gc by auto
    show "\<exists>p \<in> set (concat (map (ls_enter c ch ci) ps)).
            s \<in> mcp_gamma (map fst gcs) (fst p) \<and> s \<in> mcp_gamma (g # ds) (fst p)
            \<and> E \<in> mcp_gamma (g # ds) (snd p)"
    proof (rule bexI[OF _ q_in])
      show "s \<in> mcp_gamma (map fst gcs) (fst q) \<and> s \<in> mcp_gamma (g # ds) (fst q)
              \<and> E \<in> mcp_gamma (g # ds) (snd q)"
      proof -
        have "mcp_gamma (map fst gcs) (fst q) = mcp_gamma (map fst gcs) (fst p)"
            "mcp_gamma ds (fst q) = mcp_gamma ds (fst p)"
            "mcp_gamma ds (snd q) = mcp_gamma ds (snd p)"
          using keep by (auto simp: mcp_gamma_def intro!: INF_cong)
        then show ?thesis using p(3-5) q(2,3) by simp
      qed
    qed
  qed
  then show ?case unfolding gc by (auto simp: mcp_gamma_def)
qed

lemma mcp_qry_fold_sound:
  "s \<in> mcp_gamma (map fst gcs) x \<Longrightarrow> geval_query.channel_holds ev ch s
   \<Longrightarrow> \<forall>(g, c) \<in> set gcs. gsound_local_spec g c
   \<Longrightarrow> geval_holds ev q r s
   \<Longrightarrow> geval_holds ev q (fold (\<lambda>c r. r \<sqinter> ls_query c ch x q) (map snd gcs) r) s"
proof (induction gcs arbitrary: r)
  case (Cons gc gcs)
  obtain g c where gc: "gc = (g, c)" by fastforce
  have "geval_holds ev q (ls_query c ch x q) s"
    using Cons.prems unfolding gc by (simp add: gsound_local_spec_def)
  with Cons.prems(4) have "geval_holds ev q (r \<sqinter> ls_query c ch x q) s"
    by (rule geval_query.inf_sound)
  then show ?case
    using Cons.IH[of "r \<sqinter> ls_query c ch x q"] Cons.prems(1-3) unfolding gc by simp
qed simp

end

section \<open>A component as a specification\<close>

text \<open>
  A component runs as the specification whose fields are its own operations,
  each given the component's closed channel on the state it is asked about. The
  specification reads no global and publishes none. Its channel is a pure
  function of the state, so a transfer asks it whatever it needs while it runs,
  as a Goblint transfer asks \<open>man.ask\<close>. Entry starts both halves at the
  caller's record.
\<close>

text \<open>The step a component takes on an edge, with its own channel.\<close>

definition closed_step :: "('vr,'e,'s) glocal_spec \<Rightarrow> ('vr,'e) gedge_action \<Rightarrow> 's \<Rightarrow> 's" where
  "closed_step c a d = ls_step c (ls_channel c d) a d"

text \<open>\<open>\<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub> d\<close> is the abstract transfer of action \<open>a\<close>, the counterpart of
  the abstract evaluation \<open>\<lbrakk>e\<rbrakk>\<^sup>\<sharp> d\<close>; the subscript names the component.\<close>

abbreviation abs_step :: "('vr,'e) gedge_action \<Rightarrow> ('vr,'e,'s) glocal_spec \<Rightarrow> 's \<Rightarrow> 's"
  ("\<lbrakk>_\<rbrakk>\<^sup>\<sharp>\<^bsub>_\<^esub>") where
  "\<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub> \<equiv> closed_step c a"

definition dg_spec_of :: "('vr,'e,'s) glocal_spec \<Rightarrow> ('vr,'e,'x,'k,'v,'s::bot,'G) gdg_spec" where
  "dg_spec_of c = local_dg_spec_template\<lparr>
     dgs_skip := local_transfer \<lbrakk>EA_Nop\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>,
     dgs_assign := (\<lambda>x e. local_transfer \<lbrakk>EA_Assign x e\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_special := (\<lambda>sc x. local_transfer \<lbrakk>EA_Special sc x\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_branch := (\<lambda>b pol. local_transfer
                      \<lbrakk>if pol then EA_Assume b else EA_AssumeNot b\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_body := (\<lambda>p. local_transfer \<lbrakk>EA_Body p\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_return := (\<lambda>e p. local_transfer \<lbrakk>EA_Ret e p\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_enter := (\<lambda>ci. local_enter_transfer (\<lambda>d. ls_enter c (ls_channel c d) ci (d, d))),
     dgs_event := (\<lambda>ev. local_transfer \<lbrakk>event_action ev\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>),
     dgs_combine_env := (\<lambda>ci. local_combine_transfer
        (\<lambda>dc de. ls_combine_env c (ls_channel c dc) (ls_channel c de) ci dc de)),
     dgs_combine_assign := (\<lambda>ci. local_combine_transfer
        (\<lambda>dc de. ls_combine_assign c (ls_channel c de) ci dc de)),
     dgs_query := local_query (ls_channel c) \<rparr>"


lemma dg_spec_of_simps [simp]:
  "skip\<^sup>\<sharp> (dg_spec_of c) = local_transfer \<lbrakk>EA_Nop\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "assign\<^sup>\<sharp> (dg_spec_of c) x e = local_transfer \<lbrakk>EA_Assign x e\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "special\<^sup>\<sharp> (dg_spec_of c) sc x = local_transfer \<lbrakk>EA_Special sc x\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "branch\<^sup>\<sharp> (dg_spec_of c) b pol
     = local_transfer \<lbrakk>if pol then EA_Assume b else EA_AssumeNot b\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "body\<^sup>\<sharp> (dg_spec_of c) p = local_transfer \<lbrakk>EA_Body p\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "return\<^sup>\<sharp> (dg_spec_of c) eo p = local_transfer \<lbrakk>EA_Ret eo p\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "enter\<^sup>\<sharp> (dg_spec_of c) ci
     = local_enter_transfer (\<lambda>d. ls_enter c (ls_channel c d) ci (d, d))"
  "event\<^sup>\<sharp> (dg_spec_of c) ev = local_transfer \<lbrakk>event_action ev\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  "combine_env\<^sup>\<sharp> (dg_spec_of c) ci = local_combine_transfer
     (\<lambda>dc de. ls_combine_env c (ls_channel c dc) (ls_channel c de) ci dc de)"
  "combine_assign\<^sup>\<sharp> (dg_spec_of c) ci = local_combine_transfer
     (\<lambda>dc de. ls_combine_assign c (ls_channel c de) ci dc de)"
  "dgs_query (dg_spec_of c) = local_query (ls_channel c)"
  by (simp_all add: dg_spec_of_def)

lemma dg_spec_step_dg_spec_of [simp]:
  "dg_spec_step (dg_spec_of c) a = local_transfer \<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub>"
  by (cases a) simp_all

lemma dg_spec_combine_transfer_dg_spec_of [simp]:
  "dg_spec_combine_transfer (dg_spec_of c) ci
     = local_combine_transfer (\<lambda>dc de. ls_combine c (ls_channel c dc) (ls_channel c de) ci dc de)"
  by (intro ext) (simp add: dg_spec_combine_transfer_local local_combine_transfer_def)

lemma dg_spec_wf_dg_spec_of [intro, simp]: "dg_spec_wf (dg_spec_of c)"
  by (auto simp: dg_spec_wf_def local_query_def local_enter_transfer_def
      local_combine_transfer_def local_transfer_def)

text \<open>
  Run as a specification, a sound component's step and return are sound
  outright: its own channel holds at every store its state describes, so the
  laws it proves against every holding channel apply to that one.
\<close>

context mcp_sem
begin

lemma closed_step_sound:
  assumes sound: "gsound_local_spec gm c"
  shows "gedge_collect a (gm d) \<subseteq> gm (\<lbrakk>a\<rbrakk>\<^sup>\<sharp>\<^bsub>c\<^esub> d)"
proof -
  have "gm d = gm d \<inter> Collect (geval_query.channel_holds ev (ls_channel c d))"
    using ls_channel_sound[OF sound] by blast
  moreover have "gedge_collect a (gm d \<inter> Collect (geval_query.channel_holds ev (ls_channel c d)))
      \<subseteq> gm (ls_step c (ls_channel c d) a d)"
    using sound unfolding gsound_local_spec_def by blast
  ultimately show ?thesis by (simp add: closed_step_def)
qed

lemma closed_combine_sound:
  assumes sound: "gsound_local_spec gm c" and "s \<in> gm dc" and "t \<in> gm de"
  shows "gcombine_collect (ci_dst ci) s t
           \<in> gm (ls_combine c (ls_channel c dc) (ls_channel c de) ci dc de)"
  using assms ls_channel_sound[OF sound assms(2)] ls_channel_sound[OF sound assms(3)]
  unfolding gsound_local_spec_def by blast

theorem dg_spec_of_contract:
  assumes sound: "gsound_local_spec gm c"
  shows "ganalysis_contract ev rv conv glob (dg_spec_of c) (\<lambda>d g. gm d)"
proof (unfold_locales, goal_cases wf mono step comb)
  case wf
  then show ?case by (rule dg_spec_wf_dg_spec_of)
next
  case mono
  then show ?case using sound unfolding gsound_local_spec_def by metis
next
  case (step a \<tau> src gk)
  then show ?case
    using closed_step_sound[OF sound] by (simp add: dg_spec_edge_program_def)
next
  case comb
  then show ?case
    by (simp add: local_combine_transfer_def closed_combine_sound[OF sound])
qed

end

section \<open>Several components as one\<close>

text \<open>
  The combination of several components is itself a component. One
  component is its own combination, so a single analysis and an \<open>MCP\<close> of one
  analysis are the same specification. Several components run their returns
  one after the other, each through both of its stages: the combination's env
  stage runs every component's composite, and its assign stage keeps the state
  it is handed. Running every env stage before every assign stage would need the
  stages of different components to commute, which independence of their
  concretizations does not give. The composite needs the caller's channel, which
  only the env stage receives.
\<close>

fun mcp_combine :: "('vr,'e,'s) glocal_spec list \<Rightarrow> ('vr,'e,'s) glocal_spec" where
  "mcp_combine [c] = c"
| "mcp_combine cs =
     make_local_spec (mcp_qry cs) (mcp_step cs) (mcp_en_from cs) (mcp_comb cs) (\<lambda>ch' ci dc de. dc)"

definition mcp_spec :: "('vr,'e,'s) glocal_spec list \<Rightarrow> ('vr,'e,'x,'k,'v,'s::bot,'G) gdg_spec" where
  "mcp_spec cs = dg_spec_of (mcp_combine cs)"

context mcp_sem
begin

theorem mcp_combine_sound:
  assumes sound: "\<forall>(\<gamma>\<^sub>i, c\<^sub>i) \<in> set comps. gsound_local_spec \<gamma>\<^sub>i c\<^sub>i"
    and indep: "mcp_independent comps" and ne: "comps \<noteq> []"
  shows "gsound_local_spec (mcp_gamma (map fst comps)) (mcp_combine (map snd comps))"
proof (cases "\<exists>x. comps = [x]")
  case True
  then obtain \<gamma>\<^sub>i c\<^sub>i where "comps = [(\<gamma>\<^sub>i, c\<^sub>i)]" by fastforce
  then show ?thesis using sound by (simp add: gsound_local_spec_def mcp_gamma_def)
next
  case False
  have comb: "mcp_combine (map snd comps) =
     make_local_spec (mcp_qry (map snd comps)) (mcp_step (map snd comps))
       (mcp_en_from (map snd comps)) (mcp_comb (map snd comps)) (\<lambda>ch' ci dc de. dc)"
    using False ne by (cases "map snd comps" rule: mcp_combine.cases) (auto simp: Cons_eq_map_conv)
  have enter: "\<exists>q \<in> set (mcp_en_from (map snd comps) ch ci p).
                 s \<in> mcp_gamma (map fst comps) (fst q)
                 \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> mcp_gamma (map fst comps) (snd q)"
    if "s \<in> mcp_gamma (map fst comps) (fst p)" "geval_query.channel_holds ev ch s" for ch s ci p
    using mcp_en_fold_sound[OF sound indep, of "[]" "[p]" s _ ch ci] that
    by (auto simp: mcp_en_from_def)
  have mono: "\<forall>x y. x \<le> y \<longrightarrow> mcp_gamma (map fst comps) x \<subseteq> mcp_gamma (map fst comps) y"
    using sound by (fastforce simp: mcp_gamma_def gsound_local_spec_def)
  have qry: "\<forall>ch s x q. s \<in> mcp_gamma (map fst comps) x \<longrightarrow> geval_query.channel_holds ev ch s
               \<longrightarrow> geval_holds ev q (mcp_qry (map snd comps) ch x q) s"
    unfolding mcp_qry_def using mcp_qry_fold_sound[OF _ _ sound] by simp
  show ?thesis
    unfolding comb gsound_local_spec_def
    using mono mcp_step_sound[OF sound indep] mcp_comb_sound[OF sound indep] enter qry
    by simp
qed

theorem mcp_contract:
  assumes "\<forall>(\<gamma>\<^sub>i, c\<^sub>i) \<in> set comps. gsound_local_spec \<gamma>\<^sub>i c\<^sub>i" and "mcp_independent comps"
    and "comps \<noteq> []"
  shows "ganalysis_contract ev rv conv glob (mcp_spec (map snd comps)) (\<lambda>d g. mcp_gamma (map fst comps) d)"
  unfolding mcp_spec_def by (rule dg_spec_of_contract[OF mcp_combine_sound[OF assms]])

end

section \<open>A component on one field of a larger state\<close>

text \<open>
  A component over its own carrier \<open>'c\<close> runs on one field of the combined
  state through a lens: every operation reads the field, and writes back only
  the field, as Goblint's \<open>inner_man\<close> hands a component its own part of the
  \<open>MCP\<close> state. The channel passes through unchanged: it describes the stores
  of the whole state, which are the stores the field describes as well.
\<close>

definition lens_of :: "('s \<Rightarrow> 'c) \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> 's) \<Rightarrow> ('vr,'e,'c) glocal_spec \<Rightarrow> ('vr,'e,'s) glocal_spec"
where
  "lens_of get put c = make_local_spec
     (\<lambda>ch x. ls_query c ch (get x))
     (\<lambda>ch a x. put x (ls_step c ch a (get x)))
     (\<lambda>ch ci p. map (\<lambda>(q, e). (put (fst p) q, put (snd p) e))
                (ls_enter c ch ci (get (fst p), get (snd p))))
     (\<lambda>ch ch' ci x de. put x (ls_combine_env c ch ch' ci (get x) (get de)))
     (\<lambda>ch' ci x de. put x (ls_combine_assign c ch' ci (get x) (get de)))"

lemma get_mc_comb_lens_of:
  assumes "\<And>x v. get (put x v) = v"
  shows
    "get (ls_combine (lens_of get put c) ch ch' ci x de) = ls_combine c ch ch' ci (get x) (get de)"
  by (simp add: lens_of_def assms)

context mcp_sem
begin

theorem lens_of_sound:
  assumes sound: "gsound_local_spec g c"
    and get_put: "\<And>x v. get (put x v) = v"
    and get_mono: "\<And>x y. x \<le> y \<Longrightarrow> get x \<le> get y"
  shows "gsound_local_spec (\<lambda>x. g (get x)) (lens_of get put c)"
proof -
  have enter: "\<exists>q \<in> set (ls_enter (lens_of get put c) ch ci p).
                 s \<in> g (get (fst q))
                 \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
                     \<in> g (get (snd q))"
    if s_in: "s \<in> g (get (fst p))" and A: "geval_query.channel_holds ev ch s" for ch s ci p
  proof -
    have "s \<in> g (fst (get (fst p), get (snd p)))" using s_in by simp
    then obtain q where "q \<in> set (ls_enter c ch ci (get (fst p), get (snd p)))" "s \<in> g (fst q)"
        "gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound A unfolding gsound_local_spec_def by metis
    then show ?thesis
      by (intro bexI[of _ "(put (fst p) (fst q), put (snd p) (snd q))"])
         (auto simp: lens_of_def get_put)
  qed
  show ?thesis
    using sound get_mono enter
    unfolding gsound_local_spec_def get_mc_comb_lens_of[of get put, OF get_put]
    by (simp add: lens_of_def get_put)
qed

end

section \<open>Replacing a component's handler\<close>

text \<open>
  The handler is the only operation that neither changes a state nor is framed,
  so any other handler that answers soundly for the same states may replace it.
  This is how an analysis written without a query handler becomes a provider
  once it runs in the combined state.
\<close>

definition with_qry :: "('e gchannel \<Rightarrow> 's \<Rightarrow> 'e gchannel) \<Rightarrow> ('vr,'e,'s) glocal_spec \<Rightarrow> ('vr,'e,'s) glocal_spec" where
  "with_qry h c = c\<lparr>ls_query := h\<rparr>"

context mcp_sem
begin

theorem with_qry_sound:
  assumes "gsound_local_spec gm c"
    and "\<And>ch s x q. s \<in> gm x \<Longrightarrow> geval_query.channel_holds ev ch s \<Longrightarrow> geval_holds ev q (h ch x q) s"
  shows "gsound_local_spec gm (with_qry h c)"
  using assms unfolding gsound_local_spec_def with_qry_def by simp

end

lemma with_qry_frame: "mcp_frame c g \<Longrightarrow> mcp_frame (with_qry h c) g"
  by (simp add: mcp_frame_def with_qry_def)

section \<open>Normalizing what a component produces\<close>

text \<open>
  A normalization \<open>k\<close> that keeps a state's concretization may be applied to
  what a component produces: each step, the entered half of each entry, and
  the return after its second stage. The caller half of an entry is the
  caller's state and stays as it is. The first stage of a return is left
  alone, because the component's soundness speaks only about the composite.
  The combined state of several analyses uses this to become unreachable as
  soon as one active analysis is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close>.
\<close>

definition map_local_spec :: "('s \<Rightarrow> 's) \<Rightarrow> ('vr,'e,'s) glocal_spec \<Rightarrow> ('vr,'e,'s) glocal_spec" where
  "map_local_spec k c = make_local_spec (ls_query c)
     (\<lambda>ch a x. k (ls_step c ch a x))
     (\<lambda>ch ci p. map (\<lambda>(q, e). (q, k e)) (ls_enter c ch ci p))
     (ls_combine_env c)
     (\<lambda>ch' ci x de. k (ls_combine_assign c ch' ci x de))"

context mcp_sem
begin

theorem map_local_spec_sound:
  assumes sound: "gsound_local_spec g c"
    and keep: "\<And>x. g (k x) = g x"
  shows "gsound_local_spec g (map_local_spec k c)"
proof -
  have enter: "\<exists>q \<in> set (ls_enter (map_local_spec k c) ch ci p).
                 s \<in> g (fst q)
                 \<and> gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
    if s_in: "s \<in> g (fst p)" and A: "geval_query.channel_holds ev ch s" for ch s ci p
  proof -
    obtain q where "q \<in> set (ls_enter c ch ci p)" "s \<in> g (fst q)"
        "gcall_enter (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s \<in> g (snd q)"
      using sound s_in A unfolding gsound_local_spec_def by metis
    then show ?thesis
      by (intro bexI[of _ "(fst q, k (snd q))"]) (auto simp: map_local_spec_def keep)
  qed
  show ?thesis
    using sound enter unfolding gsound_local_spec_def
    by (simp add: map_local_spec_def keep)
qed

end

section \<open>Components whose entry answers once\<close>

text \<open>
  An entry that answers a single alternative, paired with the caller's own
  state, is what the routed pipeline consumes. Lenses, combination and
  normalization keep that shape.
\<close>

definition single_entry :: "('vr,'e,'s) glocal_spec \<Rightarrow> bool" where
  "single_entry c \<longleftrightarrow> (\<forall>ch ci p. \<exists>e. ls_enter c ch ci p = [(fst p, e)])"

lemma single_entryD:
  "single_entry c \<Longrightarrow> ls_enter c ch ci p = [(fst p, snd (hd (ls_enter c ch ci p)))]"
  unfolding single_entry_def by (metis list.sel(1) snd_conv)

lemma single_entry_lens_of:
  assumes single: "single_entry c" and put_get: "\<And>x. put x (get x) = x"
  shows "single_entry (lens_of get put c)"
  unfolding single_entry_def
proof (intro allI)
  fix ch ci p
  obtain e where "ls_enter c ch ci (get (fst p), get (snd p)) = [(get (fst p), e)]"
    using single unfolding single_entry_def by (metis fst_conv)
  then show "\<exists>e. ls_enter (lens_of get put c) ch ci p = [(fst p, e)]"
    by (simp add: lens_of_def put_get)
qed

lemma single_entry_map_local_spec:
  assumes "single_entry c"
  shows "single_entry (map_local_spec k c)"
  unfolding single_entry_def
proof (intro allI)
  fix ch ci p
  obtain e where "ls_enter c ch ci p = [(fst p, e)]"
    using assms unfolding single_entry_def by blast
  then show "\<exists>e. ls_enter (map_local_spec k c) ch ci p = [(fst p, e)]"
    by (simp add: map_local_spec_def)
qed

lemma single_entry_with_qry: "single_entry c \<Longrightarrow> single_entry (with_qry h c)"
  by (simp add: single_entry_def with_qry_def)

lemma single_entry_mcp_en_fold:
  assumes "\<forall>c \<in> set cs. single_entry c"
  shows "\<exists>e. fold (\<lambda>c ps. concat (map (ls_enter c ch ci) ps)) cs [(d, e0)] = [(d, e)]"
  using assms
proof (induction cs arbitrary: e0)
  case (Cons c cs)
  obtain e1 where "ls_enter c ch ci (d, e0) = [(d, e1)]"
    using Cons.prems unfolding single_entry_def by (metis fst_conv list.set_intros(1))
  then show ?case using Cons.IH[of e1] Cons.prems by simp
qed simp

lemma single_entry_mcp_combine:
  assumes single: "\<forall>c \<in> set cs. single_entry c" and ne: "cs \<noteq> []"
  shows "single_entry (mcp_combine cs)"
proof (cases "\<exists>c. cs = [c]")
  case True
  then show ?thesis using single by auto
next
  case False
  then have "ls_enter (mcp_combine cs) = mcp_en_from cs"
    using ne by (cases cs rule: mcp_combine.cases) auto
  then show ?thesis
    unfolding single_entry_def mcp_en_from_def
    using single_entry_mcp_en_fold[OF single] by (metis prod.collapse)
qed

section \<open>One field of a reachability-lifted record\<close>

text \<open>
  The combined state is a record of fields under one reachability lift, whose
  \<^const>\<open>Bot\<close> is the state no analysis can reach. Each field has a bottom of
  its own: a reachability-lifted field's is \<^const>\<open>Bot\<close>, and a carrier with an
  unreachable element of its own uses that. A field's lens reads the field's
  bottom from the unreachable state, and writing any other value into it starts
  from the record whose fields are all at bottom. Writing bottom into the
  unreachable state leaves it unreachable, so writing back what was read
  changes nothing.
\<close>

definition lift_get :: "('r \<Rightarrow> 'c::bot) \<Rightarrow> 'r lifted \<Rightarrow> 'c" where
  "lift_get f x = (case x of Bot \<Rightarrow> \<bottom> | Lifted r \<Rightarrow> f r)"

definition lift_put :: "('r \<Rightarrow> 'c::bot \<Rightarrow> 'r) \<Rightarrow> 'r::bot lifted \<Rightarrow> 'c \<Rightarrow> 'r lifted" where
  "lift_put u x v =
     (case x of
        Bot \<Rightarrow> (if v = \<bottom> then Bot else Lifted (u \<bottom> v))
      | Lifted r \<Rightarrow> Lifted (u r v))"

lemma lift_get_simps [simp]:
  "lift_get f Bot = \<bottom>" "lift_get f (Lifted r) = f r"
  by (simp_all add: lift_get_def)

lemma lift_get_put:
  assumes "\<And>r v. f (u r v) = v" and "f \<bottom> = \<bottom>"
  shows "lift_get f (lift_put u x v) = v"
  using assms by (cases x) (simp_all add: lift_put_def)

lemma lift_put_get:
  assumes "\<And>r. u r (f r) = r"
  shows "lift_put u x (lift_get f x) = x"
  using assms by (cases x) (simp_all add: lift_put_def)

lemma lift_get_mono:
  fixes f :: "'r::semilattice_sup \<Rightarrow> 'c::order_bot"
  assumes "\<And>r r'. r \<le> r' \<Longrightarrow> f r \<le> f r'"
  shows "x \<le> y \<Longrightarrow> lift_get f x \<le> lift_get f y"
  using assms by (cases x; cases y) simp_all

lemma lift_get_put_other:
  assumes "\<And>r v. f2 (u1 r v) = f2 r" and "f2 \<bottom> = \<bottom>"
  shows "lift_get f2 (lift_put u1 x v) = lift_get f2 x"
  using assms by (cases x) (simp_all add: lift_put_def)

text \<open>
  Components that each own a distinct field are independent: a list of
  distinct analyses, each run on its own field, satisfies
  \<^const>\<open>mcp_independent\<close> as soon as every one leaves every other field alone.
\<close>

lemma mcp_independent_map:
  assumes "distinct as"
    and "\<And>a b. a \<in> set as \<Longrightarrow> b \<in> set as \<Longrightarrow> a \<noteq> b \<Longrightarrow> mcp_frame (c a) (g b)"
  shows "mcp_independent (map (\<lambda>a. (g a, c a)) as)"
  using assms by (induction as) auto

end
