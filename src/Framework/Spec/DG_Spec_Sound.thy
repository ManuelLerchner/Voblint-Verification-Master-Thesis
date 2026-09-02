theory DG_Spec_Sound
  imports DG_Spec
begin

section \<open>What a manager-native specification owes a concretization\<close>

text \<open>
  Soundness of a manager-native \<open>dg_spec\<close> is stated against the compiled
  trees' own observations: an assumption's input is what the tree reads
  (\<open>\<tau>\<close> at the source and the routed slot), its output is the returned local
  value together with the contribution the tree actually publishes at that
  slot. There is no reconstructed \<open>'dg \<times> 'dl\<close> pair anywhere: a transfer
  that publishes nothing is judged against \<open>bot\<close>, and a concretization
  that ignores its global argument (every Base-style domain) discharges
  that side vacuously. \<open>sound_local_dg_spec\<close> below is exactly that
  collapse: for a specification built from pure local functions, all
  global obligations vanish and the locale's assumptions are the plain
  pure-transfer inclusions an existing domain already proves.
\<close>

text \<open>
  This locale is stated for a \<^emph>\<open>single\<close> global: \<open>gammaDG\<close> takes one \<open>'G\<close>, read at
  the one slot \<open>Inr gk\<close>, so a specification publishing at two distinct global
  names would have contributions this concretization never sees. The global-name
  type is therefore pinned at \<^typ>\<open>unit\<close> here and the manager is built from the
  constant embedding, rather than stating an obligation over a namespace the
  conclusion cannot account for. Every analysis in this tree has one global, so
  nothing is lost today; a second global needs \<open>gammaDG\<close> over a global
  \<^emph>\<open>environment\<close> first, and that is what would generalize this locale.
\<close>

locale sound_dg_spec =
  fixes S :: "('x,'k,unit,'D::bounded_semilattice_sup_bot,
                'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaDG_mono:
      "\<lbrakk>d \<le> d'; g \<le> g'\<rbrakk> \<Longrightarrow> gammaDG d g \<subseteq> gammaDG d' g'"
    and step_sound:
      "edge_collect a (gammaDG (locals (\<tau> src)) (globs (\<tau> (Inr gk))))
         \<subseteq> gammaDG (locals (traverse_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau>))
                   (globs (sides_of_rhs (dg_spec_edge_tree S a src (\<lambda>_. gk)) \<tau> (Inr gk)))"
    and enter_sound:
      "s \<in> gammaDG (locals (\<tau> src)) (globs (\<tau> (Inr gk))) \<Longrightarrow>
         call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
           \<in> gammaDG (locals (traverse_rhs (transfer_tree (dgs_enter S ci) src (\<lambda>_. gk)) \<tau>))
                     (globs (sides_of_rhs (transfer_tree (dgs_enter S ci) src (\<lambda>_. gk))
                                           \<tau> (Inr gk)))"
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)));
        t \<in> gammaDG (locals (\<tau> src_ex)) (globs (\<tau> (Inr gk)))\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t
          \<in> gammaDG (locals (traverse_rhs
                (dg_spec_combine_tree S ci src_cc src_ex (\<lambda>_. gk)) \<tau>))
                    (globs (sides_of_rhs (dg_spec_combine_tree S ci src_cc src_ex (\<lambda>_. gk))
                                          \<tau> (Inr gk)))"

section \<open>The collapsed obligations of a local-only specification\<close>

locale sound_local_dg_spec =
  fixes sk :: "'D::bounded_semilattice_sup_bot \<Rightarrow> 'D"
    and asn :: "vname \<Rightarrow> exp \<Rightarrow> 'D \<Rightarrow> 'D"
    and sp :: "special_call \<Rightarrow> vname \<Rightarrow> 'D \<Rightarrow> 'D"
    and br :: "exp \<Rightarrow> bool \<Rightarrow> 'D \<Rightarrow> 'D"
    and bd :: "pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and rt :: "exp option \<Rightarrow> pname \<Rightarrow> 'D \<Rightarrow> 'D"
    and en :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D"
    and ev :: "analysis_event \<Rightarrow> 'D \<Rightarrow> 'D"
    and cc :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D"
    and ce :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and ca :: "call_info \<Rightarrow> 'D \<Rightarrow> 'D \<Rightarrow> 'D"
    and gammaD :: "'D \<Rightarrow> store set"
    and gs :: "vname \<Rightarrow> bool"
  assumes gammaD_mono: "d \<le> d' \<Longrightarrow> gammaD d \<subseteq> gammaD d'"
    and step_sound_local:
      "edge_collect a (gammaD d) \<subseteq> gammaD (local_spec_step sk asn sp br rt ev a d)"
    and enter_sound_local:
      "s \<in> gammaD d \<Longrightarrow>
         call_enter gs (CallEdge (ci_dst ci) (ci_formals ci) (ci_args ci)) s
           \<in> gammaD (en ci d)"
    and combine_sound_local:
      "\<lbrakk>s \<in> gammaD dc; t \<in> gammaD de\<rbrakk> \<Longrightarrow>
        combine_collect gs (ci_dst ci) s t \<in> gammaD (ca ci (ce ci (cc ci dc) de) de)"
begin

theorem local_spec_sound:
  "sound_dg_spec (local_dg_spec sk asn sp br bd rt en ev cc ce ca) (\<lambda>d g. gammaD d) gs"
proof (unfold_locales, goal_cases)
  case 1
  then show ?case by (meson gammaD_mono)
next
  case 2
  then show ?case
    by (simp add: dg_spec_edge_tree_def dg_spec_step_local_dg_spec step_sound_local)
next
  case 3
  then show ?case by (simp add: enter_sound_local)
next
  case 4
  then show ?case
    by (simp add: dg_spec_combine_tree_def dg_spec_combine_transfer_local_dg_spec
        traverse_local_combine_tree combine_sound_local)
qed

end

end

