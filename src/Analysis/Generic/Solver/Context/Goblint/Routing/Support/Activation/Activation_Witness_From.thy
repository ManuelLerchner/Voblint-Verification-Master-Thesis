theory Activation_Witness_From
  imports Seeded_Activation_Sound Seeded_Activation_Reach
begin

section \<open>From-node-tracking activation witness (repairs the recursive-return combine)\<close>

text \<open>A from-node-tracking activation witness. \<open>twf enterc combc g w wc v ctx tr\<close>
  reads: \<open>tr\<close> starts at node \<open>w\<close> in context \<open>wc\<close> (with an arbitrary store \<open>hd tr\<close>) and
  reaches node \<open>v\<close> in context \<open>ctx\<close>.  The \<open>start\<close> rule seeds ANY store at ANY node ---
  this is exactly the callee suffix the current combine cannot derive.  The combine
  names the frame entry \<open>fe\<close> and starts \<open>rho\<close> there, so the recursive callee summary is
  built directly (non-vacuous), not borrowed from a larger trace.\<close>

inductive twf ::
  "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> trace \<Rightarrow> bool"
  for enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and g :: cfg where
  start: "twf enterc combc g v ctx v ctx [s]"
| intra: "(u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter
      \<Longrightarrow> twf enterc combc g w wc u kc tr
      \<Longrightarrow> edge_step a (last tr) = Some s'
      \<Longrightarrow> twf enterc combc g w wc v kc (tr @ [s'])"
| enter: "(u, EA_Enter, v) \<in> edges g
      \<Longrightarrow> twf enterc combc g w wc u kc tau
      \<Longrightarrow> twf enterc combc g w wc v (enterc kc (last tau)) (tau @ [enter_state (last tau)])"
| combine: "(cl, ex, v) \<in> combines g \<Longrightarrow> (cl, EA_Enter, fe) \<in> edges g
      \<Longrightarrow> twf enterc combc g w wc cl kc1 tau
      \<Longrightarrow> twf enterc combc g fe (enterc kc1 (last tau)) ex (enterc kc1 (last tau)) rho
      \<Longrightarrow> hd rho = enter_state (last tau)
      \<Longrightarrow> twf enterc combc g w wc v (combc kc1 (enterc kc1 (last tau)))
            (tau @ tl rho @ [<last tau|last rho>])"

lemma twf_nonempty: "twf enterc combc g w wc v ctx tr \<Longrightarrow> tr \<noteq> []"
  by (induction rule: twf.induct) auto

text \<open>Conditional soundness: if the START store is sound at the start unknown, the LAST
  store is sound at the reached unknown.  The combine's \<open>rho\<close> starts at the frame entry
  with \<open>enter_state (last tau)\<close>, whose soundness comes from \<open>SEED_G\<close> applied to the
  caller's (sound) call-node store --- no independent seeding from \<open>S\<close> needed.\<close>
theorem twf_sound:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a::sound_domain abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c"
  assumes EDGE: "\<And>u a v c s s'. (u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk> \<Longrightarrow> edge_step a s = Some s'
        \<Longrightarrow> s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    and SEED_G: "\<And>u v c s. (u, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>
        \<Longrightarrow> enter_state s \<in> \<lbrakk>sg (Inl (v, enterc c s))\<rbrakk>"
    and COMB: "\<And>cl ex v c1 s t. (cl, ex, v) \<in> combines g
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk> \<Longrightarrow> t \<in> \<lbrakk>sg (Inl (ex, enterc c1 s))\<rbrakk>
        \<Longrightarrow> <s|t> \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 s)))\<rbrakk>"
    and wit: "twf enterc combc g w wc v ctx tr"
    and start: "hd tr \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk>"
  shows "last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  using wit start
proof (induction rule: twf.induct)
  case (start v ctx s) thus ?case by simp
next
  case (intra u a v w wc c tr s')
  have "last tr \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>"
    using intra.IH intra.prems twf_nonempty[OF intra.hyps(3)] by simp
  hence "s' \<in> \<lbrakk>sg (Inl (v, c))\<rbrakk>"
    by (rule EDGE[OF intra.hyps(1,2) _ intra.hyps(4)])
  thus ?case using twf_nonempty[OF intra.hyps(3)] by simp
next
  case (enter u v w wc c tau)
  have "last tau \<in> \<lbrakk>sg (Inl (u, c))\<rbrakk>"
    using enter.IH enter.prems twf_nonempty[OF enter.hyps(2)] by simp
  hence "enter_state (last tau) \<in> \<lbrakk>sg (Inl (v, enterc c (last tau)))\<rbrakk>"
    by (rule SEED_G[OF enter.hyps(1)])
  thus ?case using twf_nonempty[OF enter.hyps(2)] by simp
next
  case (combine cl ex v fe w wc c1 tau rho)
  have tau_ne: "tau \<noteq> []" by (rule twf_nonempty[OF combine.hyps(3)])
  have caller: "last tau \<in> \<lbrakk>sg (Inl (cl, c1))\<rbrakk>"
    using combine.IH(1) combine.prems tau_ne by simp
  have entry_sound: "enter_state (last tau) \<in> \<lbrakk>sg (Inl (fe, enterc c1 (last tau)))\<rbrakk>"
    by (rule SEED_G[OF combine.hyps(2) caller])
  have callee: "last rho \<in> \<lbrakk>sg (Inl (ex, enterc c1 (last tau)))\<rbrakk>"
    using combine.IH(2) entry_sound combine.hyps(5) by simp
  have "<last tau|last rho> \<in> \<lbrakk>sg (Inl (v, combc c1 (enterc c1 (last tau))))\<rbrakk>"
    by (rule COMB[OF combine.hyps(1) caller callee])
  thus ?case by (metis last_appendR snoc_eq_iff_butlast)
qed

subsection \<open>Suffix reuse\<close>

text \<open>The callee side of a combine can be supplied by a suffix witness that starts at the
  frame entry.  The start store is the caller-derived entry store, so the proof does not need
  a separate global seed for the callee activation.\<close>


lemma twf_combine_reuses_callee_suffix:
  assumes cmb: "(cl, ex, v) \<in> combines g"
    and en: "(cl, EA_Enter, fe) \<in> edges g"
    and caller: "twf enterc combc g w wc cl kc tau"
    and callee: "twf enterc combc g fe (enterc kc (last tau)) ex (enterc kc (last tau)) rho"
    and hd: "hd rho = enter_state (last tau)"
  shows "twf enterc combc g w wc v (combc kc (enterc kc (last tau)))
           (tau @ tl rho @ [<last tau|last rho>])"
  by (rule twf.combine[OF cmb en caller callee hd])


section \<open>The returning fragment and query-anchored seeded soundness\<close>

text \<open>\<open>twfr\<close> is \<open>twf\<close> without the \<open>enter\<close> (inlining) rule: \<open>start\<close> / \<open>intra\<close> / \<open>combine\<close>
  only.  Every terminating run --- and in particular every recursive-return path --- is a
  \<open>twfr\<close>: each callee frame is opened by \<open>start\<close> at its frame entry, traced by \<open>intra\<close>, and
  spliced back by \<open>combine\<close>; the \<open>enter\<close> rule is only for reaching a callee interior
  mid-execution (partial / non-terminating), whose caller-frame membership is not implied
  by dependency closure.  On \<open>twfr\<close> the query's backward cone matches the solver's
  dependency graph, so \<open>cov_edge\<close> / \<open>cov_frame\<close> are \<^emph>\<open>derived\<close> from \<open>(query) \<in> vars\<close>.\<close>

inductive twfr ::
  "('c \<Rightarrow> store \<Rightarrow> 'c) \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> 'c) \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'c \<Rightarrow> trace \<Rightarrow> bool"
  for enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and combc :: "'c \<Rightarrow> 'c \<Rightarrow> 'c" and g :: cfg where
  start: "twfr enterc combc g v ctx v ctx [s]"
| intra: "(u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter
      \<Longrightarrow> twfr enterc combc g w wc u kc tr
      \<Longrightarrow> edge_step a (last tr) = Some s'
      \<Longrightarrow> twfr enterc combc g w wc v kc (tr @ [s'])"
| combine: "(cl, ex, v) \<in> combines g \<Longrightarrow> (cl, EA_Enter, fe) \<in> edges g
      \<Longrightarrow> twfr enterc combc g w wc cl kc1 tau
      \<Longrightarrow> twfr enterc combc g fe (enterc kc1 (last tau)) ex (enterc kc1 (last tau)) rho
      \<Longrightarrow> hd rho = enter_state (last tau)
      \<Longrightarrow> twfr enterc combc g w wc v (combc kc1 (enterc kc1 (last tau)))
            (tau @ tl rho @ [<last tau|last rho>])"

lemma twfr_nonempty: "twfr enterc combc g w wc v ctx tr \<Longrightarrow> tr \<noteq> []"
  by (induction rule: twfr.induct) auto

text \<open>
  \<^bold>\<open>Query-anchored seeded soundness (tasks 1--4).\<close>  The four \<open>q_*\<close> premises are the
  \<^emph>\<open>backward\<close> dependency-reachability contract: a solved unknown's intra predecessor
  (\<open>q_edge\<close>), its caller call node and routed callee exit (\<open>q_caller\<close> / \<open>q_callee\<close>), and the
  callee frame entry reached through the body (\<open>q_frame\<close>) are all solved.  These are exactly
  \<^theory>\<open>Voblint_Analysis.Seeded_Activation_Reach\<close>'s \<open>intra_pred_in_vars\<close> /
  \<open>combine_dep_in_vars\<close> / \<open>combine_reaches_frame_in_vars\<close>, which \<^const>\<open>part_post_solution\<close>'s
  dependency closure discharges from \<open>(query) \<in> vars\<close> --- no forward-closure invariant.
  With them, \<open>cov_edge\<close> / \<open>cov_frame\<close> are \<^emph>\<open>derived\<close> along the witness rather than assumed:
  the induction threads \<open>(node, ctx) \<in> vars\<close> backward from the query and discharges each
  \<open>EDGE\<close> / \<open>SEED_G\<close> / \<open>COMB\<close> off the covering-seed post-solution.  The return uses the caller
  projection \<open>combc = (\<lambda>c1 c2. c1)\<close>.
\<close>

context sound_transfer
begin

theorem twfr_sound_seeded:
  fixes sg :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and enterc :: "'c \<Rightarrow> store \<Rightarrow> 'c" and pz :: 'a and fs :: "'c \<Rightarrow> 'a abs_state"
  assumes fin: "finite (edges g)"
    and pp: "part_post_solution
               (side_cfg_T_eff_cmp_seed gkey cmb (cover_seed pz fs) g
                  (clean_etf_of_transfer tf) bot0 s0) x sg vars"
    and q_edge: "\<And>u a v kc. (u, a, v) \<in> edges g \<Longrightarrow> a \<noteq> EA_Enter
        \<Longrightarrow> (v, kc) \<in> vars \<Longrightarrow> (u, kc) \<in> vars"
    and q_caller: "\<And>cl ex v kc. (cl, ex, v) \<in> combines g \<Longrightarrow> (v, kc) \<in> vars \<Longrightarrow> (cl, kc) \<in> vars"
    and q_callee: "\<And>cl ex v kc s. (cl, ex, v) \<in> combines g \<Longrightarrow> (v, kc) \<in> vars
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, kc))\<rbrakk> \<Longrightarrow> (ex, enterc kc s) \<in> vars"
    and q_frame: "\<And>cl ex fe v kc s. (cl, ex, v) \<in> combines g \<Longrightarrow> (cl, EA_Enter, fe) \<in> edges g
        \<Longrightarrow> (v, kc) \<in> vars \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, kc))\<rbrakk> \<Longrightarrow> (fe, enterc kc s) \<in> vars"
    and SEED_glob: "\<And>u v kc s xx. (u, EA_Enter, v) \<in> edges g \<Longrightarrow> (u, kc) \<in> vars
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>
        \<Longrightarrow> is_global xx \<Longrightarrow> s xx \<in> gamma (fs (enterc kc s) xx)"
    and zero: "(0::int) \<in> gamma pz"
    and COMB_BOUND: "\<And>cl ex v kc s. (cl, ex, v) \<in> combines g \<Longrightarrow> (v, kc) \<in> vars
        \<Longrightarrow> s \<in> \<lbrakk>sg (Inl (cl, kc))\<rbrakk>
        \<Longrightarrow> \<langle>sg (Inl (cl, kc))|sg (Inl (ex, enterc kc s))\<rangle> \<le> sg (Inl (v, kc))"
    and wit: "twfr enterc (\<lambda>c1 c2. c1) g w wc v ctx tr"
  shows "(v, ctx) \<in> vars \<Longrightarrow> hd tr \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk> \<Longrightarrow> last tr \<in> \<lbrakk>sg (Inl (v, ctx))\<rbrakk>"
  using wit
proof (induction rule: twfr.induct)
  case (start v ctx s)
  thus ?case by simp
next
  case (intra u a v w wc kc tr s')
  have tr_ne: "tr \<noteq> []" by (rule twfr_nonempty[OF intra.hyps(3)])
  have qu: "(u, kc) \<in> vars" by (rule q_edge[OF intra.hyps(1,2) intra.prems(1)])
  have hd_tr: "hd tr \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk>" using intra.prems(2) tr_ne by simp
  have last_tr: "last tr \<in> \<lbrakk>sg (Inl (u, kc))\<rbrakk>" by (rule intra.IH[OF qu hd_tr])
  show ?case
    using seeded_activation_edge[OF fin pp intra.prems(1) intra.hyps(1) intra.hyps(2)
            last_tr intra.hyps(4)] by simp
next
  case (combine cl ex v fe w wc kc1 tau rho)
  have q: "(v, kc1) \<in> vars" using combine.prems(1) by simp
  have tau_ne: "tau \<noteq> []" by (rule twfr_nonempty[OF combine.hyps(3)])
  have hd_tau: "hd tau \<in> \<lbrakk>sg (Inl (w, wc))\<rbrakk>" using combine.prems(2) tau_ne by simp
  have qc: "(cl, kc1) \<in> vars" by (rule q_caller[OF combine.hyps(1) q])
  have caller: "last tau \<in> \<lbrakk>sg (Inl (cl, kc1))\<rbrakk>"
    by (rule combine.IH(1)[OF qc hd_tau])
  have qf: "(fe, enterc kc1 (last tau)) \<in> vars"
    by (rule q_frame[OF combine.hyps(1,2) q caller])
  have seedg: "enter_state (last tau) \<in> \<lbrakk>cover_seed pz fs (enterc kc1 (last tau))\<rbrakk>"
    by (rule enter_state_in_cover_seed[where fs = fs and kc = "enterc kc1 (last tau)"
          and pz = pz and s = "last tau", OF SEED_glob[OF combine.hyps(2) qc caller] zero])
  have entry: "enter_state (last tau) \<in> \<lbrakk>sg (Inl (fe, enterc kc1 (last tau)))\<rbrakk>"
    by (rule seeded_activation_seed[where enterc = enterc and kc = kc1 and s = "last tau"
          and frame_seed = "cover_seed pz fs", OF pp fin qf combine.hyps(2) seedg])
  have qe: "(ex, enterc kc1 (last tau)) \<in> vars"
    by (rule q_callee[OF combine.hyps(1) q caller])
  have hd_rho: "hd rho \<in> \<lbrakk>sg (Inl (fe, enterc kc1 (last tau)))\<rbrakk>"
    using entry combine.hyps(5) by simp
  have callee: "last rho \<in> \<lbrakk>sg (Inl (ex, enterc kc1 (last tau)))\<rbrakk>"
    by (rule combine.IH(2)[OF qe hd_rho])
  have bnd: "\<langle>sg (Inl (cl, kc1))|sg (Inl (ex, enterc kc1 (last tau)))\<rangle> \<le> sg (Inl (v, kc1))"
    by (rule COMB_BOUND[OF combine.hyps(1) q caller])
  have "<last tau|last rho> \<in> \<lbrakk>sg (Inl (v, kc1))\<rbrakk>"
    using seeded_activation_comb[where enterc = enterc and combc = "\<lambda>c1 c2. c1", OF bnd caller callee]
    by simp
  thus ?case by (simp add: combine_states_def)
qed

end

end
