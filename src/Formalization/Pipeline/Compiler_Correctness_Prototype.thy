theory Compiler_Correctness_Prototype
  imports
    "Voblint_Analysis.Analysis_Sound"
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_CFG.CFG_Collect_Runs"
    "Voblint_CFG.CFG_Collect_Trace"
    "Voblint_IMP2.IMP2_Bridge"
begin

section \<open>Source-to-analysis compiler-correctness prototype\<close>

text \<open>
  This theory fixes the interfaces of the source-to-analysis proof before the
  compiler simulation is implemented. The graph and solver layers are stated
  independently of the matching-state relation used by the compiler proof.
\<close>

subsection \<open>Compiler input\<close>

definition wf_compile_input :: "proc_table \<Rightarrow> pname list \<Rightarrow> IMP2_Proc.com \<Rightarrow> bool" where
  "wf_compile_input \<Pi> ps main \<longleftrightarrow>
     distinct ps \<and>
     set ps = {p. \<Pi> p \<noteq> None} \<and>
     source_pi \<Pi> \<and>
     source_com main"

subsection \<open>Two-pass compiler invariants\<close>

definition layout_domain_exact ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> proc_layout \<Rightarrow> bool"
where
  "layout_domain_exact \<Pi> ps lay \<longleftrightarrow>
     (\<forall>p. (\<exists>info. lay p = Some info) \<longleftrightarrow>
       p \<in> set ps \<and> \<Pi> p \<noteq> None)"

definition compile_endpoints ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> IMP2_Proc.com \<Rightarrow> nat
    \<Rightarrow> nat \<times> pp \<times> pp"
where
  "compile_endpoints \<Pi> lay cmd n =
    (case compile \<Pi> lay cmd n of
      (n', en, ex, E, C) \<Rightarrow> (n', en, ex))"

fun compile_endpoint_shape ::
  "proc_layout \<Rightarrow> IMP2_Proc.com \<Rightarrow> nat
    \<Rightarrow> nat \<times> pp \<times> pp"
where
  "compile_endpoint_shape lay IMP2_Proc.com.SKIP n = (n + 2, n, n + 1)"
| "compile_endpoint_shape lay (IMP2_Proc.com.Assign x a) n = (n + 2, n, n + 1)"
| "compile_endpoint_shape lay (IMP2_Proc.com.Seq c1 c2) n =
    (let (n1, en1, ex1) = compile_endpoint_shape lay c1 n;
         (n2, en2, ex2) = compile_endpoint_shape lay c2 n1
     in (n2, en1, ex2))"
| "compile_endpoint_shape lay (IMP2_Proc.com.If b c1 c2) n =
    (let (n1, en1, ex1) = compile_endpoint_shape lay c1 (n + 1);
         (n2, en2, ex2) = compile_endpoint_shape lay c2 n1
     in (n2 + 1, n, n2))"
| "compile_endpoint_shape lay (IMP2_Proc.com.While b body) n =
    (let (n1, en1, ex1) = compile_endpoint_shape lay body (n + 1)
     in (n1 + 1, n, n1))"
| "compile_endpoint_shape lay (IMP2_Proc.com.Scope body) n =
    (let (n1, en1, ex1) = compile_endpoint_shape lay body (n + 1)
     in (n1 + 1, n, n1))"
| "compile_endpoint_shape lay (IMP2_Proc.com.Call p) n =
    (case lay p of None \<Rightarrow> (n + 2, n, n)
     | Some info \<Rightarrow> (n + 2, n, n + 1))"
| "compile_endpoint_shape lay IMP2_Proc.com.Restore n = (n, n, n)"

lemma compile_endpoints_eq_shape:
  "compile_endpoints \<Pi> lay cmd n = compile_endpoint_shape lay cmd n"
  by (induction cmd arbitrary: n;
      fastforce simp: compile_endpoints_def split: prod.splits option.splits)

lemma compile_endpoints_domain_eq:
  assumes same_domain:
    "\<And>p. (\<exists>info. lay1 p = Some info) \<longleftrightarrow>
          (\<exists>info. lay2 p = Some info)"
  shows "compile_endpoints \<Pi> lay1 cmd n =
    compile_endpoints \<Pi> lay2 cmd n"
proof -
  have shape:
      "compile_endpoint_shape lay1 cmd n =
       compile_endpoint_shape lay2 cmd n"
  proof (induction cmd arbitrary: n)
    case SKIP
    then show ?case by simp
  next
    case (Assign x a)
    then show ?case by simp
  next
    case (Seq c1 c2)
    then show ?case by simp
  next
    case (If b c1 c2)
    then show ?case by simp
  next
    case (While b body)
    then show ?case by simp
  next
    case (Scope body)
    then show ?case by simp
  next
    case (Call p)
    have domain:
        "(\<exists>info. lay1 p = Some info) =
         (\<exists>info. lay2 p = Some info)"
      by (rule same_domain)
    show ?case
      using domain
      by (cases "lay1 p"; cases "lay2 p") auto
  next
    case Restore
    then show ?case by simp
  qed
  show ?thesis
    using shape compile_endpoints_eq_shape by metis
qed

lemma compile_endpoints_definedness:
  fixes cmd :: IMP2_Proc.com
  assumes same_domain:
    "\<And>p. (\<exists>info. lay1 p = Some info) \<longleftrightarrow>
          (\<exists>info. lay2 p = Some info)"
      and first:
    "compile \<Pi> lay1 cmd n = (n1, en1, ex1, E1, C1)"
      and second:
    "compile \<Pi> lay2 cmd n = (n2, en2, ex2, E2, C2)"
  shows "n1 = n2 \<and> en1 = en2 \<and> ex1 = ex2"
proof -
  have eq: "compile_endpoints \<Pi> lay1 cmd n =
      compile_endpoints \<Pi> lay2 cmd n"
    by (rule compile_endpoints_domain_eq[OF same_domain])
  show ?thesis
    using eq first second unfolding compile_endpoints_def by simp
qed

lemma compile_procs_layout_domain:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>p \<in> set ps. lay p = None"
      and defined: "\<forall>p \<in> set ps. \<Pi> p \<noteq> None"
      and result: "compile_procs_layout \<Pi> ps lay n = (n', lay')"
  shows "(\<exists>info. lay' q = Some info) \<longleftrightarrow>
    (\<exists>info. lay q = Some info) \<or> q \<in> set ps"
using distinct fresh defined result
proof (induction ps arbitrary: lay n n' lay')
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain body where body: "\<Pi> a = Some body"
    using Cons.prems(3) by auto
  obtain n1 en ex E C where comp:
      "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) body n =
        (n1, en, ex, E, C)"
    by (cases "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) body n") auto
  have rec:
      "compile_procs_layout \<Pi> ps
        (lay(a := Some (en, ex, {n..<n1}, {}, {}))) n1 =
        (n', lay')"
    using Cons.prems(4) body comp Cons.prems(2) by simp
  have fresh_tail:
      "\<forall>p \<in> set ps.
        (lay(a := Some (en, ex, {n..<n1}, {}, {}))) p = None"
    using Cons.prems(1,2) by auto
  have defined_tail: "\<forall>p \<in> set ps. \<Pi> p \<noteq> None"
    using Cons.prems(3) by auto
  have tail:
      "(\<exists>info. lay' q = Some info) \<longleftrightarrow>
       (\<exists>info. (lay(a := Some (en, ex, {n..<n1}, {}, {}))) q =
          Some info) \<or> q \<in> set ps"
    by (rule Cons.IH[OF _ fresh_tail defined_tail rec])
       (use Cons.prems(1) in auto)
  show ?case
    using tail Cons.prems(2) by auto
qed

lemma compile_procs_layout_domain_exact:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, lay)"
  shows "layout_domain_exact \<Pi> ps lay"
  using wf layout
    compile_procs_layout_domain[of ps "\<lambda>_. None" \<Pi> 0 n lay]
  by (auto simp: wf_compile_input_def layout_domain_exact_def)

lemma compile_procs_layout_preserves:
  assumes result: "compile_procs_layout \<Pi> ps lay n = (n', lay')"
      and present: "lay p = Some info"
  shows "lay' p = Some info"
  using result present
proof (induction ps arbitrary: lay n n' lay')
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "\<Pi> a")
    case None
    have rec: "compile_procs_layout \<Pi> ps lay n = (n', lay')"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some cmd)
    note proc = Some
    obtain k en ex E C where comp:
        "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) cmd n =
          (k, en, ex, E, C)"
      by (cases "compile \<Pi> (known_proc_layout \<Pi> (a # ps) lay) cmd n")
         auto
    show ?thesis
    proof (cases "lay a")
      case None
      note absent = None
      have rec:
          "compile_procs_layout \<Pi> ps
            (lay(a := Some (en, ex, {n..<k}, {}, {}))) k =
            (n', lay')"
        using Cons.prems(1) proc comp absent by simp
      have neq: "p \<noteq> a"
        using Cons.prems(2) absent by auto
      have updated:
          "(lay(a := Some (en, ex, {n..<k}, {}, {}))) p = Some info"
        using Cons.prems(2) neq by simp
      show ?thesis
        by (rule Cons.IH[OF rec updated])
    next
      case (Some current)
      note present_a = Some
      have rec: "compile_procs_layout \<Pi> ps lay k = (n', lay')"
        using Cons.prems(1) proc comp present_a by simp
      show ?thesis
        by (rule Cons.IH[OF rec Cons.prems(2)])
    qed
  qed
qed

lemma compile_procs_bodies_preserves:
  assumes result:
    "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
      and present: "lay p = Some info"
  shows "lay' p = Some info"
  using result present
proof (induction ps arbitrary: lay n n' lay' E C)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "\<Pi> a")
    case None
    have rec:
        "compile_procs_bodies \<Pi> ps base_lay lay n = (n', lay', E, C)"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some cmd)
    note proc = Some
    obtain k en ex Ea Ca where comp:
        "compile \<Pi> base_lay cmd n = (k, en, ex, Ea, Ca)"
      by (cases "compile \<Pi> base_lay cmd n") auto
    show ?thesis
    proof (cases "lay a")
      case None
      note absent = None
      obtain Erest Crest where rec:
          "compile_procs_bodies \<Pi> ps base_lay
            (lay(a := Some (en, ex, {n..<k}, Ea, Ca))) k =
            (n', lay', Erest, Crest)"
        using Cons.prems(1) proc comp absent
        by (auto split: prod.splits)
      have neq: "p \<noteq> a"
        using Cons.prems(2) absent by auto
      have updated:
          "(lay(a := Some (en, ex, {n..<k}, Ea, Ca))) p = Some info"
        using Cons.prems(2) neq by simp
      show ?thesis
        by (rule Cons.IH[OF rec updated])
    next
      case (Some current)
      note present_a = Some
      obtain Erest Crest where rec:
          "compile_procs_bodies \<Pi> ps base_lay lay k =
            (n', lay', Erest, Crest)"
        using Cons.prems(1) proc comp present_a
        by (auto split: prod.splits)
      show ?thesis
        by (rule Cons.IH[OF rec Cons.prems(2)])
    qed
  qed
qed

lemma compile_procs_pass_endpoint_agreement_general:
  assumes distinct: "distinct ps"
      and fresh_layout: "\<forall>q \<in> set ps. in_lay q = None"
      and fresh_bodies: "\<forall>q \<in> set ps. in_full q = None"
      and defined: "\<forall>q \<in> set ps. \<Pi> q \<noteq> None"
      and layout:
        "compile_procs_layout \<Pi> ps in_lay start = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay in_full start =
          (n', full_lay, E, C)"
      and member: "p \<in> set ps"
      and base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
  shows "\<exists>Ns' Ep Cp.
    full_lay p = Some (en, ex, Ns', Ep, Cp)"
  using distinct fresh_layout fresh_bodies defined layout bodies member base
proof (induction ps arbitrary: in_lay in_full start n base_lay
    n' full_lay E C p en ex Ns)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain cmd where cmd: "\<Pi> a = Some cmd"
    using Cons.prems(4) by auto
  obtain k en1 ex1 E1 C1 where first:
      "compile \<Pi> (known_proc_layout \<Pi> (a # ps) in_lay) cmd start =
        (k, en1, ex1, E1, C1)"
    by (cases "compile \<Pi> (known_proc_layout \<Pi> (a # ps) in_lay) cmd start")
       auto
  define next_lay where
    "next_lay = in_lay(a := Some (en1, ex1, {start..<k}, {}, {}))"
  have layout_tail:
      "compile_procs_layout \<Pi> ps next_lay k = (n, base_lay)"
    using Cons.prems(5) cmd first Cons.prems(2)
    by (simp add: next_lay_def)

  obtain k' en2 ex2 E2 C2 where second:
      "compile \<Pi> base_lay cmd start = (k', en2, ex2, E2, C2)"
    by (cases "compile \<Pi> base_lay cmd start") auto
  define next_full where
    "next_full =
      in_full(a := Some (en2, ex2, {start..<k'}, E2, C2))"
  obtain Erest Crest where bodies_tail:
      "compile_procs_bodies \<Pi> ps base_lay next_full k' =
        (n', full_lay, Erest, Crest)"
    using Cons.prems(6) cmd second Cons.prems(3)
    by (auto simp: next_full_def split: prod.splits)

  have base_domain:
      "(\<exists>info. base_lay q = Some info) \<longleftrightarrow>
       (\<exists>info. in_lay q = Some info) \<or> q \<in> set (a # ps)"
    for q
    by (rule compile_procs_layout_domain[OF Cons.prems(1)
          Cons.prems(2) Cons.prems(4) Cons.prems(5)])
  have same_domain:
      "\<And>q. (\<exists>info. known_proc_layout \<Pi> (a # ps) in_lay q = Some info) \<longleftrightarrow>
            (\<exists>info. base_lay q = Some info)"
    using base_domain Cons.prems(4)
    by (auto simp: known_proc_layout_def split: option.splits)
  have endpoints: "k = k' \<and> en1 = en2 \<and> ex1 = ex2"
    by (rule compile_endpoints_definedness[OF same_domain first second])

  show ?case
  proof (cases "p = a")
    case True
    have base_head:
        "base_lay a = Some (en1, ex1, {start..<k}, {}, {})"
      by (rule compile_procs_layout_preserves[OF layout_tail])
         (simp add: next_lay_def)
    have endpoint_values: "en = en1 \<and> ex = ex1"
      using Cons.prems(8) base_head True by simp
    have full_head:
        "full_lay a = Some (en2, ex2, {start..<k'}, E2, C2)"
      by (rule compile_procs_bodies_preserves[OF bodies_tail])
         (simp add: next_full_def)
    show ?thesis
      using endpoints endpoint_values full_head True by auto
  next
    case False
    have fresh_layout_tail: "\<forall>q \<in> set ps. next_lay q = None"
      using Cons.prems(1,2) by (auto simp: next_lay_def)
    have fresh_bodies_tail: "\<forall>q \<in> set ps. next_full q = None"
      using Cons.prems(1,3) by (auto simp: next_full_def)
    have bodies_tail_aligned:
        "compile_procs_bodies \<Pi> ps base_lay next_full k =
          (n', full_lay, Erest, Crest)"
      using bodies_tail endpoints by simp
    show ?thesis
      by (rule Cons.IH[OF _ fresh_layout_tail fresh_bodies_tail _
            layout_tail bodies_tail_aligned])
         (use Cons.prems False in auto)
  qed
qed

lemma compile_procs_pass_endpoint_agreement:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
      and member: "p \<in> set ps"
      and body: "\<Pi> p = Some cmd"
      and base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
  shows "\<exists>Ns' Ep Cp.
    full_lay p = Some (en, ex, Ns', Ep, Cp)"
  proof (rule compile_procs_pass_endpoint_agreement_general[
      OF _ _ _ _ layout bodies member base])
    show "distinct ps"
      using wf by (auto simp: wf_compile_input_def)
    show "\<forall>q\<in>set ps. (\<lambda>_. None) q = None" by simp
    show "\<forall>q\<in>set ps. (\<lambda>_. None) q = None" by simp
    show "\<forall>q\<in>set ps. \<Pi> q \<noteq> None"
      using wf by (auto simp: wf_compile_input_def)
  qed

lemma compile_procs_bodies_fragment:
  assumes bodies:
    "compile_procs_bodies \<Pi> ps base_lay in_lay n =
      (n', out_lay, E, C)"
      and fragment:
    "out_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "in_lay p = Some (en, ex, Ns, Ep, Cp) \<or>
    (Ep \<subseteq> E \<and> Cp \<subseteq> C)"
using bodies fragment
proof (induction ps arbitrary: in_lay n n' out_lay E C)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "\<Pi> a")
    case None
    have rec:
        "compile_procs_bodies \<Pi> ps base_lay in_lay n =
          (n', out_lay, E, C)"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some body)
    note proc = Some
    obtain n1 en1 ex1 E1 C1 where comp:
        "compile \<Pi> base_lay body n = (n1, en1, ex1, E1, C1)"
      by (cases "compile \<Pi> base_lay body n") auto
    show ?thesis
    proof (cases "in_lay a")
      case None
      obtain n2 lay2 E2 C2 where rec:
          "compile_procs_bodies \<Pi> ps base_lay
            (in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) n1 =
            (n2, lay2, E2, C2)"
        by (cases "compile_procs_bodies \<Pi> ps base_lay
          (in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) n1") auto
      have final:
          "n' = n2 \<and> out_lay = lay2 \<and> E = E1 \<union> E2 \<and> C = C1 \<union> C2"
        using Cons.prems(1) proc comp None rec by simp
      have tail:
          "(in_lay(a := Some (en1, ex1, {n..<n1}, E1, C1))) p =
             Some (en, ex, Ns, Ep, Cp) \<or>
           Ep \<subseteq> E2 \<and> Cp \<subseteq> C2"
        by (rule Cons.IH[OF rec])
           (use Cons.prems(2) final in auto)
      show ?thesis
        using tail final None by (cases "p = a") auto
    next
      case (Some old)
      note present = Some
      obtain n2 lay2 E2 C2 where rec:
          "compile_procs_bodies \<Pi> ps base_lay in_lay n1 =
            (n2, lay2, E2, C2)"
        by (cases "compile_procs_bodies \<Pi> ps base_lay in_lay n1") auto
      have final:
          "n' = n2 \<and> out_lay = lay2 \<and> E = E1 \<union> E2 \<and> C = C1 \<union> C2"
        using Cons.prems(1) proc comp present rec by simp
      have tail:
          "in_lay p = Some (en, ex, Ns, Ep, Cp) \<or>
           Ep \<subseteq> E2 \<and> Cp \<subseteq> C2"
        by (rule Cons.IH[OF rec])
           (use Cons.prems(2) final in auto)
      show ?thesis
        using tail final by auto
    qed
  qed
qed

lemma compile_procs_body_fragment_embedding:
  assumes wf: "wf_compile_input \<Pi> ps main"
      and layout:
        "compile_procs_layout \<Pi> ps (\<lambda>_. None) 0 = (n, base_lay)"
      and bodies:
        "compile_procs_bodies \<Pi> ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
      and fragment:
        "full_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "Ep \<subseteq> E \<and> Cp \<subseteq> C"
  using compile_procs_bodies_fragment[OF bodies fragment] by auto

lemma compile_call_defined:
  assumes layout: "lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "compile \<Pi> lay (Call p) n =
    (n + 2, n, n + 1,
      {(n, EA_Enter, en)}, {(n, ex, n + 1)})"
using layout by simp

subsection \<open>Located CFG execution\<close>

type_synonym cframe = "pp \<times> pp \<times> store"
type_synonym cconf = "pp \<times> store \<times> cframe list"

inductive cstep :: "cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for g where
  Intra:
    "(u, a, v) \<in> edges g \<Longrightarrow>
     a \<noteq> EA_Enter \<Longrightarrow>
     edge_step a s = Some s' \<Longrightarrow>
     cstep g (u, s, stk) (v, s', stk)"
| Call:
    "(call, EA_Enter, en) \<in> edges g \<Longrightarrow>
     (call, ex, ret) \<in> combines g \<Longrightarrow>
     cstep g (call, s, stk)
       (en, enter_state s, (call, ret, s) # stk)"
| Return:
    "(call, ex, ret) \<in> combines g \<Longrightarrow>
     cstep g (ex, t, (call, ret, s) # stk)
       (ret, IMP2_Globals.combine_states s t, stk)"

lemma edge_step_mem_edge_collect:
  assumes "edge_step a s = Some t"
  shows "t \<in> edge_collect a {s}"
  using assms by (cases a) (auto split: if_splits)

lemma cfg_collect_edge_step:
  assumes edge: "(u, a, v) \<in> edges g"
      and step: "edge_step a s = Some t"
      and source: "s \<in> cfg_collect g S u"
  shows "t \<in> cfg_collect g S v"
proof (rule cfg_collect_edge[OF edge])
  have "t \<in> edge_collect a {s}"
    by (rule edge_step_mem_edge_collect[OF step])
  moreover have "{s} \<subseteq> cfg_collect g S u"
    using source by simp
  ultimately show "t \<in> edge_collect a (cfg_collect g S u)"
    using edge_collect_mono by blast
qed

fun stack_sound :: "cfg \<Rightarrow> store set \<Rightarrow> cframe list \<Rightarrow> bool" where
  "stack_sound g S [] = True"
| "stack_sound g S ((call, ret, s) # stk) =
     (s \<in> cfg_collect g S call \<and> stack_sound g S stk)"

definition located_sound :: "cfg \<Rightarrow> store set \<Rightarrow> cconf \<Rightarrow> bool" where
  "located_sound g S cf \<longleftrightarrow>
     (case cf of (v, s, stk) \<Rightarrow>
        s \<in> cfg_collect g S v \<and> stack_sound g S stk)"

lemma located_sound_entry:
  assumes "s \<in> S"
  shows "located_sound g S (cfg_entry g, s, [])"
  unfolding located_sound_def
  using assms cfg_collect_entry by auto

lemma cstep_preserves_located_sound:
  assumes "located_sound g S cf"
      and "cstep g cf cf'"
  shows "located_sound g S cf'"
proof -
  from assms(2) show ?thesis
  proof cases
    case Intra
    then show ?thesis
      using assms(1)
      unfolding located_sound_def
      by (auto intro: cfg_collect_edge_step)
  next
    case Call
    then show ?thesis
      using assms(1)
      unfolding located_sound_def
      by (auto intro: cfg_collect_edge_step)
  next
    case Return
    then show ?thesis
      using assms(1)
      unfolding located_sound_def
      by (auto intro: cfg_collect_combine)
  qed
qed

lemma csteps_preserve_located_sound:
  assumes "located_sound g S cf"
      and "star (cstep g) cf cf'"
  shows "located_sound g S cf'"
proof -
  from assms(2) assms(1) show ?thesis
  proof (induction rule: star.induct)
    case (refl a)
    then show ?case .
  next
    case (step a b c)
    have "located_sound g S b"
      by (rule cstep_preserves_located_sound[OF step.prems step.hyps(1)])
    then show ?case
      by (rule step.IH)
  qed
qed

lemma cstep_imp_cfg_reaches:
  assumes "cstep g cf cf'"
  shows "cfg_reaches g (fst cf) (fst cf')"
  using assms
  by cases
     (auto intro: cfg_reaches_edge cfg_reaches_combine_exit)

lemma csteps_imp_cfg_reaches:
  assumes "star (cstep g) cf cf'"
  shows "cfg_reaches g (fst cf) (fst cf')"
  using assms
proof (induction rule: star.induct)
  case (refl cf)
  show ?case
    by (rule cfg_reaches_refl)
next
  case (step cf mid dst)
  have first: "cfg_reaches g (fst cf) (fst mid)"
    by (rule cstep_imp_cfg_reaches[OF step.hyps(1)])
  show ?case
    using first step.IH by (rule cfg_reaches_trans)
qed

subsection \<open>Arbitrary-query pruning\<close>

lemma cfg_collect_prune_to_query:
  "cfg_collect g S v \<subseteq> cfg_collect (prune_to g v) S v"
proof
  fix t
  assume "t \<in> cfg_collect g S v"
  then have witness: "cfg_witness g S v t"
    by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
  have "cfg_witness (prune_to g v) S v t"
    using cfg_witness_prune_to[OF witness] cfg_reaches_refl by blast
  then show "t \<in> cfg_collect (prune_to g v) S v"
    by (simp add: cfg_collect_eq_paths cfg_collect_paths_def)
qed

subsection \<open>Compiler simulation contract\<close>

locale compiled_source_simulation =
  fixes \<Pi> :: proc_table and ps :: "pname list" and main :: IMP2_Proc.com
    and g :: cfg
    and match :: "(IMP2_Proc.com \<times> store \<times> frame list) \<Rightarrow> cconf \<Rightarrow> bool"
  assumes g_def: "g = compile_prog \<Pi> ps main"
      and wf: "wf_compile_input \<Pi> ps main"
      and initial_match:
        "\<And>s. match (main, s, []) (cfg_entry g, s, [])"
      and step_match:
        "\<And>src src' cf.
           match src cf \<Longrightarrow>
           pstep \<Pi> src src' \<Longrightarrow>
           \<exists>cf'. star (cstep g) cf cf' \<and> match src' cf'"
begin

lemma source_steps_match:
  assumes "match src cf"
      and "star (pstep \<Pi>) src src'"
  shows "\<exists>cf'. star (cstep g) cf cf' \<and> match src' cf'"
proof -
  from assms(2) show ?thesis
    using assms(1)
  proof (induction arbitrary: cf rule: star.induct)
    case (refl src)
    show ?case
    proof (rule exI[where x = cf], intro conjI)
      show "star (cstep g) cf cf"
        by (rule star.refl)
      show "match src cf"
        by (rule refl.prems)
    qed
  next
    case (step src mid dst)
    obtain cf_mid where run1: "star (cstep g) cf cf_mid"
        and match_mid: "match mid cf_mid"
      using step_match[OF step.prems step.hyps(1)] by blast
    obtain cf_dst where run2: "star (cstep g) cf_mid cf_dst"
        and match_dst: "match dst cf_dst"
      using step.IH[OF match_mid] by blast
    have "star (cstep g) cf cf_dst"
      using run1 run2 by (rule star_trans)
    then show ?case
      using match_dst by blast
  qed
qed

theorem source_reaches_cfg_collect:
  assumes run: "psteps \<Pi> (main, s, []) src'"
  shows "\<exists>v t stk.
     match src' (v, t, stk) \<and>
     t \<in> cfg_collect g {s} v \<and>
     cfg_reaches g (cfg_entry g) v"
proof -
  have initial: "match (main, s, []) (cfg_entry g, s, [])"
    by (rule initial_match)
  obtain cf' where cfg_run:
      "star (cstep g) (cfg_entry g, s, []) cf'"
      and matched: "match src' cf'"
    using source_steps_match[OF initial run] by blast
  have sound_initial: "located_sound g {s} (cfg_entry g, s, [])"
    by (rule located_sound_entry) simp
  have sound_final: "located_sound g {s} cf'"
    by (rule csteps_preserve_located_sound[OF sound_initial cfg_run])
  obtain v t stk where cf': "cf' = (v, t, stk)"
    by (cases cf') auto
  have reachable: "cfg_reaches g (cfg_entry g) v"
    using csteps_imp_cfg_reaches[OF cfg_run]
    unfolding cf' by simp
  show ?thesis
    using matched sound_final reachable
    unfolding cf' located_sound_def
    by blast
qed

corollary source_reaches_post_fixpoint:
  fixes env :: "pp \<Rightarrow> 'a::sound_domain abs_state"
    and s0 :: "'a abs_state"
  assumes stf: "sound_transfer tf"
      and run: "psteps \<Pi> (main, s, []) src'"
      and post: "is_post_fixpoint g tf (\<squnion>) bot s0 env"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
  shows "\<exists>v t stk.
     match src' (v, t, stk) \<and> t \<in> \<lbrakk>env v\<rbrakk>"
proof -
  interpret sound_transfer tf
    by (rule stf)
  obtain v t stk where matched: "match src' (v, t, stk)"
      and collected: "t \<in> cfg_collect g {s} v"
    using source_reaches_cfg_collect[OF run] by blast
  have fin: "finite (edges g)"
    using compile_prog_finite g_def by blast
  have finC: "finite (combines g)"
    using compile_prog_finite g_def by blast
  have initial: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using init by simp
  have "cfg_collect g {s} v \<le> \<lbrakk>env v\<rbrakk>"
    by (rule unified_post_fixpoint_sound[OF fin finC post initial])
  then have "t \<in> \<lbrakk>env v\<rbrakk>"
    using collected by blast
  then show ?thesis
    using matched by blast
qed

end


subsection \<open>Arbitrary-query side-solver result\<close>

theorem side_collect_sound_at_pruned_eff:
  fixes g :: cfg and \<sigma> :: "pp + 'g::finite \<Rightarrow> 'a::sound_domain abs_state"
    and bot0 s0 :: "'a abs_state" and S :: "store set"
    and etf :: "('g, 'a) effectful_domain_transfer"
    and gseed :: 'g and v :: pp
  assumes se: "sound_effectful_transfer etf"
      and pp: "part_post_solution (side_cfg_T_eff g etf bot0 s0 gseed)
                 v \<sigma> vars"
      and fin: "finite (edges g)"
      and finC: "finite (combines g)"
      and entry: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
      and cone: "cone_compatible_etf etf"
      and inr: "inr_slot_locals_bot \<sigma>"
  shows "cfg_collect g S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf
    by (rule se)
  define pg where "pg = prune_to g v"
  have fin_pg: "finite (edges pg)"
    using fin by (auto simp: pg_def)
  have finC_pg: "finite (combines pg)"
    using finC by (auto simp: pg_def)
  have step_le:
    "\<And>u a w. (u, a, w) \<in> edges pg \<Longrightarrow>
       etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
  proof -
    fix u a w
    assume edge_pg: "(u, a, w) \<in> edges pg"
    have edge_g: "(u, a, w) \<in> edges g"
      using edge_pg by (simp add: pg_def)
    have reaches: "cfg_reaches g w v"
      using edge_pg by (simp add: pg_def cone_def)
    have "w \<in> vars"
      by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone reaches])
    then show "etf_full (apply_etf etf a u) \<sigma> \<le> side_env \<sigma> w"
      by (rule etf_combined_le_eff[OF pp _ edge_g fin])
  qed
  have combine_le:
    "\<And>call ex ret. (call, ex, ret) \<in> combines pg \<Longrightarrow>
       etf_full (etf_combine etf call ex) \<sigma> \<le> side_env \<sigma> ret"
  proof -
    fix call ex ret
    assume combine_pg: "(call, ex, ret) \<in> combines pg"
    have combine_g: "(call, ex, ret) \<in> combines g"
      using combine_pg by (simp add: pg_def)
    have reaches: "cfg_reaches g ret v"
      using combine_pg by (simp add: pg_def cone_def)
    have "ret \<in> vars"
      by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone reaches])
    then show "etf_full (etf_combine etf call ex) \<sigma> \<le> side_env \<sigma> ret"
      by (rule etf_combine_combined_le_eff[OF pp _ combine_g finC])
  qed
  have entry_pg: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry pg)\<rbrakk>"
    using entry by (simp add: pg_def)
  have collect_pg: "cfg_collect pg S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule se.post_fixpoint_sound_at_eff[OF inr entry_pg step_le combine_le order_refl])
  have frame: "cfg_collect g S v \<subseteq> cfg_collect pg S v"
    using cfg_collect_prune_to_query[of g S v] by (simp add: pg_def)
  show ?thesis
    using frame collect_pg by blast
qed

theorem side_analyse_eff_collect_sound_at_pruned:
  fixes \<Pi> ps main and s0 :: "'a::sound_domain abs_state"
    and S :: "store set"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g and v :: pp
  defines "g \<equiv> compile_prog \<Pi> ps main"
  assumes se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and dom: "side_cfg_solve_dom_eff g etf bot s0 gseed v"
      and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
      and entry_reaches: "cfg_reaches g (cfg_entry g) v"
  shows "cfg_collect g S v
         \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
proof -
  interpret se: sound_effectful_transfer etf
    by (rule se)
  interpret ip: td_cfg_side_solver_eff g etf bot s0 gseed
    using threefold_monoD_eq[OF tfm]
      threefold_monoD_sides[OF tfm]
      threefold_monoD_deps[OF tfm]
    by unfold_locales
  define \<sigma> where "\<sigma> = ip.nu_at v"
  have fin: "finite (edges g)"
    unfolding g_def using compile_prog_finite by simp
  have finC: "finite (combines g)"
    unfolding g_def using compile_prog_finite by simp
  have pp: "part_post_solution (side_cfg_T_eff g etf bot s0 gseed)
      v \<sigma> (ip.stabl_at v)"
    using ip.part_post_at_cfg[OF dom] unfolding \<sigma>_def by simp
  have entry_in: "cfg_entry g \<in> ip.stabl_at v"
    by (rule side_cone_in_vars_eff_cone[OF pp fin finC cone entry_reaches])
  have entry_le: "s0 \<le> side_env \<sigma> (cfg_entry g)"
    by (rule s0_le_side_env_entry_eff[OF pp entry_in])
  have entry_cov: "S \<le> \<lbrakk>side_env \<sigma> (cfg_entry g)\<rbrakk>"
    using S_sound gamma_state_mono[OF entry_le] by blast
  have least: "least_part_post_solution (side_cfg_T_eff g etf bot s0 gseed)
      v \<sigma> (ip.stabl_at v)"
    by (metis (mono_tags, opaque_lifting) dom ip.cfg_pkg_eff_eq
        ip.least_part_post_at_cfg \<sigma>_def)
  have inr: "inr_slot_locals_bot \<sigma>"
    by (metis cone_compatible_etf_comb_inr
        cone_compatible_etf_comb_static
        cone_compatible_etf_edge_inr
        cone_compatible_etf_edge_static
        least
        least_part_post_solution_inr_slot_locals_bot_eff
        threefold_monoD_eq[OF tfm]
        threefold_monoD_sides[OF tfm]
        cone)
  have collect: "cfg_collect g S v \<le> \<lbrakk>side_env \<sigma> v\<rbrakk>"
    by (rule side_collect_sound_at_pruned_eff[OF se pp fin finC entry_cov cone inr])
  have analyse_eq:
      "side_analyse_eff \<Pi> ps main etf bot s0 gseed v = side_env \<sigma> v"
    unfolding side_analyse_eff_def \<sigma>_def g_def by simp
  show ?thesis
    using collect analyse_eq by simp
qed
context compiled_source_simulation
begin

corollary source_reaches_side_analyse_eff:
  fixes s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes run: "psteps \<Pi> (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom: "\<And>v. cfg_reaches g (cfg_entry g) v \<Longrightarrow>
        side_cfg_solve_dom_eff g etf bot s0 gseed v"
  shows "\<exists>v t stk.
    match src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
proof -
  obtain v t stk where matched: "match src' (v, t, stk)"
      and collected: "t \<in> cfg_collect g {s} v"
      and reachable: "cfg_reaches g (cfg_entry g) v"
    using source_reaches_cfg_collect[OF run] by blast
  have init_set: "{s} \<le> \<lbrakk>s0\<rbrakk>"
    using init by simp
  have bound:
      "cfg_collect (compile_prog \<Pi> ps main) {s} v
       \<le> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
  proof (rule side_analyse_eff_collect_sound_at_pruned)
    show "sound_effectful_transfer etf"
      by (rule se)
    show "threefold_mono
        (side_cfg_T_eff (compile_prog \<Pi> ps main) etf bot s0 gseed)"
      using tfm unfolding g_def .
    show "cone_compatible_etf etf"
      by (rule cone)
    show "side_cfg_solve_dom_eff
        (compile_prog \<Pi> ps main) etf bot s0 gseed v"
      using dom[OF reachable] unfolding g_def .
    show "{s} \<le> \<lbrakk>s0\<rbrakk>"
      by (rule init_set)
    show "cfg_reaches (compile_prog \<Pi> ps main)
        (cfg_entry (compile_prog \<Pi> ps main)) v"
      using reachable unfolding g_def .
  qed
  have "t \<in> \<lbrakk>side_analyse_eff \<Pi> ps main etf bot s0 gseed v\<rbrakk>"
    using collected bound unfolding g_def by blast
  then show ?thesis
    using matched by blast
qed

end

end
