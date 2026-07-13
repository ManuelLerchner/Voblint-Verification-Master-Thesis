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

fun endpoint_view :: "proc_info option \<Rightarrow> (pp \<times> pp) option"
where
  "endpoint_view None = None"
| "endpoint_view (Some (en, ex, Ns, E, C)) = Some (en, ex)"

definition layouts_agree :: "proc_layout \<Rightarrow> proc_layout \<Rightarrow> bool"
where
  "layouts_agree lay1 lay2 \<longleftrightarrow>
    (\<forall>p. endpoint_view (lay1 p) = endpoint_view (lay2 p))"

lemma compile_layouts_agree:
  assumes agree: "layouts_agree lay1 lay2"
  shows "compile Pi lay1 cmd n = compile Pi lay2 cmd n"
  using agree
proof (induction cmd arbitrary: n)
  case SKIP
  show ?case by simp
next
  case Assign
  show ?case by simp
next
  case (Seq c1 c2)
  show ?case
    by (simp add: Seq.IH(1)[OF Seq.prems] Seq.IH(2)[OF Seq.prems])
next
  case If
  show ?case
    by (simp add: If.IH(1)[OF If.prems] If.IH(2)[OF If.prems])
next
  case While
  show ?case
    by (simp add: While.IH[OF While.prems])
next
  case Scope
  show ?case
    by (simp add: Scope.IH[OF Scope.prems])
next
  case (Call p)
  have view: "endpoint_view (lay1 p) = endpoint_view (lay2 p)"
    using Call.prems unfolding layouts_agree_def by blast
  show ?case
    using view
    by (cases "lay1 p"; cases "lay2 p")
       (auto split: prod.splits)
next
  case Restore
  show ?case by simp
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
  assumes result: "compile_procs_layout Pi ps lay n = (n', lay')"
      and present: "lay p = Some info"
  shows "lay' p = Some info"
  using result present
proof (induction ps arbitrary: lay n n' lay')
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "Pi a")
    case None
    have rec: "compile_procs_layout Pi ps lay n = (n', lay')"
      using Cons.prems(1) None by simp
    show ?thesis
      by (rule Cons.IH[OF rec Cons.prems(2)])
  next
    case (Some cmd)
    note proc = Some
    obtain k en ex E C where comp:
        "compile Pi (known_proc_layout Pi (a # ps) lay) cmd n =
          (k, en, ex, E, C)"
      by (cases "compile Pi (known_proc_layout Pi (a # ps) lay) cmd n")
         auto
    show ?thesis
    proof (cases "lay a")
      case None
      note absent = None
      have rec:
          "compile_procs_layout Pi ps
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
      have rec: "compile_procs_layout Pi ps lay k = (n', lay')"
        using Cons.prems(1) proc comp present_a by simp
      show ?thesis
        by (rule Cons.IH[OF rec Cons.prems(2)])
    qed
  qed
qed

lemma compile_procs_layout_member:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>q \<in> set ps. in_lay q = None"
      and defined: "\<forall>q \<in> set ps. Pi q \<noteq> None"
      and result:
        "compile_procs_layout Pi ps in_lay n = (n', out_lay)"
      and member: "p \<in> set ps"
  shows "\<exists>en ex Ns.
    out_lay p = Some (en, ex, Ns, {}, {})"
  using distinct fresh defined result member
proof (induction ps arbitrary: in_lay n n' out_lay p)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  obtain head_cmd where head: "Pi a = Some head_cmd"
    using Cons.prems(3) by auto
  obtain k head_en head_ex head_E head_C where comp:
      "compile Pi (known_proc_layout Pi (a # ps) in_lay)
        head_cmd n =
        (k, head_en, head_ex, head_E, head_C)"
    by (cases "compile Pi
      (known_proc_layout Pi (a # ps) in_lay) head_cmd n") auto
  define next_lay where
    "next_lay =
      in_lay(a := Some (head_en, head_ex, {n..<k}, {}, {}))"
  have rec:
      "compile_procs_layout Pi ps next_lay k = (n', out_lay)"
    using Cons.prems(4) head comp Cons.prems(2)
    by (simp add: next_lay_def)
  show ?case
  proof (cases "p = a")
    case True
    have stored:
        "out_lay a =
          Some (head_en, head_ex, {n..<k}, {}, {})"
      by (rule compile_procs_layout_preserves[OF rec])
         (simp add: next_lay_def)
    then show ?thesis
      using True by blast
  next
    case False
    have fresh_tail: "\<forall>q \<in> set ps. next_lay q = None"
      using Cons.prems(1,2)
      by (auto simp: next_lay_def)
    show ?thesis
      by (rule Cons.IH[OF _ fresh_tail _ rec])
         (use Cons.prems False in auto)
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

lemma compile_procs_bodies_lookup:
  assumes distinct: "distinct ps"
      and fresh: "\<forall>q \<in> set ps. in_lay q = None"
      and bodies:
        "compile_procs_bodies Pi ps base_lay in_lay n =
          (n', out_lay, E, C)"
      and member: "p \<in> set ps"
      and body: "Pi p = Some cmd"
      and lookup:
        "out_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "\<exists>start finish.
    compile Pi base_lay cmd start = (finish, en, ex, Ep, Cp)"
  using distinct fresh bodies member body lookup
proof (induction ps arbitrary: in_lay n n' out_lay E C p cmd
    en ex Ns Ep Cp)
  case Nil
  then show ?case by simp
next
  case (Cons a ps)
  show ?case
  proof (cases "Pi a")
    case None
    have neq: "p \<noteq> a"
      using Cons.prems(5) None by auto
    have rec:
        "compile_procs_bodies Pi ps base_lay in_lay n =
          (n', out_lay, E, C)"
      using Cons.prems(3) None by simp
    show ?thesis
      by (rule Cons.IH[OF _ _ rec])
         (use Cons.prems neq in auto)
  next
    case (Some head_cmd)
    note head = Some
    obtain k head_en head_ex head_E head_C where comp:
        "compile Pi base_lay head_cmd n =
          (k, head_en, head_ex, head_E, head_C)"
      by (cases "compile Pi base_lay head_cmd n") auto
    define next_lay where
      "next_lay =
        in_lay(a := Some
          (head_en, head_ex, {n..<k}, head_E, head_C))"
    have absent: "in_lay a = None"
      using Cons.prems(2) by simp
    obtain Erest Crest where rec:
        "compile_procs_bodies Pi ps base_lay next_lay k =
          (n', out_lay, Erest, Crest)"
      using Cons.prems(3) head comp absent
      by (auto simp: next_lay_def split: prod.splits)
    show ?thesis
    proof (cases "p = a")
      case True
      have stored:
          "out_lay a = Some
            (head_en, head_ex, {n..<k}, head_E, head_C)"
        by (rule compile_procs_bodies_preserves[OF rec])
           (simp add: next_lay_def)
      have cmd_eq: "cmd = head_cmd"
        using Cons.prems(5) head True by simp
      show ?thesis
        using comp Cons.prems(6) stored True cmd_eq by auto
    next
      case False
      have fresh_tail: "\<forall>q \<in> set ps. next_lay q = None"
        using Cons.prems(1,2)
        by (auto simp: next_lay_def)
      show ?thesis
        by (rule Cons.IH[OF _ fresh_tail rec])
           (use Cons.prems False in auto)
    qed
  qed
qed

lemma compile_procs_bodies_outside:
  assumes result:
    "compile_procs_bodies Pi ps base_lay in_lay n =
      (n', out_lay, E, C)"
      and outside: "p \<notin> set ps"
      and absent: "in_lay p = None"
  shows "out_lay p = None"
  using result outside absent
  by (induction ps arbitrary: in_lay n n' out_lay E C)
     (auto split: option.splits prod.splits)

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

lemma compile_procs_pass_layouts_agree:
  assumes wf: "wf_compile_input Pi ps main"
      and layout:
        "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
          (n, base_lay)"
      and bodies:
        "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
          (n', full_lay, E, C)"
  shows "layouts_agree base_lay full_lay"
proof (unfold layouts_agree_def, intro allI)
  fix p
  show "endpoint_view (base_lay p) = endpoint_view (full_lay p)"
  proof (cases "p \<in> set ps")
    case True
    obtain cmd where body: "Pi p = Some cmd"
      using wf True
      by (auto simp: wf_compile_input_def)
    have distinct: "distinct ps"
      using wf by (auto simp: wf_compile_input_def)
    have defined: "\<forall>q\<in>set ps. Pi q \<noteq> None"
      using wf by (auto simp: wf_compile_input_def)
    have member_info:
        "\<exists>en ex Ns. base_lay p = Some (en, ex, Ns, {}, {})"
      by (rule compile_procs_layout_member[
            OF distinct _ defined layout True])
         simp
    then obtain en ex Ns where base:
        "base_lay p = Some (en, ex, Ns, {}, {})"
      by blast
    obtain Ns' Ep Cp where full:
        "full_lay p = Some (en, ex, Ns', Ep, Cp)"
      using compile_procs_pass_endpoint_agreement[
        OF wf layout bodies True body base] by blast
    show ?thesis
      using base full by simp
  next
    case False
    have base_none: "base_lay p = None"
      using compile_procs_layout_domain_exact[OF wf layout] False
      unfolding layout_domain_exact_def
      by (cases "base_lay p") auto
    have full_none: "full_lay p = None"
      by (rule compile_procs_bodies_outside[OF bodies False]) simp
    show ?thesis
      using base_none full_none by simp
  qed
qed


lemma compile_procs_list_decompose:
  assumes result:
    "compile_procs_list Pi ps (\<lambda>_. None) 0 =
      (nout, full_lay, E, C)"
  shows "\<exists>nbase base_lay.
    compile_procs_layout Pi ps (\<lambda>_. None) 0 =
      (nbase, base_lay) \<and>
    compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
      (nout, full_lay, E, C)"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
    by (cases "compile_procs_layout Pi ps (\<lambda>_. None) 0") auto
  obtain nbody body_lay Ebody Cbody where bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nbody, body_lay, Ebody, Cbody)"
    by (cases "compile_procs_bodies Pi ps base_lay
      (\<lambda>_. None) 0") auto
  show ?thesis
    using result layout bodies
    unfolding compile_procs_list_def
    by simp
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

subsection \<open>Residual commands inside compiled fragments\<close>

type_synonym frame_site = "pp \<times> pp"

inductive control_at ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> IMP2_Proc.com \<Rightarrow> nat \<Rightarrow>
   IMP2_Proc.com \<Rightarrow> pp \<Rightarrow> frame_site list \<Rightarrow> bool"
  for Pi :: proc_table and lay :: proc_layout
where
  Skip:
    "control_at Pi lay IMP2_Proc.com.SKIP n
       IMP2_Proc.com.SKIP n []"
| Assign:
    "control_at Pi lay (IMP2_Proc.com.Assign x a) n
       (IMP2_Proc.com.Assign x a) n []"
| AssignDone:
    "control_at Pi lay (IMP2_Proc.com.Assign x a) n
       IMP2_Proc.com.SKIP (n + 1) []"
| SeqLeft:
    "compile Pi lay c1 n = (n1, en1, ex1, E1, C1) \<Longrightarrow>
     source_com c2 \<Longrightarrow>
     control_at Pi lay c1 n residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
       (IMP2_Proc.com.Seq residual c2) v sites"
| SeqRight:
    "compile Pi lay c1 n = (n1, en1, ex1, E1, C1) \<Longrightarrow>
     control_at Pi lay c2 n1 residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
       residual v sites"
| IfHead:
    "source_com c1 \<Longrightarrow>
     source_com c2 \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
       (IMP2_Proc.com.If b c1 c2) n []"
| IfLeft:
    "control_at Pi lay c1 (n + 1) residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
       residual v sites"
| IfRight:
    "compile Pi lay c1 (n + 1) = (n1, en1, ex1, E1, C1) \<Longrightarrow>
     control_at Pi lay c2 n1 residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
       residual v sites"
| IfDone:
    "compile Pi lay (IMP2_Proc.com.If b c1 c2) n =
       (n1, en, ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
       IMP2_Proc.com.SKIP ex []"
| WhileHead:
    "source_com body \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b body) n
       (IMP2_Proc.com.While b body) n []"
| WhileUnfolded:
    "source_com body \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b body) n
       (IMP2_Proc.com.If b
         (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
         IMP2_Proc.com.SKIP) n []"
| WhileBody:
    "source_com body \<Longrightarrow>
     control_at Pi lay body (n + 1) residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b body) n
       (IMP2_Proc.com.Seq residual (IMP2_Proc.com.While b body))
       v sites"
| WhileDone:
    "compile Pi lay (IMP2_Proc.com.While b body) n =
       (n1, en, ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b body) n
       IMP2_Proc.com.SKIP ex []"
| ScopeHead:
    "source_com body \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope body) n
       (IMP2_Proc.com.Scope body) n []"
| ScopeBody:
    "compile Pi lay (IMP2_Proc.com.Scope body) n =
       (n1, en, scope_ex, E, C) \<Longrightarrow>
     control_at Pi lay body (n + 1) residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope body) n
       (IMP2_Proc.com.Seq residual IMP2_Proc.com.Restore)
       v (sites @ [(n, scope_ex)])"
| ScopeRestore:
    "compile Pi lay body (n + 1) = (n1, en, body_ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope body) n
       IMP2_Proc.com.Restore body_ex [(n, n1)]"
| ScopeDone:
    "compile Pi lay (IMP2_Proc.com.Scope body) n =
       (n1, en, scope_ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope body) n
       IMP2_Proc.com.SKIP scope_ex []"
| CallHead:
    "control_at Pi lay (IMP2_Proc.com.Call p) n
       (IMP2_Proc.com.Call p) n []"
| CallBody:
    "Pi p = Some body \<Longrightarrow>
     lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     compile Pi lay body proc_en =
       (n1, body_en, proc_ex, E, C) \<Longrightarrow>
     control_at Pi lay body proc_en residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call p) n
       (IMP2_Proc.com.Seq residual IMP2_Proc.com.Restore)
       v (sites @ [(n, n + 1)])"
| CallRestore:
    "lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call p) n
       IMP2_Proc.com.Restore proc_ex [(n, n + 1)]"
| CallDone:
    "lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call p) n
       IMP2_Proc.com.SKIP (n + 1) []"

lemma control_at_initial:
  assumes source: "source_com cmd"
  shows "control_at Pi lay cmd n cmd n []"
  using source
proof (induction cmd arbitrary: n)
  case SKIP
  show ?case by (rule control_at.Skip)
next
  case Assign
  show ?case by (rule control_at.Assign)
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 E1 C1 where first:
      "compile Pi lay c1 n = (n1, en1, ex1, E1, C1)"
    by (cases "compile Pi lay c1 n") auto
  have left: "control_at Pi lay c1 n c1 n []"
    by (rule Seq.IH(1)) (use Seq.prems in simp)
  show ?case
    by (rule control_at.SeqLeft[OF first _ left])
       (use Seq.prems in simp)
next
  case If
  show ?case
    by (rule control_at.IfHead) (use If.prems in simp_all)
next
  case While
  show ?case
    by (rule control_at.WhileHead) (use While.prems in simp)
next
  case Scope
  show ?case
    by (rule control_at.ScopeHead) (use Scope.prems in simp)
next
  case Call
  show ?case by (rule control_at.CallHead)
next
  case Restore
  then show ?case by simp
qed

lemma compile_endpoint_shape_entry:
  "(case compile_endpoint_shape lay cmd n of
      (n', en, ex) \<Rightarrow> en) = n"
proof (induction cmd arbitrary: n)
  case SKIP
  then show ?case by simp
next
  case Assign
  then show ?case by simp
next
  case (Seq c1 c2)
  obtain n1 en1 ex1 where first:
      "compile_endpoint_shape lay c1 n = (n1, en1, ex1)"
    by (cases "compile_endpoint_shape lay c1 n") auto
  obtain n2 en2 ex2 where second:
      "compile_endpoint_shape lay c2 n1 = (n2, en2, ex2)"
    by (cases "compile_endpoint_shape lay c2 n1") auto
  have "en1 = n"
    using Seq.IH(1)[of n] first by simp
  then show ?case
    using first second by simp
next
  case If
  then show ?case by (simp split: prod.splits)
next
  case While
  then show ?case by (simp split: prod.splits)
next
  case Scope
  then show ?case by (simp split: prod.splits)
next
  case Call
  then show ?case by (simp split: option.splits)
next
  case Restore
  then show ?case by simp
qed

lemma compile_entry_eq:
  assumes comp: "compile Pi lay cmd n = (n', en, ex, E, C)"
  shows "en = n"
proof -
  have shape:
      "compile_endpoints Pi lay cmd n =
        compile_endpoint_shape lay cmd n"
    by (rule compile_endpoints_eq_shape)
  show ?thesis
    using shape compile_endpoint_shape_entry[of lay cmd n] comp
    unfolding compile_endpoints_def
    by (cases "compile_endpoint_shape lay cmd n") simp
qed

lemma compile_procs_list_body:
  assumes wf: "wf_compile_input Pi ps main"
      and procs:
        "compile_procs_list Pi ps (\<lambda>_. None) 0 =
          (nout, full_lay, Eall, C_all)"
      and body: "Pi p = Some cmd"
      and lookup:
        "full_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "\<exists>finish.
    compile Pi full_lay cmd en = (finish, en, ex, Ep, Cp)"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
      and bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nout, full_lay, Eall, C_all)"
    using compile_procs_list_decompose[OF procs] by blast
  have member: "p \<in> set ps"
    using wf body by (auto simp: wf_compile_input_def)
  have distinct: "distinct ps"
    using wf by (auto simp: wf_compile_input_def)
  have compiled_info:
      "\<exists>start finish. compile Pi base_lay cmd start =
        (finish, en, ex, Ep, Cp)"
    by (rule compile_procs_bodies_lookup[
          OF distinct _ bodies member body lookup])
       simp
  then obtain start finish where compiled_base:
      "compile Pi base_lay cmd start =
        (finish, en, ex, Ep, Cp)"
    by blast
  have agree: "layouts_agree base_lay full_lay"
    by (rule compile_procs_pass_layouts_agree[
          OF wf layout bodies])
  have same:
      "compile Pi base_lay cmd start =
       compile Pi full_lay cmd start"
    by (rule compile_layouts_agree[OF agree])
  have start: "start = en"
    by (rule sym, rule compile_entry_eq[OF compiled_base])
  have compiled_full:
      "compile Pi full_lay cmd start =
        (finish, en, ex, Ep, Cp)"
    using compiled_base same by simp
  show ?thesis
    using compiled_full start by simp
qed

lemma compile_procs_list_complete:
  assumes wf: "wf_compile_input Pi ps main"
      and procs:
        "compile_procs_list Pi ps (\<lambda>_. None) 0 =
          (nout, full_lay, Eall, C_all)"
      and body: "Pi p = Some cmd"
  shows "\<exists>en ex Ns Ep Cp.
    full_lay p = Some (en, ex, Ns, Ep, Cp)"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
      and bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nout, full_lay, Eall, C_all)"
    using compile_procs_list_decompose[OF procs] by blast
  have member: "p \<in> set ps"
    using wf body by (auto simp: wf_compile_input_def)
  have distinct: "distinct ps"
    using wf by (auto simp: wf_compile_input_def)
  have defined: "\<forall>q \<in> set ps. Pi q \<noteq> None"
    using wf by (auto simp: wf_compile_input_def)
  obtain en ex Ns where base:
      "base_lay p = Some (en, ex, Ns, {}, {})"
    using compile_procs_layout_member[
      OF distinct _ defined layout member]
    by auto
  obtain Ns' Ep Cp where full:
      "full_lay p = Some (en, ex, Ns', Ep, Cp)"
    using compile_procs_pass_endpoint_agreement[
      OF wf layout bodies member body base]
    by blast
  show ?thesis using full by blast
qed

subsection \<open>Located CFG execution\<close>

type_synonym cframe = "pp \<times> pp \<times> store"
type_synonym cconf = "pp \<times> store \<times> cframe list"

fun frames_match ::
  "frame_site list \<Rightarrow> frame list \<Rightarrow> cframe list \<Rightarrow> bool"
where
  "frames_match [] [] [] = True"
| "frames_match ((call, ret) # sites) (saved # frs)
     ((call', ret', saved') # stk) =
     (call = call' \<and> ret = ret' \<and> saved = saved' \<and>
      frames_match sites frs stk)"
| "frames_match _ _ _ = False"

definition concrete_program_match ::
  "proc_table \<Rightarrow> pname list \<Rightarrow> IMP2_Proc.com \<Rightarrow>
   (IMP2_Proc.com \<times> store \<times> frame list) \<Rightarrow> cconf \<Rightarrow> bool"
where
  "concrete_program_match Pi ps main src cf \<longleftrightarrow>
    (case src of (residual, s, frs) \<Rightarrow>
     case cf of (v, t, stk) \<Rightarrow>
       s = t \<and>
       (\<exists>nproc lay Eproc Cproc nend main_en main_ex Emain Cmain sites.
          compile_procs_list Pi ps (\<lambda>_. None) 0 =
            (nproc, lay, Eproc, Cproc) \<and>
          compile Pi lay main nproc =
            (nend, main_en, main_ex, Emain, Cmain) \<and>
          control_at Pi lay main nproc residual v sites \<and>
          frames_match sites frs stk))"

lemma concrete_program_initial_match:
  assumes source: "source_com main"
  shows "concrete_program_match Pi ps main
    (main, s, []) (cfg_entry (compile_prog Pi ps main), s, [])"
proof -
  obtain nproc lay Eproc Cproc where procs:
      "compile_procs_list Pi ps (\<lambda>_. None) 0 =
        (nproc, lay, Eproc, Cproc)"
    by (cases "compile_procs_list Pi ps (\<lambda>_. None) 0") auto
  obtain nend main_en main_ex Emain Cmain where main_comp:
      "compile Pi lay main nproc =
        (nend, main_en, main_ex, Emain, Cmain)"
    by (cases "compile Pi lay main nproc") auto
  have entry: "main_en = nproc"
    by (rule compile_entry_eq[OF main_comp])
  have control: "control_at Pi lay main nproc main nproc []"
    by (rule control_at_initial[OF source])
  show ?thesis
    unfolding concrete_program_match_def compile_prog_def
      compile_prog_with_regions_def
    using procs main_comp entry
    apply simp
    apply (rule exI[where x = "[]"])
    using control
    apply simp
    done
qed

lemma compile_procs_list_fragment:
  assumes procs:
    "compile_procs_list Pi ps (\<lambda>_. None) 0 =
      (nout, full_lay, Eall, C_all)"
      and lookup:
    "full_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "Ep \<subseteq> Eall \<and> Cp \<subseteq> C_all"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
      and bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nout, full_lay, Eall, C_all)"
    using compile_procs_list_decompose[OF procs] by blast
  show ?thesis
    using compile_procs_bodies_fragment[OF bodies lookup]
    by auto
qed

lemma compile_prog_sets:
  assumes procs:
    "compile_procs_list Pi ps (\<lambda>_. None) 0 =
      (nproc, lay, Eproc, Cproc)"
      and main_comp:
    "compile Pi lay main nproc =
      (nend, main_en, main_ex, Emain, Cmain)"
  shows "edges (compile_prog Pi ps main) = Eproc \<union> Emain"
    and "combines (compile_prog Pi ps main) = Cproc \<union> Cmain"
  using procs main_comp
  unfolding compile_prog_def compile_prog_with_regions_def
  by simp_all

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


lemma cstep_star_single:
  assumes step: "cstep g cf cf'"
  shows "star (cstep g) cf cf'"
  apply (rule star.step)
   apply (rule step)
  apply (rule star.refl)
  done

lemma cstep_nop:
  assumes edge: "(u, EA_Nop, v) \<in> edges g"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF edge]) simp_all

lemma cstep_assign:
  assumes edge: "(u, EA_Assign x a, v) \<in> edges g"
  shows "cstep g (u, s, stk)
    (v, s(x := IMP2_Expr.aval a s), stk)"
  by (rule cstep.Intra[OF edge]) simp_all

lemma cstep_assume:
  assumes edge: "(u, EA_Assume b, v) \<in> edges g"
      and guard: "IMP2_Expr.bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF edge]) (simp_all add: guard)

lemma cstep_assume_not:
  assumes edge: "(u, EA_AssumeNot b, v) \<in> edges g"
      and guard: "\<not> IMP2_Expr.bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF edge]) (simp_all add: guard)

lemma cstep_star_nop_right:
  assumes run: "star (cstep g) cf (u, s, stk)"
      and edge: "(u, EA_Nop, v) \<in> edges g"
  shows "star (cstep g) cf (v, s, stk)"
  by (rule star_trans[OF run cstep_star_single[OF cstep_nop[OF edge]]])

theorem control_finish_simulation:
  assumes compiled:
        "compile Pi lay original n = (n', en, ex, E, C)"
      and edges: "E \<subseteq> edges g"
      and control:
        "control_at Pi lay original n residual v sites"
      and finished: "residual = IMP2_Proc.com.SKIP"
      and frames: "frames_match (sites @ suffix) frs stk"
  shows "\<exists>stk'.
    star (cstep g) (v, s, stk) (ex, s, stk') \<and>
    frames_match suffix frs stk'"
  using control finished compiled edges frames
  by (induction arbitrary: n' en ex E C suffix frs stk
      rule: control_at.induct;
      fastforce intro: star.refl cstep_star_single cstep_nop cstep_star_nop_right star_trans
        split: prod.splits if_splits)

definition proc_layout_sound ::
  "proc_table \<Rightarrow> proc_layout \<Rightarrow> cfg \<Rightarrow> bool"
where
  "proc_layout_sound Pi lay g \<longleftrightarrow>
    source_pi Pi \<and>
    (\<forall>p body. Pi p = Some body \<longrightarrow>
      (\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp))) \<and>
    (\<forall>p body en ex Ns Ep Cp.
      Pi p = Some body \<longrightarrow>
      lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
      (\<exists>finish.
        compile Pi lay body en = (finish, en, ex, Ep, Cp)) \<and>
      Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g)"

theorem control_step_simulation:
  assumes compiled:
        "compile Pi lay original n = (n', en, ex, E, C)"
      and edges: "E \<subseteq> edges g"
      and combines: "C \<subseteq> combines g"
      and procedures: "proc_layout_sound Pi lay g"
      and control:
        "control_at Pi lay original n residual v sites"
      and frames: "frames_match (sites @ suffix) frs stk"
      and step:
        "pstep Pi (residual, s, frs) (residual', s', frs')"
  shows "\<exists>v' sites' stk'.
    star (cstep g) (v, s, stk) (v', s', stk') \<and>
    control_at Pi lay original n residual' v' sites' \<and>
    frames_match (sites' @ suffix) frs' stk'"  using control compiled edges combines procedures frames step
proof (induction arbitrary: n' en ex E C suffix frs stk
    residual' s' frs' rule: control_at.induct)
  case Skip
  then show ?case by (elim SkipSE)
next
  case (Assign x a n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.SKIP, s(x := IMP2_Expr.aval a s), frs)"
    using Assign.prems(6)
    by (rule AssignSE) simp
  have shape:
      "n = en \<and> ex = n + 1 \<and>
       E = {(n, EA_Assign x a, n + 1)}"
    using Assign.prems(1) by auto
  have edge: "(n, EA_Assign x a, n + 1) \<in> edges g"
    using Assign.prems(2) shape by blast
  have concrete:
      "cstep g (n, s, stk)
        (n + 1, s(x := IMP2_Expr.aval a s), stk)"
    by (rule cstep_assign[OF edge])
  have run:
      "star (cstep g) (n, s, stk)
        (n + 1, s(x := IMP2_Expr.aval a s), stk)"
    by (rule cstep_star_single[OF concrete])
  have located:
      "control_at Pi lay (IMP2_Proc.com.Assign x a) n
        IMP2_Proc.com.SKIP (n + 1) []"
    by (rule control_at.AssignDone)
  have matched: "frames_match ([] @ suffix) frs stk"
    using Assign.prems(5) by simp
  show ?case
    using source_result run located matched by blast
next
  case AssignDone
  then show ?case by (elim SkipSE)
next
  case (SeqLeft c1 n n1 en1 ex1 E1 C1 c2 residual v sites)
  show ?case
  proof (rule SeqSE[OF SeqLeft.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') = (c2, s, frs)"
    obtain n2 en2 ex2 E2 C2 where second:
        "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
      by (cases "compile Pi lay c2 n1") auto
    have parent_edges:
        "E = E1 \<union>
          (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
          \<union> E2"
      using SeqLeft.prems(1) SeqLeft.hyps(1) second by simp
    have sub_edges: "E1 \<subseteq> edges g"
      using SeqLeft.prems(2) parent_edges by blast
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (ex1, s, stk1)"
        and body_frames: "frames_match suffix frs stk1"
      using control_finish_simulation[
          OF SeqLeft.hyps(1) sub_edges SeqLeft.hyps(3)
             residual_skip SeqLeft.prems(5)]
      by blast
    have entry: "en2 = n1"
      by (rule compile_entry_eq[OF second])
    have bridge:
        "star (cstep g) (ex1, s, stk1) (en2, s, stk1)"
    proof (cases "ex1 = en2")
      case True
      show ?thesis
        using True star.refl[of "cstep g" "(ex1, s, stk1)"] by simp
    next
      case False
      have edge: "(ex1, EA_Nop, en2) \<in> edges g"
        using SeqLeft.prems(2) parent_edges False by auto
      show ?thesis
        by (rule cstep_star_single, rule cstep_nop[OF edge])
    qed
    have run: "star (cstep g) (v, s, stk) (en2, s, stk1)"
      by (rule star_trans[OF body_run bridge])
    have next_control:
        "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n c2 n1 []"
      by (rule control_at.SeqRight[OF SeqLeft.hyps(1)])
         (rule control_at_initial[OF SeqLeft.hyps(2)])
    show ?case
      apply (rule exI[of _ en2])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk1])
      using source_result entry run next_control body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' c2, t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    obtain n2 en2 ex2 E2 C2 where second:
        "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
      by (cases "compile Pi lay c2 n1") auto
    have parent_sets:
        "E = E1 \<union>
          (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
          \<union> E2 \<and>
         C = C1 \<union> C2"
      using SeqLeft.prems(1) SeqLeft.hyps(1) second by simp
    have sub_edges: "E1 \<subseteq> edges g"
      using SeqLeft.prems(2) parent_sets by blast
    have sub_combines: "C1 \<subseteq> combines g"
      using SeqLeft.prems(3) parent_sets by blast
    obtain v' sites' stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay c1 n inner' v' sites'"
        and matched:
          "frames_match (sites' @ suffix) frs1 stk'"
      using SeqLeft.IH[
          OF SeqLeft.hyps(1) sub_edges sub_combines
             SeqLeft.prems(4) SeqLeft.prems(5) inner_step]
      by blast
    have next_control:
        "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
          (IMP2_Proc.com.Seq inner' c2) v' sites'"
      by (rule control_at.SeqLeft[
            OF SeqLeft.hyps(1) SeqLeft.hyps(2) inner_control])
    show ?case
      using source_result run next_control matched by blast
  qed
next
  case (SeqRight c1 n n1 en1 ex1 E1 C1 c2 residual v sites)
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = E1 \<union>
        (if ex1 = en2 then {} else {(ex1, EA_Nop, en2)})
        \<union> E2 \<and>
       C = C1 \<union> C2"
    using SeqRight.prems(1) SeqRight.hyps(1) second by simp
  have sub_edges: "E2 \<subseteq> edges g"
    using SeqRight.prems(2) parent_sets by blast
  have sub_combines: "C2 \<subseteq> combines g"
    using SeqRight.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c2 n1 residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using SeqRight.IH[
        OF second sub_edges sub_combines SeqRight.prems(4)
           SeqRight.prems(5) SeqRight.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.Seq c1 c2) n
        residual' v' sites'"
    by (rule control_at.SeqRight[
          OF SeqRight.hyps(1) inner_control])
  show ?case
    using run next_control matched by blast
next

  case (IfHead c1 c2 b n)
  obtain n1 en1 ex1 E1 C1 where first:
      "compile Pi lay c1 (n + 1) = (n1, en1, ex1, E1, C1)"
    by (cases "compile Pi lay c1 (n + 1)") auto
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_edges:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))"
    using IfHead.prems(1) first second by auto
  show ?case
  proof (rule IfSE[OF IfHead.prems(6)])
    assume guard: "IMP2_Expr.bval b s"
       and source_result: "(residual', s', frs') = (c1, s, frs)"
    have edge: "(n, EA_Assume b, en1) \<in> edges g"
      using IfHead.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (en1, s, stk)"
      by (rule cstep_star_single, rule cstep_assume[OF edge guard])
    have entry: "en1 = n + 1"
      by (rule compile_entry_eq[OF first])
    have branch:
        "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n c1 en1 []"
      apply (rule control_at.IfLeft)
      using control_at_initial[OF IfHead.hyps(1), of Pi lay "n + 1"] entry
      apply simp
      done
    show ?case
      apply (rule exI[of _ en1])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run branch IfHead.prems(5)
      apply simp
      done
  next
    assume guard: "\<not> IMP2_Expr.bval b s"
       and source_result: "(residual', s', frs') = (c2, s, frs)"
    have edge: "(n, EA_AssumeNot b, en2) \<in> edges g"
      using IfHead.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (en2, s, stk)"
      by (rule cstep_star_single, rule cstep_assume_not[OF edge guard])
    have entry: "en2 = n1"
      by (rule compile_entry_eq[OF second])
    have branch:
        "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n c2 en2 []"
      apply (rule control_at.IfRight[OF first])
      using control_at_initial[OF IfHead.hyps(2), of Pi lay n1] entry
      apply simp
      done
    show ?case
      apply (rule exI[of _ en2])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run branch IfHead.prems(5)
      apply simp
      done
  qed
next
  case (IfLeft c1 n residual v sites b c2)  obtain n1 en1 ex1 E1 C1 where first:
      "compile Pi lay c1 (n + 1) = (n1, en1, ex1, E1, C1)"
    by (cases "compile Pi lay c1 (n + 1)") auto
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))
       \<and> C = C1 \<union> C2"
    using IfLeft.prems(1) first second by auto
  have sub_edges: "E1 \<subseteq> edges g"
    using IfLeft.prems(2) parent_sets by blast
  have sub_combines: "C1 \<subseteq> combines g"
    using IfLeft.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c1 (n + 1) residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using IfLeft.IH[
        OF first sub_edges sub_combines IfLeft.prems(4)
           IfLeft.prems(5) IfLeft.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
        residual' v' sites'"
    by (rule control_at.IfLeft[OF inner_control])
  show ?case
    using run next_control matched by blast
next
  case (IfRight c1 n n1 en1 ex1 E1 C1 c2 residual v sites b)
  obtain n2 en2 ex2 E2 C2 where second:
      "compile Pi lay c2 n1 = (n2, en2, ex2, E2, C2)"
    by (cases "compile Pi lay c2 n1") auto
  have parent_sets:
      "E = insert (ex1, EA_Nop, n2)
            (insert (ex2, EA_Nop, n2)
              (insert (n, EA_Assume b, en1)
                (insert (n, EA_AssumeNot b, en2) (E1 \<union> E2))))
       \<and> C = C1 \<union> C2"
    using IfRight.prems(1) IfRight.hyps(1) second by auto
  have sub_edges: "E2 \<subseteq> edges g"
    using IfRight.prems(2) parent_sets by blast
  have sub_combines: "C2 \<subseteq> combines g"
    using IfRight.prems(3) parent_sets by blast
  obtain v' sites' stk' where run:
      "star (cstep g) (v, s, stk) (v', s', stk')"
      and inner_control:
        "control_at Pi lay c2 n1 residual' v' sites'"
      and matched:
        "frames_match (sites' @ suffix) frs' stk'"
    using IfRight.IH[
        OF second sub_edges sub_combines IfRight.prems(4)
           IfRight.prems(5) IfRight.prems(6)]
    by blast
  have next_control:
      "control_at Pi lay (IMP2_Proc.com.If b c1 c2) n
        residual' v' sites'"
    by (rule control_at.IfRight[
          OF IfRight.hyps(1) inner_control])
  show ?case
    using run next_control matched by blast
next
  case IfDone
  then show ?case by (elim SkipSE)
next
  case (WhileHead body b n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.If b
         (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
         IMP2_Proc.com.SKIP, s, frs)"
    using WhileHead.prems(6)
    by (rule WhileSE) simp
  have run: "star (cstep g) (n, s, stk) (n, s, stk)"
    by (rule star.refl)
  have located:
      "control_at Pi lay (IMP2_Proc.com.While b body) n
        (IMP2_Proc.com.If b
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
          IMP2_Proc.com.SKIP) n []"
    by (rule control_at.WhileUnfolded[OF WhileHead.hyps(1)])
  show ?case
    apply (rule exI[of _ n])
    apply (rule exI[of _ "[]"])
    apply (rule exI[of _ stk])
    using source_result run located WhileHead.prems(5)
    apply simp
    done
next
  case (WhileUnfolded body b n)
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_edges:
      "E = insert (body_ex, EA_Nop, n)
            (insert (n, EA_Assume b, body_en)
              (insert (n, EA_AssumeNot b, n1) Eb))"
    using WhileUnfolded.prems(1) body_comp by auto
  show ?case
  proof (rule IfSE[OF WhileUnfolded.prems(6)])
    assume guard: "IMP2_Expr.bval b s"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body),
           s, frs)"
    have edge: "(n, EA_Assume b, body_en) \<in> edges g"
      using WhileUnfolded.prems(2) parent_edges by blast
    have run:
        "star (cstep g) (n, s, stk) (body_en, s, stk)"
      by (rule cstep_star_single, rule cstep_assume[OF edge guard])
    have entry: "body_en = n + 1"
      by (rule compile_entry_eq[OF body_comp])
    have body_control:
        "control_at Pi lay body (n + 1) body body_en []"
      using control_at_initial[OF WhileUnfolded.hyps(1), of Pi lay "n + 1"]
        entry by simp
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.Seq body (IMP2_Proc.com.While b body))
          body_en []"
      by (rule control_at.WhileBody[
            OF WhileUnfolded.hyps(1) body_control])
    show ?case
      apply (rule exI[of _ body_en])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run located WhileUnfolded.prems(5)
      apply simp
      done
  next
    assume guard: "\<not> IMP2_Expr.bval b s"
       and source_result:
         "(residual', s', frs') = (IMP2_Proc.com.SKIP, s, frs)"
    have edge: "(n, EA_AssumeNot b, n1) \<in> edges g"
      using WhileUnfolded.prems(2) parent_edges by blast
    have run: "star (cstep g) (n, s, stk) (n1, s, stk)"
      by (rule cstep_star_single, rule cstep_assume_not[OF edge guard])
    have exit: "ex = n1"
      using WhileUnfolded.prems(1) body_comp by auto
    have finished:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          IMP2_Proc.com.SKIP ex []"
      by (rule control_at.WhileDone[OF WhileUnfolded.prems(1)])
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          IMP2_Proc.com.SKIP n1 []"
      using finished exit by simp
    show ?case
      apply (rule exI[of _ n1])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk])
      using source_result run located WhileUnfolded.prems(5)
      apply simp
      done
  qed
next
  case (WhileBody body n residual v sites b)
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_sets:
      "E = insert (body_ex, EA_Nop, n)
            (insert (n, EA_Assume b, body_en)
              (insert (n, EA_AssumeNot b, n1) Eb))
       \<and> C = Cb"
    using WhileBody.prems(1) body_comp by auto
  have sub_edges: "Eb \<subseteq> edges g"
    using WhileBody.prems(2) parent_sets by blast
  have sub_combines: "Cb \<subseteq> combines g"
    using WhileBody.prems(3) parent_sets by blast
  show ?case
  proof (rule SeqSE[OF WhileBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.While b body, s, frs)"
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (body_ex, s, stk1)"
        and body_frames: "frames_match suffix frs stk1"
      using control_finish_simulation[
          OF body_comp sub_edges WhileBody.hyps(2)
             residual_skip WhileBody.prems(5)]
      by blast
    have back_edge: "(body_ex, EA_Nop, n) \<in> edges g"
      using WhileBody.prems(2) parent_sets by blast
    have back_run:
        "star (cstep g) (body_ex, s, stk1) (n, s, stk1)"
      by (rule cstep_star_single, rule cstep_nop[OF back_edge])
    have run: "star (cstep g) (v, s, stk) (n, s, stk1)"
      by (rule star_trans[OF body_run back_run])
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.While b body) n []"
      by (rule control_at.WhileHead[OF WhileBody.hyps(1)])
    show ?case
      apply (rule exI[of _ n])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk1])
      using source_result run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.While b body),
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    obtain v' sites' stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay body (n + 1) inner' v' sites'"
        and matched:
          "frames_match (sites' @ suffix) frs1 stk'"
      using WhileBody.IH[
          OF body_comp sub_edges sub_combines WhileBody.prems(4)
             WhileBody.prems(5) inner_step]
      by blast
    have located:
        "control_at Pi lay (IMP2_Proc.com.While b body) n
          (IMP2_Proc.com.Seq inner' (IMP2_Proc.com.While b body))
          v' sites'"
      by (rule control_at.WhileBody[
            OF WhileBody.hyps(1) inner_control])
    show ?case
      using source_result run located matched by blast
  qed
next
  case WhileDone
  then show ?case by (elim SkipSE)
next
  case (ScopeHead body n)
  have source_result:
      "(residual', s', frs') =
       (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore,
        enter_state s, s # frs)"
    using ScopeHead.prems(6)
    by (rule ScopeSE) simp
  obtain n1 body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (n1, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have shape:
      "ex = n1 \<and>
       (n, EA_Enter, body_en) \<in> E \<and>
       (n, body_ex, n1) \<in> C"
    using ScopeHead.prems(1) body_comp by auto
  have enter_edge:
      "(n, EA_Enter, body_en) \<in> edges g"
    using ScopeHead.prems(2) shape by blast
  have combine:
      "(n, body_ex, n1) \<in> combines g"
    using ScopeHead.prems(3) shape by blast
  have concrete:
      "cstep g (n, s, stk)
        (body_en, enter_state s, (n, n1, s) # stk)"
    by (rule cstep.Call[OF enter_edge combine])
  have run:
      "star (cstep g) (n, s, stk)
        (body_en, enter_state s, (n, n1, s) # stk)"
    by (rule cstep_star_single[OF concrete])
  have entry: "body_en = n + 1"
    by (rule compile_entry_eq[OF body_comp])
  have body_control:
      "control_at Pi lay body (n + 1) body body_en []"
    using control_at_initial[OF ScopeHead.hyps(1), of Pi lay "n + 1"]
      entry by simp
  have raw_location:
      "control_at Pi lay (IMP2_Proc.com.Scope body) n
        (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore)
        body_en ([] @ [(n, ex)])"
    by (rule control_at.ScopeBody[
          OF ScopeHead.prems(1) body_control])
  have located:
      "control_at Pi lay (IMP2_Proc.com.Scope body) n
        (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore)
        body_en [(n, n1)]"
    using raw_location shape by simp
  have matched:
      "frames_match ([(n, n1)] @ suffix) (s # frs)
        ((n, n1, s) # stk)"
    using ScopeHead.prems(5) by simp
  show ?case
    apply (rule exI[of _ body_en])
    apply (rule exI[of _ "[(n, n1)]"])
    apply (rule exI[of _ "(n, n1, s) # stk"])
    using source_result run located matched
    apply simp
    done
next
  case (ScopeBody body n n1 en scope_ex E0 C0 residual v sites)
  obtain body_n body_en body_ex Eb Cb where body_comp:
      "compile Pi lay body (n + 1) =
       (body_n, body_en, body_ex, Eb, Cb)"
    by (cases "compile Pi lay body (n + 1)") auto
  have parent_shape:
      "scope_ex = body_n \<and>
       E = insert (n, EA_Enter, body_en) Eb \<and>
       C = insert (n, body_ex, body_n) Cb"
    using ScopeBody.prems(1) ScopeBody.hyps(1) body_comp by auto
  have sub_edges: "Eb \<subseteq> edges g"
    using ScopeBody.prems(2) parent_shape by blast
  have sub_combines: "Cb \<subseteq> combines g"
    using ScopeBody.prems(3) parent_shape by blast
  have frame_assoc:
      "(sites @ [(n, scope_ex)]) @ suffix =
       sites @ ([(n, scope_ex)] @ suffix)"
    by simp
  show ?case
  proof (rule SeqSE[OF ScopeBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Restore, s, frs)"
    have input_frames:
        "frames_match
          (sites @ ([(n, scope_ex)] @ suffix)) frs stk"
      using ScopeBody.prems(5) frame_assoc by simp
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (body_ex, s, stk1)"
        and body_frames:
          "frames_match ([(n, scope_ex)] @ suffix) frs stk1"
      using control_finish_simulation[
          OF body_comp sub_edges ScopeBody.hyps(2)
             residual_skip input_frames]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.Restore body_ex [(n, body_n)]"
      by (rule control_at.ScopeRestore[OF body_comp])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.Restore body_ex [(n, scope_ex)]"
      using raw_location parent_shape by simp
    show ?case
      apply (rule exI[of _ body_ex])
      apply (rule exI[of _ "[(n, scope_ex)]"])
      apply (rule exI[of _ stk1])
      using source_result body_run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' IMP2_Proc.com.Restore,
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    have input_frames:
        "frames_match
          (sites @ ([(n, scope_ex)] @ suffix)) frs stk"
      using ScopeBody.prems(5) frame_assoc by simp
    obtain v' inner_sites stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay body (n + 1) inner' v' inner_sites"
        and matched:
          "frames_match
            (inner_sites @ ([(n, scope_ex)] @ suffix))
            frs1 stk'"
      using ScopeBody.IH[
          OF body_comp sub_edges sub_combines ScopeBody.prems(4)
             input_frames inner_step]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          (IMP2_Proc.com.Seq inner' IMP2_Proc.com.Restore)
          v' (inner_sites @ [(n, scope_ex)])"
      by (rule control_at.ScopeBody[
            OF ScopeBody.hyps(1) inner_control])
    have output_frames:
        "frames_match
          ((inner_sites @ [(n, scope_ex)]) @ suffix)
          frs1 stk'"
      using matched by simp
    show ?case
      using source_result run raw_location output_frames by blast
  qed
next
  case (ScopeRestore body n body_n body_en body_ex Eb Cb)
  have parent_shape:
      "ex = body_n \<and>
       (n, body_ex, body_n) \<in> C"
    using ScopeRestore.prems(1) ScopeRestore.hyps(1) by auto
  have combine: "(n, body_ex, body_n) \<in> combines g"
    using ScopeRestore.prems(3) parent_shape by blast
  show ?case
  proof (rule RestoreSE[OF ScopeRestore.prems(6)])
    fix saved outer
    assume source_frames: "frs = saved # outer"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.SKIP,
           IMP2_Globals.combine_states saved s, outer)"
    have stack_shape:
        "\<exists>stk0.
          stk = (n, body_n, saved) # stk0 \<and>
          frames_match suffix outer stk0"
      using ScopeRestore.prems(5) source_frames
      by (cases stk) auto
    then obtain stk0 where concrete_stack:
        "stk = (n, body_n, saved) # stk0"
        and outer_frames: "frames_match suffix outer stk0"
      by blast
    have concrete:
        "cstep g (body_ex, s, stk)
          (body_n, IMP2_Globals.combine_states saved s, stk0)"
      unfolding concrete_stack
      by (rule cstep.Return[OF combine])
    have run:
        "star (cstep g) (body_ex, s, stk)
          (body_n, IMP2_Globals.combine_states saved s, stk0)"
      by (rule cstep_star_single[OF concrete])
    have finished:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.SKIP ex []"
      by (rule control_at.ScopeDone[OF ScopeRestore.prems(1)])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Scope body) n
          IMP2_Proc.com.SKIP body_n []"
      using finished parent_shape by simp
    have result_cmd: "residual' = IMP2_Proc.com.SKIP"
      and result_store:
        "s' = IMP2_Globals.combine_states saved s"
      and result_frames: "frs' = outer"
      using source_result by simp_all
    show ?case
      apply (rule exI[of _ body_n])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk0])
      apply (intro conjI)
       apply (subst result_store)
       apply (rule run)
       using result_cmd located apply simp
      using result_frames outer_frames apply simp
      done
  qed
next
  case ScopeDone
  then show ?case by (elim SkipSE)
next
  case (CallHead p n)
  show ?case
  proof (rule CallSE[OF CallHead.prems(6)])
    fix body
    assume body: "Pi p = Some body"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore,
           enter_state s, s # frs)"
    have source_pi: "source_pi Pi"
      using CallHead.prems(4)
      unfolding proc_layout_sound_def
      by (elim conjE) assumption
    have source_body: "source_com body"
      using source_pi body unfolding source_pi_def by auto
    have layout_complete:
        "\<forall>p body. Pi p = Some body \<longrightarrow>
          (\<exists>en ex Ns Ep Cp.
            lay p = Some (en, ex, Ns, Ep, Cp))"
      using CallHead.prems(4)
      unfolding proc_layout_sound_def
      by (elim conjE) assumption
    obtain proc_en proc_ex Ns Ep Cp where lookup:
        "lay p = Some (proc_en, proc_ex, Ns, Ep, Cp)"
      using layout_complete[rule_format, OF body] by blast
    have layout_fragments:
        "\<forall>p body en ex Ns Ep Cp.
          Pi p = Some body \<longrightarrow>
          lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
          (\<exists>finish.
            compile Pi lay body en =
              (finish, en, ex, Ep, Cp)) \<and>
          Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g"
      using CallHead.prems(4)
      unfolding proc_layout_sound_def
      by (elim conjE) assumption
    obtain finish where body_comp:
        "compile Pi lay body proc_en =
         (finish, proc_en, proc_ex, Ep, Cp)"
      using layout_fragments[rule_format, OF body lookup] by blast
    have call_shape:
        "(n, EA_Enter, proc_en) \<in> E \<and>
         (n, proc_ex, n + 1) \<in> C"
      using CallHead.prems(1) lookup by auto
    have enter_edge:
        "(n, EA_Enter, proc_en) \<in> edges g"
      using CallHead.prems(2) call_shape by blast
    have combine:
        "(n, proc_ex, n + 1) \<in> combines g"
      using CallHead.prems(3) call_shape by blast
    have concrete:
        "cstep g (n, s, stk)
          (proc_en, enter_state s, (n, n + 1, s) # stk)"
      by (rule cstep.Call[OF enter_edge combine])
    have run:
        "star (cstep g) (n, s, stk)
          (proc_en, enter_state s, (n, n + 1, s) # stk)"
      by (rule cstep_star_single[OF concrete])
    have body_control:
        "control_at Pi lay body proc_en body proc_en []"
      by (rule control_at_initial[OF source_body])
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Call p) n
          (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore)
          proc_en ([] @ [(n, n + 1)])"
      by (rule control_at.CallBody[
            OF body lookup body_comp body_control])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Call p) n
          (IMP2_Proc.com.Seq body IMP2_Proc.com.Restore)
          proc_en [(n, n + 1)]"
      using raw_location by simp
    have matched:
        "frames_match ([(n, n + 1)] @ suffix) (s # frs)
          ((n, n + 1, s) # stk)"
      using CallHead.prems(5) by simp
    show ?case
      apply (rule exI[of _ proc_en])
      apply (rule exI[of _ "[(n, n + 1)]"])
      apply (rule exI[of _ "(n, n + 1, s) # stk"])
      using source_result run located matched
      apply simp
      done
  qed
next
  case (CallBody p body proc_en proc_ex Ns Ep Cp n1 body_en Eb Cb
      residual v sites n)
  have proc_sound:
      "(\<exists>finish.
         compile Pi lay body proc_en =
           (finish, proc_en, proc_ex, Ep, Cp)) \<and>
       Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g"
    using CallBody.prems(4) CallBody.hyps(1,2)
    unfolding proc_layout_sound_def by blast
  then obtain finish where canonical:
      "compile Pi lay body proc_en =
       (finish, proc_en, proc_ex, Ep, Cp)"
      and proc_edges: "Ep \<subseteq> edges g"
      and proc_combines: "Cp \<subseteq> combines g"
    by blast
  have output_eq: "Eb = Ep \<and> Cb = Cp"
    using CallBody.hyps(3) canonical by simp
  have sub_edges: "Eb \<subseteq> edges g"
    using proc_edges output_eq by simp
  have sub_combines: "Cb \<subseteq> combines g"
    using proc_combines output_eq by simp
  have frame_assoc:
      "(sites @ [(n, n + 1)]) @ suffix =
       sites @ ([(n, n + 1)] @ suffix)"
    by simp
  show ?case
  proof (rule SeqSE[OF CallBody.prems(6)])
    assume residual_skip: "residual = IMP2_Proc.com.SKIP"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.Restore, s, frs)"
    have input_frames:
        "frames_match
          (sites @ ([(n, n + 1)] @ suffix)) frs stk"
      using CallBody.prems(5) frame_assoc by simp
    obtain stk1 where body_run:
        "star (cstep g) (v, s, stk) (proc_ex, s, stk1)"
        and body_frames:
          "frames_match ([(n, n + 1)] @ suffix) frs stk1"
      using control_finish_simulation[
          OF CallBody.hyps(3) sub_edges CallBody.hyps(4)
             residual_skip input_frames]
      by blast
    have located:
        "control_at Pi lay (IMP2_Proc.com.Call p) n
          IMP2_Proc.com.Restore proc_ex [(n, n + 1)]"
      using CallBody.hyps(2)
      by (rule control_at.CallRestore)
    show ?case
      apply (rule exI[of _ proc_ex])
      apply (rule exI[of _ "[(n, n + 1)]"])
      apply (rule exI[of _ stk1])
      using source_result body_run located body_frames
      apply simp
      done
  next
    fix inner' t frs1
    assume source_result:
        "(residual', s', frs') =
         (IMP2_Proc.com.Seq inner' IMP2_Proc.com.Restore,
          t, frs1)"
       and inner_step:
         "pstep Pi (residual, s, frs) (inner', t, frs1)"
    have input_frames:
        "frames_match
          (sites @ ([(n, n + 1)] @ suffix)) frs stk"
      using CallBody.prems(5) frame_assoc by simp
    obtain v' inner_sites stk' where run:
        "star (cstep g) (v, s, stk) (v', t, stk')"
        and inner_control:
          "control_at Pi lay body proc_en inner' v' inner_sites"
        and matched:
          "frames_match
            (inner_sites @ ([(n, n + 1)] @ suffix))
            frs1 stk'"
      using CallBody.IH[
          OF CallBody.hyps(3) sub_edges sub_combines CallBody.prems(4)
             input_frames inner_step]
      by blast
    have raw_location:
        "control_at Pi lay (IMP2_Proc.com.Call p) n
          (IMP2_Proc.com.Seq inner' IMP2_Proc.com.Restore)
          v' (inner_sites @ [(n, n + 1)])"
      by (rule control_at.CallBody[
            OF CallBody.hyps(1) CallBody.hyps(2)
               CallBody.hyps(3) inner_control])
    have output_frames:
        "frames_match
          ((inner_sites @ [(n, n + 1)]) @ suffix)
          frs1 stk'"
      using matched by simp
    show ?case
      using source_result run raw_location output_frames by blast
  qed
next
  case (CallRestore p proc_en proc_ex Ns Ep Cp n)
  have call_shape: "(n, proc_ex, n + 1) \<in> C"
    using CallRestore.prems(1) CallRestore.hyps(1) by auto
  have combine: "(n, proc_ex, n + 1) \<in> combines g"
    using CallRestore.prems(3) call_shape by blast
  show ?case
  proof (rule RestoreSE[OF CallRestore.prems(6)])
    fix saved outer
    assume source_frames: "frs = saved # outer"
       and source_result:
         "(residual', s', frs') =
          (IMP2_Proc.com.SKIP,
           IMP2_Globals.combine_states saved s, outer)"
    have stack_shape:
        "\<exists>stk0.
          stk = (n, n + 1, saved) # stk0 \<and>
          frames_match suffix outer stk0"
      using CallRestore.prems(5) source_frames
      by (cases stk) auto
    then obtain stk0 where concrete_stack:
        "stk = (n, n + 1, saved) # stk0"
        and outer_frames: "frames_match suffix outer stk0"
      by blast
    have concrete:
        "cstep g (proc_ex, s, stk)
          (n + 1, IMP2_Globals.combine_states saved s, stk0)"
      unfolding concrete_stack
      by (rule cstep.Return[OF combine])
    have run:
        "star (cstep g) (proc_ex, s, stk)
          (n + 1, IMP2_Globals.combine_states saved s, stk0)"
      by (rule cstep_star_single[OF concrete])
    have located:
        "control_at Pi lay (IMP2_Proc.com.Call p) n
          IMP2_Proc.com.SKIP (n + 1) []"
      using CallRestore.hyps(1)
      by (rule control_at.CallDone)
    have result_cmd: "residual' = IMP2_Proc.com.SKIP"
      and result_store:
        "s' = IMP2_Globals.combine_states saved s"
      and result_frames: "frs' = outer"
      using source_result by simp_all
    show ?case
      apply (rule exI[of _ "n + 1"])
      apply (rule exI[of _ "[]"])
      apply (rule exI[of _ stk0])
      apply (intro conjI)
       apply (subst result_store)
       apply (rule run)
      using result_cmd located apply simp
      using result_frames outer_frames apply simp
      done
  qed
next
  case CallDone
  then show ?case by (elim SkipSE)
qed

theorem concrete_program_step_match:
  assumes wf: "wf_compile_input Pi ps main"
      and matched: "concrete_program_match Pi ps main src cf"
      and step: "pstep Pi src src'"
  shows "\<exists>cf'.
    star (cstep (compile_prog Pi ps main)) cf cf' \<and>
    concrete_program_match Pi ps main src' cf'"
proof -
  obtain residual s frs where src: "src = (residual, s, frs)"
    by (cases src) auto
  obtain residual' s' frs' where src':
      "src' = (residual', s', frs')"
    by (cases src') auto
  obtain v t stk where cf: "cf = (v, t, stk)"
    by (cases cf) auto
  obtain nproc lay Eproc Cproc nend main_en main_ex Emain Cmain sites
    where store: "s = t"
      and procs:
        "compile_procs_list Pi ps (\<lambda>_. None) 0 =
          (nproc, lay, Eproc, Cproc)"
      and main_comp:
        "compile Pi lay main nproc =
          (nend, main_en, main_ex, Emain, Cmain)"
      and control:
        "control_at Pi lay main nproc residual v sites"
      and frames: "frames_match sites frs stk"
    using matched
    unfolding concrete_program_match_def src cf
    by auto
  have edge_sets:
      "edges (compile_prog Pi ps main) = Eproc \<union> Emain"
    by (rule compile_prog_sets(1)[OF procs main_comp])
  have combine_sets:
      "combines (compile_prog Pi ps main) = Cproc \<union> Cmain"
    by (rule compile_prog_sets(2)[OF procs main_comp])
  have main_edges:
      "Emain \<subseteq> edges (compile_prog Pi ps main)"
    unfolding edge_sets by blast
  have main_combines:
      "Cmain \<subseteq> combines (compile_prog Pi ps main)"
    unfolding combine_sets by blast
  have layout_sound:
      "proc_layout_sound Pi lay (compile_prog Pi ps main)"
  proof (unfold proc_layout_sound_def, intro conjI)
    show "source_pi Pi"
      using wf unfolding wf_compile_input_def by blast
    show "\<forall>p body. Pi p = Some body \<longrightarrow>
      (\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp))"
    proof (intro allI impI)
      fix p body
      assume body: "Pi p = Some body"
      show "\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp)"
        using compile_procs_list_complete[OF wf procs body] .
    qed
    show "\<forall>p body en ex Ns Ep Cp.
      Pi p = Some body \<longrightarrow>
      lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
      (\<exists>finish.
        compile Pi lay body en = (finish, en, ex, Ep, Cp)) \<and>
      Ep \<subseteq> edges (compile_prog Pi ps main) \<and>
      Cp \<subseteq> combines (compile_prog Pi ps main)"
    proof (intro allI impI)
      fix p body en ex Ns Ep Cp
      assume body: "Pi p = Some body"
      assume lookup: "lay p = Some (en, ex, Ns, Ep, Cp)"
      obtain finish where compiled_body:
          "compile Pi lay body en = (finish, en, ex, Ep, Cp)"
        using compile_procs_list_body[OF wf procs body lookup] by blast
      have fragment: "Ep \<subseteq> Eproc \<and> Cp \<subseteq> Cproc"
        by (rule compile_procs_list_fragment[OF procs lookup])
      show "(\<exists>finish.
          compile Pi lay body en = (finish, en, ex, Ep, Cp)) \<and>
          Ep \<subseteq> edges (compile_prog Pi ps main) \<and>
          Cp \<subseteq> combines (compile_prog Pi ps main)"
        using compiled_body fragment edge_sets combine_sets by blast
    qed
  qed
  have source_step:
      "pstep Pi (residual, s, frs) (residual', s', frs')"
    using step unfolding src src' .
  have frames_suffix: "frames_match (sites @ []) frs stk"
    using frames by simp
  obtain v' sites' stk' where run:
      "star (cstep (compile_prog Pi ps main))
        (v, s, stk) (v', s', stk')"
      and control':
        "control_at Pi lay main nproc residual' v' sites'"
      and frames': "frames_match sites' frs' stk'"
    using control_step_simulation[
      OF main_comp main_edges main_combines layout_sound
        control frames_suffix source_step]
    by auto
  show ?thesis
  proof (rule exI[where x = "(v', s', stk')"], intro conjI)
    show "star (cstep (compile_prog Pi ps main)) cf (v', s', stk')"
      using run store unfolding cf by simp
    show "concrete_program_match Pi ps main src' (v', s', stk')"
      unfolding concrete_program_match_def src'
      using procs main_comp control' frames'
      by auto
  qed
qed

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

theorem concrete_source_reaches_side_analyse_eff:
  fixes s0 :: "'a::sound_domain abs_state"
    and etf :: "('g::finite, 'a) effectful_domain_transfer"
    and gseed :: 'g
  assumes wf: "wf_compile_input Pi ps main"
      and run: "psteps Pi (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm:
        "threefold_mono
          (side_cfg_T_eff (compile_prog Pi ps main) etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
      and dom:
        "\<And>v.
          cfg_reaches (compile_prog Pi ps main)
            (cfg_entry (compile_prog Pi ps main)) v \<Longrightarrow>
          side_cfg_solve_dom_eff
            (compile_prog Pi ps main) etf bot s0 gseed v"
  shows "\<exists>v t stk.
    concrete_program_match Pi ps main src' (v, t, stk) \<and>
    t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
proof -
  have source_main: "source_com main"
    using wf unfolding wf_compile_input_def by blast
  interpret sim: compiled_source_simulation
      Pi ps main "compile_prog Pi ps main"
      "concrete_program_match Pi ps main"
  proof
    show "compile_prog Pi ps main = compile_prog Pi ps main"
      by simp
    show "wf_compile_input Pi ps main"
      by (rule wf)
    fix t
    show "concrete_program_match Pi ps main
      (main, t, []) (cfg_entry (compile_prog Pi ps main), t, [])"
      by (rule concrete_program_initial_match[OF source_main])
    fix source source' concrete
    assume matched:
        "concrete_program_match Pi ps main source concrete"
       and stepped: "pstep Pi source source'"
    show "\<exists>concrete'.
      star (cstep (compile_prog Pi ps main)) concrete concrete' \<and>
      concrete_program_match Pi ps main source' concrete'"
      by (rule concrete_program_step_match[OF wf matched stepped])
  qed
  show ?thesis
    by (rule sim.source_reaches_side_analyse_eff[
          OF run se tfm cone init dom])
qed

locale source_to_analysis_bridge =
  fixes Pi :: proc_table
    and ps :: "pname list"
    and main :: IMP2_Proc.com
    and g :: cfg
    and s :: store
    and src' :: "(IMP2_Proc.com \<times> store \<times> frame list)"
    and etf :: "('g::finite, 'a::sound_domain) effectful_domain_transfer"
    and s0 :: "'a abs_state"
    and gseed :: 'g
  assumes g_def: "g = compile_prog Pi ps main"
      and wf: "wf_compile_input Pi ps main"
      and run: "psteps Pi (main, s, []) src'"
      and se: "sound_effectful_transfer etf"
      and tfm: "threefold_mono (side_cfg_T_eff g etf bot s0 gseed)"
      and cone: "cone_compatible_etf etf"
      and init: "s \<in> \<lbrakk>s0\<rbrakk>"
begin

theorem source_reaches_side_analyse_eff:
  assumes dom:
    "\<And>v. cfg_reaches g (cfg_entry g) v \<Longrightarrow>
      side_cfg_solve_dom_eff g etf bot s0 gseed v"
  shows "\<exists>v t stk.
     concrete_program_match Pi ps main src' (v, t, stk) \<and>
     t \<in> \<lbrakk>side_analyse_eff Pi ps main etf bot s0 gseed v\<rbrakk>"
proof -
  have tfm':
      "threefold_mono (side_cfg_T_eff (compile_prog Pi ps main) etf bot s0 gseed)"
    using tfm g_def by simp
  have dom':
      "\<And>v. cfg_reaches (compile_prog Pi ps main)
            (cfg_entry (compile_prog Pi ps main)) v \<Longrightarrow>
          side_cfg_solve_dom_eff
            (compile_prog Pi ps main) etf bot s0 gseed v"
    using dom g_def by simp
  show ?thesis
    by (rule concrete_source_reaches_side_analyse_eff[
          OF wf run se tfm' cone init dom'])
qed

end


end
