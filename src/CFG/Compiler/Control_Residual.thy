theory Control_Residual
  imports Compile_Invariants
begin

subsection \<open>Residual commands inside compiled fragments\<close>

type_synonym frame_site = "pp \<times> pp \<times> vname option"

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
    "source_com cbody \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b cbody) n
       (IMP2_Proc.com.While b cbody) n []"
| WhileUnfolded:
    "source_com cbody \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b cbody) n
       (IMP2_Proc.com.If b
         (IMP2_Proc.com.Seq cbody (IMP2_Proc.com.While b cbody))
         IMP2_Proc.com.SKIP) n []"
| WhileBody:
    "source_com cbody \<Longrightarrow>
     control_at Pi lay cbody (n + 1) residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b cbody) n
       (IMP2_Proc.com.Seq residual (IMP2_Proc.com.While b cbody))
       v sites"
| WhileDone:
    "compile Pi lay (IMP2_Proc.com.While b cbody) n =
       (n1, en, ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.While b cbody) n
       IMP2_Proc.com.SKIP ex []"
| ScopeHead:
    "source_com cbody \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope cbody) n
       (IMP2_Proc.com.Scope cbody) n []"
| ScopeBody:
    "compile Pi lay (IMP2_Proc.com.Scope cbody) n =
       (n1, en, scope_ex, E, C) \<Longrightarrow>
     control_at Pi lay cbody (n + 1) residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope cbody) n
       (IMP2_Proc.com.Seq residual (IMP2_Proc.com.RestoreInternal None))
       v (sites @ [(n, scope_ex, None)])"
| ScopeRestore:
    "compile Pi lay cbody (n + 1) = (n1, en, body_ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope cbody) n
       (IMP2_Proc.com.RestoreInternal None) body_ex [(n, n1, None)]"
| ScopeDone:
    "compile Pi lay (IMP2_Proc.com.Scope cbody) n =
       (n1, en, scope_ex, E, C) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Scope cbody) n
       IMP2_Proc.com.SKIP scope_ex []"
| CallHead:
    "control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
       (IMP2_Proc.com.Call dst p actuals) n []"
| CallBody:
    "Pi p = Some decl \<Longrightarrow>
     lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     compile Pi lay (body decl) proc_en =
       (n1, body_en, proc_ex, E, C) \<Longrightarrow>
     control_at Pi lay (body decl) proc_en residual v sites \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
       (IMP2_Proc.com.Seq residual (IMP2_Proc.com.RestoreInternal (result decl)))
       v (sites @ [(n, n + 1, dst)])"
| CallRestore:
    "Pi p = Some decl \<Longrightarrow>
     lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
       (IMP2_Proc.com.RestoreInternal (result decl)) proc_ex [(n, n + 1, dst)]"

| CallDone:
    "Pi p = Some decl \<Longrightarrow>
     lay p = Some (proc_en, proc_ex, Ns, Ep, Cp) \<Longrightarrow>
     control_at Pi lay (IMP2_Proc.com.Call dst p actuals) n
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
  case (RestoreInternal r)
  then show ?case by simp
qed

lemma compile_endpoint_shape_entry:
  "(case compile_endpoint_shape Pi lay cmd n of
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
      "compile_endpoint_shape Pi lay c1 n = (n1, en1, ex1)"
    by (cases "compile_endpoint_shape Pi lay c1 n") auto
  obtain n2 en2 ex2 where second:
      "compile_endpoint_shape Pi lay c2 n1 = (n2, en2, ex2)"
    by (cases "compile_endpoint_shape Pi lay c2 n1") auto
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
  case (RestoreInternal r)
  then show ?case by simp
qed

lemma compile_entry_eq:
  assumes comp: "compile Pi lay cmd n = (n', en, ex, E, C)"
  shows "en = n"
proof -
  have shape:
      "compile_endpoints Pi lay cmd n =
        compile_endpoint_shape Pi lay cmd n"
    by (rule compile_endpoints_eq_shape)
  show ?thesis
    using shape compile_endpoint_shape_entry[of Pi lay cmd n] comp
    unfolding compile_endpoints_def
    by (cases "compile_endpoint_shape Pi lay cmd n") simp
qed

lemma compile_procs_list_body:
  assumes wf: "wf_compile_input Pi ps main"
      and procs:
        "compile_procs_list Pi ps (\<lambda>_. None) 0 =
          (nout, full_lay, Eall, C_all)"
      and proc: "Pi p = Some decl"
      and lookup:
        "full_lay p = Some (en, ex, Ns, Ep, Cp)"
  shows "\<exists>finish.
    compile Pi full_lay (body decl) en = (finish, en, ex, Ep, Cp)"
proof -
  obtain nbase base_lay where layout:
      "compile_procs_layout Pi ps (\<lambda>_. None) 0 =
        (nbase, base_lay)"
      and bodies:
      "compile_procs_bodies Pi ps base_lay (\<lambda>_. None) 0 =
        (nout, full_lay, Eall, C_all)"
    using compile_procs_list_decompose[OF procs] by blast
  have member: "p \<in> set ps"
    using wf proc by (auto simp: wf_compile_input_def)
  have distinct: "distinct ps"
    using wf by (auto simp: wf_compile_input_def)
  have compiled_info:
      "\<exists>start finish. compile Pi base_lay (body decl) start =
        (finish, en, ex, Ep, Cp)"
    by (rule compile_procs_bodies_lookup[
          OF distinct _ bodies member proc lookup])
       simp
  then obtain start finish where compiled_base:
      "compile Pi base_lay (body decl) start =
        (finish, en, ex, Ep, Cp)"
    by blast
  have agree: "layouts_agree base_lay full_lay"
    by (rule compile_procs_pass_layouts_agree[
          OF wf layout bodies])
  have same:
      "compile Pi base_lay (body decl) start =
       compile Pi full_lay (body decl) start"
    by (rule compile_layouts_agree[OF agree])
  have start: "start = en"
    by (rule sym, rule compile_entry_eq[OF compiled_base])
  have compiled_full:
      "compile Pi full_lay (body decl) start =
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
      and proc: "Pi p = Some decl"
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
    using wf proc by (auto simp: wf_compile_input_def)
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
      OF wf layout bodies member proc base]
    by blast
  show ?thesis using full by blast
qed

end
