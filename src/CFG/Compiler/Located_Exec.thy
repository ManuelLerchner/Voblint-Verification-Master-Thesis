theory Located_Exec
  imports Control_Residual CFG_Transfer
begin

subsection \<open>Located CFG execution\<close>

type_synonym cframe = "pp \<times> pp \<times> store"
type_synonym cconf = "pp \<times> store \<times> cframe list"
fun frames_match ::
  "frame_site list \<Rightarrow> frame list \<Rightarrow> cframe list \<Rightarrow> bool"
where
  "frames_match [] [] [] = True"
| "frames_match ((call, ret, dst') # sites) (Frame saved dst # frs)
     ((call', ret', saved') # stk) =
     (call = call' \<and> ret = ret' \<and> dst' = dst \<and> saved = saved' \<and>
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

lemma cfg_exit_compile_prog:
  assumes procs:
    "compile_procs_list Pi ps (\<lambda>_. None) 0 =
      (nproc, lay, Eproc, Cproc)"
      and main_comp:
    "compile Pi lay main nproc =
      (nend, main_en, main_ex, Emain, Cmain)"
  shows "cfg_exit (compile_prog Pi ps main) = main_ex"
  using procs main_comp
  unfolding compile_prog_def compile_prog_with_regions_def
  by simp

inductive cstep :: "cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for g where
  Intra:
    "(u, a, v) \<in> edges g \<Longrightarrow>
     \<not> is_enter_action a \<Longrightarrow>
     edge_step a s = Some s' \<Longrightarrow>
     cstep g (u, s, stk) (v, s', stk)"
| Call:
    "(call, EA_Enter xs es, en) \<in> edges g \<Longrightarrow>
     (call, ex, ret, dst) \<in> combines g \<Longrightarrow>
     edge_step (EA_Enter xs es) s = Some s' \<Longrightarrow>
     cstep g (call, s, stk)
       (en, s', (call, ret, s) # stk)"
| Return:
    "(call, ex, ret, dst) \<in> combines g \<Longrightarrow>
     cstep g (ex, t, (call, ret, s) # stk)
       (ret, combine_assign dst (t ret_var) (IMP2_Globals.combine_states s t), stk)"


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
  by (rule cstep.Intra[OF edge]) (simp_all add: is_enter_action_def)

lemma cstep_assign:
  assumes edge: "(u, EA_Assign x a, v) \<in> edges g"
  shows "cstep g (u, s, stk)
    (v, s(x := IMP2_Expr.aval a s), stk)"
  by (rule cstep.Intra[OF edge]) (simp_all add: is_enter_action_def)

lemma cstep_assume:
  assumes edge: "(u, EA_Assume b, v) \<in> edges g"
      and guard: "IMP2_Expr.bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF edge]) (simp_all add: guard is_enter_action_def)

lemma cstep_assume_not:
  assumes edge: "(u, EA_AssumeNot b, v) \<in> edges g"
      and guard: "\<not> IMP2_Expr.bval b s"
  shows "cstep g (u, s, stk) (v, s, stk)"
  by (rule cstep.Intra[OF edge]) (simp_all add: guard is_enter_action_def)

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
    (\<forall>p decl. Pi p = Some decl \<longrightarrow>
      (\<exists>en ex Ns Ep Cp.
        lay p = Some (en, ex, Ns, Ep, Cp))) \<and>
    (\<forall>p decl en ex Ns Ep Cp.
      Pi p = Some decl \<longrightarrow>
      lay p = Some (en, ex, Ns, Ep, Cp) \<longrightarrow>
      (\<exists>finish.
        compile Pi lay (with_result (body decl) (result decl)) en = (finish, en, ex, Ep, Cp)) \<and>
      Ep \<subseteq> edges g \<and> Cp \<subseteq> combines g)"


end
