theory Config_Tables
  imports
    Analysis_Config
begin

section \<open>The resolver's support matrix\<close>

text \<open>
  GENERATED FILE. Source: \<^verbatim>\<open>assembly/analyses.yaml\<close>; generator:
  \<^verbatim>\<open>scripts/gen_analysis_assembly.py\<close>. Regenerate with the generator
  rather than hand-editing; a drift check compares regenerated output against
  this file.

  One table over domain, solver and context. A cell is supported when the registry
  publishes a route there: at \<^const>\<open>Ctx_None\<close> that means a published
  report, at the two context modes a routed instance. \<^const>\<open>None\<close>
  everywhere else, and an unsupported cell is a missing proof, never a missing
  case.

  The same list decides \<open>analyse_with_solver\<close>, so the two cannot disagree
  about what is supported.

  A call-string cell carries the shortest bound its domain publishes, and the
  resolver rejects anything below it: every domain sets that to 1 today, so
  \<open>k = 0\<close> answers \<^const>\<open>None\<close>. That is a usability decision
  rather than a soundness one. \<open>cs_route\<close> at \<open>k = 0\<close> routes every
  activation to the context \<^term>\<open>[]\<close>, as well-defined and as finite as
  any other bound, and it is not \<^const>\<open>Ctx_None\<close> in disguise: the
  equation system stays call-string keyed, and the published result carries
  call-string contexts, all of them empty. Lowering the bound is a real
  behaviour change, not a relaxation of a check.
\<close>

fun resolve_analysis_config ::
    "analysis_config \<Rightarrow> analysis_plan option" where
  "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_PerOrigin)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Sign_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Sign_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Sign_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Sign_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Interval Solver_Warrow)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Interval s)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Warrow)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState s)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Interval_CallString Solver_Warrow k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Interval_CallString s k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Parity Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Parity Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Parity Solver_PerOrigin)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Parity_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Parity_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Parity_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Parity_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_Warrow,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Parity_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Int Solver_Warrow)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some s, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Int s)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Int_EntryState Solver_Warrow)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Int_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Int_EntryState Solver_Warrow)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Int_CallString Solver_Warrow k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Int_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Int_CallString Solver_Warrow k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Congruence Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Congruence Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_None \<rparr>
     = Some (Plan_Congruence Solver_PerOrigin)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Congruence_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Join,
        cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Congruence_EntryState Solver_Join)"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Warrow,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Congruence_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Join,
        cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Congruence_CallString Solver_Join k))"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_PerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_Warrow,
        cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config
     \<lparr> cfg_domain = Congruence_Analysis, cfg_solver = Some Solver_WarrowPerOrigin,
        cfg_context = Ctx_CallString k \<rparr>
     = None"

definition valid_analysis_config :: "analysis_config \<Rightarrow> bool" where
  "valid_analysis_config cfg = (resolve_analysis_config cfg \<noteq> None)"

end
