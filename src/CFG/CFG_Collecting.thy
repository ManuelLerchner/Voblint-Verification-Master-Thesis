theory CFG_Collecting
  imports CFG_Runs_To_Bridge
begin

(*
  CFG collecting semantics and source-level surface (umbrella).

  Core spec: cfg_collect (per-pp lfp) and cfg_edges_collect (paths).
  Canonical soundness uses cfg_collect at every program point (Pipeline).

  runs_to c s t is definitional exit sugar (runs_to_def), not a second
  operational semantics. Small-step is linked via runs_to_iff_small_step.

  Implementation split across:
    CFG_Edges_Collect, CFG_Collecting_Core, CFG_Compound_Paths,
    CFG_Path_Bridge, CFG_Runs_To_Bridge.
*)

end
