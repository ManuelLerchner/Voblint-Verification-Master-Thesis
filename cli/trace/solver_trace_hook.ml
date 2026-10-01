(* The target of Isabelle's trace_event.

   Voblint_CLI.Trace_Run maps the HOL constant trace_event to [emit]: the
   exported solver calls it with a channel name and a suspended event at every
   step its traced code equations name. In the logic trace_event returns (), so
   the obligations here are the ones every target-language mapping carries:
   return (), raise nothing, and leave the solver's values alone.

   [emit] forces the suspension only when tracing is on, so an untraced run
   builds no event. This module is compiled before the generated one and cannot
   name its types; it keeps each event as an [Obj.t] under its channel, and
   Solver_trace, which can, reads them back after the run. *)

let enabled = ref false
let events : (string * Obj.t) list ref = ref []

(* At most [limit] events are kept, later ones only counted: a run that never
   finishes would otherwise keep growing the list, and every solver value an
   event names, until it is killed. *)
let limit = ref max_int
let kept = ref 0
let dropped = ref 0

(* Sees each kept event as it is recorded, so a viewer can show the trace of a
   run that is still solving, or never finishes. *)
let listener : (string -> Obj.t -> unit) ref = ref (fun _ _ -> ())

let emit channel event =
  if !enabled then
    try
      if !kept < !limit then begin
        let o = Obj.repr (event ()) in
        events := (channel, o) :: !events;
        incr kept;
        !listener channel o
      end
      else incr dropped
    with _ -> ()

let reset () =
  events := [];
  kept := 0;
  dropped := 0

(* Hands the events over, with how many the limit left out, and forgets them:
   the browser adapter lives across runs, and the events keep the run's solver
   values alive. *)
let recorded () =
  let es = List.rev !events and d = !dropped in
  reset ();
  (es, d)
