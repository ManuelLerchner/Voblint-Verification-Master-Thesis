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

let emit channel event =
  if !enabled then
    try events := (channel, Obj.repr (event ())) :: !events with _ -> ()

(* Hands the events over and forgets them: the browser adapter lives across
   runs, and the events keep the run's solver values alive. *)
let recorded () =
  let es = List.rev !events in
  events := [];
  es
