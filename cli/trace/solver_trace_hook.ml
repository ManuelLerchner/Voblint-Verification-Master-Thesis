(* The recording side of the solver tracer.

   The build patches the generated solver (trace/patch_generated.ml) with calls
   into this module. The solver is polymorphic in its unknowns and values, so an
   event keeps them as [Obj.t]; the generated code also installs, where the
   concrete types are in scope, the functions that read them back. Rendering
   happens after the solve, in Solver_trace, once every printer is installed.

   With [enabled] false every hook is one branch on a reference: tracing is
   opt-in and costs nothing otherwise. Nothing here feeds back into the solve. *)

type event =
  | Solve of Obj.t  (** a local unknown whose right-hand side is evaluated *)
  | Query_local of Obj.t * Obj.t  (** current unknown, queried local unknown *)
  | Value_local of Obj.t * Obj.t * Obj.t
      (** current, queried, the value the query returned *)
  | Query_global of Obj.t * Obj.t * Obj.t  (** current, global unknown, value *)
  | Side of Obj.t * Obj.t * Obj.t
      (** current, global unknown, published value *)
  | Update_global of Obj.t * Obj.t * Obj.t  (** global unknown, old, new *)
  | Update_local of Obj.t * Obj.t * Obj.t  (** local unknown, old, new *)
  | Answer of Obj.t * Obj.t
      (** current unknown, value of its right-hand side *)
  | Route of Obj.t * Obj.t * Obj.t
      (** calling local unknown, entry value (local part), routed context *)

let enabled = ref false

(* Route is also consulted after the solve, to read the result back; only
   calls made while solving are events. *)
let solving = ref false
let events : event list ref = ref []
let record e = if !enabled && !solving then events := e :: !events
let solve x = record (Solve x)
let query_local x y = record (Query_local (x, y))
let value_local x y d = record (Value_local (x, y, d))
let query_global x y d = record (Query_global (x, y, d))
let side x y d = record (Side (x, y, d))
let update_global y o n = record (Update_global (y, o, n))
let update_local x o n = record (Update_local (x, o, n))
let answer x d = record (Answer (x, d))
let route u d c = record (Route (u, d, c))

let start_solve () =
  events := [];
  solving := true

let end_solve () = solving := false

(* Readers installed by the generated code. [state_local] and [state_global]
   read the local and the global half of a solver value back into the result
   state the report shows; [local_part] does the same for a bare local value
   such as an entry value. [view] renders such a state, [context] renders a
   context. Each returns an [Obj.t] of the exported result types. *)
let no_reader : Obj.t -> Obj.t =
 fun _ -> failwith "solver trace: reader not installed"

let state_local = ref no_reader
let state_global = ref no_reader
let local_part = ref no_reader
let view = ref no_reader
let context = ref no_reader

let install_readers ~state_local:sl ~state_global:sg ~local_part:lp =
  if !enabled then begin
    state_local := sl;
    state_global := sg;
    local_part := lp
  end

(* The global unknowns have a generated datatype that depends on the context
   mode. The generated module installs, where that type is fixed, a decoder by
   constructor: [None] for the analysis global, [Some (entry node, context)]
   for an activation seed. *)
let global : (Obj.t -> (Obj.t * Obj.t) option) ref =
  ref (fun _ -> failwith "solver trace: global decoder not installed")

let install_global decode = if !enabled then global := decode

let install_views ~view:v ~context:c =
  if !enabled then begin
    view := v;
    context := c
  end

let recorded () = List.rev !events
