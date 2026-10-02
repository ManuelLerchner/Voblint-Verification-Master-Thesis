(* The one module the handwritten OCaml names: the Isabelle export, re-exposed.

   Voblint_Generated is written by `pixi run codegen` from
   src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy. Its signature is
   the export's root list, so this facade adds nothing and hides nothing; it
   exists so that consumers do not spell the generated file's packaging, and a
   change to that packaging touches this file alone.

   The analysis report run_voblint returns is opaque here: the export lists no
   selector of analysis_report, and render_report is the only reader. *)

include Voblint_Generated.Generated
