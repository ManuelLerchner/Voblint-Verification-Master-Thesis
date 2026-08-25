// The vocabulary this thesis assumes, in one place. Entries mirror
// docs/GLOSSARY.md, which is the project's own record; keeping the wording
// close means a reader who moves between the two is not learning two
// vocabularies for one system.
//
// First use in the text expands to "control-flow graph (CFG)" and later uses
// are short, so the prose never has to choose between being readable on page 3
// and being readable on page 93.

#let entries = (
  (key: "vimp", short: "VIMP", long: "the source language",
   description: [The procedural imperative language this thesis analyses:
     structured commands, procedures with explicit returns, and runtime-only
     restore and unwind commands.]),
  (key: "cfg", short: "CFG", long: "control-flow graph",
   description: [The procedure-aware graph a program compiles to. Local edges
     carry an edge action; call sites live in a separate `calls` relation, with
     `FunctionEntry` and `FunctionResult` nodes as procedure boundaries.]),
  (key: "ai", short: "AI", long: "abstract interpretation",
   description: [Computing a sound over-approximation of every execution by
     interpreting the program over an abstract domain rather than over
     concrete values.]),
  (key: "td", short: "TD", long: "top-down solver",
   description: [The vendored, verified fixpoint solver. Its side-effecting
     extension is what a mixed flow-sensitive analysis needs.]),
  (key: "dg", short: "D/G", long: "local/global framework",
   description: [The interface splitting an analysis into a flow-sensitive
     local fact and a shared global fact routed through side effects --
     Goblint's `D` and `G`.]),
  (key: "ltr", short: "LTR", long: "activation-local trace",
   description: [A trace that keeps one activation plus a structural link to
     its caller, rather than the whole stack. What makes the collecting
     semantics finite per activation.]),
  (key: "cli", short: "CLI", long: "command-line interface",
   description: [The unverified OCaml harness around the code generated from
     the formalization.]),
  (key: "ast", short: "AST", long: "abstract syntax tree",
   description: [The parsed form of a source program; the first object inside
     the trust boundary.]),
  (key: "afp", short: "AFP", long: "Archive of Formal Proofs",
   description: [The refereed library of Isabelle developments.]),
)
