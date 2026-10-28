#import "../lib/stats.typ": stat

= Abstract <abstract>

A static analyzer predicts properties of a program without running it, for
example, whether a division can divide by zero, whether an array index stays
within bounds, or whether an assertion always holds. Such an analyzer is _sound_ if
its answers hold in every execution of the program. Developers and verification
tools rely on this guarantee, but commonly used analyzers are themselves complex programs that
may contain bugs. If such a bug makes the analyzer report a property that does not
hold, its users miss exactly the error they wanted to find. Machine-checked
soundness proofs drastically reduce the likelihood of such bugs.

This thesis presents Voblint, short for verified Goblint, a static analyzer
modeled on the Goblint analyzer for C programs. Like Goblint, Voblint translates the program into a
control-flow graph, derives a system of equations from the graph, and solves
the system with a generic solver. Previous work proved a formalization of the solver algorithm
partially correct @stade24 @tilscher26, so whenever it terminates, its result
satisfies the equations. This alone does not make the analyzer sound. The graph
also has to cover every execution of the program, and the equations have to
account for these executions in every calling context. Finally, the reported
answers have to follow from the solver's result. Voblint proves all of these
properties together for VIMP, a small C-like language with integer variables and
recursive procedures, defined for this work. The proof, developed in the proof assistant
Isabelle/HOL, thus covers the analysis from the parsed program to the reported
answers. The main theorem states that the reported answers hold in every state
that a finite execution of the program reaches. For example, if the analyzer proves an
assertion, the assertion holds whenever an execution reaches it. Likewise, the
analyzer is proved to flag every program point where a division can divide by
zero. This guarantee applies whenever the analyzer finishes, since
termination of the solver is not proved for every program.

Voblint distinguishes calls to the same procedure by their calling contexts,
avoiding the loss of precision that would result from merging their values. To prove
these per-context results sound, Voblint introduces _activation traces_, a
semantics that distinguishes individual procedure activations and relates them
to their calling contexts. This
construction fits into a modular soundness proof that follows Goblint's
architecture. Abstract domains, analyses,
and context policies each prove their own soundness properties, and a single
theorem combines them with the solver's correctness. The resulting guarantee
holds for every analysis configuration that Voblint offers. To our knowledge, no
earlier mechanized analyzer combines recursive procedures, calling contexts,
and a verified solver in one soundness proof.

The verified analyzer is exported to executable code, runs in a command-line
tool and a browser playground, and is tested on #stat("corpus.cases") regression
programs. Proofs on concrete programs show that the assumptions of the main
theorem can be met, so the theorem does not hold vacuously. The proof does not
cover parsing, presentation of results, or code generation. Because the theorem
concerns VIMP rather than C, the thesis also documents where the two languages
differ.
