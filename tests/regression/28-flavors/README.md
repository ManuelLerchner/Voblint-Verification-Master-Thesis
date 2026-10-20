# Flavors of abstract interpretation

The examples of David Monniaux's ETAPS 2024 tutorial "Flavors of abstract
interpretation" (HAL hal-04750222) that VIMP can express. Every check holds in
every run, so a PROVED check is in `precision/` and an UNKNOWN one in
`known-imprecision/`.

- Vanilla (finite lattices): `precision/01` (rule of signs), `precision/04` and
  `known-imprecision/05` (an invariant that is not inductive for Sign).
- Coffee (relational domains, paths): `known-imprecision/01` and `02`.
- Fudge (widening and narrowing): `precision/02` and `03`.
- Blackcurrant (policy iteration, guided analysis): `known-imprecision/03` and
  `04`.
- Fiore di latte (arrays, relative completeness) has no VIMP form: VIMP has no
  arrays.

`thesis/shared/code/goblint-flavors` holds C versions of the same programs and
Goblint's verdicts on them. Run with `pixi run python3 tests/run.py 28-flavors`.
