# Flavors of abstract interpretation

The examples of David Monniaux's ETAPS 2024 tutorial "Flavors of abstract
interpretation" (HAL hal-04750222), at i32. Each fixture pins what Voblint finds
today; every check holds in every run, so a PROVED check is in `precision/` and
an UNKNOWN one in `known-imprecision/`.

- Vanilla (finite lattices): `precision/01` (Interval), `known-imprecision/01`
  (Sign, which cannot bound the sum of two negatives at a machine kind),
  `known-imprecision/06` (an abstraction that is not inductive).
- Coffee (relational domains, paths): `known-imprecision/02` and `03`.
- Fudge (widening and narrowing): `precision/02` and `03`.
- Blackcurrant (policy iteration, guided analysis): `known-imprecision/04` and
  `05`.
- Fiore di latte (arrays, relative completeness) has no VIMP form: VIMP has no
  arrays.

Run with `pixi run python3 tests/run.py 28-flavors`.
