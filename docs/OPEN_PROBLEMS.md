# Open problems

This file records research or engineering boundaries, not completed migration
history.

## Solver termination hypotheses

The verified solver supplies conditional correctness. Concrete executable
examples discharge termination by evaluation. A general total-correctness
result requires assumptions on update rules, widening, and generated equation
systems.

## Finite context domains

Activation soundness is generic over context keys, but executable solvers need
finite or canonical key representations. Arbitrary interval states are poor
keys because recursion and widening can create an unbounded sequence.

## Context precision

Sound routing does not guarantee that caller contexts distinguish every global
fact relevant to a callee. Precision claims need concrete witnesses and must be
separated from collecting-soundness claims.

## D/G products

The mixed Sign/Interval analysis is a concrete heterogeneous instance. The
repository has no generic product or reduced-product constructor. Such a
constructor needs carrier, order, concretization, communication, and reduction
laws.

## Numeric transfer precision

Backward guard refinement and widening determine useful loop invariants.
Soundness permits coarse transfers; precision improvements require executable
regressions that state the intended bounds.

## Richer source language

The verified source is scalar VIMP. Arrays, pointers, and C memory require an
explicit semantic model and cannot be inherited from the current compiler
proofs.
