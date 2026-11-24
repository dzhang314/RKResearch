# Native unrestricted-DIRK forward-rank increments

Two additive modules, checked and independently replayed on pinned Lean and
Mathlib v4.36.0. This uses the exact reviewed tree-order predicate and its
actual graded defect spaces. Neither a legacy order equivalence, a strict
(diagonal-zero) tableau, characteristic zero, signs, distinct nodes, nor
individual nonzero weights are assumed.

- `RKCert.ReviewedNative.TwoSeedRank` is Mathlib-only. It converts a given
  two-seed forcing implication into a strict submodule inclusion, and adds
  the ranks of strict steps on a finite interval. It does not implement
  operator-specific forcing or define another E/F flag.
- `RKCert.ReviewedNative.DIRKForwardRank` applies that bookkeeping to the
  reviewed native (F_j), reusing the separate checked native DIRK
  two-seed forcing theorem and its reviewed order payments.

The three main native interfaces are in `RKResearch.Certified.Graded`:

* `dirk_forward_zeroSpace_lt_succ`: (F_j<F_{j+1}) when (2le j) and
  (j+1le p).
* `dirk_forward_zeroSpace_rank_floor`: (q-2ledim F_q), replaced by
  (q-1) when the actual quadratic monomial stage defect is nonzero,
  when (2le qle p).
* `dirk_forward_rank_three`: the precise (1/2) grade-three split for
  the p15 rank budget, at order at least three.

This does not claim the 20-stage rank floor or a reviewed p15 endpoint:
the true grade-six surplus, reverse dimension, and stage-budget assembly
are separate. No moment, two-seed algebra, or elimination chart is repeated.

The exact source import closure (each non-Mathlib module, its direct
imports and source SHA-256) appears in `IMPORT-CLOSURE.json`.
It is reviewed/Mathlib-only, with no frozen legacy proof dependency.
The four audited declarations use only standard Lean axioms. No other
source changed, and no sealed arithmetic was rebuilt.
