# Unrestricted DIRK: genuine grade-six surplus and orders 12–13

Lean and Mathlib are unchanged at v4.36.0. This additive source overlay was
tested on top of the preceding published proofs.
The existing `RKCert.lean` gains one public import of `RKCert.DirkGradeSix`.
No baseline proof module, manifest, dependency version, or compatibility
pilot file is replaced. Import and SHA manifests isolate the exact change.

## Main statements

- `RKCert.Paired.dirk_grade_six_surplus`: for every unrestricted lower
  triangular tableau of attained all-tree order at least 8 over a
  characteristic-zero field, the genuine ordinary zero-profile spaces
  satisfy `dim F6 ≥ dim F3 + 4`.
- `RKCert.Paired.dirk_order12_charZero_field`: attained order at least 12
  implies `15 ≤ s`; `dirk_order13_charZero_field`: attained order at least
  13 implies `17 ≤ s`. No ordering, sign assumptions, distinct clocks,
  zero first row, or nonzero individual weight or diagonal is required.
- The corresponding `RKCert.dirk_order12_charZero_ring` and
  `dirk_order13_charZero_ring` use prime specialization. They apply to all
  characteristic-zero commutative rings, including rings with nonzero
  torsion and nilpotents; no arbitrary-characteristic promotion is claimed.
- `dirk_order14_native_rank` and `dirk_order15_native_rank` are prerequisites,
  not the strongest known finite exclusions. They prove 18 at order 14
  (19 in the nonzero quadratic-defect case) and 20 at order 15. The stronger
  unrestricted characteristic-zero endpoints 19 and 21 need separate proofs.
  Existing uniform nontrivial-ring endpoints remain unchanged.

## What the proof actually certifies

Inclusive exact scalar tests detecting retained diagonal taps make a flat
three-step defect band yield one of two genuine head profiles. The grade-4
branch is eliminated using four physical clock debuts, including heads that
vary inside masked physical classes. In the grade-3 branch, only the earliest
physical row of each eligible clock/head signature is sampled, with
zero slots retained for discarded coordinates. The replay map reconstructs
the same actual profile **after each** A-application in the commutator; this
does not claim that the folded array is itself an order-p method. Two native
chronologies force the first five actual dirty signatures onto the same
three predecessors; two independent origin jets contradict their rank.
These steps use fixed moment systems and exact root counts, not positivity
of an unknown coefficient or a squared variable residual.

The stage-count bridge independently checks anchored or delayed polynomial
separation and counts backward annihilators. At equality it selects the
last *weighted* stage, not necessarily the physical last row, and refunds
only that actual endpoint. No claim presupposes that all weights are nonzero.

## Reproduce

With pinned Mathlib packages present:

```sh
lake build
lake build RKCert.DirkGradeSixRegression
lake env lean AuditDIRKGradeSix.lean
```

The regression explicitly checks the complex order-13 limit, the order-12
limit over `ℚ × ZMod 529`, and the separate arbitrary-characteristic floor.
