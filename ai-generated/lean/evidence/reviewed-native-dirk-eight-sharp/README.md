# Sharp reviewed-native DIRK at order eight

Eight is the minimum number of physical stages for ordinary lower triangular
DIRK of order at least eight over both the reals and the real algebraic
numbers. The archived eight-stage Lobatto tableau has a literal zero first
row. It has exactly order eight; the factorial-scaled ninth bush is
`3921/3920`. This is not a strict SDIRK or stability result.

The public endpoints are `RKResearch.Certified.dirk_order_eight_isLeast_real`
and `dirk_order_eight_isLeast_realAlgebraic`. The corresponding
`LobattoDIRK88.exists_exact_real{,Algebraic}` theorems exhibit the actual
zero-row method and its next-order failure. Over any characteristic-zero
field possessing a square root of 21, `exists_exact_of_root` and
`dirk_order_eight_isLeast_of_root` give the same conclusions.

## What was checked

- The archived exact reconstruction reduces every coefficient to
  `a + b√21` with rational `a,b`. Independent replay checks all 200 unordered
  tree weights and the residual `1/3920`. A separate literal comparison checks
  every entry of the emitted 8×8 matrix and the eight weights.
- The matrix numerator has denominator 60480 and the weight numerator 360.
  The sparse action is proved to be reviewed matrix multiplication. The
  order proof clears and then cancels those two units via the preexisting
  `FiniteScaledOrderCheck`.
- The new reusable `CanonicalStageMemo.cover` proves by induction on the
  reviewed constructors that every reviewed binary tree is represented.
  The arithmetic checks cover 200 cache labels and payments, 312 bounded
  constructor joins, and 85 sparse derivative columns. The labels track
  both order and the actual forest factorial. Therefore order does not
  depend on an external symmetry classification or Python enumeration.
- The exact ninth-bush proof uses a separate constant-quadratic identity;
  it does not run a ninth-order search. The reviewed-native
  `HasOrder.dirk_order_eight_stages` supplies the independent lower bound.

## Replaying

Use the reviewed base and pinned Lean/Mathlib revisions in `result.json`.
Build or overlay the predecessor sources providing
`FiniteOrderCheck`, `ChangeCoefficients`, `FiniteScaledOrderCheck`,
`IntegerHornerCertificate`, `QuadraticHornerReplay`,
`LaguerreGauss76Real`, and `DIRKUniform` and their dependencies.
With their objects and the pinned Mathlib libraries on `LEAN_PATH`,
build the 34 listed files in `rebuild-order.txt` under `ai-generated/lean`.
One invocation of `lean -j1 -M 3000` per file is enough; no network, new
coefficient search, or giant build is needed. Then run
`AuditReviewedLobattoDIRK88.lean`. The source-only delta has no compiled
objects; the object fingerprints are receipts.

For provenance independently of Lean, run
`python3 replay-lobatto.py tableau.json` in the evidence directory, then
`python3 compare-tableau.py ../../RKCert/ReviewedNative/LobattoDIRK88Data.lean tableau.json`.
The exact check uses SymPy for rational multiplication-matrix inverses.
It is not part of the Lean trust boundary.
