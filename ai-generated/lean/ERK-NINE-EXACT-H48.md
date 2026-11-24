# Exact H48 and localized endpoint transfer (supporting proof)

Pinned Lean 4.36.0 commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9;
Mathlib fc4f59e577feb1a4956671bc04ac18aaaf8cd842. This additive source
overlay expects the sealed ERK order-nine physical chart based on
1e545bba. Copy the RKCert sources into a project already containing that
chart. Mathlib.Algebra.Polynomial.CoeffList is a direct pinned import.

## Verified statements

- `RKCert.GoodPrimeDense.h48_raw_check`: exact 49-entry rational norm
  identity by local arithmetic checkpoints of the 4/3/2 ordered-root
  tower, including the nonzero scale relating it to primitive H48.
- `RKCert.GoodPrimeDense.h48_zero_of_k8` and
  `h48_zero_of_distinct_pencil`: H48 vanishes for the sealed K8 equation
  on the corresponding chart, over any characteristic-zero field. The
  degree is exactly 48.
- `normStages_vanish`: the three exact intermediate eliminants with
  denominators cleared also vanish on that chart.
- `terminalAt_legacy`: the executable terminal product is the exact
  sealed physical terminal product, not a substitute or weakened test.
- `endpoint_good_prime`: generic localized residue-field transfer
  for the scalar parameter, ordered-root relations, and three arbitrary
  integer tests. It never reduces an RK tableau.
- `slots_of_rootSystem` and `SelectorDatum.terminal_nonzero`: verified
  implication from the finite-factor data and its unit certificates.
  The synthetic equations select distinct slots even if under
  specialization some slots have equal values.

The finite unit tests for every parameter factor are outside this
supporting packet. It does not prove the complete five-off/six-on
exclusion, does not cover the one-off atlas, and does not promote any
numerical stage bound. The recovered historical prime-101 script is
included for provenance and reproducibility. It is not an axiom or a
substitute for the unfinished kernel arithmetic.

All included Lean leaves were checked by the pinned Lean kernel. Seven
primary axiom receipts list only propext, Classical.choice and
Quot.sound. The H48 bridge is independently replayed with leanchecker;
no fresh transitive Mathlib build is claimed.
