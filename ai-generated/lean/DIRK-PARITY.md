# DIRK parity floor and order-17 release delta
Baseline: 182d77cc03ed53d47f349588b99ef0260c283f9b; Lean and Mathlib v4.36.0. No other packages beyond the pinned project.
New source: RKCert/DirkParityFloor.lean, with the only direct local import RKCert.DirkGradeSix, already on the baseline. No shared source replacement.
Public endpoints: RKCert.Paired.dirk_order17_charZero_field and RKCert.dirk_order17_charZero_ring take a lower triangular array, full rooted-tree order at least p, and 17≤p, and prove 23≤s, with no ordering, realness, or stage-pruning premise.
Uniform endpoints for m≥7: p=2m gives s≥3m−3; over a field, non-C(2) strengthens that to s≥3m−2.  p=2m+1 gives s≥3m−1. The two basic numerical floors transfer to all commutative characteristic-zero rings.
Proof: join the published grade-six surplus with strict native growth, use the scalar/tree-space separation at the earned midpoint, then use the previous published terminal count. The odd case needs different terminal probe budgets depending on whether C(2) holds.
Not an ordered-field 24-stage proof; not an exclusion of equality in any even-order floor.
Replay: lake build RKCert; lake env lean AuditDIRKParity.lean. Kernel-only check: lake env leanchecker RKCert.DirkParityFloor.
