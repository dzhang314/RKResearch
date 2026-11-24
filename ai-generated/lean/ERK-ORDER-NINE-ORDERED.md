# Complete ordered-field explicit RK order-nine lower bound

Public import: `RKCert.ERKOrderNineOrderedComplete`.

`RKCert.Paired.explicit_order_nine_at_least_thirteen`:
for arbitrary finite stage count s and ordered field K, a literal strictly
lower triangular K-valued tableau satisfying all through-order-nine rooted
tree conditions has 13 ≤ s. No positivity of the tableau weights, no
abscissa separation, and no irredundancy or nonvanishing assumptions.
This certifies the existing lower bound; it does not assert attainment or
promote the unordered characteristic-zero case.

`RKCert.Paired.order9_one_off_impossible` is the genuine last branch.
The new characteristic-zero leaves derive the seventh on row and its
second clean fibre, the exact nonzero terminal quadratic coefficient, the
actual grade-six profile, and both actual vector identities behind the
cubic/quartic reflected moment collision. Fields with an order enter only
where needed, including the existing non-one-off census and terminal
positivity. The sixth through ninth numbered rows are literal rows of
the supplied tableau. Off rows at a coincident on abscissa remain
distinguished, and the two late on clocks are not assumed different
from 1.

Build: pinned Lean 4.36.0
(611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9) and Mathlib
fc4f59e577feb1a4956671bc04ac18aaaf8cd842; eleven public standard-axiom
checks, no new custom axioms and no `sorry` or `native_decide`. The new
small exact rational certificates use ordinary `field_simp`, `ring`
and `linear_combination`; previous finite tapes remain untouched. This
packet reports leaf checks against the existing compiled dependencies,
not a fresh full or older-toolchain build. Harmless linter warnings are
retained in the original receipts.


Reproduce with `lake build RKCert.ERKOrderNineOrderedComplete` and `lake env lean AuditERKOrderNineOrdered.lean` under Lean and Mathlib 4.36.0.
