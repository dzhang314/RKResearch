module

public import RKCert.ReviewedNative.PositiveIntervalGrid19

@[expose] public section

/-! # The tableau-free order-sixteen centered strong-three cut -/
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial RKCert.ReviewedNative.PositiveRule19

variable {K : Type*} [Field K] [CharZero K]

/-- Six oriented local payments and the seven global weighted moments.
The pivots are named in physical order; no numerical order is assumed. -/
structure Moments (q : K[X]) (a z : K) : Prop where
  qNonzero : q ≠ 0
  qDegree : q.natDegree ≤ 5
  pivotsDistinct : a ≠ z
  forwardFirst : integral 0 a (X*q) = 0
  forwardSecond : integral 0 a (X^2*q) = 0
  forwardMasked : integral 0 z (X*(X-C a)*q) = 0
  reverseFirst : integral z 1 ((1-X)*q) = 0
  reverseSecond : integral z 1 ((1-X)^2*q) = 0
  reverseMasked : integral a 1 ((1-X)*(X-C z)*q) = 0
  weightedMoments : ∀ H : K[X], H.natDegree ≤ 6 →
    integral 0 1 (X*(1-X)*((X-C a)*(X-C z)*q)*H) = 0

/-- In particular, the seven individual tests have spectators
`1,X,...,X^6`. Keeping all degree-six spectators avoids replaying
an interpolation argument in the scalar proof. -/
theorem Moments.weightedPower {q : K[X]} {a z : K} (h : Moments q a z) (k : Fin 7) :
    integral 0 1 (X*(1-X)*((X-C a)*(X-C z)*q)*X^k.val) = 0 := by
  apply h.weightedMoments
  rw [natDegree_X_pow]
  exact Nat.le_of_lt_succ k.isLt

end RKCert.ReviewedNative.StrongCentered16
