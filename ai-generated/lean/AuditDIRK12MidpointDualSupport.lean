import RKCert.ReviewedNative.DualSupport12

open RKResearch
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.DualSupport12

set_option autoImplicit false

example {ι R : Type} [Fintype ι] [CommRing R] (A : Matrix ι ι R) (b : ι → R)
    (h : LowChecks A b) : HasOrder 12 A b :=
  LowChecks.hasOrder h

example {ι R : Type} [Fintype ι] [CommRing R] (A : Matrix ι ι R) (b : ι → R)
    (scalar : ∀ j < 12, ((j+1 : Nat) : R) * row b ((nodes A)^j) = 1)
    (l k : Nat) (h : l+k+1 < 12) :
    ((k+1 : Nat) : R) * row (moment A b (l+1)) ((nodes A)^k) =
      ((l+1 : Nat) : R) * row (moment A b l) ((nodes A)^(k+1)) :=
  mixed_scalar A b scalar l k h

#print axioms RKResearch.Certified.Graded.DualSupport12.LowChecks.hasOrder
#print axioms RKResearch.Certified.Graded.DualSupport12.mixed_scalar
