module

public import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic.LinearCombination

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveRegularLiteral

/-- The actual two literal front readings determine both homogeneous
corrected-profile coefficients. The identity itself is valid without
a rank hypothesis; the regular branch uses the true nonzero determinant. -/
theorem actualTwoLiteralHomogeneousProfile {R : Type*} [CommRing R]
    (La Lb Ka Kb Ha Hb α β : R)
    (hA : La*α+Ka*β=Ha) (hB : Lb*α+Kb*β=Hb) :
    (La*Kb-Lb*Ka)*α=Ha*Kb-Hb*Ka ∧
      (La*Kb-Lb*Ka)*β=La*Hb-Lb*Ha := by
  constructor
  · linear_combination Kb*hA-Ka*hB
  · linear_combination La*hB-Lb*hA

#print axioms actualTwoLiteralHomogeneousProfile

end RKCert.ReviewedNative.SDIRK8ReverseLiveAffineSharedQuinticHoleFiveRegularLiteral
