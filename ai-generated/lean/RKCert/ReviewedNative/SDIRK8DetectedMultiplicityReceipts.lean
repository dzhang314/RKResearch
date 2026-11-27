module

public import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8DetectedMultiplicityReceipts

/-- Two paid moments isolate the signed second defect masses at two
different physical clocks. -/
theorem twoSecondMasses {K : Type*} [Field K] (a b s t : K)
    (h : a≠b) (h₀ : s+t=0) (h₁ : a*s+b*t=0) : s=0 ∧ t=0 := by
  have f : (a-b)*s=0 := by linear_combination h₁-b*h₀
  have hs := (mul_eq_zero.mp f).resolve_left (sub_ne_zero.mpr h)
  exact ⟨hs, by simpa [hs] using h₀⟩

/-- The exact reverse-third numerator has a known artificial factor
in the nonzero penultimate-residual branch. The cubic used in the
finite certificate is obtained by this exact division before reduction. -/
theorem thirdReverseFactor {R : Type*} [CommRing R] (u : R) :
    (1+4*u-4*u^2)*(-2+u+4*u^2-u^3)+4*u^2*(3*u-2)=
      -(1+2*u-u^2)*(4*u^3-12*u^2+3*u+2) := by ring

#print axioms twoSecondMasses
#print axioms thirdReverseFactor

end RKCert.ReviewedNative.SDIRK8DetectedMultiplicityReceipts
