module

public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace RKCert.ReviewedNative.SDIRK8ArithmeticFifth

/-- The arithmetic rear removes the true reverse site from two literal
affine tail reads. The factor canceled is the actual nonzero gap
times the reverse factor and terminal Legendre value. -/
theorem eliminateArithmeticReverseClock
    {K : Type*} [Field K] (qx qc qd lx lc ld H T k δ w : K)
    (h : δ * k * lx ≠ 0)
    (hn : (qx * lc - k * qc * lx) * w + δ * k * qc * lx = 0)
    (he : (H * qx * ld + k * T * qd * lx) * w -
      2 * δ * k * T * qd * lx = 0) :
    H * qx * qc * ld + 2 * T * qx * qd * lc - k * T * qc * qd * lx = 0 := by
  have h' : δ * k * lx *
      (H * qx * qc * ld + 2 * T * qx * qd * lc - k * T * qc * qd * lx) = 0 := by
    linear_combination (H * qx * ld + k * T * qd * lx) * hn -
      (qx * lc - k * qc * lx) * he
  exact (mul_eq_zero.mp h').resolve_left h

/-- A denominator-cleared cubic read has no residue denominator
hypothesis; the transported fifth need not itself be integral. -/
theorem homogeneousCubicRead
    {R : Type*} [CommRing R] (a₀ a₁ a₂ a₃ num den y : R)
    (h : den * y = num)
    (he : a₀ + a₁ * y + a₂ * y^2 + a₃ * y^3 = 0) :
    a₀ * den^3 + a₁ * num * den^2 + a₂ * num^2 * den + a₃ * num^3 = 0 := by
  rw [← h]
  linear_combination den^3 * he

end RKCert.ReviewedNative.SDIRK8ArithmeticFifth

#print axioms RKCert.ReviewedNative.SDIRK8ArithmeticFifth.eliminateArithmeticReverseClock
#print axioms RKCert.ReviewedNative.SDIRK8ArithmeticFifth.homogeneousCubicRead
