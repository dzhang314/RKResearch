import RKCert.ReviewedNative.SDIRKNineParameter

open RKResearch.Certified.SDIRKNineParameter

example :
    ∃ x v w : ℝ, x ∈ Set.Ioo (lo:ℝ) (hi:ℝ) ∧ 0 < x ∧ value pCoeffs x = 0 ∧
      IsAlgebraic ℚ x ∧ IsAlgebraic ℚ v ∧ IsAlgebraic ℚ w ∧ 0 < rho x ∧
      rho x ^ 2 = 2 ∧ v < w ∧ v+w = U x ∧ v*w = V x :=
  exists_algebraic_parameters

#print axioms RKCert.ReviewedNative.PolynomialBracket.box_real_sound
#print axioms RKCert.ReviewedNative.PolynomialBracket.exists_real_horner_root
#print axioms exists_algebraic_parameters
#print axioms reduced_bush_positive
