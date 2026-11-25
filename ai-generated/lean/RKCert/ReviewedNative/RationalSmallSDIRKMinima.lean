module

public import RKCert.ReviewedNative.RationalSmallSDIRKLower
public import RKCert.ReviewedNative.RationalStrictSDIRKSmallUpper

@[expose] public section

namespace RKResearch.Certified

theorem rational_strictSDIRK_three_minima :
    IsLeast (rationalStrictSDIRKStages 3) 3 ∧ IsLeast (rationalStrictSDIRKExactStages 3) 3 := by
  obtain ⟨A, b, ha, hdiagonal, hnonzero, _, horder, _⟩ :=
    exists_rational_strictSDIRK_exact_three
  exact rational_strictSDIRK_three_minima_of_witness
    ⟨A, b, 1 / 6, ha, hdiagonal, hnonzero, horder⟩

theorem rational_strictSDIRK_four_minima :
    IsLeast (rationalStrictSDIRKStages 4) 4 ∧ IsLeast (rationalStrictSDIRKExactStages 4) 4 := by
  obtain ⟨A, b, ha, hdiagonal, hnonzero, _, horder, _⟩ :=
    exists_rational_strictSDIRK_exact_four
  exact rational_strictSDIRK_four_minima_of_witness
    ⟨A, b, 1 / 6, ha, hdiagonal, hnonzero, horder⟩

end RKResearch.Certified
