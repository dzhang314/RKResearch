module

public import RKCert.ReviewedNative.RationalStrictSDIRKFiveStageFiveUpper
public import RKCert.ReviewedNative.RationalSmallSDIRKLower

@[expose] public section

namespace RKResearch.Certified

theorem rational_strictSDIRK_five_minima :
    IsLeast (rationalStrictSDIRKStages 5) 5 ∧ IsLeast (rationalStrictSDIRKExactStages 5) 5 := by
  obtain ⟨A, b, ha, hc, hn, ho, hnext⟩ := exists_five_stage_rational_strictSDIRK_exact_five
  refine ⟨⟨⟨A, b, 1, ha, hc, hn, ho⟩, ?_⟩, ⟨⟨A, b, 1, ha, hc, hn, ho, hnext⟩, ?_⟩⟩
  · rintro s ⟨A', b', γ, ha', hc', _, ho'⟩
    exact ho'.common_diagonal_order_five_stages ha' hc'
  · rintro s ⟨A', b', γ, ha', hc', _, ho', _⟩
    exact ho'.common_diagonal_order_five_stages ha' hc'

end RKResearch.Certified
