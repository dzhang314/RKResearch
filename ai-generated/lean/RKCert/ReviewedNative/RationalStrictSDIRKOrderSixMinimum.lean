module

public import RKCert.ReviewedNative.RationalStrictSDIRKSevenStageSixUpper
public import RKCert.ReviewedNative.RationalSmallSDIRKLower
public import RKCert.ReviewedNative.SDIRKOrderSix

@[expose] public section

namespace RKResearch.Certified

theorem rational_strictSDIRK_six_minima :
    IsLeast (rationalStrictSDIRKStages 6) 7 ∧ IsLeast (rationalStrictSDIRKExactStages 6) 7 := by
  obtain ⟨A, b, ha, hc, hn, ho, hnext⟩ := exists_seven_stage_rational_strictSDIRK_exact_six
  refine ⟨⟨⟨A, b, 1/4, ha, hc, hn, ho⟩, ?_⟩,
    ⟨⟨A, b, 1/4, ha, hc, hn, ho, hnext⟩, ?_⟩⟩
  · rintro s ⟨A', b', γ, ha', hc', hγ, ho'⟩
    exact ho'.sdirk_order_six_stages_field ha' hc' hγ
  · rintro s ⟨A', b', γ, ha', hc', hγ, ho', _⟩
    exact ho'.sdirk_order_six_stages_field ha' hc' hγ

end RKResearch.Certified
