module

public import RKCert.ReviewedNative.ERKOrder16StrongCenteredShape
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredIncreasing
public import RKCert.ReviewedNative.ERKOrder16StrongCenteredDecreasing

@[expose] public section
namespace RKCert.ReviewedNative.StrongCentered16

open Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem not_moments {q : K[X]} {a z : K} (h : Moments q a z) : False := by
  have S := h.shape
  rcases lt_or_gt_of_ne h.pivotsDistinct with haz | hza
  · exact increasing_local_impossible h.qNonzero h.qDegree S.firstInterior.1 haz
      S.lastInterior.2 h.forwardFirst h.forwardSecond h.forwardMasked
      h.reverseFirst h.reverseSecond h.reverseMasked
  · exact decreasing_local_impossible h.qNonzero h.qDegree S.lastInterior.1 hza
      S.firstInterior.2 S.firstValue S.lastValue S.oddContrast
      h.forwardFirst h.forwardSecond h.forwardMasked h.reverseFirst h.reverseSecond h.reverseMasked

end RKCert.ReviewedNative.StrongCentered16
