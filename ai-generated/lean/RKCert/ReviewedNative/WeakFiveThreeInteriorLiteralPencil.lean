module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralClosedCover

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The finite strip receipt supplied at the concrete released corpus. -/
theorem threeInterior_literal_pencil_receipt :
    ThreeInteriorPencilReceipt (K := K) threeInteriorLiteralRows :=
  threeInterior_pencilReceipt_of_finite_rows threeInterior_literal_finite_strips

end RKCert.ReviewedNative.ThreeInteriorPencil
