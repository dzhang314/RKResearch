module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralTable
public import RKCert.ReviewedNative.WeakFiveThreeInteriorActualOrder
public import RKCert.ReviewedNative.WeakFiveThreeInteriorLiteralPencil

@[expose] public section

namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.WeakFive16
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The genuine three-interior callback for the remaining-scalar classifier.
No external table, parameter choice or list of postulated orders is an input. -/
theorem no_actual_threeInterior_of_literal_table {q Z : K[X]} {c : Fin 5 → K}
    (M : Moments q Z c) : ThreeInterior q c → False :=
  no_actual_threeInterior_of_exact_receipts threeInteriorLiteralTable M
    (fun _ => threeInterior_orderReceipt)
    (fun _ => threeInterior_literal_pencil_receipt)
    (fun _ => threeInterior_literal_ratio_receipt)

end RKCert.ReviewedNative.ThreeInteriorPencil
