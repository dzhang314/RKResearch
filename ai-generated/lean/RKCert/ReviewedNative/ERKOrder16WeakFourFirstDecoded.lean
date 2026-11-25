module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataCubic
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataUnit
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataLow
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDataHigh

@[expose] public section

/-! # Replay entrance for the concrete weak-four first-stop receipts

No acceptance equality is postulated. These are explicit theorem arguments
until serial Lean replay of the finite numerical proofs is finished.
-/
namespace RKCert.ReviewedNative.WeakFourFirstOnly

open Polynomial

theorem weakFourScalarExclusion_of_decoded_receipts
    (A : checkOrdinaryReceipts DataCubic.table referenceJList referenceJList=true)
    (B : checkOrdinaryReceipts DataUnit.table referenceP₀List referenceP₁List=true)
    (C : checkExteriorReceipts DataLow.table referenceJList referenceP₀List false=true)
    (D : checkExteriorReceipts DataHigh.table referenceJList referenceN₁List true=true)
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q Z : K[X]} {a c : K}
    (H : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) : False :=
  weakFourScalarExclusion_of_checked_rational_tables DataCubic.table DataUnit.table
    DataLow.table DataHigh.table A B C D H

end RKCert.ReviewedNative.WeakFourFirstOnly
