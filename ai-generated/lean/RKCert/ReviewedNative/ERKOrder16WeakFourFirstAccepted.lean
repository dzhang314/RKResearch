module

public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceCubic
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceUnit
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceLow
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAcceptanceHigh
public import RKCert.ReviewedNative.ERKOrder16WeakFourFirstDecoded

@[expose] public section

namespace RKCert.ReviewedNative.WeakFourFirstOnly.Replay

open Polynomial

theorem weakFourScalarExclusion_of_accepted_tables
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q Z : K[X]} {a c : K}
    (H : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) : False :=
  weakFourScalarExclusion_of_decoded_receipts Cubic.accepted Unit.accepted
    Low.accepted High.accepted H

end RKCert.ReviewedNative.WeakFourFirstOnly.Replay
