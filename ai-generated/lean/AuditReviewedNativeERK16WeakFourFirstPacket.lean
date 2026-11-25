module

import RKCert.ReviewedNative.ERKOrder16WeakFourFirstAccepted

open Polynomial

-- The literal reviewed port, not a package-defined replacement or a
-- weaker first-stop packet. There is no receipt or weak-five premise.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {Q Z : K[X]} {a c : K}
    (ports : RKResearch.Certified.ERK16.WeakFourChronologicalPorts Q Z a c) : False :=
  RKCert.ReviewedNative.WeakFourFirstOnly.Replay.weakFourScalarExclusion_of_accepted_tables ports

#print axioms RKCert.ReviewedNative.WeakFourFirstOnly.Replay.weakFourScalarExclusion_of_accepted_tables
