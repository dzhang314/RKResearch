import RKCert.ReviewedNative.ERKOrder16StrongCenteredEndpoint

open RKResearch Module
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}

example (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 16 A b)
    (_seedZero : firstSeed A b=0) (r7 : finrank K (zeroSpace A 7)=8) : False :=
  RKResearch.Certified.ERK16.width24_strong_seventh_rank_ne_eight ha ho r7

end

#print axioms RKResearch.Certified.ERK16.width24_strong_seventh_rank_ne_eight
