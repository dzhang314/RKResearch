import RKCert.ReviewedNative.ERK17FourPortProducer

open RKResearch Polynomial RKResearch.Certified.ERK17
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.ReviewedNative.OriginSignedSquares

section
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {P : K[X]} {u v w : K} (H : ThreeClockMoments P u v w) :
    0 < w ∧ (0 < u → (1-u)*(u-w)<0) :=
  H.signed_cut

example {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (gate : RadauFirstGate K) (ha : ∀ i j,i≤j→A i j=0)
    (ho : HasOrder 17 A b) (zero : firstSeed A b=0) :
    ∃ W θ : Fin 26 → K, ∃ P : K[X], PhysicalFourPort (s:=25) A W θ P ∧
      (active W).card=4 ∧ ActualReflectedAffinePacket A b W (reflectedProfile P) :=
  ordered_width26_actual_four_port gate ha ho zero

example {A : Matrix (Fin 26) (Fin 26) K} {b W θ : Fin 26 → K} {P : K[X]}
    (H : PhysicalFourPort (s:=25) A W θ P) (ha : ∀ i j,i≤j→A i j=0)
    (origin : (0:K)∈sites (nodes A) W) (rows : (active W).card=4)
    (reverse : ActualReflectedAffinePacket A b W (reflectedProfile P))
    (positive : PositiveFirstClock K) (smallest : NoSmallestClock K) : False := by
  obtain ⟨u,v,w,T⟩ := H.actual_two_sided_origin ha origin rows reverse
  exact T.impossible_of_positive_and_not_smallest positive smallest

end

#print axioms RKCert.ReviewedNative.OriginSignedSquares.ThreeClockMoments.signed_cut
#print axioms RKCert.ReviewedNative.OriginSignedSquares.ThreeClockMoments.mesh_mirrored
#print axioms RKCert.ReviewedNative.OriginSignedSquares.TwoSidedThreeClockMoments.impossible_of_positive_and_not_smallest
#print axioms RKResearch.Certified.ERK17.ActualReflectedAffinePacket.of_contrast
#print axioms RKResearch.Certified.ERK17.PhysicalFourPort.actual_two_sided_origin
#print axioms RKResearch.Certified.ERK17.width26_actual_four_port_from_cover
#print axioms RKResearch.Certified.ERK17.ordered_width26_actual_four_port
#print axioms RKResearch.Certified.ERK17.ordered_width26_physical_four_port
