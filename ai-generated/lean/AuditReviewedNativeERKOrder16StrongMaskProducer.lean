import RKCert.ReviewedNative.ERKOrder16StrongMaskProducer

open RKResearch Polynomial Module RKCert.Endpoint
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse RKResearch.Certified.ERK16

theorem audit_width24_strong_actual_origin {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 16 A b)
    (r7 : finrank K (zeroSpace A 7)=8) :
    ∃ (w g : Fin 24→K) (Q P : K[X]) (ι : Fin 3→Fin 24),
      StrongThreeActualMask A b w g Q P ∧ StrongThreePhysicalPorts A b Q P ι ∧ ι 0=0 :=
  width24_strong_actual_ports_and_origin ha ho r7

#print axioms RKResearch.Certified.ERK16.width24_strong_reverse_cover
#print axioms RKResearch.Certified.ERK16.Width24StrongCover.two_traces
#print axioms RKResearch.Certified.ERK16.strong_three_physical_ports
#print axioms RKResearch.Certified.ERK16.strong_three_origin_of_ports
#print axioms RKResearch.Certified.ERK16.width24_strong_hidden_five
#print axioms RKResearch.Certified.ERK16.width24_strong_actual_mask
#print axioms RKResearch.Certified.ERK16.width24_strong_actual_ports_and_origin
#print axioms audit_width24_strong_actual_origin
