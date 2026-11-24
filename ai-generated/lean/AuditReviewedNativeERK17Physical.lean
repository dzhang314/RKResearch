import RKCert.ReviewedNative.ERK17PhysicalFromReplay

open RKResearch RKResearch.Certified.ERK17
open Polynomial

-- A native rank/geometry derivation is still needed for 'ports'.
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b)
    (ports : HasOrder 17 A b → ∃ w θ : Fin 26 → K, ∃ P : K[X], PhysicalFourPort A w θ P) :
    False := by
  obtain ⟨w,θ,P,H⟩ := ports ho
  exact no_physical_four_port ha H

#print axioms RKResearch.Certified.ERK17.PhysicalFourPort.primitive_zero_of_prefix
#print axioms RKResearch.Certified.ERK17.PhysicalFourPort.mesh_of_origin
#print axioms RKResearch.Certified.ERK17.PhysicalFourPort.no_origin_of_quartic
#print axioms RKResearch.Certified.ERK17.ordered_quartic_gate
#print axioms RKResearch.Certified.ERK17.no_physical_four_port
