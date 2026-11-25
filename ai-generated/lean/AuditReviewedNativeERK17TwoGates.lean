import RKCert.ReviewedNative.ERK17OrderedTwoGates

open RKResearch Polynomial RKResearch.Certified.ERK17
open RKCert.ReviewedNative.ERK17.Scalar

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (radau : RadauFirstGate K)
    (mesh : ∀ (P N : K[X]) (u : K), MeshPorts P N u → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  ordered_erk17_stage_floor27_of_radau_and_mesh radau mesh ha ho

#print axioms RKResearch.Certified.ERK17.native_ordered_quartic_gate
#print axioms RKResearch.Certified.ERK17.ordered_erk17_stage_floor27_of_radau_and_mesh
