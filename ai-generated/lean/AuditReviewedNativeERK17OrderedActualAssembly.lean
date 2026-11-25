import RKCert.ReviewedNative.ERK17OrderedActualAssembly

open RKResearch RKResearch.Certified.ERK17 RKCert.ReviewedNative.OriginSignedSquares

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example
    (radau : RadauFirstGate K) (smallest : NoSmallestClock K)
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : False :=
  ordered_width26_impossible_of_actual_origin_gates radau smallest ha ho

example
    (radau : RadauFirstGate K) (smallest : NoSmallestClock K)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  ordered_erk17_stage_floor27_of_actual_origin_gates radau smallest ha ho

#print axioms ordered_width26_impossible_of_actual_origin_gates
#print axioms ordered_erk17_stage_floor27_of_actual_origin_gates
