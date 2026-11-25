import RKCert.ReviewedNative.ERK17OrderedStageFloor27Native

open RKResearch RKResearch.Certified.ERK17

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

example {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  ordered_erk17_stage_floor27_native ha ho

example {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : False := by
  have hw : 27 ≤ (26 : ℕ) := ordered_erk17_stage_floor27_native ha ho
  exact (by decide : ¬27 ≤ (26 : ℕ)) hw

#print axioms ordered_erk17_stage_floor27_native
