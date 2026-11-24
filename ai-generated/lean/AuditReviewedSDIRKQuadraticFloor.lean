import RKCert.ReviewedNative.NonsingularDIRKQuadraticFloor

open RKResearch RKResearch.Certified.Graded

example : nonsingularStageFloor 1 = 1 := by decide

example {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder 21 A b) (ha : A.IsLowerTriangular) (hu : ∀ i, IsUnit (A i i)) :
    61 ≤ s :=
  h.nonsingular_quadratic_stage_floor ha hu (by decide)

#print axioms nonsingularStageFloor_eq_quadratic
#print axioms HasOrder.nonsingular_quadratic_stage_floor_field
#print axioms HasOrder.nonsingular_quadratic_stage_floor

