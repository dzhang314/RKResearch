import RKCert.ReviewedNative.SDIRKFiveSharp

open RKResearch RKResearch.Certified RKResearch.Certified.Graded

example : (List.range 20).map (fun k => nonsingularStageFloor (k+1)) =
    [1,1,2,3,5,6,8,10,13,15,18,21,25,28,32,36,41,45,50,55] := by decide

example {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (h : HasOrder A b 5) (ha : A.IsLowerTriangular) (hn : ∀ i, A i i ≠ 0) : 5 ≤ s :=
  nonsingular_stageFloor_field h ha hn (by decide)

example {R : Type*} [CommRing R] [Nontrivial R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}
    (h : HasOrder A b 5) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) : 5 ≤ s :=
  h.common_diagonal_order_five_stages ha hc

#print axioms volterra_treeSpace
#print axioms volterra_injective
#print axioms nonsingular_rank_step
#print axioms nonsingular_stageFloor_field
#print axioms HasOrder.nonsingular_stageFloor
#print axioms HasOrder.nonsingular_order_five_stages
#print axioms HasOrder.common_diagonal_order_five_stages
#print axioms strictSDIRK_order_five_isLeast_of_sqrt_six
#print axioms strictSDIRK_order_five_isLeast_realAlgebraic
#print axioms strictSDIRK_order_five_isLeast_real

