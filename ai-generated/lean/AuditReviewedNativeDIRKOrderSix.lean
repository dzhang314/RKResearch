module
import RKCert.ReviewedNative.DIRKOrderSix

open RKResearch
universe u

/-- Independent consumer using only the human predicate and the original matrix. -/
example {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder p A b) (ha : A.IsLowerTriangular) (hp : 6 ≤ p) : 5 ≤ s :=
  (show HasOrder 6 A b from fun t ht => h t (ht.trans hp)).dirk_order_six_stages ha

#check RKResearch.Certified.Graded.dirk_even_forward_stage_count
#check RKResearch.HasOrder.dirk_order_six_stages_field
#check RKResearch.HasOrder.dirk_order_six_stages
#print axioms RKResearch.Certified.Graded.dirk_even_forward_stage_count
#print axioms RKResearch.HasOrder.dirk_order_six_stages_field
#print axioms RKResearch.HasOrder.dirk_order_six_stages
