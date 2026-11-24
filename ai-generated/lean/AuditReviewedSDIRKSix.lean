import RKCert.ReviewedNative.SDIRKSharpStageFloor

open RKResearch RKResearch.Certified.Graded

-- The baseline and improved counts really differ at six.
example : nonsingularStageFloor 6 = 6 ∧ strictSDIRKStageFloor 6 = 7 := by decide
-- Adjacent orders, plus a case outside the legacy through-20 table.
example : [5,7,21].map strictSDIRKStageFloor = [5,8,61] := by decide

-- Direct consumption of the public, reviewed predicate on a matrix of fixed size.
example {K : Type*} [Field K] [CharZero K] {A : Matrix (Fin 6) (Fin 6) K}
    {b : Fin 6 → K} {γ : K} (h : HasOrder A b 6) (ht : A.IsLowerTriangular)
    (hd : ∀ i, A i i = γ) (hn : γ ≠ 0) : False := by
  have bound := h.sdirk_order_six_stages_field ht hd hn
  omega

-- No unit is required when the exact marker condition has been supplied.
example {R : Type*} [CommRing R] {s : ℕ} {A : Matrix (Fin s) (Fin s) R}
    {b : Fin s → R} {γ : R} (h : HasOrder A b 6) (ht : A.IsLowerTriangular)
    (hd : ∀ i, A i i = γ) (hm : ∀ n k : ℕ, 0 < n → (n:R)*γ^k ≠ 0) : 7 ≤ s :=
  h.sdirk_order_six_stages_marked ht hd hm

#print axioms HasOrder.sdirk_order_six_stages_field
#print axioms HasOrder.sdirk_order_six_stages_marked
#print axioms HasOrder.sdirk_order_six_stages
#print axioms HasOrder.strict_sdirk_stage_floor_field
#print axioms HasOrder.strict_sdirk_stage_floor_marked
#print axioms HasOrder.strict_sdirk_stage_floor
#print axioms RKCert.ReviewedNative.all_charZero_field_images_zero_iff
