module
public import RKCert.ReviewedNative.SDIRKOrderSix
public import RKCert.ReviewedNative.MarkedCoefficientField

public section

/-! # Transfer of the strict six-stage obstruction to coefficient rings

A common nonzero ring entry alone is not the premise used in field
specialization: the chosen characteristic-zero image must preserve it. -/
namespace RKResearch

universe u
variable {R : Type u} [CommRing R] {s : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}

/-- Exact simultaneous characteristic-zero and common-diagonal survival
condition. No freestanding characteristic assumption is required. -/
theorem HasOrder.sdirk_order_six_stages_marked (ho : HasOrder 6 A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hm : ∀ n k : ℕ, 0 < n → (n:R) * γ^k ≠ 0) : 7 ≤ s :=
  RKCert.ReviewedNative.with_marked_charZero_field hm fun _ _ _ f hf =>
    (ho.map_coefficients f).sdirk_order_six_stages_field (ha.map f)
      (fun i => congrArg f (hc i)) hf

/-- In a characteristic-zero ring, every unit diagonal survives, even if
the ring has zero divisors. -/
theorem HasOrder.sdirk_order_six_stages [CharZero R] (ho : HasOrder 6 A b)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (hu : IsUnit γ) : 7 ≤ s :=
  RKCert.ReviewedNative.with_charZero_field fun _ _ _ f =>
    (ho.map_coefficients f).sdirk_order_six_stages_field (ha.map f)
      (fun i => congrArg f (hc i)) (hu.map f).ne_zero

end RKResearch
