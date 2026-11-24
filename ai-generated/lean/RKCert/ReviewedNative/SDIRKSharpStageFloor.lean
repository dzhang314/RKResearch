module
public import RKCert.ReviewedNative.SDIRKOrderSixRing
public import RKCert.ReviewedNative.NonsingularDIRKQuadraticFloor

@[expose] public section

namespace RKResearch.Certified.Graded

/-- Closed form of the proved strict SDIRK floor, with its special
sixth-order improvement. It is a lower bound, not a general existence theorem. -/
def strictSDIRKStageFloor (p : ℕ) : ℕ := if p = 6 then 7 else ((p+1)^2/4+1)/2

end RKResearch.Certified.Graded

namespace RKResearch

open Certified.Graded
universe u

theorem HasOrder.strict_sdirk_stage_floor_field {K : Type*} [Field K] [CharZero K]
    {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {γ : K}
    (ho : HasOrder A b p) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hγ : γ ≠ 0) (hp : 0 < p) : strictSDIRKStageFloor p ≤ s := by
  by_cases he : p = 6
  · subst p; exact ho.sdirk_order_six_stages_field ha hc hγ
  · simpa [strictSDIRKStageFloor, he] using
      ho.nonsingular_quadratic_stage_floor_field ha (fun i => hc i ▸ hγ) hp

variable {R : Type u} [CommRing R] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}

theorem HasOrder.strict_sdirk_stage_floor_marked (ho : HasOrder A b p)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hm : ∀ n k : ℕ, 0 < n → (n:R)*γ^k ≠ 0) (hp : 0 < p) : strictSDIRKStageFloor p ≤ s :=
  RKCert.ReviewedNative.with_marked_charZero_field hm fun _ _ _ f hf =>
    (ho.map_coefficients f).strict_sdirk_stage_floor_field (ha.map f)
      (fun i => congrArg f (hc i)) hf hp

theorem HasOrder.strict_sdirk_stage_floor [CharZero R] (ho : HasOrder A b p)
    (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) (hu : IsUnit γ) (hp : 0 < p) :
    strictSDIRKStageFloor p ≤ s :=
  RKCert.ReviewedNative.with_charZero_field fun _ _ _ f =>
    (ho.map_coefficients f).strict_sdirk_stage_floor_field (ha.map f)
      (fun i => congrArg f (hc i)) (hu.map f).ne_zero hp

end RKResearch
