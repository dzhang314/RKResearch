module

public import Mathlib.RingTheory.Nilpotent.Lemmas
public import RKCert.ReviewedNative.CommonDiagonalStageFloor

public section

/-! # Transfer a good-field bound to a common-diagonal ring tableau

The exceptional scalar only needs to survive in one field image.
Equivalently, it must not be nilpotent. Alternatively the common
diagonal may be nonunit, when the existing explicit branch suffices.
The field-level bound is a premise, not a new elimination computation.
-/

namespace RKCert.ReviewedNative
universe u

/-- A scalar vanishes in every (same-universe) field image precisely
when it is nilpotent. Nonzero alone does not suffice over a ring. -/
theorem isNilpotent_iff_forall_field_images_eq_zero
    {R : Type u} [CommRing R] (d : R) :
    IsNilpotent d ↔ ∀ (K : Type u) [Field K] (f : R →+* K), f d = 0 := by
  constructor
  · intro hd K _ f
    exact isNilpotent_iff_eq_zero.mp (hd.map f)
  · intro hall
    refine nilpotent_iff_mem_prime.mpr ?_
    intro I hI
    letI := hI
    let K := FractionRing (R ⧸ I)
    let f : R →+* K := (algebraMap (R ⧸ I) K).comp (Ideal.Quotient.mk I)
    have hz : algebraMap (R ⧸ I) K (Ideal.Quotient.mk I d) = 0 := hall K f
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ I) K
    simpa only [map_zero] using hz

end RKCert.ReviewedNative

namespace RKResearch
universe u

open scoped Matrix

variable {R : Type u} [CommRing R] {s p k : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}

/-- Generic scalar transfer for the original tableau. Only its strict
field images in which the chosen scalar survives need be covered. A
nonunit common diagonal is already settled by the explicit branch, so
in that case no scalar-survival hypothesis is required. -/
theorem HasOrder.common_diagonal_stage_floor_at_scalar
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    {d : R} (hgood : ¬ IsUnit γ ∨ ¬ IsNilpotent d)
    (strict : ∀ (K : Type u) [Field K] (f : R →+* K), f d ≠ 0 →
      HasOrder p (A.map f) (f ∘ b) → (A.map f).IsLowerTriangular →
      (∀ i, (A.map f) i i = f γ) → f γ ≠ 0 → k ≤ s) :
    min (erkUniformFloor p) k ≤ s := by
  by_cases hu : IsUnit γ
  · have hdn : ¬ IsNilpotent d := hgood.resolve_left (fun h => h hu)
    by_contra hsmall
    apply hdn
    apply (RKCert.ReviewedNative.isNilpotent_iff_forall_field_images_eq_zero d).mpr
    intro K _ f
    by_contra hd
    have hdiag (i : Fin s) : (A.map f) i i = f γ := congrArg f (hc i)
    exact hsmall ((min_le_right _ _).trans
      (strict K f hd (RKResearch.HasOrder.map ho f) (ha.map f) hdiag (hu.map f).ne_zero))
  · exact (min_le_left _ _).trans (ho.common_diagonal_erk_floor_of_not_isUnit ha hc hu)

/-- For a natural exception product use the same integer in every field.
For example, with `p = 6` and strict bound `k = 7`,
`min (erkUniformFloor 6) 7 = 7`. -/
theorem HasOrder.common_diagonal_stage_floor_away_nat
    (ho : HasOrder p A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    {D : ℕ} (hgood : ¬ IsUnit γ ∨ ¬ IsNilpotent (D : R))
    (strict : ∀ (K : Type u) [Field K] (B : Matrix (Fin s) (Fin s) K)
      (w : Fin s → K) (δ : K), (D : K) ≠ 0 → HasOrder p B w →
      B.IsLowerTriangular → (∀ i, B i i = δ) → δ ≠ 0 → k ≤ s) :
    min (erkUniformFloor p) k ≤ s := by
  apply ho.common_diagonal_stage_floor_at_scalar ha hc hgood
  intro K _ f hd horder hlower hdiag hδ
  exact strict K (A.map f) (f ∘ b) (f γ)
    (by simpa only [map_natCast] using hd) horder hlower hdiag hδ

end RKResearch
