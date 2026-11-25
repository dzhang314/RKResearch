module

public import RKCert.ReviewedNative.CommonDiagonalGoodScalar
public import RKCert.ReviewedNative.SDIRKSixPaidPhysical

public section

/-! # Seven original stages for common-diagonal order six away from the
four SDIRK6 multipliers

The field result comes from the actual reviewed physical-chart proof,
not a field-bound premise or an extra chart-existence assumption. The
ring result also covers every nonunit common diagonal by the existing
explicit specialization. -/

namespace RKResearch

universe u
open scoped Matrix
open RKCert.ReviewedNative.SDIRKSixReceipts (fourExceptionProduct)

/-- Strict order-six floor over any field surviving the explicit
four-factor product. The only order contract is reviewed HasOrder. -/
theorem HasOrder.sdirk_order_six_stages_field_away_four
    {K : Type*} [Field K] {s : ℕ} {A : Matrix (Fin s) (Fin s) K}
    {b : Fin s → K} {γ : K} (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular)
    (hc : ∀ i, A i i = γ) (hγ : γ ≠ 0) (hD : (fourExceptionProduct : K) ≠ 0) :
    7 ≤ s :=
  Certified.Graded.SDIRKSix.seven_le_of_strict_order_six_away_four hD ho ha hc hγ

variable {R : Type u} [CommRing R] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R} {γ : R}

private theorem erkFloorSix : erkUniformFloor 6 = 7 := by
  have h := congrArg (fun xs : List ℕ => xs[6]?) erkUniformFloor_through_twenty
  change some (erkUniformFloor 6) = some 7 at h
  exact Option.some.inj h

/-- Six stages are necessary over any nontrivial commutative ring. -/
theorem HasOrder.common_diagonal_order_six_stages_universal [Nontrivial R]
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ) : 6 ≤ s := by
  have h := ho.common_diagonal_stage_floor ha hc
  exact (show 6 ≤ min (erkUniformFloor 6) ((((6 : ℕ)+1)^2/4+1)/2) by rw [erkFloorSix] <;> decide).trans h

/-- A lower-triangular original order-six tableau with common diagonal
has at least seven stages unless the diagonal is a unit and all
field images kill the four-factor exception product. -/
theorem HasOrder.common_diagonal_order_six_stages_away_four_or_nonunit
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hgood : ¬ IsUnit γ ∨ ¬ IsNilpotent (fourExceptionProduct : R)) : 7 ≤ s := by
  have h := ho.common_diagonal_stage_floor_away_nat (D := fourExceptionProduct) (k := 7)
    ha hc hgood
    (fun K _ B w δ hd ho' hB hδ hdδ =>
      ho'.sdirk_order_six_stages_field_away_four hB hδ hdδ hd)
  exact (show 7 ≤ min (erkUniformFloor 6) 7 by rw [erkFloorSix] <;> decide).trans h

/-- Arbitrary commutative coefficient ring, with no characteristic or
unit-diagonal premise. Nonnilpotence suffices, rather than invertibility,
for the explicit four-factor product. -/
theorem HasOrder.common_diagonal_order_six_stages_away_four
    (ho : HasOrder 6 A b) (ha : A.IsLowerTriangular) (hc : ∀ i, A i i = γ)
    (hD : ¬ IsNilpotent (fourExceptionProduct : R)) : 7 ≤ s :=
  ho.common_diagonal_order_six_stages_away_four_or_nonunit ha hc (Or.inr hD)

end RKResearch
