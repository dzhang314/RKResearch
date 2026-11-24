module

public import RKCert.ReviewedNative.CoefficientField
public import RKCert.ReviewedNative.ChangeCoefficients

public section

/-! # Exact coefficient descent for the reviewed stage predicate -/
namespace RKResearch
universe u

/-- A characteristic-zero field restriction can be removed while preserving
the same reviewed tableau size, triangularity, and tree order. -/
theorem HasOrder.lower_triangular_of_charZero_fields
    {R : Type u} [CommRing R] [CharZero R] {s p : ℕ} {Q : Prop}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder p A b) (ha : A.IsLowerTriangular)
    (hfield : ∀ (K : Type u) [Field K] [CharZero K]
      (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K),
      T.IsLowerTriangular → HasOrder p T w → Q) : Q :=
  RKCert.ReviewedNative.with_charZero_field fun K _ _ f =>
    hfield K (A.map f) (f ∘ b) (ha.map f) (h.map_coefficients f)

end RKResearch
