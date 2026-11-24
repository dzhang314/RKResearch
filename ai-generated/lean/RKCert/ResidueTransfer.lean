module

public import RKCert.BaseChange
public import Mathlib.RingTheory.Ideal.Quotient.Basic

@[expose] public section

/-! # Transport of uniform stage obstructions to coefficient rings

For any nonzero commutative ring we choose a maximal ideal and map the actual
tableau to its residue field. A unit (but not merely a nonzero element) is
guaranteed to remain nonzero after this specialization. No ring-to-field map
or bound on the residue characteristic appears among the final ring hypotheses.
-/

namespace RKCert
universe u

variable {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ} {Q : Prop}

/-- Uniform ERK stage conclusions descend from fields to all nonzero rings. -/
theorem explicit_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K),
      StrictLower A → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) : Q := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hfield (R ⧸ I) _ _ (ha.map f) (ho.map f)

/-- DIRK, allowing arbitrary diagonal values before and after reduction. -/
theorem lowerTriangular_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K),
      (∀ i j, i.val < j.val → A i j = 0) → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j, i.val < j.val → A i j = 0) (ho : HasTreeOrderAtLeast A b p) : Q := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hfield (R ⧸ I) _ _ (lowerTriangular_map ha f) (ho.map f)

/-- Nonsingular lower triangular tableaux: each diagonal entry is required
to be a unit in the ring but the entries need not coincide. -/
theorem unitDiagonal_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K),
      (∀ i j, i.val < j.val → A i j = 0) → (∀ i, A i i ≠ 0) → HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R}
    (ha : ∀ i j, i.val < j.val → A i j = 0)
    (hd : ∀ i, IsUnit (A i i)) (ho : HasTreeOrderAtLeast A b p) : Q := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hfield (R ⧸ I) _ _ (lowerTriangular_map ha f)
    (fun i => ((hd i).map f).ne_zero) (ho.map f)

/-- Strict singly diagonal methods keep a common **nonzero** residue diagonal
provided the common ring diagonal is a unit. -/
theorem unitCommonDiagonal_of_all_fields
    (hfield : ∀ (K : Type u) [Field K] (A : Fin s → Fin s → K) (b : Fin s → K) (d : K),
      (∀ i j, i.val < j.val → A i j = 0) → (∀ i, A i i=d) → d≠0 →
      HasTreeOrderAtLeast A b p → Q)
    {A : Fin s → Fin s → R} {b : Fin s → R} {d : R}
    (ha : ∀ i j, i.val < j.val → A i j = 0)
    (he : ∀ i, A i i=d) (hd : IsUnit d) (ho : HasTreeOrderAtLeast A b p) : Q := by
  obtain ⟨I,hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  obtain ⟨he',hd'⟩ := map_unit_diagonal he hd f
  exact hfield (R ⧸ I) _ _ (f d) (lowerTriangular_map ha f) he' hd' (ho.map f)

end RKCert
