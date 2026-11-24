module

public import RKResearch.OrderConditions
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.RingTheory.Ideal.Quotient.Basic

public section

/-! # Native coefficient specialization

A unital coefficient map preserves exactly the reviewed matrix and tree
order conditions. Uniform lower triangular stage obstructions thereby
extend from fields to arbitrary nontrivial commutative rings. -/

namespace RKResearch

open scoped Matrix

section Change

variable {ι R S : Type*} [Fintype ι] [CommSemiring R] [CommSemiring S]

/-- Matrix and pointwise multiplication in the reviewed tree weight commute
with a unital coefficient map. -/
theorem map_Φ_coefficients (f : R →+* S) (A : Matrix ι ι R) (t : FiniteRootedTree) :
    f ∘ Φ t A = Φ t (A.map f) := by
  induction t with
  | leaf => funext i; simp [Φ]
  | butcherProduct t u ht hu =>
    funext i
    simp only [Φ, Function.comp_apply, Pi.mul_apply, map_mul, f.map_mulVec, hu]
    exact congrArg (fun x : ι → S => x i * ((A.map f) *ᵥ Φ u (A.map f)) i) ht

/-- No inverse, characteristic condition or stage restriction is required. -/
theorem HasOrder.map_coefficients {A : Matrix ι ι R} {b : ι → R} {p : ℕ}
    (h : HasOrder A b p) (f : R →+* S) :
    HasOrder (A.map f) (f ∘ b) p := by
  intro t ht
  simpa only [map_mul, map_natCast, RingHom.map_dotProduct, map_Φ_coefficients, map_one]
    using congrArg f (h t ht)

end Change

universe u

/-- In a lower triangular matrix the first coordinate where a column can be
nonzero sees only the diagonal. This is valid before choosing a field. -/
theorem lowerTriangular_mulVec_pivot {s : ℕ} {R : Type*} [CommSemiring R]
    {A : Matrix (Fin s) (Fin s) R} (ha : A.IsLowerTriangular) (i : Fin s)
    (v : Fin s → R) (hv : ∀ j, j < i → v j = 0) :
    (A *ᵥ v) i = A i i * v i := by
  rw [Matrix.mulVec_apply_eq_sum]
  apply Finset.sum_eq_single i
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with hjl | hjr
    · rw [hv j hjl, mul_zero]
    · have hz : A i j = 0 := ha hjr
      rw [hz, zero_mul]
  · simp

/-- Uniform lower-triangular bounds descend through a maximal ideal. The
unital map is chosen by the proof and is not a hypothesis on the input. -/
theorem HasOrder.lower_triangular_of_all_fields
    {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ} {C : Prop}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : A.IsLowerTriangular)
    (hf : ∀ (K : Type u) [Field K] (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K),
      T.IsLowerTriangular → HasOrder T w p → C) : C := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hf (R ⧸ I) (A.map f) (f ∘ b) (ha.map f) (h.map_coefficients f)

/-- Version preserving genuinely nonsingular diagonal entries. Unit
entries, not arbitrary nonzero entries, survive the proof's residue map. -/
theorem HasOrder.unit_diagonal_of_all_fields
    {R : Type u} [CommRing R] [Nontrivial R] {s p : ℕ} {C : Prop}
    {A : Matrix (Fin s) (Fin s) R} {b : Fin s → R}
    (h : HasOrder A b p) (ha : A.IsLowerTriangular) (hu : ∀ i, IsUnit (A i i))
    (hf : ∀ (K : Type u) [Field K] (T : Matrix (Fin s) (Fin s) K) (w : Fin s → K),
      T.IsLowerTriangular → (∀ i, T i i ≠ 0) → HasOrder T w p → C) : C := by
  obtain ⟨I, hI⟩ := Ideal.exists_maximal R
  let := hI
  let := Ideal.Quotient.field I
  let f := Ideal.Quotient.mk I
  exact hf (R ⧸ I) (A.map f) (f ∘ b) (ha.map f)
    (fun i => ((hu i).map f).ne_zero) (h.map_coefficients f)

end RKResearch
