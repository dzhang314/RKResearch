module

public import RKCert.ReviewedNative.RationalUpper
public import RKCert.ReviewedNative.RationalDIRK7
public import RKCert.ReviewedNative.ChangeCoefficients
public import Mathlib.Data.Rat.Cast.CharZero

public section

/-!
# Characteristic-zero upper witnesses

The only extra ingredient beyond the native rational certificates and the
native coefficient-map theorem is injectivity: an embedding also reflects the
order conditions, so an explicit failed tree cannot disappear.
-/

namespace RKResearch

open scoped Matrix

/-- An injective coefficient map preserves *and reflects* every reviewed order.
In particular a strict failure transfers with the positive order assertion. -/
theorem hasOrder_map_coefficients_iff {ι R S : Type*} [Fintype ι]
    [CommSemiring R] [CommSemiring S] (f : R →+* S) (hf : Function.Injective f)
    (A : Matrix ι ι R) (b : ι → R) (p : ℕ) :
    HasOrder p (A.map f) (f ∘ b) ↔ HasOrder p A b :=
  RKResearch.hasOrder_map_iff (p := p) (A := A) (b := b) (f := f) hf

namespace Certified

variable (K : Type*) [Field K] [CharZero K]

/-- A four-stage explicit tableau of exact order four over every characteristic-zero field. -/
theorem exists_explicit_exact_four :
    ∃ (T : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → K),
      (∀ i j, i ≤ j → T i j = 0) ∧ HasOrder 4 T w ∧ ¬ HasOrder 5 T w := by
  let f := Rat.castHom K
  refine ⟨ClassicalRK4.A.map f, f ∘ ClassicalRK4.b, ?_, ClassicalRK4.order_four.map_coefficients f,
    fun h => ClassicalRK4.not_order_five ((hasOrder_map_coefficients_iff f f.injective _ _ _).mp h)⟩
  intro i j hij
  exact (congrArg f (ClassicalRK4.explicit i j hij)).trans (map_zero f)

/-- A strict SDIRK witness: one stage, common nonzero diagonal, exact order two. -/
theorem exists_strictSDIRK_exact_two :
    ∃ (T : Matrix (Fin 1) (Fin 1) K) (w : Fin 1 → K) (γ : K),
      T.IsLowerTriangular ∧ (∀ i, T i i = γ) ∧ γ ≠ 0 ∧ HasOrder 2 T w ∧ ¬ HasOrder 3 T w := by
  let f := Rat.castHom K
  refine ⟨ImplicitMidpoint.A.map f, f ∘ ImplicitMidpoint.b, f (1/2), ImplicitMidpoint.lowerTriangular.map f,
    fun i => congrArg f (ImplicitMidpoint.common_diagonal i), ?_, ImplicitMidpoint.order_two.map_coefficients f,
    fun h => ImplicitMidpoint.not_order_three ((hasOrder_map_coefficients_iff f f.injective _ _ _).mp h)⟩
  exact fun hz => ImplicitMidpoint.diagonal_ne_zero 0 (f.injective (hz.trans (map_zero f).symm))

/-- A three-stage DIRK tableau with genuinely nonconstant diagonal and exact order four. -/
theorem exists_DIRK_variable_diagonal_exact_four :
    ∃ (T : Matrix (Fin 3) (Fin 3) K) (w : Fin 3 → K),
      T.IsLowerTriangular ∧ (¬ ∃ γ, ∀ i, T i i = γ) ∧ HasOrder 4 T w ∧ ¬ HasOrder 5 T w := by
  let f := Rat.castHom K
  refine ⟨MidpointExtrapolation4.A.map f, f ∘ MidpointExtrapolation4.b,
    MidpointExtrapolation4.lowerTriangular.map f, ?_, MidpointExtrapolation4.order_four.map_coefficients f,
    fun h => MidpointExtrapolation4.not_order_five ((hasOrder_map_coefficients_iff f f.injective _ _ _).mp h)⟩
  rintro ⟨γ, h⟩
  have heq := f.injective ((h 0).trans (h 1).symm)
  exact (by decide +kernel : MidpointExtrapolation4.A 0 0 ≠ MidpointExtrapolation4.A 1 1) heq

/-- The seven-stage genuinely implicit, variable-diagonal tableau has exact order seven. -/
theorem exists_DIRK_variable_diagonal_exact_seven :
    ∃ (T : Matrix (Fin 7) (Fin 7) K) (w : Fin 7 → K),
      T.IsLowerTriangular ∧ T 1 1 ≠ 0 ∧ T 1 1 ≠ T 2 2 ∧ HasOrder 7 T w ∧ ¬ HasOrder 8 T w := by
  let f := Rat.castHom K
  refine ⟨RationalDIRK7.A.map f, f ∘ RationalDIRK7.b, RationalDIRK7.lowerTriangular.map f, ?_, ?_,
    RationalDIRK7.order_seven.map_coefficients f,
    fun h => RationalDIRK7.not_order_eight ((hasOrder_map_coefficients_iff f f.injective _ _ _).mp h)⟩
  · exact fun hz => RationalDIRK7.variable_diagonal.1 (f.injective (hz.trans (map_zero f).symm))
  · exact fun h => RationalDIRK7.variable_diagonal.2 (f.injective h)

end Certified
end RKResearch
