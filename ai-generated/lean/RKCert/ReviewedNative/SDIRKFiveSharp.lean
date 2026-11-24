module

public import RKCert.ReviewedNative.NonsingularDIRKStageFloor
public import RKCert.ReviewedNative.CooperSayfy55Real

public section

/-! # Sharp order-five stage count for strict SDIRK

The lower bound concerns all tableaux of order *at least* five; the
matching five-stage Cooper–Sayfy tableau even has exact order five.
Keep this consumer separate from the field- and ring-uniform obstruction.
-/

namespace RKResearch.Certified

private theorem strictSDIRK_order_five_isLeast_of_exact_witness {K : Type*} [Field K]
    (hw : ∃ (A : Matrix (Fin 5) (Fin 5) K) (b : Fin 5 → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b ∧ ¬ HasOrder 6 A b) :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b} 5 := by
  obtain ⟨A, b, γ, ht, hc, hn, ho, -⟩ := hw
  refine ⟨⟨A, b, γ, ht, hc, hn, ho⟩, ?_⟩
  rintro s ⟨T, w, d, hT, hd, -, h⟩
  exact h.common_diagonal_order_five_stages hT hd

/-- Sharp over any characteristic-zero field containing a square root of six.
No square-root or number-field hypothesis enters the lower bound. -/
theorem strictSDIRK_order_five_isLeast_of_sqrt_six {K : Type*} [Field K] [CharZero K]
    (x : K) (hx : x^2 = 6) :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b} 5 := by
  let f := CooperSayfy55.specialize x hx
  exact strictSDIRK_order_five_isLeast_of_exact_witness
    ⟨CooperSayfy55.A.map f, f ∘ CooperSayfy55.b, f CooperSayfy55.gamma,
      CooperSayfy55.specialized_exact x hx⟩

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

/-- Five is the least physical stage count for order-five strict SDIRK over
the actual field of real algebraic numbers. -/
theorem strictSDIRK_order_five_isLeast_realAlgebraic :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) ℝₐ) (b : Fin s → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b} 5 :=
  strictSDIRK_order_five_isLeast_of_exact_witness exists_strictSDIRK_exact_five_realAlgebraic

theorem strictSDIRK_order_five_isLeast_real :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 5 A b} 5 :=
  strictSDIRK_order_five_isLeast_of_exact_witness exists_strictSDIRK_exact_five_real

end RKResearch.Certified

