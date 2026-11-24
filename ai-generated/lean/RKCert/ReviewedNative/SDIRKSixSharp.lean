module

public import RKCert.ReviewedNative.LaguerreGauss76Real
public import RKCert.ReviewedNative.SDIRKOrderSix

public section

/-! # Sharp stage count at order six for strict SDIRK -/

namespace RKResearch.Certified

private theorem strictSDIRK_order_six_isLeast_of_exact_witness {K : Type*} [Field K] [CharZero K]
    (hw : ∃ (A : Matrix (Fin 7) (Fin 7) K) (b : Fin 7 → K),
      A.IsLowerTriangular ∧ (∀ i, A i i = 1/2) ∧ (1/2:K) ≠ 0 ∧
        HasOrder 6 A b ∧ ¬ HasOrder 7 A b) :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 6 A b} 7 := by
  obtain ⟨A, b, ht, hc, hn, ho, -⟩ := hw
  refine ⟨⟨A, b, 1/2, ht, hc, hn, ho⟩, ?_⟩
  rintro s ⟨T, w, d, hT, hd, hn', h⟩
  exact h.sdirk_order_six_stages_field hT hd hn'

/-- Sharp over any characteristic-zero field where both radical
coordinates can be interpreted. The lower bound itself needs no roots. -/
theorem strictSDIRK_order_six_isLeast_of_sq_roots {K : Type*} [Field K] [CharZero K]
    {x y : K} (hx : x^2 = 2) (hy : y^2 = 15) :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (γ : K),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 6 A b} 7 := by
  let f := LaguerreGauss76.specialize x y hx hy
  exact strictSDIRK_order_six_isLeast_of_exact_witness
    ⟨LaguerreGauss76.A.map f, f ∘ LaguerreGauss76.b, LaguerreGauss76.exact_map f⟩

local notation "ℝₐ" => (algebraicClosure ℚ ℝ : Type)

/-- Seven is the least physical stage count at order six over the real
algebraic numbers. There is no positivity or stability constraint on the
competing tableaux. -/
theorem strictSDIRK_order_six_isLeast_realAlgebraic :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) ℝₐ) (b : Fin s → ℝₐ) (γ : ℝₐ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 6 A b} 7 :=
  strictSDIRK_order_six_isLeast_of_exact_witness LaguerreGauss76.exact_realAlgebraic

/-- Seven is the least physical stage count at order six over ℝ. -/
theorem strictSDIRK_order_six_isLeast_real :
    IsLeast {s : ℕ | ∃ (A : Matrix (Fin s) (Fin s) ℝ) (b : Fin s → ℝ) (γ : ℝ),
      A.IsLowerTriangular ∧ (∀ i, A i i = γ) ∧ γ ≠ 0 ∧ HasOrder 6 A b} 7 :=
  strictSDIRK_order_six_isLeast_of_exact_witness LaguerreGauss76.exact_real

end RKResearch.Certified
