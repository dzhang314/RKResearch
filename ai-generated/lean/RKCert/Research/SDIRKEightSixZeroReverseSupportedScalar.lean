import Mathlib.Tactic.Ring.Basic

/-!
Division-free reverse supported-read identities. The actual flag and
chronological ingress is supplied by the mathematical source proof.
-/

namespace RKResearch.Certified.SDIRKEightSixZeroReverseSupportedScalar

variable {R : Type*} [CommRing R]

/-- Multiplying a supported reverse diagonal by its ordinary nodal derivative
gives the corresponding cardinal-numerator equality without dividing by a weight. -/
theorem cardinal_diagonal_clear {b₁ b₂ d₁ d₂ e₁ e₂ u₁ u₂ μ α B₁ B₂ : R}
    (h₁ : b₁*d₁ = μ*e₁) (h₂ : b₂*d₂ = μ*e₂)
    (hb₁ : b₁*u₁ = B₁) (hb₂ : b₂*u₂ = B₂)
    (he₁ : e₁*u₁ = α) (he₂ : e₂*u₂ = α) :
    B₁*d₁ = B₂*d₂ := by
  calc
    _ = (b₁*d₁)*u₁ := by rw [← hb₁]; ring1
    _ = μ*α := by rw [h₁, mul_assoc, he₁]
    _ = (b₂*d₂)*u₂ := by rw [h₂, mul_assoc, he₂]
    _ = _ := by rw [← hb₂]; ring1

/-- Form a graph profile of degree at most three that vanishes at the two
omitted forward zero clocks, with no inversion of either graph value. -/
def reverseTest (P Q : R → R) (a b x : R) : R :=
  P a * P b * (b-a) * Q x -
    P x * (P b * Q a * (b-x) + P a * Q b * (x-a))

theorem reverseTest_at_first (P Q : R → R) (a b : R) :
    reverseTest P Q a b a = 0 := by
  unfold reverseTest
  ring1

theorem reverseTest_at_second (P Q : R → R) (a b : R) :
    reverseTest P Q a b b = 0 := by
  unfold reverseTest
  ring1

/-- A forward linear graph gate may be used to clear its parameter before
the fourth reverse read, including the singular forward coefficient. -/
theorem clear_graph_parameter {F₀ F₁ ℓ p r : R} (h : F₀+ℓ*F₁ = 0) :
    F₁*p-F₀*r = F₁*(p+ℓ*r) := by
  calc
    _ = F₁*(p+ℓ*r)-(F₀+ℓ*F₁)*r := by ring1
    _ = _ := by rw [h]; ring1

end RKResearch.Certified.SDIRKEightSixZeroReverseSupportedScalar
