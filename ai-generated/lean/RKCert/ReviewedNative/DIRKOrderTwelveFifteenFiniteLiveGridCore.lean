import Lean.Elab.Tactic.Omega

/-! Denominator-cleared coefficient contradictions for the exact cubic
site gate. The real affine-line arithmetic and true quadrature rank
are documented separately. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.FiniteLiveGridCore

theorem constantBDegenerate (b u : Int) (hb : b ≠ 0)
    (h0 : b*u = 0) (h1 : b+6*(u*u) = 0) : False := by
  rcases Int.mul_eq_zero.mp h0 with h | h
  · exact hb h
  · rw [h] at h1
    simp at h1
    exact hb h1

/-- The coefficient of the pole at the variable second symmetric sum
is minus 216 times the cube of delta. -/
theorem poleResidue (δ : Int) (h : -216*(δ*(δ*δ)) = 0) : δ = 0 := by
  have h' : δ*(δ*δ) = 0 := by omega
  rcases Int.mul_eq_zero.mp h' with h0 | h0
  · exact h0
  · rcases Int.mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exact h1

theorem variableBDegenerate (γ η α : Int) (hg : γ ≠ 0)
    (h0 : (-6*γ)*(η*η) = 0)
    (h1 : η-γ-12*(γ*α*η) = 0) : False := by
  rcases Int.mul_eq_zero.mp h0 with h | h
  · have hg' : γ = 0 := by omega
    exact hg hg'
  · rcases Int.mul_eq_zero.mp h with hη | hη
    · rw [hη] at h1
      simp at h1
      exact hg h1
    · rw [hη] at h1
      simp at h1
      exact hg h1

#print axioms constantBDegenerate
#print axioms poleResidue
#print axioms variableBDegenerate
end RKResearch.Certified.Graded.OrderTwelveFifteen.FiniteLiveGridCore
