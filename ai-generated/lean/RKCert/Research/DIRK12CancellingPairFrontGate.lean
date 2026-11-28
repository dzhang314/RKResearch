import Lean

/-! Scalar closure for the true two-primitive gate at a first clean clock. -/
namespace RKResearch.DIRK12CancellingPairFrontGate
open Lean.Grind

/-- For P(x) = x(x-u)(a+bx), the two hypotheses are the actual
primitive equations J(P)(u)=J(xP)(u)=0, scaled by -12 and -60. -/
theorem twoPrimitives {K : Type} [Field K]
    (u a b : K) (hu : u ≠ 0)
    (h₀ : 2*a*u^3 + b*u^4 = 0)
    (h₁ : 5*a*u^4 + 3*b*u^5 = 0) : a = 0 ∧ b = 0 := by
  have e₀ : u^3*(2*a+b*u)=0 := by grind
  have e₁ : u^4*(5*a+3*b*u)=0 := by grind
  have n₂ : u*u ≠ 0 := fun h => (Field.of_mul_eq_zero h).elim hu hu
  have n₃ : u^3 ≠ 0 := by
    intro h
    have v : (u*u)*u=0 := by grind
    exact (Field.of_mul_eq_zero v).elim n₂ hu
  have n₄ : u^4 ≠ 0 := by
    intro h
    have v : u^3*u=0 := by grind
    exact (Field.of_mul_eq_zero v).elim n₃ hu
  have r₀ := (Field.of_mul_eq_zero e₀).resolve_left n₃
  have r₁ := (Field.of_mul_eq_zero e₁).resolve_left n₄
  have a₀ : a=0 := by grind
  have bu : b*u=0 := by grind
  exact ⟨a₀,(Field.of_mul_eq_zero bu).resolve_right hu⟩

end RKResearch.DIRK12CancellingPairFrontGate
#print axioms RKResearch.DIRK12CancellingPairFrontGate.twoPrimitives
