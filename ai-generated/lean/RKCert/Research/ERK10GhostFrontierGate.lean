import Lean

/-! Scalar checks used by the singular-output ERK10 frontier. -/
namespace RKResearch.ERK10GhostFrontierGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

theorem lastTwoTaps (x y w z t : K) (nw : w ≠ 0) (nz : z ≠ 0) (nt : t ≠ 0)
    (h₀ : w*x+z*y=0) (h₁ : w*t*x=0) : x=0 ∧ y=0 := by
  have hx := (Field.of_mul_eq_zero h₁).resolve_left (nzMul nw nt)
  have hy : z*y=0 := by grind
  exact ⟨hx,(Field.of_mul_eq_zero hy).resolve_left nz⟩

theorem lastThreeTaps (x y z b₀ b₁ b₂ c₀ c₁ d₀ d₁ : K)
    (nb₀ : b₀ ≠ 0) (nb₁ : b₁ ≠ 0) (nb₂ : b₂ ≠ 0)
    (delta : c₀*d₁-c₁*d₀ ≠ 0)
    (h₀ : b₀*x+b₁*y+b₂*z=0)
    (h₁ : b₀*c₀*x+b₁*c₁*y=0)
    (h₂ : b₀*d₀*x+b₁*d₁*y=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  have hx : (c₀*d₁-c₁*d₀)*(b₀*x)=0 := by grind
  have hy : (c₀*d₁-c₁*d₀)*(b₁*y)=0 := by grind
  have xx := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero hx).resolve_left delta)).resolve_left nb₀
  have yy := (Field.of_mul_eq_zero ((Field.of_mul_eq_zero hy).resolve_left delta)).resolve_left nb₁
  have hz : b₂*z=0 := by grind
  exact ⟨xx,yy,(Field.of_mul_eq_zero hz).resolve_left nb₂⟩

theorem threeVisibleMoments (a b c x y z : K)
    (nab : a-b ≠ 0) (nac : a-c ≠ 0) (nbc : b-c ≠ 0)
    (h₀ : x+y+z=0) (h₁ : a*x+b*y+c*z=0)
    (h₂ : a^2*x+b^2*y+c^2*z=0) : x=0 ∧ y=0 ∧ z=0 := by
  have hx : ((a-b)*(a-c))*x=0 := by grind
  have xx := (Field.of_mul_eq_zero hx).resolve_left (nzMul nab nac)
  have hy : (b-c)*y=0 := by grind
  have yy := (Field.of_mul_eq_zero hy).resolve_left nbc
  exact ⟨xx,yy,by grind⟩

/-- After removal of a ghost block, its one quotient response
is transferred to the same surviving row of the full annihilator. -/
theorem exchangeOneGhostResponse (u v w k : K) (h : u+v=0) (hw : w=k*v) :
    -w=k*u := by grind

def ghostOriginModel (x : K) : K := 1-30*x+210*x^2-560*x^3+630*x^4-252*x^5

theorem originTerminal : ghostOriginModel (0:K)=1 ∧ ghostOriginModel (1:K)= -1 := by
  unfold ghostOriginModel
  grind

def originGram (j : Int) : Int :=
  2520/(j+1)-30*(2520/(j+2))+210*(2520/(j+3))
    -560*(2520/(j+4))+630*(2520/(j+5))-252*(2520/(j+6))

theorem originMoments : ∀ i : Fin 5, originGram i.val=0 := by decide

end RKResearch.ERK10GhostFrontierGate
#print axioms RKResearch.ERK10GhostFrontierGate.lastTwoTaps
#print axioms RKResearch.ERK10GhostFrontierGate.lastThreeTaps
#print axioms RKResearch.ERK10GhostFrontierGate.threeVisibleMoments
#print axioms RKResearch.ERK10GhostFrontierGate.exchangeOneGhostResponse
#print axioms RKResearch.ERK10GhostFrontierGate.originTerminal
#print axioms RKResearch.ERK10GhostFrontierGate.originMoments
