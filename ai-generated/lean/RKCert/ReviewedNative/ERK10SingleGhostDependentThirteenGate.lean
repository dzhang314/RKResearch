import Lean

/-! Exact contacts for the dependent reversed ghost at physical stage 13. -/
namespace RKResearch.ERK10SingleGhostDependentThirteenGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem twoDistinctRoots (a b x y : K) (different : x ≠ y)
    (rootX : a+b*x=0) (rootY : a+b*y=0) : a=0 ∧ b=0 := by
  have h : b*(x-y)=0 := by grind
  have hb : b=0 := by grind
  exact ⟨by grind,hb⟩

theorem equalFirstCarrier (w tap : K) (hw : w ≠ 0)
    (quad : tap*w-w^2/2=-(w^2/2)) : tap=0 := by
  have h : tap*w=0 := by grind
  grind

/-- At the fourth reversed row the only earlier carrier was row two,
so the true quadratic/cubic read gives both entries separately. -/
theorem fourthCarrier (t a b : K) (ht : t ≠ 0)
    (quad : a+t*b=0) (cubic : 2*t*a+3*t^2*b=0) : a=0 ∧ b=0 := by
  have hb0 : t^2*b=0 := by
    calc
      t^2*b = (2*t*a+3*t^2*b)-2*t*(a+t*b) := by grind
      _ = 0 := by rw [quad,cubic]; grind
  have hb : b=0 := by grind
  exact ⟨by grind,hb⟩

theorem fourthNoncarrier (t x a b : K) (_ht : t ≠ 0)
    (quad : 2*a+2*t*b=x^2) (cubic : 2*t*a+3*t^2*b=x^3) :
    t^2*b=x^2*(x-t) ∧ 2*t*a=x^2*(3*t-2*x) := by
  constructor
  · calc
      t^2*b = (2*t*a+3*t^2*b)-t*(2*a+2*t*b) := by grind
      _ = x^2*(x-t) := by rw [quad,cubic]; grind
  · calc
      2*t*a = 3*t*(2*a+2*t*b)-2*(2*t*a+3*t^2*b) := by grind
      _ = x^2*(3*t-2*x) := by rw [quad,cubic]; grind

theorem responseTap (b_i b_j r s a : K) (bi : b_i ≠ 0) (sj : s ≠ 0)
    (adjoint : b_i*s=b_j*a*r) : a ≠ 0 := by
  intro hz
  grind

/-- The noncarrier correction removes the middle term in Q'(x). -/
theorem fifthPolynomialContact (t x y : K) :
    (2*x*(x-y)*(2*x-3*t)+x^2*(2*x-3*t)+2*x^2*(x-y))-
      x^2*(2*x-3*t)=6*x*(x-t)*(x-y) := by grind

/-- epsilon may be nonzero at the repeated fifth row. The extra term
    vanishes because any actual carrier has normalized clock p=1. -/
theorem repeatNumerator (t p a epsilon : K) :
    let dB := p*(2*t-3*p)*a+epsilon*(t-1)
    let dR := 3*p*(p-t)*a+epsilon*(1-(3/2:K)*t)
    t*((3*t-2*p)*dB-2*(p-t)*dR)+(3*t-2*p)^2*p^2*a =
      4*a*p^2*(p-t)*(p-2*t)+epsilon*t^2*(p-1) := by
  dsimp
  grind

theorem repeatDoubles (t p a epsilon : K) (pLive : p ≠ 0)
    (aLive : a ≠ 0) (distinct : p ≠ t) (carrier : epsilon=0 ∨ p=1)
    (moment : 4*a*p^2*(p-t)*(p-2*t)+epsilon*t^2*(p-1)=0) :
    p=2*t := by
  have hzero : epsilon*t^2*(p-1)=0 := by
    rcases carrier with e | h <;> grind
  have hproduct : 4*a*p^2*(p-t)*(p-2*t)=0 := by grind
  grind

end RKResearch.ERK10SingleGhostDependentThirteenGate
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.twoDistinctRoots
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.equalFirstCarrier
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.fourthCarrier
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.fourthNoncarrier
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.responseTap
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.fifthPolynomialContact
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.repeatNumerator
#print axioms RKResearch.ERK10SingleGhostDependentThirteenGate.repeatDoubles
