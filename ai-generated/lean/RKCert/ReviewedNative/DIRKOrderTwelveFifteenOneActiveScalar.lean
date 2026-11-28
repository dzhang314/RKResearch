import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Field identities for the exact third-live-debut and same-clock return
conditions in the localized weighted cubic chart. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.OneActiveScalar

variable {K : Type*} [Field K] [CharZero K]

/-- Denominator-cleared moments of X(X-d)(X-v) and its first lift. -/
theorem thirdMoments (d v u : K) (hu : u ≠ 0)
    (h0 : 15*u^2 - 20*(d+v)*u + 30*d*v = 0)
    (h1 : 12*u^2 - 15*(d+v)*u + 20*d*v = 0) :
    5*(d+v) = 6*u ∧ 10*d*v = 3*u^2 ∧
    10*v^2 - 12*u*v + 3*u^2 = 0 ∧ 5*v^2 - 14*d*v + 5*d^2 = 0 := by
  have hc : u * (5*(d+v) - 6*u) = 0 := by
    linear_combination 2*h0 - 3*h1
  have hs : 5*(d+v) = 6*u := sub_eq_zero.mp ((mul_eq_zero.mp hc).resolve_left hu)
  have hp : 10*d*v = 3*u^2 := by linear_combination h0/3 + (4*u/3)*hs
  have hg : 10*v^2 - 12*u*v + 3*u^2 = 0 := by
    linear_combination (2*v)*hs - hp
  have hh : 5*v^2 - 14*d*v + 5*d^2 = 0 := by
    linear_combination (d+v+6*u/5)*hs - (12/5)*hp
  exact ⟨hs,hp,hg,hh⟩

/-- The degree-four scalar nodal integral with a receiver at its root. -/
theorem nodalIntegral (a b u : K) :
    u^5/5 - (a+b+u)*u^4/4 + (a*b+(a+b)*u)*u^3/3 - a*b*u^3/2 =
      -u^3*(3*u^2 - 5*(a+b)*u + 10*a*b)/60 := by ring

/-- Defect at a same-clock return when only the first two live nonzero
numeric sites have appeared. The last two premises are the true paid
linear and quadratic weighted primitive reads, after normalization only at a live row. -/
theorem quarticReturn (d v td tv sigma e : K)
    (h1 : d*td + v*tv = d^2/2)
    (h2 : d^2*td + v^2*tv = d^3/3 + sigma)
    (h3 : e = d^3*td + v^3*tv - d^4/4) :
    e - (3*d/2)*sigma = (v-d/2)*(sigma-d^3/6) := by
  linear_combination h3 + (d+v)*h2 - (d*v)*h1

#print axioms thirdMoments
#print axioms nodalIntegral
#print axioms quarticReturn

end RKResearch.Certified.Graded.OrderTwelveFifteen.OneActiveScalar
