module

public import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace RKResearch.Certified.ERK10MirrorFactorialGate

/-- At the only paid scalar geometry of the six regular aligned branches,
the old endpoint clock-1 weight is forced by the first three nonconstant
scalar moments. The parameters represent its active masses at physical
clocks 2/5, 4/5 and 4/27; zero-clock mass drops out. -/
theorem forced_old_mass (a b c : ℚ)
    (h₁ : a*(2/5)+b*(4/5)+c*(4/27)=1/8)
    (h₂ : a*(2/5)^2+b*(4/5)^2+c*(4/27)^2=1/24)
    (h₃ : a*(2/5)^3+b*(4/5)^3+c*(4/27)^3=1/64) :
    a=5875/26112 := by
  linear_combination (-(3375:ℚ)/136) *
    (h₃ - ((4:ℚ)/5+4/27)*h₂ + ((4:ℚ)/5*(4/27))*h₁)

theorem unpaid_divisor : (17:ℕ) ∣ 26112 ∧ ¬ (17:ℕ) ∣ 5875 := by
  decide +kernel

end RKResearch.Certified.ERK10MirrorFactorialGate

#print axioms RKResearch.Certified.ERK10MirrorFactorialGate.forced_old_mass
#print axioms RKResearch.Certified.ERK10MirrorFactorialGate.unpaid_divisor
