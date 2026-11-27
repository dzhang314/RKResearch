import Lean

/-! Exact coefficient gate for the two-weight clean-node reduction. -/
namespace RKResearch.ERK11CleanJacobiGate
open Lean.Grind
variable {K : Type} [Field K]

/-- For J=Z(Z−1) and R=1−kZ, the columns J,ZJ,R,ZR are
independent when 1−k is live. The extra column Z²J then supplies
the missing leading degree for the five-column space. -/
theorem independentFour (k a b c d : K) (g : 1-k ≠ 0)
    (at0 : c=0) (at1 : -a-k*c+d=0)
    (at2 : a-b-k*d=0) (at3 : b=0) :
    a=0 ∧ b=0 ∧ c=0 ∧ d=0 := by
  have e : (1-k)*a=0 := by grind
  have ez := (Field.of_mul_eq_zero e).resolve_left g
  exact ⟨ez,at3,at0,by grind⟩

/-- Factors stay coprime even if k=0. -/
theorem paidBezout (k z : K) :
    k*k*(z*(z-1))+(k*z+1-k)*(1-k*z)=1-k := by grind

end RKResearch.ERK11CleanJacobiGate
#print axioms RKResearch.ERK11CleanJacobiGate.independentFour
#print axioms RKResearch.ERK11CleanJacobiGate.paidBezout
