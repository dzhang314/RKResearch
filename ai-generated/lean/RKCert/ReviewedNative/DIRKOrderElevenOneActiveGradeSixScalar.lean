module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

@[expose] public section

/-! # Scalar gates for the paid grade-six suffix exclusion.
The tableau chronology, grading, and exact finite coefficient receipts
are separate from these purely algebraic eliminations. -/
namespace RKResearch.Certified.Graded.OrderElevenOneActiveGradeSix

variable {K : Type*} [CommRing K]

/-- One same-column correction cancels before any division by its
coefficient, including if that tap is zero. -/
theorem cancel_exterior_tap (P Q F G z e : K)
    (h0 : P+e=F) (h1 : Q+z*e=G) : Q-z*P=G-z*F := by
  linear_combination h1-z*h0

/-- Necessary quadratic Sylvester gate at a common finite root.
No division by a quadratic leader is used here. -/
theorem quadratic_gate (a b c d e f x : K)
    (hp : a*x^2+b*x+c=0) (hq : d*x^2+e*x+f=0) :
    (a*f-c*d)^2-(a*e-b*d)*(b*f-c*e)=0 := by
  have h0 : a*f-c*d=-(a*e-b*d)*x := by
    linear_combination a*hq-d*hp
  have h1 : b*f-c*e=(a*e-b*d)*x^2 := by
    linear_combination b*hq-e*hp
  rw [h0,h1]
  ring

/-- The real-only replay rejects negative fourth-column discriminants.
The good-reduction tower instead handles both quadratic roots at once. -/
theorem real_discriminant_gate {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b c x : R) (hp : a*x^2+b*x+c=0) : 0≤b^2-4*a*c := by
  have h : b^2-4*a*c=(2*a*x+b)^2 := by
    linear_combination -4*a*hp
  rw [h]
  exact sq_nonneg _

/-- Shape of the two fifth-column polynomials when a shared weight
variable multiplies the last donor tap. -/
theorem fifth_rows_clear (k z a b p q r s f g h : K)
    (h0 : (a+b*k)*k+p+q*k=f*k)
    (h1 : z*(a+b*k)*k+r+s*k=g*k+h) :
    (b*k^2+(a+q-f)*k+p=0) ∧
    (z*b*k^2+(z*a+s-g)*k+r-h=0) := by
  constructor
  · linear_combination h0
  · linear_combination h1

end RKResearch.Certified.Graded.OrderElevenOneActiveGradeSix
