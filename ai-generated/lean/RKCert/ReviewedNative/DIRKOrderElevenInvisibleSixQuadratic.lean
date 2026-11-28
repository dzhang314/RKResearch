module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharP.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

@[expose] public section
/-! # Leading and zero-clock gates for the invisible quadratic carrier -/
namespace RKResearch.Certified.Graded.OrderElevenInvisibleSixQuadratic

variable {K : Type*} [Field K] [CharZero K]

/-- The top and first two low coefficients of the supported grade-six
primitive identity recover the affine and quadratic carrier data.
The final relation is cleared, so the two necessary later divisions
are solely by the live first clock and the paid head scalar. -/
theorem profile_coefficient_recovery (b t s ell mu q : K)
    (lead : (1/5:K)=q+ell)
    (first : q=42*b*t*mu)
    (second : (ell-1/2)*b*t+q/3-mu*(t-b*s)=0) :
    ell=(1/5:K)-q ∧
    q*(b*s-t+14*b*t)=42*b^2*t^2*((3/10:K)+q) := by
  have h : ell=(1/5:K)-q := by linear_combination -lead
  refine ⟨h,?_⟩
  linear_combination 42*b*t*second-(t-b*s)*first-42*b^2*t^2*h

def pairQuartic (y : K) : K := 66*y^4-132*y^3+84*y^2-18*y+1
def jacobiFour (y : K) : K := 42*y^4-84*y^3+56*y^2-14*y+1

/-- At each noncentral clock of the fixed Lobatto pencil the
barycentric ratio is proportional to the literal clock. -/
theorem noncentral_head (y : K) (h : pairQuartic y=0) :
    jacobiFour y=(28/11:K)*(y^2-y+1/7) := by
  unfold jacobiFour pairQuartic at *
  linear_combination (7/11:K)*h

/-- The first ghost need not have a nonzero clock. The actual first
two paid marks force its clock to zero rather than exclude it. -/
theorem first_ghost_clock_zero (k x d : K)
    (h0 : d=x/2) (h1 : k+x*d=k+x^2/3) : x=0 := by
  have h : x^2=0 := by linear_combination 6*h1-6*x*h0
  by_contra xn
  exact (pow_ne_zero 2 xn) h

omit [CharZero K] in
/-- At that zero-clock ghost a live carrier value removes the clean
head coefficient from the next genuine marked row. -/
theorem head_calibration_zero (u tau e : K) (un : u≠0) (tn : tau≠0)
    (h : e*(u/tau)=0) : e=0 :=
  (mul_eq_zero.mp h).resolve_right (div_ne_zero un tn)

/-- The next ghost differs numerically from the first by the actual
dirty-clock census. Its two uncanceled own reads contradict. -/
theorem second_ghost_impossible (y d : K) (yn : y≠0)
    (h0 : y*d=y^2/3) (h1 : y^2*d=y^3/4) : False := by
  have h : y^3=0 := by linear_combination 12*h1-12*y*h0
  exact (pow_ne_zero _ yn) h

end RKResearch.Certified.Graded.OrderElevenInvisibleSixQuadratic
