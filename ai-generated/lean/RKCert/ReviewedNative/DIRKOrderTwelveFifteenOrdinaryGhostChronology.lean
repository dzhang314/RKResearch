import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Native scalar gates for the genuine ordinary fourth-ghost chronology.
    The row and pure-space deductions have separate exact analytic proofs. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.OrdinaryGhostChronology

variable {K : Type*} [Field K] [CharZero K]

def s (a b : K) : K := b*(10*b^2-12*a*b+3*a^2)
def j (a b : K) : K := b^2*(b-a)*(5*b-3*a)/2
def ell (a b : K) : K := b^3*(b-a)^2/2
def f (a b : K) : K := b^2*(b-a)^2*(4*b-3*a)/2
def jx₂ (a b : K) : K := 5*b^6/3-12*a*b^5/5+3*a^2*b^4/4

/-- Determinant of the two paid primitive reads. Scaling the cubic by a
    nonzero constant scales both sides by its square. -/
theorem primitiveDeterminant (a b : K) :
    f a b*j a b-ell a b*(b-a)*s a b=-3*a*b^4*(a-b)^4/4 := by
  unfold f j ell s
  ring

/-- The actual two degree-six commutator hypotheses force the next live
    diagonal to be zero, without a factor involving the late ghost tap. -/
theorem secondDiagonal (a b beta M : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a-b ≠ 0)
    (hU : M*(f a b-beta*(b-a)*s a b)=beta^2*(b-a)*s a b)
    (hW : M*(ell a b-beta*j a b)=beta^2*j a b) :
    beta=0 := by
  have hd : beta^2*(f a b*j a b-ell a b*(b-a)*s a b)=0 := by
    linear_combination (ell a b-beta*j a b)*hU -
      (f a b-beta*(b-a)*s a b)*hW
  have hne : f a b*j a b-ell a b*(b-a)*s a b ≠ 0 := by
    rw [primitiveDeterminant]
    exact div_ne_zero
      (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha)
        (pow_ne_zero 4 hb)) (pow_ne_zero 4 hab)) (by norm_num)
  have hh := (mul_eq_zero.mp hd).resolve_right hne
  by_contra nz
  exact pow_ne_zero 2 nz hh

/-- The two primitive reads without an intervening ghost cannot both arise
    from a single physical diagonal. -/
theorem noLateCubicFit (a b beta : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : a-b ≠ 0)
    (hU : f a b=beta*(b-a)*s a b)
    (hW : ell a b=beta*j a b) : False := by
  have hd : f a b*j a b-ell a b*(b-a)*s a b=0 := by
    linear_combination j a b*hU - ((b-a)*s a b)*hW
  rw [primitiveDeterminant] at hd
  exact (div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero 4 hb))
       (pow_ne_zero 4 hab)) (by norm_num)) hd

/-- Once the literal ghost diagonal is b-z, its grade-five commutator read
    fixes the numerical ghost clock in terms of the first two live ones. -/
theorem fourthClock (a b z delta : K) (hb : b ≠ 0) (hba : b-a ≠ 0)
    (hd : delta=b-z)
    (h : (z-a-delta)*ell a b=delta*f a b) :
    (6*b-3*a)*z=b*(5*b-2*a) := by
  rw [hd] at h
  unfold ell f at h
  have hz : (b^2*(b-a)^2/2)*((6*b-3*a)*z-b*(5*b-2*a))=0 := by
    linear_combination h
  have hn : b^2*(b-a)^2/2 ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero 2 hb) (pow_ne_zero 2 hba)) (by norm_num)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hn)

/-- Exact grade-six coefficient combination after fixing the ghost clock. -/
theorem gradeSixCoefficient (x z : K)
    (hz : 3*(2*x-1)*z=x*(5*x-2)) :
    60*(2*x-1)*(jx₂ 1 x-j 1 x-(z+1)*f 1 x)
      = x^4*(2*x^2-6*x+5) := by
  unfold jx₂ j f
  linear_combination (-20*(x^2*(x-1)^2*(4*x-3)/2))*hz

/-- Explicit shifted Legendre derivative used by the actual F6 projection. -/
def L₆d (a : K) : K :=
  -42+840*a-5040*a^2+12600*a^3-13860*a^4+5544*a^5

/-- Coefficient identity for the late ghost at numerical zero. -/
theorem zeroGhostQuintic (a : K) :
    625*L₆d (2*a/5)+584*L₆d a =
      (126/5)*(129888*a^5-330000*a^4+312000*a^3-136800*a^2+27800*a-2015) := by
  unfold L₆d
  ring

#print axioms primitiveDeterminant
#print axioms secondDiagonal
#print axioms noLateCubicFit
#print axioms fourthClock
#print axioms gradeSixCoefficient
#print axioms zeroGhostQuintic

end RKResearch.Certified.Graded.OrderTwelveFifteen.OrdinaryGhostChronology
