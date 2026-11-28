import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! Scalar no-late implicit diagonal projection, separated from actual rooted
    stage hypotheses. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.NoLateAffineMasks

variable {K : Type*} [Field K] [CharZero K]

def jc (x c₁ c₂ c₃ : K) : K := c₁*x^2/2+c₂*x^3/3+c₃*x^4/4
def jxc (x c₁ c₂ c₃ : K) : K := c₁*x^3/3+c₂*x^4/4+c₃*x^5/5
def linearGate (x c₁ c₂ c₃ : K) : K :=
  (2*x^2-2*x+3)*c₁+(x^2+2*x)*c₂+3*x^2*c₃

/-- Cleared coefficient of the genuine AC error comparison. -/
theorem acFactor (x c₁ c₂ c₃ : K) :
    6*(2*x-1)*(jc x c₁ c₂ c₃-jxc x c₁ c₂ c₃)
      -6*x^4*(2*x^2-6*x+5)*(jc 1 c₁ c₂ c₃-jxc 1 c₁ c₂ c₃)
      = -x^2*(x-1)^2*linearGate x c₁ c₂ c₃ := by
  unfold jc jxc linearGate
  ring

/-- The literal tap relation after the normalized masked cubic is used. -/
theorem tapRelation (x c₁ c₂ c₃ d p : K)
    (hs : c₁+c₂+c₃=1) (hlin : linearGate x c₁ c₂ c₃=0)
    (hd : d=jc 1 c₁ c₂ c₃) (hp : p=jc x c₁ c₂ c₃) :
    2*(5*x-3)*p+x^4*((6*x-10)*d-x+1)=0 := by
  rw [hd, hp]
  unfold jc
  unfold linearGate at hlin
  linear_combination ((x-1)*x^2)*hlin+((x-1)*x^4)*hs

def diagonalPoly (x d : K) : K :=
  20*(x-1)^2*d^2+(-12*x^2+24*x-9)*d+2*x^2-3*x+1

omit [CharZero K] in
/-- Eliminate the true tap with no division by 5x-3. -/
theorem diagonalProjection (x d p : K) (hx : x ≠ 0) (hx₁ : x-1 ≠ 0)
    (hp : 2*(5*x-3)*p+x^4*((6*x-10)*d-x+1)=0)
    (hr : (2*x-1)*(x-1-d)*p+d^2*x^4*(2*x^2-6*x+5)=0) :
    diagonalPoly x d=0 := by
  have hc : x^4*(x-1)*diagonalPoly x d=0 := by
    unfold diagonalPoly
    linear_combination 2*(5*x-3)*hr - ((2*x-1)*(x-1-d))*hp
  exact (mul_eq_zero.mp hc).resolve_left (mul_ne_zero (pow_ne_zero 4 hx) hx₁)

omit [CharZero K] in
/-- A zero first physical diagonal is excluded away from the literal clock
    collisions and the already excluded half-clock. -/
theorem implicitFirst (x d : K) (hx₁ : x-1 ≠ 0) (hxhalf : 2*x-1 ≠ 0)
    (h : diagonalPoly x d=0) : d ≠ 0 := by
  intro hz
  rw [hz] at h
  unfold diagonalPoly at h
  have hc : (x-1)*(2*x-1)=0 := by linear_combination h
  exact (mul_ne_zero hx₁ hxhalf) hc

/-- The exact real discriminant gate. -/
theorem discrimNonnegative {L : Type*} [Field L] [LinearOrder L] [IsStrictOrderedRing L]
    (x d : L) (h : diagonalPoly x d=0) :
    0 ≤ -(2*x-1)*(8*x^3+12*x^2-30*x+1) := by
  have he : (40*(x-1)^2*d+(-12*x^2+24*x-9))^2 =
      -(2*x-1)*(8*x^3+12*x^2-30*x+1) := by
    unfold diagonalPoly at h
    linear_combination 80*(x-1)^2*h
  rw [← he]
  exact sq_nonneg _

#print axioms acFactor
#print axioms tapRelation
#print axioms diagonalProjection
#print axioms implicitFirst
#print axioms discrimNonnegative

end RKResearch.Certified.Graded.OrderTwelveFifteen.NoLateAffineMasks
