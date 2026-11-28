import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10ZeroHighLargestScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

def headL (b c z : R) : R := 5*b*c-3*b*z-4*c^2+3*c*z
def headN (b c z : R) : R := b*c+3*b*z-2*c^2
def headM (b c z : R) : R := -3*z^2+4*(b+c)*z-6*b*c
def headT (b c z : R) : R := (2*c-b)*z-3*b*c

/-- Clearing the same row multipliers in the two actual reverse reads
cancels the first active clock entirely from the determinant. -/
theorem pureZeroHeadDet (b c z : R) :
    headL b c z * headT b c z - headN b c z * headM b c z =
      9*b*(z-b)*(z-c)^2 := by
  unfold headL headN headM headT
  grind

theorem pureZeroRepeatFactors (b c : R) :
    headL b c b = (2*c-b)*(3*b-2*c) ∧
    headN b c b = (b+c)*(3*b-2*c) ∧
    headL b c c = c*(2*b-c) ∧ headN b c c = 2*c*(2*b-c) := by
  unfold headL headN
  grind

theorem forwardResidualSecondDifference (r a s : R)
    (h2 : r^2 = a+2*s) (h3 : r^3 = a+3*s)
    (h4 : r^4 = a+4*s) : r^2*(r-1)^2=0 := by
  calc
    _ = r^2-2*r^3+r^4 := by clear h2 h3 h4; grind
    _ = 0 := by rw [h2,h3,h4]; grind

theorem twoReadElimination (p q l n m t h s : R)
    (r1 : p*l*h=q*m*s) (r2 : p*n*h=q*t*s) :
    p*(l*t-n*m)*h=0 := by
  calc
    _ = t*(p*l*h)-m*(p*n*h) := by clear r1 r2; grind
    _ = 0 := by rw [r1,r2]; grind

end Ring

private theorem cancelLeftZero {F : Type} [Field F] {p q : F}
    (pn : p ≠ 0) (pq : p*q=0) : q=0 := by
  have hp := congrArg (fun v => p⁻¹ * v) pq
  simpa [← Semiring.mul_assoc, Field.inv_mul_cancel pn, Semiring.one_mul, Semiring.mul_zero] using hp

private theorem timesNeZero {F : Type} [Field F] {p q : F}
    (pn : p ≠ 0) (qn : q ≠ 0) : p*q ≠ 0 :=
  fun h => qn (cancelLeftZero pn h)

theorem pureZeroDistinctExit {F : Type} [Field F] (a b c z h s : F)
    (nine : (9:F) ≠ 0) (four : (4:F) ≠ 0) (bn : b ≠ 0)
    (zb : z ≠ b) (zc : z ≠ c)
    (r1 : 4*b*headL b c z*h=a*(3*b-2*c)*headM b c z*s)
    (r2 : 4*b*headN b c z*h=a*(3*b-2*c)*headT b c z*s) :
    h=0 := by
  have hh := twoReadElimination (4*b) (a*(3*b-2*c))
    (headL b c z) (headN b c z) (headM b c z) (headT b c z)
    h s r1 r2
  rw [pureZeroHeadDet] at hh
  clear r1 r2
  have zb0 : z-b ≠ 0 := by clear hh; grind
  have zc0 : z-c ≠ 0 := by clear hh; grind
  have zc2 : (z-c)^2 ≠ 0 := by
    have hn := timesNeZero zc0 zc0
    have he : (z-c)^2 = (z-c)*(z-c) := by clear hh hn; grind
    rw [he]
    exact hn
  exact cancelLeftZero
    (timesNeZero (timesNeZero four bn) (timesNeZero (timesNeZero (timesNeZero nine bn) zb0) zc2))
    hh

end RKResearch.Certified.ERK10ZeroHighLargestScalars
#print axioms RKResearch.Certified.ERK10ZeroHighLargestScalars.pureZeroHeadDet
#print axioms RKResearch.Certified.ERK10ZeroHighLargestScalars.pureZeroRepeatFactors
#print axioms RKResearch.Certified.ERK10ZeroHighLargestScalars.forwardResidualSecondDifference
#print axioms RKResearch.Certified.ERK10ZeroHighLargestScalars.pureZeroDistinctExit
