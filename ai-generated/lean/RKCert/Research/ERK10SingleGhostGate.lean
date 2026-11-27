import Lean

/-! Scalar receipts for the single invisible-ghost ERK10 chart.
The graded-space and restricted-transpose consequences are proved in the note. -/
namespace RKResearch.ERK10SingleGhostGate
open Lean.Grind
variable {K : Type} [Field K]

private theorem mulNZ {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

theorem stageThreeRead (theta t r : K) (ht : t ≠ 0)
    (paid : 2*theta*r=t^2) : r ≠ 0 := by
  intro zero
  have ht2 := mulNZ ht ht
  apply ht2
  grind

/-- Only for the additional rank-two F3 chart: the cubic error is
fitted at rows 2 and 3, yielding these two actual row-4 equations. -/
theorem rankTwoRowFour (theta t z a h : K)
    (quadratic : 2*(theta*a+t*h)=z^2)
    (cubic : 2*theta*t*a+3*t^2*h=z^3) :
    2*theta*t*a=z^2*(3*t-2*z) ∧ t^2*h=z^2*(z-t) := by
  have q := congrArg (fun x : K => t*x) quadratic
  have h₁ : t^2*h=z^2*(z-t) := by grind
  exact ⟨by grind,h₁⟩

theorem twoClockLocalization (alpha beta x y : K) (h : alpha-beta ≠ 0)
    (m₀ : x+y=0) (m₁ : alpha*x+beta*y=0) : x=0 ∧ y=0 := by
  have t : (alpha-beta)*x=0 := by grind
  exact ⟨(Field.of_mul_eq_zero t).resolve_left h,by grind⟩

/-- Here x,y,z are already multiplied by their nonzero defect amplitudes.
These are local scalar tests on amplitude groups, not aggregated clock tests. -/
theorem threeAmplitudeLocalization (a b c x y z : K)
    (hab : a-b ≠ 0) (hac : a-c ≠ 0) (hbc : b-c ≠ 0)
    (m₀ : x+y+z=0) (m₁ : a*x+b*y+c*z=0)
    (m₂ : a^2*x+b^2*y+c^2*z=0) :
    x=0 ∧ y=0 ∧ z=0 := by
  have h : ((a-b)*(a-c))*x=0 := by grind
  have hx := (Field.of_mul_eq_zero h).resolve_left (mulNZ hab hac)
  have k : (b-c)*y=0 := by grind
  exact ⟨hx,(Field.of_mul_eq_zero k).resolve_left hbc,by grind⟩

/-- If a clock has two opposing uniform-amplitude pairs, a nonzero
second-amplitude marked Gram needs both pairs to have already split. -/
theorem opposingPairSplits (a b w v delta eta : K)
    (first : a*w*delta+b*v*eta=0)
    (mark : a^2*w*delta+b^2*v*eta ≠ 0) :
    delta ≠ 0 ∧ eta ≠ 0 := by
  constructor
  · intro dz
    have cert := congrArg (fun x : K => b*x) first
    apply mark
    grind
  · intro ez
    have cert := congrArg (fun x : K => a*x) first
    apply mark
    grind

def beta4 (i j : Nat) : Int := 2520 / ((i+j+2)*(i+j+3) : Int)
def det2 (a : Nat → Nat → Int) : Int := a 0 0*a 1 1-a 0 1*a 1 0
def lowerMinor (a : Nat → Nat → Int) (j : Nat) : Nat → Nat → Int :=
  fun r c => a (r+1) (if c<j then c else c+1)
def det3 (a : Nat → Nat → Int) : Int :=
  a 0 0*det2 (lowerMinor a 0)-a 0 1*det2 (lowerMinor a 1)+a 0 2*det2 (lowerMinor a 2)
def det4 (a : Nat → Nat → Int) : Int :=
  a 0 0*det3 (lowerMinor a 0)-a 0 1*det3 (lowerMinor a 1)+
  a 0 2*det3 (lowerMinor a 2)-a 0 3*det3 (lowerMinor a 3)

theorem anchoredBetaPivots :
    beta4 0 0=420 ∧ det2 beta4=8820 ∧ det3 beta4=10584 ∧ det4 beta4=756 := by decide

end RKResearch.ERK10SingleGhostGate
#print axioms RKResearch.ERK10SingleGhostGate.stageThreeRead
#print axioms RKResearch.ERK10SingleGhostGate.rankTwoRowFour
#print axioms RKResearch.ERK10SingleGhostGate.twoClockLocalization
#print axioms RKResearch.ERK10SingleGhostGate.threeAmplitudeLocalization
#print axioms RKResearch.ERK10SingleGhostGate.opposingPairSplits
#print axioms RKResearch.ERK10SingleGhostGate.anchoredBetaPivots
