import Lean.Elab.Tactic.Grind

namespace RKResearch.Certified.ERK10NineLabelHeadScalars
open Lean.Grind

section Ring
variable {R : Type} [CommRing R]

/-- After eliminating the first two taps and the output score, this
is the numerator of the exact 2×2 head compatibility determinant. -/
theorem reducedHeadDeterminant (b c z k : R) :
    let s := b*k-2*c*k+c
    let a2 := 4*(2*k-1)*(3*b*c*k+s*z)
    let a3 := 12*b^2*c*k^2+(2*k-1)*s*z^2
    let b2 := 4*k*(2*k-1)
    let b3 := k*(3*b*k+(2*k-1)*z)
    a2*b3-a3*b2=12*b^2*k^3*(2*k-1)*(z-c) := by
  dsimp
  grind

def Ncleared (b k y : R) : R :=
  2*(4*b*k^2*y-4*b*k^2+2*b*k*y+2*b*k-2*k*y+y)

theorem closedRepeatAnchors (b c k : R) (gate : c*(2*k-1)=4*b*k) :
    Ncleared b k 1=(-2)*(2*k-1)*(1-c) ∧
    Ncleared b k b=(-2)*(1+2*k*(b-1))*(2*k-1)*(b-c) := by
  constructor
  · calc
      _=2*(c*(2*k-1)-(2*k-1)) := by unfold Ncleared; rw [gate]; grind
      _=_ := by clear gate; grind
  · calc
      _=2*(1+2*k*(b-1))*(4*b*k-(2*k-1)*b) := by unfold Ncleared; clear gate; grind
      _=_ := by rw [←gate]; grind

theorem halfReadFactor (y w u : R) (p : w*y^2+2*u=-2*(y-1)*u) :
    y*(w*y+2*u)=0 := by
  calc
    _=(w*y^2+2*u)+2*(y-1)*u := by clear p; grind
    _=0 := by rw [p]; grind
end Ring

theorem halfReadExit {F : Type} [Field F] (y w u : F) (nz : y ≠0)
    (p : w*y^2+2*u=-2*(y-1)*u) : w*y+2*u=0 := by
  have h := halfReadFactor y w u p
  grind

end RKResearch.Certified.ERK10NineLabelHeadScalars
#print axioms RKResearch.Certified.ERK10NineLabelHeadScalars.reducedHeadDeterminant
#print axioms RKResearch.Certified.ERK10NineLabelHeadScalars.closedRepeatAnchors
#print axioms RKResearch.Certified.ERK10NineLabelHeadScalars.halfReadExit
