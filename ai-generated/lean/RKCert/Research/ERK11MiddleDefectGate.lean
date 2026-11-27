import Lean

/-! Polynomial arithmetic for the first/last middle-stage gate in the
six–five–six four-carrier ERK11 chart. -/
namespace RKResearch.ERK11MiddleDefectGate
open Lean.Grind
variable {K : Type} [Field K]

def G (z : K) : K := 6*z*z-15*z+10
def R (x z : K) : K :=
  6*x*x*z*z-24*x*x*z+20*x*x+3*x*z*z+12*x*z-18*x-7*z*z+8*z
def Kq (a : K) : K := 75*a*a+15*a+62

private theorem nzMul {a b : K} (ha : a ≠ 0) (hb : b ≠ 0) : a*b ≠ 0 :=
  fun h => hb ((Field.of_mul_eq_zero h).resolve_left ha)

/-- Numerator of the exact left-zero-lift moment, in normalized
clock coordinates. The denominator is 30(z−1)². -/
theorem middleFactor (x z : K) :
    (z-1)*(z-1)*x*G x+(1-x)*R x z =
      (x-z)*(2*x-1)*((6*z-7)*x-7*z+8) := by
  unfold G R
  grind

theorem interpolationAtHalf (x z : K)
    (half : 2*x=1) : R x z= -4*(z-1)*(z-1) := by
  unfold R
  grind

theorem interpolationAtOne (z : K) :
    R 1 z=2*(z-1)*(z-1) := by unfold R; grind

theorem interpolationAtZ (z : K) :
    R z z=z*(z-1)*G z := by unfold R G; grind

/-- Both roots of the left quadratic share the other degree-two
state only at the stated coefficient ratio. -/
theorem newSideRatio (z x a : K)
    (phi : (6*z-7)*x=7*z-8)
    (cubicValueAtOne : (1-z)*(1-x)= -1)
    (quadraticCoeff : 2*(z+x)+5*a=1) :
    5*a=9 := by grind

/-- Repeated first-middle clock and quadratic state force
a precise ratio polynomial, clearing rather than dividing by a pivot. -/
theorem repeatSideRatio (z a : K) (n3 : (3:K) ≠ 0)
    (g : G z=0)
    (fit : 5*a*(z-1)+2*z*z-z-3=0) : Kq a=0 := by
  have l : (15*a+12)*z=15*a+19 := by
    unfold G at g
    grind
  have e : (15*a+12)*(15*a+12)*G z =
      6*((15*a+12)*z)*((15*a+12)*z) -
        15*((15*a+12)*z)*(15*a+12)+10*(15*a+12)*(15*a+12) := by
    unfold G
    grind
  rw [g,Semiring.mul_zero,l] at e
  have q : (3:K)*Kq a=0 := by unfold Kq; grind
  exact (Field.of_mul_eq_zero q).resolve_left n3

/-- The opposing directions cannot both support that same
quadratic state; guards expose every exceptional prime of this
three-way exact gate. -/
theorem opposedQuadratic (a b : K)
    (inverse : a*b=1) (notMinus : a+1 ≠ 0)
    (n56 : (56:K) ≠ 0) (n7572 : (7572:K) ≠ 0)
    (n13 : (13:K) ≠ 0) (n152 : (152:K) ≠ 0)
    (front : 5*a=9 ∨ Kq a=0) (rear : 5*b=9 ∨ Kq b=0) : False := by
  rcases front with x|x <;> rcases rear with y|y
  · apply n56
    have p1 := congrArg (fun z => z*(5*b)) x
    have p2 := congrArg (fun z => (9:K)*z) y
    have p3 := congrArg (fun z => (25:K)*z) inverse
    grind
  · have row : 9*b=5 := by
      have p1 := congrArg (fun z => z*b) x
      have p2 := congrArg (fun z => (5:K)*z) inverse
      grind
    apply n7572
    have w : (81:K)*Kq b=75*(9*b)*(9*b)+135*(9*b)+5022 := by
      unfold Kq
      grind
    rw [y,Semiring.mul_zero,row] at w
    grind
  · have row : 9*a=5 := by
      have p1 := congrArg (fun z => a*z) y
      have p2 := congrArg (fun z => (5:K)*z) inverse
      grind
    apply n7572
    have w : (81:K)*Kq a=75*(9*a)*(9*a)+135*(9*a)+5022 := by
      unfold Kq
      grind
    rw [x,Semiring.mul_zero,row] at w
    grind
  · have w : (a*a)*Kq b=75*(a*b)*(a*b)+15*a*(a*b)+62*a*a := by
      unfold Kq
      grind
    rw [y,Semiring.mul_zero,inverse] at w
    simp only [Semiring.mul_one] at w
    have x' : 75*a*a+15*a+62=0 := x
    have h : (13:K)*((a-1)*(a+1))=0 := by
      calc
        _ = (75*a*a+15*a+62)-(75+15*a+62*a*a) := by
          clear inverse notMinus n56 n7572 n13 n152 x y w x'
          grind
        _ = 0 := by rw [x',←w,AddCommGroup.sub_self]
    have hv := (Field.of_mul_eq_zero h).resolve_left n13
    have ez := AddCommGroup.sub_eq_zero_iff.mp ((Field.of_mul_eq_zero hv).resolve_right notMinus)
    have atOne : Kq (1:K)=152 := by unfold Kq; grind
    rw [ez,atOne] at x
    exact n152 x

/-- Cubic rather than quadratic state is also excluded when both
middle boundaries are new. The coefficient sign comes from reflection
of the same physical cubic. -/
theorem opposedNewCubic (a b k h : K)
    (inverse : a*b=1) (notMinus : a+1 ≠ 0) (n4 : (4:K) ≠ 0)
    (front : k=a*(5*a-9)) (rear : h=b*(5*b-9))
    (reflect : a*a*a*h= -k) : False := by
  have rv : a*a*a*h=a*(5-9*a) := by
    rw [rear]
    have m : a*a*a*(b*(5*b-9))=a*(a*b)*(5*(a*b)-9*a) := by grind
    rw [m,inverse]
    grind
  have nonzero : a ≠ 0 := by intro zz; grind
  have zz : a*((4:K)*(a+1))=0 := by grind
  exact nzMul n4 notMinus ((Field.of_mul_eq_zero zz).resolve_left nonzero)

/-- The middle two-path moment has this centered positive
numerator over any ordered field. -/
theorem centeredPath (x : K) :
    16*(660*x^4-1320*x^3+1045*x^2-385*x+56) =
       660*(2*x-1)^4+220*(2*x-1)^2+16 := by grind

end RKResearch.ERK11MiddleDefectGate
#print axioms RKResearch.ERK11MiddleDefectGate.middleFactor
#print axioms RKResearch.ERK11MiddleDefectGate.interpolationAtHalf
#print axioms RKResearch.ERK11MiddleDefectGate.interpolationAtOne
#print axioms RKResearch.ERK11MiddleDefectGate.interpolationAtZ
#print axioms RKResearch.ERK11MiddleDefectGate.newSideRatio
#print axioms RKResearch.ERK11MiddleDefectGate.repeatSideRatio
#print axioms RKResearch.ERK11MiddleDefectGate.opposedQuadratic
#print axioms RKResearch.ERK11MiddleDefectGate.opposedNewCubic
#print axioms RKResearch.ERK11MiddleDefectGate.centeredPath