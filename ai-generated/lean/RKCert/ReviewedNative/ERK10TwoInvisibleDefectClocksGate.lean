import Lean

/-! Distinct-Lobatto mixed seam with the original origin masked
by the cubic scalar factor X. -/
namespace RKResearch.ERK10TwoInvisibleDefectClocksGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

def L (x : K) : K := 42*x^4 - 84*x^3 + 56*x^2 - 14*x + 1
def quo (x y : K) : K := 42*x^3 + 42*x^2*y - 84*x^2 + 42*x*y^2 - 84*x*y + 56*x + 42*y^3 - 84*y^2 + 56*y - 14
def cross (x y : K) : K := 11340*x^2*y^3 - 17640*x^2*y^2 + 7740*x^2*y - 840*x^2 + 11340*x*y^4 - 32760*x*y^3 + 31500*x*y^2 - 11415*x*y + 1170*x + 11340*y^5 - 32760*y^4 + 36900*y^3 - 19995*y^2 + 5055*y - 442
def rho (x : K) : K := 32130*x^3 - 78855*x^2 + 49995*x - 5531

def a0 (y : K) : K := 42*y^3-84*y^2+56*y-14
def a1 (y : K) : K := 42*y^2-84*y+56
def a2 (y : K) : K := 42*y-84
def g0 (x y : K) : K := 42*(x^2+x*y+y^2)-84*(x+y)+56
def g1 (x y : K) : K := 42*(x+y)-84
def quoTwo (x y z : K) : K := g0 x y+g1 x y*z+42*z^2

theorem integralScale (x y : K) :
    196*cross x y =
    a0 y*(1260*g0 x y+840*g1 x y+600*42)
    +a1 y*(560*g0 x y+400*g1 x y+300*42)
    +a2 y*(300*g0 x y+225*g1 x y+175*42)
    +42*(180*g0 x y+140*g1 x y+112*42) := by
  unfold cross a0 a1 a2 g0 g1
  grind

theorem quotientTwoIdentity (x y z : K) :
    (z-y)*quoTwo x y z=quo x z-quo x y := by
  unfold quoTwo quo g0 g1
  grind

def m00 (x : K) : K := -11340*x^3 + 16800*x^2 - 6930*x + 686
def m01 (x : K) : K := 70560*x^3 - 98280*x^2 + 36855*x - 3255
def m02 (x : K) : K := -79380*x^3 + 105840*x^2 - 37800*x + 3255
def m10 (x : K) : K := -3255*x^3 + 4620*x^2 - 1820*x + 185
def m11 (x : K) : K := 26460*x^3 - 35595*x^2 + 12810*x - 1134
def m12 (x : K) : K := -35280*x^3 + 45360*x^2 - 15540*x + 1365
def m20 (x : K) : K := -1365*x^3 + 1890*x^2 - 740*x + 85
def m21 (x : K) : K := 12285*x^3 - 16065*x^2 + 5670*x - 555
def m22 (x : K) : K := -18900*x^3 + 23625*x^2 - 7875*x + 756

def determinant (a b c d e f g h i : K) : K :=
  a*(e*i-f*h)-b*(d*i-f*g)+c*(d*h-e*g)

theorem annihilator (a b c d e f g h i y : K)
    (r0 : a+b*y+c*y^2=0) (r1 : d+e*y+f*y^2=0)
    (r2 : g+h*y+i*y^2=0) :
    determinant a b c d e f g h i=0 := by
  have ha : a= -b*y-c*y^2 := by grind
  have hd : d= -e*y-f*y^2 := by grind
  have hg : g= -h*y-i*y^2 := by grind
  rw [ha,hd,hg]
  unfold determinant
  clear r0 r1 r2 ha hd hg
  grind

theorem quotientIdentity (x y : K) : (y-x)*quo x y=L y-L x := by
  unfold quo L
  grind

theorem action0 (x y : K) :
    7*cross x y*y^0=
      1*(m00 x+m01 x*y+m02 x*y^2)
       +(1890*y^2 - 1680*y + 270)*quo x y
       +(0)*L x := by
  unfold cross quo L m00 m01 m02
  grind

theorem action1 (x y : K) :
    14*cross x y*y^1=
      2*(m10 x+m11 x*y+m12 x*y^2)
       +(-3780*x^3 + 5040*x^2 - 1800*x + 3780*y^3 - 3360*y^2 + 540*y + 155)*quo x y
       +(3780*x^2 + 3780*x*y - 5040*x + 3780*y^2 - 5040*y + 1800)*L x := by
  unfold cross quo L m10 m11 m12
  grind

theorem action2 (x y : K) :
    14*cross x y*y^2=
      2*(m20 x+m21 x*y+m22 x*y^2)
       +(3780*x^4 - 3780*x^3*y - 9240*x^3 + 5040*x^2*y + 7200*x^2 - 1800*x*y - 2000*x + 3780*y^4 - 3360*y^3 + 540*y^2 + 155*y + 155)*quo x y
       +(-3780*x^3 + 9240*x^2 + 4200*x*y - 7200*x + 4200*y^2 - 5400*y + 2000)*L x := by
  unfold cross quo L m20 m21 m22
  grind

theorem detReduce (x : K) :
    determinant (m00 x) (m01 x) (m02 x) (m10 x) (m11 x)
       (m12 x) (m20 x) (m21 x) (m22 x)=(2868594750*x^5 - 6265066500*x^4 + 4815058500*x^3 - 1576354500*x^2 + 225694350*x - 11985750)*L x-126*rho x := by
  unfold determinant m00 m01 m02 m10 m11 m12 m20 m21 m22 L rho
  grind

theorem detBezout (x : K) :
    (86704902767700*x^2 + 310475101345500*x - 650122641669675)*L x+(-113339742180*x^3 - 457334198370*x^2 + 564360943230*x - 125826816836)*rho x=45825482250241 := by
  unfold L rho
  grind

theorem noCross (x y : K) (left : L x=0) (right : L y=0)
    (distinct : x≠y) (paid : cross x y=0) : False := by
  have h := quotientIdentity x y
  rw [left,right] at h
  have q : quo x y=0 := by grind
  have p0 := action0 x y
  have p1 := action1 x y
  have p2 := action2 x y
  rw [left,q,paid] at p0 p1 p2
  have h0 : m00 x+m01 x*y+m02 x*y^2=0 := by grind
  have h1 : m10 x+m11 x*y+m12 x*y^2=0 := by grind
  have h2 : m20 x+m21 x*y+m22 x*y^2=0 := by grind
  have D := annihilator _ _ _ _ _ _ _ _ _ y h0 h1 h2
  have dd := detReduce x
  rw [D,left] at dd
  have rr : rho x=0 := by grind
  have bb := detBezout x
  rw [left,rr] at bb
  grind


theorem adjacentClock (t v k p a : K) (pn : p ≠ 0)
    (quad : 2*a*(t+k*v)=p^2)
    (cube : 3*a*(t^2+k*v^2)=p^3) :
    t+k*v≠0 ∧ 2*p*(t+k*v)=3*(t^2+k*v^2) := by
  have hn : t+k*v≠0 := by
    intro q
    rw [q] at quad
    grind
  have an : a≠0 := by
    intro q
    rw [q] at quad
    grind
  have q : a*(2*p*(t+k*v)-3*(t^2+k*v^2))=0 := by
    have q2 := congrArg (fun z : K => p*z) quad
    grind
  exact ⟨hn,by grind⟩

end RKResearch.ERK10TwoInvisibleDefectClocksGate
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.integralScale
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.quotientTwoIdentity
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.annihilator
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.quotientIdentity
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.action0
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.action1
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.action2
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.detReduce
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.detBezout
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.noCross
#print axioms RKResearch.ERK10TwoInvisibleDefectClocksGate.adjacentClock
