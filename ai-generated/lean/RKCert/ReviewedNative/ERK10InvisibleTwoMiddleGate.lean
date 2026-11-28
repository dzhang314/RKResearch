import Lean

/-! Integer determinant certificate for the distinct-Lobatto-site
two-middle ERK10 causality seam. -/
namespace RKResearch.ERK10InvisibleTwoMiddleGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

def L (x : K) : K := 42*x^4 - 84*x^3 + 56*x^2 - 14*x + 1
def quo (x y : K) : K := 42*x^3 + 42*x^2*y - 84*x^2 + 42*x*y^2 - 84*x*y + 56*x + 42*y^3 - 84*y^2 + 56*y - 14
def cross (x y : K) : K := 18900*x^3*y^3 - 30240*x^3*y^2 + 13860*x^3*y - 1620*x^3 - 26460*x^2*y^3 + 42840*x^2*y^2 - 19980*x^2*y + 2400*x^2 + 10080*x*y^3 - 16560*x*y^2 + 7905*x*y - 990*x - 900*y^3 + 1500*y^2 - 735*y + 98
def a0 (x : K) : K := 42*x^3-84*x^2+56*x-14
def a1 (x : K) : K := 42*x^2-84*x+56
def a2 (x : K) : K := 42*x-84

theorem integralScale (x y : K) :
    196*cross x y =
    a0 y*(2100*a0 x+1260*a1 x+840*a2 x+600*42)
    +a1 y*(840*a0 x+560*a1 x+400*a2 x+300*42)
    +a2 y*(420*a0 x+300*a1 x+225*a2 x+175*42)
    +42*(240*a0 x+180*a1 x+140*a2 x+112*42) := by
  unfold cross a0 a1 a2
  grind

def rho (x : K) : K := 32130*x^3 - 38535*x^2 + 11985*x - 923
def m00 (x : K) : K := -10080*x^3 + 14700*x^2 - 5880*x + 532
def m01 (x : K) : K := 52920*x^3 - 73080*x^2 + 27090*x - 2310
def m02 (x : K) : K := -52920*x^3 + 70560*x^2 - 25200*x + 2100
def m10 (x : K) : K := -2100*x^3 + 2940*x^2 - 1120*x + 100
def m11 (x : K) : K := 15120*x^3 - 20160*x^2 + 7140*x - 588
def m12 (x : K) : K := -17640*x^3 + 22680*x^2 - 7770*x + 630
def m20 (x : K) : K := -630*x^3 + 840*x^2 - 300*x + 25
def m21 (x : K) : K := 5670*x^3 - 7350*x^2 + 2520*x - 200
def m22 (x : K) : K := -7560*x^3 + 9450*x^2 - 3150*x + 252

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
    14*cross x y*y^0=
      1*(m00 x+m01 x*y+m02 x*y^2)
       +(6300*x^3 - 8820*x^2 + 3360*x - 300)*quo x y
       +(-6300*x^2 - 6300*x*y + 8820*x - 6300*y^2 + 8820*y - 3360)*L x := by
  unfold cross quo L m00 m01 m02
  grind

theorem action1 (x y : K) :
    14*cross x y*y^1=
      1*(m10 x+m11 x*y+m12 x*y^2)
       +(-6300*x^4 + 6300*x^3*y + 11340*x^3 - 8820*x^2*y - 6720*x^2 + 3360*x*y + 1500*x - 300*y - 100)*quo x y
       +(6300*x^3 - 11340*x^2 - 2520*x*y + 6720*x - 2520*y^2 + 3360*y - 1500)*L x := by
  unfold cross quo L m10 m11 m12
  grind

theorem action2 (x y : K) :
    14*cross x y*y^2=
      1*(m20 x+m21 x*y+m22 x*y^2)
       +(-6300*x^4*y - 2520*x^4 + 6300*x^3*y^2 + 11340*x^3*y + 4620*x^3 - 8820*x^2*y^2 - 6720*x^2*y - 2820*x^2 + 3360*x*y^2 + 1500*x*y + 655*x - 300*y^2 - 100*y - 45)*quo x y
       +(6300*x^3*y + 2520*x^3 - 8820*x^2*y - 4620*x^2 + 2100*x*y + 2820*x - 1260*y^2 + 1320*y - 655)*L x := by
  unfold cross quo L m20 m21 m22
  grind

theorem detReduce (x : K) :
    determinant (m00 x) (m01 x) (m02 x) (m10 x) (m11 x)
       (m12 x) (m20 x) (m21 x) (m22 x)=(428652000*x^5 - 857304000*x^4 + 603288000*x^3 - 182044800*x^2 + 23908500*x - 1020600)*L x+84*rho x := by
  unfold determinant m00 m01 m02 m10 m11 m12 m20 m21 m22 L rho
  grind

theorem detBezout (x : K) :
    (49158900*x^2 - 52264800*x + 11219275)*L x+(-64260*x^3 + 119770*x^2 - 69370*x + 12124)*rho x=28823 := by
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

def LthreeHalves (x : K) : K := 1701*x^4 - 2268*x^3 + 1008*x^2 - 168*x + 8

theorem threeHalvesClear (x : K) : LthreeHalves x=8*L (3*x/2) := by
  unfold LthreeHalves L
  grind

theorem threeHalvesBezout (x : K) :
    (-12308436*x^3 + 13451508*x^2 - 3902094*x + 273591)*L x+(303912*x^3 - 534744*x^2 + 272748*x - 33038)*LthreeHalves x=9287 := by
  unfold L LthreeHalves
  grind

theorem noThreeHalves (x : K) (a : L x=0) (b : L (3*x/2)=0) : False := by
  have h := threeHalvesClear x
  rw [b] at h
  have q : LthreeHalves x=0 := by grind
  have z := threeHalvesBezout x
  rw [a,q] at z
  grind

theorem twoThirdsNotRoot : L ((2 : K)/3)= -1/27 := by
  unfold L
  grind

end RKResearch.ERK10InvisibleTwoMiddleGate
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.annihilator
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.quotientIdentity
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.action0
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.action1
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.action2
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.detReduce
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.detBezout
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.noCross
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.noThreeHalves
#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.twoThirdsNotRoot

#print axioms RKResearch.ERK10InvisibleTwoMiddleGate.integralScale
