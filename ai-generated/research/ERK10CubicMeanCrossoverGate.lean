import Lean

/-! Three paid mixed moments exclude the all-live two-pair ERK10 crossover. -/
namespace RKResearch.ERK10CubicMeanCrossoverGate
open Lean.Grind
variable {K : Type} [Field K]

def m0 (p q : K) : K :=
  42*p^2*q^2-42*p^2*q+12*p^2-42*p*q^2+48*p*q-15*p+12*q^2-15*q+5
def m1 (p q : K) : K :=
  -6*p^2*q+3*p^2-6*p*q^2+12*p*q-5*p+3*q^2-5*q+2
def m2 (p q : K) : K :=
  70*p^2*q^2-80*p^2*q+25*p^2-60*p*q^2+75*p*q-25*p+15*q^2-20*q+7
def z0 (k h : K) : K := 48*h^2-84*h*k+18*h+42*k^2-12*k+2
def z2 (k h : K) : K := 100*h^2-160*h*k+50*h+70*k^2-35*k+7
theorem center0 (m h : K) : m0 (1+m+h) (m-h)=z0 (m^2-h^2) h := by
  unfold m0 z0
  grind
theorem center1 (m h : K) : m1 (1+m+h) (m-h)=2*m*(6*h-6*(m^2-h^2)+1) := by
  unfold m1
  grind
theorem center2 (m h : K) : m2 (1+m+h) (m-h)=z2 (m^2-h^2) h := by
  unfold m2 z2
  grind

def d0 (h : K) : K := 42*h^4+84*h^3+60*h^2+18*h+2
def d2 (h : K) : K := 70*h^4+160*h^3+135*h^2+50*h+7
theorem zeroReduced (h : K) : z0 (-h^2) h=d0 h ∧ z2 (-h^2) h=d2 h := by
  unfold z0 z2 d0 d2
  constructor <;> grind
theorem zeroBezout (h : K) :
    5*(6510*h^3+9840*h^2+5025*h+914)*d0 h-
    6*(3255*h^3+3990*h^2+1605*h+217)*d2 h=26 := by
  unfold d0 d2
  grind

def p0 (h : K) : K := 36*h^2+36*h+7
def p2 (h : K) : K := 90*h^2+105*h+28
theorem firstReduced (k h : K) :
    6*z0 k h-p0 h=(42*k-42*h-5)*(6*k-6*h-1) := by
  unfold z0 p0
  grind
theorem thirdReduced (k h : K) :
    9*z2 k h-p2 h=5*(21*k-27*h-7)*(6*k-6*h-1) := by
  unfold z2 p2
  grind
theorem quadraticBezout (h : K) :
    (-75*h-35)*p0 h+(30*h+9)*p2 h=7 := by
  unfold p0 p2
  grind

theorem centeredNoCommonZero [IsCharP K 0] (m h : K)
    (a : m0 (1+m+h) (m-h)=0) (b : m1 (1+m+h) (m-h)=0)
    (c : m2 (1+m+h) (m-h)=0) : False := by
  have f0 := center0 m h
  have f1 := center1 m h
  have f2 := center2 m h
  by_cases hz : m=0
  · subst m
    have hd := zeroReduced h
    have hb := zeroBezout h
    grind
  · let k := m^2-h^2
    have hf : 6*k-6*h-1=0 := by
      have hf' : (2*m)*(6*h-6*k+1)=0 := by grind
      grind
    have hr0 := firstReduced k h
    have hr2 := thirdReduced k h
    have hbc := quadraticBezout h
    grind

theorem noCommonZero [IsCharP K 0] (p q : K)
    (a : m0 p q=0) (b : m1 p q=0) (c : m2 p q=0) : False := by
  let m : K := (p+q-1)/2
  let h : K := (p-q-1)/2
  have hp : 1+m+h=p := by grind
  have hq : m-h=q := by grind
  apply centeredNoCommonZero m h <;> simpa [hp,hq]

def term (a : List Int) (i : Nat) : Int := (a[i]?).getD 0
def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)
def left (p : Int) : List Int := [0,0,p^2,-2*p,1]
def right (q : Int) : List Int := product (product [1,-1] [1,-1]) (product [-q,1] [-q,1])
def secondLeft (p : Int) : List Int := [0,0,0,20*p^2,-30*p,12]
def integral (a : List Int) : Int :=
  a.zipIdx.foldl (fun s (g,j) => s+g*(2520/(j+1):Int)) 0
def im0 (p q : Int) : Int :=
  42*p^2*q^2-42*p^2*q+12*p^2-42*p*q^2+48*p*q-15*p+12*q^2-15*q+5
def im1 (p q : Int) : Int :=
  -6*p^2*q+3*p^2-6*p*q^2+12*p*q-5*p+3*q^2-5*q+2
def im2 (p q : Int) : Int :=
  70*p^2*q^2-80*p^2*q+25*p^2-60*p*q^2+75*p*q-25*p+15*q^2-20*q+7

/-- Each of the mixed integral polynomials has bidegree at most (2,2). -/
theorem allIntegralGrids : ∀ i j : Fin 3,
    let p := Int.ofNat i.val
    let q := Int.ofNat j.val
    integral (product (left p) (right q))=2*im0 p q ∧
    integral (product [-1,2] (product (left p) (right q)))=2*im1 p q ∧
    integral (product (secondLeft p) (right q))=12*im2 p q := by decide

end RKResearch.ERK10CubicMeanCrossoverGate
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.center0
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.center1
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.center2
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.zeroReduced
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.zeroBezout
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.firstReduced
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.thirdReduced
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.quadraticBezout
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.centeredNoCommonZero
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.noCommonZero
#print axioms RKResearch.ERK10CubicMeanCrossoverGate.allIntegralGrids
