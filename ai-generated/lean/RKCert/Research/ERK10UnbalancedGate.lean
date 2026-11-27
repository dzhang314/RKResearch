import Lean

/-! Exact integer-grid receipts for the three centered ERK10 unbalanced gates.
The polynomial interpolation and rooted chronology bridges are mathematical. -/
namespace RKResearch.ERK10UnbalancedGate

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def horner (xs : List Int) (h : Int) : Int :=
  xs.foldl (fun v c => v*h+c) 0
def f0c3 (h : Int) : Int := 630*h^2 - 273*h + 28
def f0c2 (h : Int) : Int := -1890*h^4 + 1701*h^3 - 294*h^2 - 63*h + 7
def f0c1 (h : Int) : Int := 1890*h^6 - 2583*h^5 + 756*h^4 + 378*h^3 - 144*h^2 - 39*h + 14
def f0c0 (h : Int) : Int := -630*h^8 + 1155*h^7 - 490*h^6 - 315*h^5 + 389*h^4 - 135*h^3 + 4*h^2 + 7*h - 1
def f0 (h t : Int) : Int := ((f0c3 h*t+f0c2 h)*t+f0c1 h)*t+f0c0 h
def f1c3 (h : Int) : Int := 4032*h^2 - 2184*h + 315
def f1c2 (h : Int) : Int := -7308*h^4 + 6468*h^3 - 2189*h^2 + 420*h - 91
def f1c1 (h : Int) : Int := 2520*h^6 - 2856*h^5 - 1007*h^4 + 2160*h^3 - 342*h^2 - 368*h + 117
def f1c0 (h : Int) : Int := 756*h^8 - 1428*h^7 + h^6 + 1236*h^5 - 315*h^4 - 436*h^3 + 155*h^2 + 52*h - 21
def f1 (h t : Int) : Int := ((f1c3 h*t+f1c2 h)*t+f1c1 h)*t+f1c0 h
def bmc3 (h : Int) : Int := -18900*h^2 + 6300*h - 525
def bmc2 (h : Int) : Int := 56700*h^4 - 49140*h^3 - 27405*h^2 + 22890*h - 3185
def bmc1 (h : Int) : Int := -56700*h^6 + 79380*h^5 + 11025*h^4 - 54420*h^3 + 9130*h^2 + 8840*h - 2375
def bmc0 (h : Int) : Int := 18900*h^8 - 36540*h^7 + 16905*h^6 + 5610*h^5 - 3065*h^4 - 2720*h^3 + 1287*h^2 + 178*h - 107
def bm (h t : Int) : Int := ((bmc3 h*t+bmc2 h)*t+bmc1 h)*t+bmc0 h

def centeredAux (h t : Int) : Int × Int × Int × Int × Int :=
  let d := 1-2*h
  let a := 1-3*h
  let b := 6*d
  let n := 4*a*t-3*d*(t+h*h)+2*d*h-d
  (b,-12*d-6*a,6*d*(t-h*h)+12*a*t+n,-6*a*(t-h*h)-2*n,n*(t-h*h))

def centeredEquations (h t : Int) : Prop :=
  let (b,k3,k2,k1,k0) := centeredAux h t
  18*f0 h t=(3*k1+2*k3)*(b-21*k0)-k3*(3*k2+2*b) ∧
  9*f1 h t=(3*k1+2*k3)*t*(9*k3+21*k1)-(5*b+9*k2+21*k0)*(3*k2+2*b)

instance (h t : Int) : Decidable (centeredEquations h t) := by
  unfold centeredEquations
  infer_instance

theorem centeredGrid : ∀ h : Fin 9, ∀ t : Fin 4,
    centeredEquations h.val t.val := by decide

def mulQuadratics (a b c d e f : Int) : List Int :=
  [a*d, a*e+b*d, a*f+b*e+c*d, b*f+c*e, c*f]

def primitiveGram : List (List Int) :=
  [[3150,1050,1050,630,630],
   [-1050,0,-210,0,-90],
   [1050,210,350,150,210],
   [-630,0,-150,0,-70],
   [630,90,210,70,126]]

def mixedNumerator (h m : Int) : Int :=
  let d := 1-2*h
  let a := 1-3*h
  let n := 4*a*m*m-3*d*(m*m+h*h)+2*d*h-d
  let l := mulQuadratics n (-6*a*m) (6*d) (-m-h) (1-m-h) 1
  let r := mulQuadratics n (-6*a*m) (6*d) (m-h) (-1-m+h) 1
  l.zipIdx.foldl (fun v (x,i) => r.zipIdx.foldl (fun w (y,j) =>
    w+x*y*((primitiveGram[i]?.getD [])[j]?.getD 0)) v) 0

theorem mixedGrid : ∀ h : Fin 9, ∀ m : Fin 7,
    2*bm h.val ((m.val : Int)^2)=mixedNumerator h.val m.val := by decide
def cubicRes (a b c d e f g j : Int) : Int :=
  a^3*j^3 - a^2*b*g*j^2 - 2*a^2*c*f*j^2 + a^2*c*g^2*j - 3*a^2*d*e*j^2 + 3*a^2*d*f*g*j - a^2*d*g^3 + a*b^2*f*j^2 + 3*a*b*c*e*j^2 - a*b*c*f*g*j - a*b*d*e*g*j - 2*a*b*d*f^2*j + a*b*d*f*g^2 - 2*a*c^2*e*g*j + a*c^2*f^2*j + a*c*d*e*f*j + 2*a*c*d*e*g^2 - a*c*d*f^2*g + 3*a*d^2*e^2*j - 3*a*d^2*e*f*g + a*d^2*f^3 - b^3*e*j^2 + b^2*c*e*g*j + 2*b^2*d*e*f*j - b^2*d*e*g^2 - b*c^2*e*f*j - 3*b*c*d*e^2*j + b*c*d*e*f*g + 2*b*d^2*e^2*g - b*d^2*e*f^2 + c^3*e^2*j - c^2*d*e^2*g + c*d^2*e^2*f - d^3*e^3
def p19 (h : Int) : Int := horner [
    441946335600000, -1024065549360000, -1716533703801000, 10187613046453500,
    -18834576856532100, 19218982627705500, -11213233500544200, 2441419352562060,
    1578545809904970, -1562052983391630, 527881588475850, 4227770565495,
    -74457934523808, 29919279355936, -4803680324868, -252873665710,
    267188770570, -52730244326, 4905475082, -186251641] h
def q22 (h : Int) : Int := horner [
    13296116214284400000, -75081991091126040000, 172227661902117297000, -188218368191026750500,
    59272492408673304600, 78794526182080942800, -77929143913093164300, -6041921419900520460,
    41274925917081423660, -15629634084286158300, -8022149813035986390, 7485957746255680515,
    -521823336061114197, -1445005961744669919, 553080683491480719, 50213493241938018,
    -84341329666946766, 19087113977172438, 1588034900594488, -1649288693790549,
    358507957593695, -36311514435595, 1486547316275] h
def bezA (h : Int) : Int := horner [
    12, 8, -23, -20,
    2, -2, 7, -5,
    2, 18, -13, -8,
    -8, 5, 6, -16,
    -15, 23, -10, 21,
    2, -8] h
def bezB (h : Int) : Int := horner [
    -19, -14, 1, 7,
    17, 13, 5, 13,
    -9, 9, -9, -17,
    5, -2, -10, -16,
    23, -11, 6, 0] h

def result₀ (h : Int) : Int :=
  cubicRes (f0c3 h) (f0c2 h) (f0c1 h) (f0c0 h)
    (bmc3 h) (bmc2 h) (bmc1 h) (bmc0 h)
def result₁ (h : Int) : Int :=
  cubicRes (f1c3 h) (f1c2 h) (f1c1 h) (f1c0 h)
    (bmc3 h) (bmc2 h) (bmc1 h) (bmc0 h)

theorem resultantsGrid : ∀ i : Fin 49,
    let h : Int := i.val
    result₀ h=112896*(2*h-1)*(6*h-1)*p19 h ∧
    result₁ h=(-43008)*(2*h-1)^2*q22 h := by decide

theorem modularGrid : ∀ i : Fin 42,
    let h : Int := i.val
    (bezA h*(6*h-1)*p19 h+bezB h*q22 h-1)%47=0 := by decide

theorem leadingCoeffs :
    ((2651678013600000:Int)%47) ≠ 0 ∧ ((13296116214284400000:Int)%47) ≠ 0 := by decide

theorem symmetricNumeratorGrid : ∀ i : Fin 9,
    let h : Int := i.val
    bm h 0=(2*h-1)^2*
      (4725*h^6-4410*h^5-1365*h^4+1140*h^3+715*h^2-250*h-107) := by decide


open Lean.Grind
variable {K : Type} [Field K]

theorem singularMoment (s w : K)
    (h₀ : 40*s+47*w=0) (h₂ : 88*s+73*w=0)
    (h₁ : 120*s*w+73=0) (n1216 : (1216:K) ≠ 0)
    (n73 : (73:K) ≠ 0) : False := by
  have hz : (1216:K)*s=0 := by grind
  rw [(Field.of_mul_eq_zero hz).resolve_left n1216] at h₁
  exact n73 (by grind)

def symmetricP (h : K) : K := 21*h^3+7*h^2-13*h-7
def symmetricQ (h : K) : K :=
  4725*h^6-4410*h^5-1365*h^4+1140*h^3+715*h^2-250*h-107

theorem symmetricBezout (h : K) :
    (-11552625*h^5-2943675*h^4+6876450*h^3+574590*h^2-970545*h-692675)*symmetricP h
    +(51345*h^2+78120*h+29759)*symmetricQ h = 1664512 := by
  unfold symmetricP symmetricQ
  grind

end RKResearch.ERK10UnbalancedGate
#print axioms RKResearch.ERK10UnbalancedGate.centeredGrid
#print axioms RKResearch.ERK10UnbalancedGate.mixedGrid
#print axioms RKResearch.ERK10UnbalancedGate.resultantsGrid
#print axioms RKResearch.ERK10UnbalancedGate.modularGrid
#print axioms RKResearch.ERK10UnbalancedGate.leadingCoeffs
#print axioms RKResearch.ERK10UnbalancedGate.singularMoment
#print axioms RKResearch.ERK10UnbalancedGate.symmetricBezout
#print axioms RKResearch.ERK10UnbalancedGate.symmetricNumeratorGrid
