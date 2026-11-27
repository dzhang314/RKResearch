import Lean

/-! Exact scalar certificates for the one-crossing five-pair ERK10 chart. -/
namespace RKResearch.ERK10FivePairOneCrossGate
open Lean.Grind
variable {K : Type} [Field K]

def F (u : K) : K := 126*u^6-138*u^4+51*u^2-5
def P (u : K) : K := 245*u^6-126*u^4+28*u^2-1
def M00 (u : K) : K := -105*u^3
def M01 (u : K) : K := 3*(14*u^2-1)
def M02 (u : K) : K := -3*u*(7*u^2+2)
def M12 (u : K) : K := 18*u^2-1
def M22 (u : K) : K := -u*(9*u^2+4)

theorem pivot (u : K) : M00 u*M02 u-M01 u^2=9*P u := by
  unfold M00 M02 M01 P
  grind

theorem determinant (u : K) :
    M00 u*(M02 u*M22 u-M12 u^2)-
    M01 u*(M01 u*M22 u-M12 u*M02 u)+
    M02 u*(M01 u*M12 u-M02 u^2)= -84*u^3*F u := by
  unfold M00 M01 M02 M12 M22 F
  grind

def n0 (u : K) : K := -3*(2982*u^4-2608*u^2+625)
def n1 (u : K) : K := -5*u*(4410*u^4-3528*u^2+521)

theorem solveFirstTwo (u : K) :
    M00 u*n0 u+M01 u*n1 u+1390*M02 u=105*u*F u ∧
    M01 u*n0 u+M02 u*n1 u+1390*M12 u=(3675*u^2-847)*F u := by
  unfold M00 M01 M02 M12 n0 n1 F
  constructor <;> grind

def iF (u : Int) : Int := 126*u^6-138*u^4+51*u^2-5
def iG (u : Int) : Int := 9015*u^4-6000*u^2+853
def iN0 (u : Int) : Int := -3*(2982*u^4-2608*u^2+625)
def iN1 (u : Int) : Int := -5*u*(4410*u^4-3528*u^2+521)
def mixA (u : Int) : Int := 210*u^4-60*u^2+10
def mixB (u : Int) : Int := -70*u^4+60*u^3+35*u^2-10*u-7
def normQuot (u : Int) : Int :=
  -50*(9724050*u^7+3500658*u^6-4769415*u^5-2841804*u^4+
      926100*u^3+960288*u^2+9261*u-28604)

/-- Degree bound 13 for the integer divisibility identity. -/
theorem seamNormGrid : ∀ i : Fin 14,
    let u := Int.ofNat i.val
    189*(1390*(mixB u)^2-iN1 u*mixA u*mixB u+iN0 u*(mixA u)^2)+
      13*1390*iG u=normQuot u*iF u := by decide

def term (a : List Int) (i : Nat) : Int := (a[i]?).getD 0
def product (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)

def integrated (u b : Int) : Int :=
  let p := 1+u
  let h := [0,0,0,10*p^2,-15*p,6]
  let rhs := product (product [-1,1] [-u,1]) (product [-b-1,2] [-u-1,2])
  (product h rhs).zipIdx.foldl (fun a (c,i) => a+c*(2520/(i+1):Int)) 0

/-- The integrand is degree at most 4 in U and affine in the last clock B. -/
theorem mixedGrid : ∀ i : Fin 5, ∀ j : Fin 2,
    let u := Int.ofNat i.val
    let b := Int.ofNat j.val
    integrated u b=6*(mixA u*b+mixB u) := by decide

def add37 (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map (fun i => (term a i+term b i)%37)
def fs : List Int := [-5,0,51,0,-138,0,126]
def ps : List Int := [-1,0,28,0,-126,0,245]
def gs : List Int := [853,0,-6000,0,9015]

theorem pivotBezout37 :
    add37 (product [19,0,21,0,15] fs) (product [15,0,26,0,24] ps) =
    [1,0,0,0,0,0,0,0,0,0,0] := by decide

theorem seamBezout37 :
    add37 (product [11] fs) (product [28,0,7] gs) =
    [1,0,0,0,0,0,0] := by decide

end RKResearch.ERK10FivePairOneCrossGate
#print axioms RKResearch.ERK10FivePairOneCrossGate.pivot
#print axioms RKResearch.ERK10FivePairOneCrossGate.determinant
#print axioms RKResearch.ERK10FivePairOneCrossGate.solveFirstTwo
#print axioms RKResearch.ERK10FivePairOneCrossGate.seamNormGrid
#print axioms RKResearch.ERK10FivePairOneCrossGate.mixedGrid
#print axioms RKResearch.ERK10FivePairOneCrossGate.pivotBezout37
#print axioms RKResearch.ERK10FivePairOneCrossGate.seamBezout37
