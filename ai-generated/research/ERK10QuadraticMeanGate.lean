import Lean

/-! Exact scalar identities for the quadratic \(br\)-mean ERK10 exclusion.
The full nested rational norms and finite quotient algebras are replayed separately. -/
namespace RKResearch.ERK10QuadraticMeanGate
open Lean.Grind

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def f6 : List Int := [-59,283,109,1767,-864,31860,32400]
def lobatto : List Int := [1,-14,56,-84,42]
def jacobi : List Int := [-1,9,-21,14]
def poly (q : List Int) (x : Int) : Int := q.foldr (fun a z => a+x*z) 0

def val (a : List (List Int)) (i j : Nat) : Int :=
  ((a[i]?).getD [])[j]?.getD 0

/-- Fraction-free Bareiss determinant, with literal row swaps and singular exits. -/
def integerDet (a : List (List Int)) : Int :=
  let n := a.length
  let res := (List.range (n-1)).foldl (fun (s : List (List Int) × Int × Int) k =>
    let (M, prev, sign) := s
    if sign=0 then s else
      match ((List.range n).drop k).find? (fun i => val M i k != 0) with
      | none => (M,prev,0)
      | some i =>
        let N := (List.range n).map (fun t =>
          (M[if t=k then i else if t=i then k else t]?).getD [])
        let pivot := val N k k
        let D := (List.range n).map (fun r =>
          (List.range n).map (fun c =>
            if k<r ∧ k<c then (pivot*val N r c-val N r k*val N k c)/prev
            else val N r c))
        (D, pivot, if i=k then sign else -sign)) (a,1,1)
  res.2.2*val res.1 (n-1) (n-1)


def shifted (d : Int) : List Int :=
  (List.range 5).map (fun k =>
    (lobatto[k]?).getD 0+3*d*(jacobi[k]?).getD 0)

def sylvester (d : Int) : List (List Int) :=
  let a := (shifted d).reverse
  let b := (shifted d).zipIdx.map (fun (q,i) => q*(2:Int)^(4-i)) |>.reverse
  (List.range 8).map (fun i =>
    (List.range 8).map (fun j =>
      let k := i%4
      if j<k then 0 else ((if i<4 then a else b)[j-k]?).getD 0))

/-- The rescaled Sylvester determinant has parameter degree at most eight. -/
theorem contactResultantGrid : ∀ i : Fin 9,
    let d := Int.ofNat i.val
    integerDet (sylvester d)=1037232*(3*d-1)*poly f6 d := by decide

def momentX (q : List Int) : Int :=
  q.zipIdx.foldl (fun s (a,i) => s+a*(2520/(i+2):Int)) 0

theorem endpointMoment : momentX lobatto=84 ∧ momentX jacobi=126 := by decide

theorem outerClear {K : Type} [Field K] (x t a b : K) :
    t^3*(x^2+a*x+b)+(t^2+a*t+b)*x^2*(x-2*t) =
    (x-t)*((t^2+a*t+b)*x^2-(a*t^2+b*t)*x-b*t^2) := by grind

def term (a : List Int) (i : Nat) : Int := (a[i]?).getD 0
def product37 (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    ((List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)%37)
def cubicA : List Int := [35,15,17,1]
def cubicB : List Int := [33,8,29,1]
theorem factor37 : product37 [25] (product37 cubicA cubicB) =
    f6.map (fun a => a%37) := by decide

theorem cubicIrreducibleTests37 : ∀ i : Fin 37,
    poly cubicA (Int.ofNat i.val)%37≠0 ∧ poly cubicB (Int.ofNat i.val)%37≠0 := by decide

end RKResearch.ERK10QuadraticMeanGate
#print axioms RKResearch.ERK10QuadraticMeanGate.contactResultantGrid
#print axioms RKResearch.ERK10QuadraticMeanGate.endpointMoment
#print axioms RKResearch.ERK10QuadraticMeanGate.outerClear
#print axioms RKResearch.ERK10QuadraticMeanGate.factor37
#print axioms RKResearch.ERK10QuadraticMeanGate.cubicIrreducibleTests37
