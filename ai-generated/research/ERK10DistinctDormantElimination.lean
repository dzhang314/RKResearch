import Lean

/-! Exact integer determinant and scalar exits for the distinct dormant ERK10 seam.
The finite algebra tower is checked separately by the dependency-free replay. -/
namespace RKResearch.ERK10DistinctDormantElimination

set_option maxRecDepth 100000
set_option maxHeartbeats 0

def eCoeffs : List (List Int) := [[11, -3, -196, 60, 882, -378, -1764, 1260, 1323, -1323], [10, 156, 630, -2184, -714, 5964, -2646], [-336, 210, 2184, -6636, 0, 7938], [294, -588, 2646, -10584], [-1323, 3969]]
def oCoeffs : List (List Int) := [[-67, -126, 378, 1218, -1596, -3738, 4998, 2646, -3969], [222, -42, -924, 2940, -714, -7938, 10584], [168, 798, -4494, 7938, -7938], [210, -2646], [1323]]
def j4 : List Int := [1, 0, -14, 0, 21]
def g4 : List Int := [1, 0, -21, 0, 63]
def s5 : List Int := [-11, 3, 42, -18, -63, 63]
def g14 : List Int := [-2748, 8696, 79836, -432414, -1245339, 9348750, 15272853, -133142562, -16381260, 1084875624, -1844793216, -516287520, 4494130452, -4778612496, 1712893392]
def factors0 : List (List Int) := [[17, 12, 1], [17, 29, 1], [20, 2, 28, 29, 40, 1]]
def factors2 : List (List Int) := [[6, 1], [35, 1], [35, 1], [22, 0, 1], [38, 32, 5, 33, 11, 31, 5, 7, 17, 5, 16, 5, 17, 1]]

def poly (cs : List Int) (x : Int) : Int := cs.foldr (fun a z => a+x*z) 0
def rowAt (rs : List (List Int)) (h : Int) : List Int := rs.map (fun p => poly p h)
def bivar (rs : List (List Int)) (h t : Int) : Int := poly (rowAt rs h) t
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

def wt (k : Nat) : Int :=
  if k%2=0 then 1260/((k+1)*(k+3) : Int) else 0

def base (m h : Int) : List (List Int) :=
  (List.range 4).map (fun i =>
    (List.range 4).map (fun j =>
      if i<3 then wt (i+j+2)-2*m*wt (i+j+1)+(m^2-h^2)*wt (i+j)
      else 8*(m+h)^j+(2:Int)^(5-j)*(m+h-1)^j))

/-- Degrees in either grid variable are at most nine. -/
theorem baseDetGrid : ∀ i j : Fin 10,
    let m := Int.ofNat i.val
    let h := Int.ofNat j.val
    integerDet (base m h) =
      6144*(bivar eCoeffs h (m^2)+m*bivar oCoeffs h (m^2)) := by decide

theorem centeredFactorGrid : ∀ j : Fin 10,
    let h := Int.ofNat j.val
    bivar eCoeffs h 0 = -poly j4 h*poly s5 h := by decide

def sylvester (h : Int) : List (List Int) :=
  let E := (rowAt eCoeffs h).reverse
  let O := (rowAt oCoeffs h).reverse
  (List.range 8).map (fun i =>
    (List.range 8).map (fun j =>
      let k := i%4
      if j<k then 0 else
      ((if i<4 then E else O)[j-k]?).getD 0))

def resultChecks (h : Int) : Prop :=
  integerDet (sylvester h) = -3288952542855168*poly g4 h*poly g14 h
instance : Decidable (resultChecks h) := by unfold resultChecks; infer_instance

/-- Sylvester determinant degree bound: 4·9+4·8=68. -/
theorem resultantGrid1 : ∀ i : Fin 23, resultChecks (Int.ofNat i.val) := by decide
theorem resultantGrid2 : ∀ i : Fin 23, resultChecks (23+Int.ofNat i.val) := by decide
theorem resultantGrid3 : ∀ i : Fin 23, resultChecks (46+Int.ofNat i.val) := by decide

def mod41 (x : Int) : Int := x%41
def term (a : List Int) (i : Nat) : Int := (a[i]?).getD 0
def product41 (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    mod41 ((List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0))

theorem factor0 : factors0.foldl product41 [11] = product41 j4 s5 := by decide
theorem factor2 : factors2.foldl product41 [17] = product41 g4 g14 := by decide

end RKResearch.ERK10DistinctDormantElimination
#print axioms RKResearch.ERK10DistinctDormantElimination.baseDetGrid
#print axioms RKResearch.ERK10DistinctDormantElimination.centeredFactorGrid
#print axioms RKResearch.ERK10DistinctDormantElimination.resultantGrid1
#print axioms RKResearch.ERK10DistinctDormantElimination.resultantGrid2
#print axioms RKResearch.ERK10DistinctDormantElimination.resultantGrid3
#print axioms RKResearch.ERK10DistinctDormantElimination.factor0
#print axioms RKResearch.ERK10DistinctDormantElimination.factor2
