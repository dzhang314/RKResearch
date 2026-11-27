module

public import RKCert.ReviewedNative.DIRKOrderTenOffCoreTwoOffScalar

@[expose] public section

/-! # Active off-core DIRK10/11 with an exterior head at 1

Unlike the terminal-unique certificate, the affine barycentric numerator
need not have a real terminal zero. The two paid h moments determine it
up to the affine terminal-profile coefficient; the companion proof
checks this bridge and each exact factor outside the finite replay. -/
namespace RKResearch.Certified.Graded.OffCoreHeadOneScalar

open ConstantOneOffScalar UniformOneOffPolynomialScalar
open FixedCoreTwoOffScalar (fastUnit fastQuot fastCop inverse earlyOrders)

theorem all_head_one_late_forward_cases :
    interior.all (OffCoreTwoOffScalar.lateForward 1) = true := by decide

/-- The four polynomials supported on the suffix affine line, with
the true excepted diagonal never read from a repeated numerical label. -/
def checkPoly (u v r x mU mW c₀ d₀ : Nat) : Bool :=
  let t := q
  let D := lin c₀
  let B := plus (scale c₀ t) (k d₀)
  let tD := times t D
  let T := minus B tD
  let B1 := minus B D
  let Bu := minus B (scale u D)
  let Bv := minus B (scale v D)
  let Br := minus B (scale r D)
  let Ct := scale 42 (lin x)
  let Cq := scale 42 (minus B (scale x D))
  let lₜ := sub (mul mW (sub c₀ v)) (mul mU (sub c₀ u))
  let l_q := mul (sub mW mU) (inverse (sub c₀ r))
  let l₁ := plus (scale (mul (sub v 1) mU) (times (lin u) Bu))
    (scale (mul (sub 1 u) mW) (times (lin v) Bv))
  let Pt := plus (minus (scale 10 B) (scale 5 (times (plus D B) t)))
    (scale 3 (times (power t 2) D))
  let Pq := plus (minus (scale 10 (times t (power D 2)))
    (scale 5 (prod [plus (k 1) t,B,D]))) (scale 3 (power B 2))
  let P1 := plus (minus (scale 10 (times t B)) (scale 5 (plus tD B))) (scale 3 D)
  let absentNum := minus (minus (scale lₜ (prod [B1,power t 2,Pt,Cq]))
    (scale l_q (prod [lin 1,D,power B 2,Pq,Ct]))) (prod [T,P1,l₁,Ct,Cq])
  let beforeOff := plus (scale l_q (prod [D,power B 2,minus B (scale 2 tD),Ct]))
    (scale lₜ (prod [power t 2,minus (scale 2 B) tD,Cq]))
  let beforeOne := plus (prod [minus (k 1) (scale 2 t),Ct,l₁])
    (scale lₜ (times (power t 2) (minus (k 2) t)))
  let after := plus (scale l_q (prod [D,power B 2,minus B (scale 2 D)]))
    (prod [minus (scale 2 B) D,Cq,l₁])
  match fastQuot absentNum (prod [T,lin 1,B1]) with
  | none => false
  | some A =>
    [lₜ,l_q,sub c₀ 1,sub c₀ r,add d₀ (pow c₀ 2),val T 1,val T r].all fastUnit &&
    (minus (scale mW Bv) (scale mU Bu)) == scale lₜ (lin r) &&
    (minus (scale mW (lin v)) (scale mU (lin u))) == scale l_q Br &&
    deg l₁ 2 && deg A 4 && deg beforeOff 6 && deg beforeOne 4 && deg after 4 &&
    fastCop A beforeOff && fastCop A beforeOne && fastCop A after

def allEarlyCase (U W R X : Nat) : Bool :=
  if PaidOneOffRepairScalar.distinct4 U W R X then
    match PaidOneOffRepairScalar.fixedK U W R with
    | none => false
    | some (kU,kW,kR) =>
      let aU := mul (PaidOneOffRepairScalar.massTimesDerivative U) kU
      let aW := mul (PaidOneOffRepairScalar.massTimesDerivative W) kW
      let aR := mul (PaidOneOffRepairScalar.massTimesDerivative R) kR
      let mU := mul aU (sub W R)
      let mW := mul aW (sub R U)
      let mR := mul aR (sub U W)
      let total := add (add mU mW) mR
      let invTotal := inverse total
      let α := mul (add (add (mul mU U) (mul mW W)) (mul mR R)) invTotal
      let β := mul (sub 0 (add (add (mul mU (pow U 2)) (mul mW (pow W 2))) (mul mR (pow R 2)))) invTotal
      [aU,aW,aR,total].all fastUnit &&
        checkPoly (sub 1 U) (sub 1 W) (sub 1 R) (sub 1 X) aU aW (sub 1 α) (sub (add (mul 2 α) β) 1)
  else true

def checkEarlyOrder (v : Nat × Nat × Nat × Nat) : Bool :=
  match v with | (u,w,r,X) => allEarlyCase u w r X

private def orderTable : List (Nat × Nat × Nat × Nat) :=
  [(67,141,279,353),
   (67,141,353,279),
   (67,279,141,353),
   (67,279,353,141),
   (67,353,141,279),
   (67,353,279,141),
   (141,67,279,353),
   (141,67,353,279),
   (141,279,67,353),
   (141,279,353,67),
   (141,353,67,279),
   (141,353,279,67),
   (279,67,141,353),
   (279,67,353,141),
   (279,141,67,353),
   (279,141,353,67),
   (279,353,67,141),
   (279,353,141,67),
   (353,67,141,279),
   (353,67,279,141),
   (353,141,67,279),
   (353,141,279,67),
   (353,279,67,141),
   (353,279,141,67)]
private theorem orderTable_complete : earlyOrders = orderTable := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row0 : allEarlyCase 67 141 279 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row1 : allEarlyCase 67 141 353 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row2 : allEarlyCase 67 279 141 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row3 : allEarlyCase 67 279 353 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row4 : allEarlyCase 67 353 141 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row5 : allEarlyCase 67 353 279 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row6 : allEarlyCase 141 67 279 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row7 : allEarlyCase 141 67 353 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row8 : allEarlyCase 141 279 67 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row9 : allEarlyCase 141 279 353 67 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row10 : allEarlyCase 141 353 67 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row11 : allEarlyCase 141 353 279 67 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row12 : allEarlyCase 279 67 141 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row13 : allEarlyCase 279 67 353 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row14 : allEarlyCase 279 141 67 353 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row15 : allEarlyCase 279 141 353 67 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row16 : allEarlyCase 279 353 67 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row17 : allEarlyCase 279 353 141 67 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row18 : allEarlyCase 353 67 141 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row19 : allEarlyCase 353 67 279 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row20 : allEarlyCase 353 141 67 279 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row21 : allEarlyCase 353 141 279 67 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row22 : allEarlyCase 353 279 67 141 = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
private theorem row23 : allEarlyCase 353 279 141 67 = true := by decide

/-- Kernel checking is separated by physical clock order to bound memory.
This last step is just list coverage and the proved row booleans. -/
theorem all_early_off_core_head_one_cases : earlyOrders.all checkEarlyOrder = true := by
  rw [orderTable_complete]
  simp only [orderTable,List.all_cons,List.all_nil,checkEarlyOrder,row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23,Bool.true_and]

end RKResearch.Certified.Graded.OffCoreHeadOneScalar
