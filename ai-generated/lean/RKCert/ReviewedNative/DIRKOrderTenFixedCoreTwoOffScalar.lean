module

public import RKCert.ReviewedNative.DIRKOrderTenUniformOneOffPolynomialScalar
public import RKCert.ReviewedNative.DIRKOrderTenPaidOneOffRepairScalar

@[expose] public section

/-! # Two off heads and a fixed active cubic core at DIRK10/11

All polynomials have fixed-root coefficients after the correctly paid
reflected suffix and the clock-aggregate comparison. The companion
note derives the two chronological charts from the actual tableau. -/
namespace RKResearch.Certified.Graded.FixedCoreTwoOffScalar

open ConstantOneOffScalar UniformOneOffPolynomialScalar

abbrev d4 := PaidOneOffRepairScalar.distinct4
abbrev late := PaidOneOffRepairScalar.lateClock

/-- Small modular powers avoid the large intermediate natural powers in
repeated kernel Euclidean division. 419−2=256+128+32+1. -/
def inverse (a : Nat) : Nat :=
  let a2 := mul a a
  let a4 := mul a2 a2
  let a8 := mul a4 a4
  let a16 := mul a8 a8
  let a32 := mul a16 a16
  let a64 := mul a32 a32
  let a128 := mul a64 a64
  let a256 := mul a128 a128
  mul (mul a256 a128) (mul a32 a)

def fastUnit (a : Nat) : Bool := mul a (inverse a) == 1

def fastDiv : Nat → Poly → Poly → Nat → Poly → Poly × Poly
  | 0, n, _, _, a => (a,n)
  | fuel+1, n, d, inv_d, a =>
    if n.isEmpty || d.isEmpty || n.length < d.length then (a,n)
    else
      let j := n.length-d.length
      let v := mul (leading n) inv_d
      fastDiv fuel (minus n (shift j (scale v d))) d inv_d (plus a (shift j (k v)))

def fastQuot (n d : Poly) : Option Poly :=
  let iv := inverse (leading d)
  let (a,r) := fastDiv (n.length+1) n d iv []
  if r.isEmpty && !d.isEmpty && mul (leading d) iv == 1 then some a else none

def fastCopFuel : Nat → Poly → Poly → Bool
  | 0, _, _ => false
  | m+1, a, b =>
    if b.isEmpty then a.length == 1 && fastUnit (leading a)
    else
      let iv := inverse (leading b)
      if mul (leading b) iv == 1 then
        fastCopFuel m b (fastDiv (a.length+1) a b iv []).2
      else false

def fastCop (a b : Poly) : Bool := fastCopFuel (a.length+b.length+1) a b


def lateEventGuard (u w r X : Nat) : Bool :=
  if d4 u w r X then
    let z := late u w r
    unit (mul 6 (pow (sub u w) 2)) && z != 0 && !(fixed.contains z)
  else true

theorem all_late_events_off :
    interior.all (fun u => interior.all (fun w => interior.all (fun r =>
      interior.all (lateEventGuard u w r)))) = true := by decide

/-- The lone earlier exterior head is fixed by the true degree-four
nodal integral at x, not by an unpaid quintic. -/
def oneLateForward (ξ x : Nat) : Bool :=
  if ξ=x then true else
    let d := mul 5 (sub (mul 2 ξ) x)
    let a := div (mul x (sub (mul 5 ξ) (mul 3 x))) d
    let h := div (mul (pow ξ 2) (pow a 3)) (mul 36 (sub a ξ))
    let γ := div (pow ξ 3) 6
    let α := div (mul 3 (mul (sub a ξ) (sub a (mul 2 ξ)))) (pow ξ 2)
    let Sξ := div (mul (pow x 3) (sub (mul 2 a) x))
      (mul 12 (mul3 ξ (sub ξ a) (sub ξ x)))
    let Sa := div (mul (pow x 3) (sub (mul 2 ξ) x))
      (mul 12 (mul3 a (sub a ξ) (sub a x)))
    unit d && unit (mul36 a ξ) && unit (pow ξ 2) &&
      !(fixed.contains a) && unit a && unit (sub a x) &&
      mul3 α Sa h != mul3 (sub a (div ξ 2)) γ Sξ
where
  mul36 (a ξ : Nat) : Nat := mul 36 (sub a ξ)

theorem all_one_late_forward_obstructions :
    interior.all (fun ξ => interior.all (oneLateForward ξ)) = true := by decide

def evalP (a : List Nat) (x : Poly) : Poly :=
  a.reverse.foldl (fun n z => plus (k z) (times n x)) []
def hval (a : List Nat) (B D : Poly) : Poly :=
  a.zipIdx.foldl (fun n (z,i) => plus n (scale z (times (power B i) (power D (3-i))))) []
def inv60 : Nat := inv 60

def pinned (ξ sum product : Nat) : Bool :=
  let a := q
  let b := minus (k sum) a
  let T := k ξ
  let Q := plus (minus (power a 2) (scale sum a)) (k product)
  let pol := [k 0,T,a,b]
  let pξ := I pol T
  let pa := I pol a
  let pb := I pol b
  let sa := neg (evalP (Fpoly ξ) a)
  let sb := neg (evalP (Fpoly ξ) b)
  let Lnum := neg (plus (prod [pa,sb,minus b T]) (prod [pb,sa,minus T a]))
  let Lden := prod [sa,sb,minus b a]
  let before := minus (scale (pow ξ 3) (prod [minus (scale 2 a) T,sa,Lnum]))
    (prod [pξ,power a 3,minus a (scale 2 T),Lden])
  let after := plus (prod [power a 3,minus a (scale 2 b),sb]) (prod [power b 3,minus (scale 2 a) b,sa])
  deg Q 2 && fastCop Q before && fastCop Q after

/-- After the suffix comparison, b=(c·a+d)/(a−c). We reduce both
prefix polynomials by only exact fixed-clock factors. -/
def mobius (ξ x r s c0 d0 : Nat) : Bool :=
  let a := q
  let T := k ξ
  let D := lin c0
  let B := plus (scale c0 a) (k d0)
  let aD := times a D
  let bminusa := minus B aD
  let C := Ctpoly ξ
  let Ca := evalP C a
  let Cb := hval C B D
  let PA := plus (minus (scale (mul 10 ξ) B)
    (scale 5 (times (plus (scale ξ D) B) a))) (scale 3 (times (power a 2) D))
  let PB := plus (minus (scale (mul 10 ξ) (times a (power D 2)))
    (scale 5 (prod [plus T a,B,D]))) (scale 3 (power B 2))
  let PV := plus (minus (scale 10 (times a B)) (scale (mul 5 ξ) (plus aD B))) (scale (mul 3 (pow ξ 2)) D)
  let MX := plus (prod [power a 2,PA,Cb,minus B (scale ξ D)])
    (prod [power B 2,PB,Ca,minus T a,D])
  let PX := plus (minus (scale 10 (times a B)) (scale (mul 5 x) (plus aD B))) (scale (mul 3 (pow x 2)) D)
  let nξ := scale (sub 0 (mul (pow x 3) inv60)) PX
  let vξ := scale (mul ξ (sub ξ x)) (times (minus T a) (minus (scale ξ D) B))
  let BS := minus (scale (val (Fpoly ξ) ξ) nξ) (times (integral (QFcoeff ξ) (k x)) vξ)
  let before := plus (prod [power a 2,minus a (scale 2 T),BS])
    (scale (pow ξ 3) (prod [minus (scale 2 a) T,Ca,nξ]))
  let afterRaw := plus (prod [power a 2,minus aD (scale 2 B),Cb])
    (prod [power B 2,minus (scale 2 aD) B,Ca,D])
  let G2 := times (lin r) (lin s)
  let G3 := times G2 (lin ξ)
  match fastQuot MX bminusa, fastQuot afterRaw bminusa with
  | some M, some after =>
    let beforeAbs := plus (times (minus (scale 2 a) T) M)
      (prod [power a 2,minus a (scale 2 T),PV,Cb])
    let afterAbs := minus (times M BS) (scale (pow ξ 3) (prod [PV,nξ,Ca,Cb]))
    match fastQuot before G3, fastQuot beforeAbs G3, fastQuot after G2, fastQuot afterAbs G2 with
    | some b1, some b2, some a1, some a2 =>
      unit (add d0 (pow c0 2)) && unit (val bminusa ξ) &&
        deg b1 3 && deg b2 6 && deg a1 4 && deg a2 8 && fastCop b1 b2 && fastCop a1 a2
    | _, _, _, _ => false
  | _, _ => false

def point (u w r X V Eu Ew Er : Nat) : Bool :=
  let ξ := sub 1 V
  let x := sub 1 X
  let z := if V=w then r else w
  let Ez := if V=w then Er else Ew
  let δ := sub Ez Eu
  let α := div (sub (mul Ez z) (mul Eu u)) δ
  let β := div (sub (mul Eu (pow u 2)) (mul Ez (pow z 2))) δ
  let c0 := sub 1 α
  let d0 := sub (add β (mul 2 α)) 1
  if !(unit δ) then false else
  if V=X then
    let δ₂ := add (sub (mul Eu u) (mul Er r)) (mul (sub Er Eu) α)
    let S := div (add (sub (mul Eu (pow u 2)) (mul Er (pow r 2))) (mul (sub Eu Er) β)) δ₂
    let P := add (mul α S) β
    unit δ₂ && pinned ξ (sub 2 S) (add (sub 1 S) P)
  else mobius ξ x (sub 1 u) (sub 1 z) c0 d0

def allEarlyCase (u w r X : Nat) : Bool :=
  if d4 u w r X then
    match PaidOneOffRepairScalar.fixedK u w r with
    | none => false
    | some (ku,kw,kr) =>
      let Eu := div (mul (PaidOneOffRepairScalar.massTimesDerivative u) ku) u
      let Ew := div (mul (PaidOneOffRepairScalar.massTimesDerivative w) kw) w
      let Er := div (mul (PaidOneOffRepairScalar.massTimesDerivative r) kr) r
      [u,w,r,Eu,Ew,Er].all unit && [w,r,X].all (fun V => point u w r X V Eu Ew Er)
  else true

/-- The actual distinct four-clock orders, without unreachable repeated
candidate rows. The finite coverage equality is checked separately. -/
def earlyOrders : List (Nat × Nat × Nat × Nat) :=
  interior.flatMap (fun u => interior.flatMap (fun w => interior.flatMap (fun r =>
    (interior.filter (fun X => d4 u w r X)).map (fun X => (u,w,r,X)))))
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

def checkEarlyOrder (v : Nat × Nat × Nat × Nat) : Bool :=
  match v with | (u,w,r,X) => allEarlyCase u w r X

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
theorem all_early_fixed_core_cases : earlyOrders.all checkEarlyOrder = true := by
  rw [orderTable_complete]
  simp only [orderTable,List.all_cons,List.all_nil,checkEarlyOrder,row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23,Bool.true_and]

end RKResearch.Certified.Graded.FixedCoreTwoOffScalar
