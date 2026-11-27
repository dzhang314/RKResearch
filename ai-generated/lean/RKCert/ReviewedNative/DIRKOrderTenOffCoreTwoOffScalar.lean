module

public import RKCert.ReviewedNative.DIRKOrderTenFixedCoreTwoOffScalar

@[expose] public section

/-! # Active off-core two-off scalar tests with a unique terminal clock

Exact coefficient calculations at the splitting prime 419. The companion
note derives the polynomials from actual paid forward/reverse rows and
proves each removed factor before this residue test is applied. -/
namespace RKResearch.Certified.Graded.OffCoreTwoOffScalar

open ConstantOneOffScalar UniformOneOffPolynomialScalar
open FixedCoreTwoOffScalar (fastUnit fastQuot fastCop evalP earlyOrders)

def radau (t x : Nat) : Nat :=
  add (sub (mul 10 (pow t 2)) (mul 12 (mul t x))) (mul 3 (pow x 2))

/-- A fixed early head t, an off dirty clock a determined at x, and
the late off head. Also checks the Radau guard for a late core event. -/
def lateForward (t x : Nat) : Bool :=
  if t=x then true else
  let D := mul 5 (sub (mul 2 t) x)
  let a := div (mul x (sub (mul 5 t) (mul 3 x))) D
  let m := mul 720 (mul3 (sub (mul 2 x) (mul 5 t)) (sub x (mul 2 t)) (sub x t))
  let Sa := div (mul (pow x 3) (sub (mul 2 t) x)) (mul 12 (mul3 a (sub a t) (sub a x)))
  let St := div (mul (pow x 3) (sub (mul 2 a) x)) (mul 12 (mul3 t (sub t a) (sub t x)))
  let Δ := sub (mul (div (mul (pow t 3) (sub t (mul 2 a))) 12) St)
    (mul3 (sub t (div a 2)) (div (pow a 3) 6) Sa)
  [t,x,D,m,radau t x,a,sub a t,sub a x,Δ].all fastUnit &&
    !(fixed.contains a) && Δ == div (mul (pow x 4) (pow (radau t x) 2)) m

theorem all_late_forward_cases :
    interior.all (fun t => interior.all (lateForward t)) = true := by decide

def H : Poly := [0,1,405,56,335,42]

/-- 60 times the negative primitive at a of the anchored quartic
with remaining roots u,v. The factor -60 cancels from the pinned test. -/
def p0 (a u v : Poly) : Poly :=
  times (power a 3)
    (plus (minus (scale 10 (times u v)) (scale 5 (times (plus u v) a))) (scale 3 (power a 2)))

/-- Both τ=0 and τ=x make the marked primitive value at the shared
head vanish. No fictitious split of the shared aggregate tap is used. -/
def pinned (τ s₁ s₂ : Nat) : Bool :=
  let a := q
  let b := minus (k s₁) a
  let Q := plus (minus (power a 2) (scale s₁ a)) (k s₂)
  let test := minus (times (p0 a b (k τ)) (evalP H b)) (times (p0 b a (k τ)) (evalP H a))
  deg Q 2 && fastCop Q test

def mobius (τ x r s c₀ d₀ : Nat) : Bool :=
  let a := q
  let D := lin c₀
  let B := plus (scale c₀ a) (k d₀)
  let aD := times a D
  let T := minus B aD
  let Bτ := minus B (scale τ D)
  let Bx := minus B (scale x D)
  let K := times (lin r) (lin s)
  let Ca := scale 42 (lin x)
  let Cb := scale (mul3 42 (sub c₀ r) (sub c₀ s)) Bx
  let PX := plus (minus (scale 10 (times a B)) (scale (mul 5 x) (plus aD B))) (scale (mul 3 (pow x 2)) D)
  let N := scale (sub 0 (mul (pow x 3) (inv 60))) PX
  let vτ := scale (mul τ (sub τ x)) (times (lin τ) Bτ)
  let fτ := val (Fpoly τ) τ
  let mτ := c (integral (QFcoeff τ) (k x)) 0
  let S := minus (scale mτ vτ) (scale fτ N)
  let PA := plus (minus (scale (mul 10 τ) B) (scale 5 (times (plus (scale τ D) B) a)))
    (scale 3 (times (power a 2) D))
  let PB := plus (minus (scale (mul 10 τ) (times a (power D 2)))
    (scale 5 (prod [plus (k τ) a,B,D]))) (scale 3 (power B 2))
  let Pτ := plus (minus (scale 10 (times a B)) (scale (mul 5 τ) (plus aD B))) (scale (mul 3 (pow τ 2)) D)
  match fastQuot S K with
  | none => false
  | some ss =>
    let h := c ss 0
    let num := plus
      (plus (scale (sub 0 h) (prod [D,Ca,power B 2,PB,lin τ]))
        (scale (pow τ 3) (prod [Ca,Pτ,Cb,T,N])))
      (scale h (prod [power a 2,PA,Cb,Bτ]))
    let beforeOff := plus (prod [D,power B 2,minus B (scale 2 aD),Ca])
      (prod [power a 2,minus (scale 2 B) aD,Cb])
    let beforeFixed := minus (scale (pow τ 3) (prod [minus (k τ) (scale 2 a),Ca,N]))
      (scale h (times (power a 2) (minus (k (mul 2 τ)) a)))
    let after := minus (scale h (prod [D,power B 2,minus B (scale (mul 2 τ) D)]))
      (scale (pow τ 3) (prod [minus (scale 2 B) (scale τ D),Cb,N]))
    match fastQuot num (prod [T,lin τ,Bτ]) with
    | none => false
    | some A =>
      [mτ,sub τ c₀,sub c₀ r,sub c₀ s,add d₀ (pow c₀ 2),val T τ].all fastUnit &&
      deg ss 0 && deg N 2 && deg A 4 && deg beforeOff 6 && deg beforeFixed 4 && deg after 4 &&
      fastCop A beforeOff && fastCop A beforeFixed && fastCop A after

/-- Given any two singleton suffix labels, the barycentric equality
gives a line in the sum and product of the reflected off clocks. -/
def line (s z Es Ez : Nat) : Option (Nat × Nat) :=
  let δ := sub Ez Es
  if fastUnit δ then
    some (mul (sub (mul Ez z) (mul Es s)) (FixedCoreTwoOffScalar.inverse δ),
      mul (sub (mul Es (pow s 2)) (mul Ez (pow z 2))) (FixedCoreTwoOffScalar.inverse δ))
  else none

def point (u w r X V Eu Ew Er : Nat) : Bool :=
  let τ := sub 1 V
  let x := sub 1 X
  let (s,z,Es,Ez) :=
    if V=u then (w,r,Ew,Er) else if V=w then (u,r,Eu,Er) else (u,w,Eu,Ew)
  match line s z Es Ez with
  | none => false
  | some (α,β) =>
    if V=1 || V=X then
      let δ₂ := add (sub (mul Eu u) (mul Er r)) (mul (sub Er Eu) α)
      let S := mul (add (sub (mul Eu (pow u 2)) (mul Er (pow r 2))) (mul (sub Eu Er) β))
        (FixedCoreTwoOffScalar.inverse δ₂)
      let P := add (mul α S) β
      fastUnit δ₂ && pinned τ (sub 2 S) (add (sub 1 S) P)
    else mobius τ x (sub 1 s) (sub 1 z) (sub 1 α) (sub (add (mul 2 α) β) 1)

def allEarlyCase (u w r X : Nat) : Bool :=
  if PaidOneOffRepairScalar.distinct4 u w r X then
    match PaidOneOffRepairScalar.fixedK u w r with
    | none => false
    | some (ku,kw,kr) =>
      let E := fun t k₀ => mul3 (PaidOneOffRepairScalar.massTimesDerivative t) k₀
        (FixedCoreTwoOffScalar.inverse t)
      let Eu := E u ku
      let Ew := E w kw
      let Er := E r kr
      [u,w,r,Eu,Ew,Er].all fastUnit && [1,X,u,w,r].all (fun V => point u w r X V Eu Ew Er)
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
theorem all_early_off_core_terminal_unique_cases : earlyOrders.all checkEarlyOrder = true := by
  rw [orderTable_complete]
  simp only [orderTable,List.all_cons,List.all_nil,checkEarlyOrder,row0, row1, row2, row3, row4, row5, row6, row7, row8, row9, row10, row11, row12, row13, row14, row15, row16, row17, row18, row19, row20, row21, row22, row23,Bool.true_and]

end RKResearch.Certified.Graded.OffCoreTwoOffScalar
