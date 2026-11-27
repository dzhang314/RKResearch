module

public import RKCert.ReviewedNative.DIRKOrderTenConstantOneOffScalar

@[expose] public section

/-! # Corrected one-off clock tests with degree-four forward input

The old quintic primitive is not used. The constant branch uses a
common-root resultant; the nonconstant branch fixes the exceptional
clock from the literal D(2), D(3), D(4), D(5) suffix and barycentric
clock masses. Only the resulting finite residue tests are certified here.
-/
namespace RKResearch.Certified.Graded.PaidOneOffRepairScalar

open ConstantOneOffScalar

def H (x : Nat) : Nat := mul x (jacobi x)

def add3 (a b c : Nat) : Nat := add (add a b) c

def mul3 (a b c : Nat) : Nat := mul (mul a b) c

def polyMulEval (a b u x : Nat) : Nat := mul (mul x (sub x a)) (mul (sub x b) (sub x u))

def first60 (a b x : Nat) : Nat :=
  add (sub (mul 15 (pow x 4)) (mul3 20 (add a b) (pow x 3))) (mul 30 (mul (mul a b) (pow x 2)))

def second60 (a b x : Nat) : Nat :=
  add (sub (mul 3 (pow x 5)) (mul3 5 (add a b) (pow x 4))) (mul 10 (mul (mul a b) (pow x 3)))

def correctedScalar (τ x a b u : Nat) : Nat :=
  let J := primitive60 0 a b u x
  if x=τ then J else
    sub (mul3 60 (second60 a b x) (polyMulEval a b u x)) (mul (first60 a b x) J)

/-- The three point queries recover degree-at-most-two coefficients.
The displayed scalar equations in the companion note have that degree
by inspection, before any residue calculation. -/
def coeff₂ (f : Nat → Nat) : Nat × Nat × Nat :=
  let a := f 0
  let c := div (add (sub (f 2) (mul 2 (f 1))) a) 2
  (a, sub (sub (f 1) a) c, c)

/-- Distinguishes the known linear and quadratic cases, guards the
leading coefficient, and excludes common roots over the algebraic
closure of the residue field (not merely over F_p). -/
def separated (linear : Bool) (P S : Nat → Nat) : Bool :=
  let (p0,p1,p2) := coeff₂ P
  let (s0,s1,s2) := coeff₂ S
  if linear then
    p2 == 0 && unit p1 && add3 (mul s2 (pow p0 2)) (sub 0 (mul3 s1 p0 p1)) (mul s0 (pow p1 2)) != 0
  else
    let t0 := sub (mul p2 s0) (mul s2 p0)
    let t1 := sub (mul p2 s1) (mul s2 p1)
    unit p2 &&
      if t1=0 then t0 != 0 else
      add3 (mul p2 (pow t0 2)) (sub 0 (mul3 p1 t0 t1)) (mul p0 (pow t1 2)) != 0

def constCase (τ x : Nat) : Bool :=
  separated true (paired τ 1) (correctedScalar τ x τ 1) &&
  separated false (fun q => paired q 1 τ) (fun q => correctedScalar τ x q 1 τ) &&
  separated false (fun q => paired q τ 1) (fun q => correctedScalar τ x q τ 1)

/-- Deleting the true zero diagonal leaves a three-node Radau stencil.
Its two early heads cannot contain a nonzero fixed head. -/
def noFixedRadau (a x : Nat) : Bool :=
  add (sub (mul 10 (pow a 2)) (mul3 12 a x)) (mul 3 (pow x 2)) != 0

theorem fixed_radau_guards : fixed.all (fun a => interior.all (noFixedRadau a)) = true := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2500000 in
theorem all_corrected_constant_cuts :
    interior.all (fun τ => interior.all (constCase τ)) = true := by decide

/-- Integrate a coefficient list, including the constant term. -/
def integral (cs : List Nat) (x : Nat) : Nat :=
  cs.zipIdx.foldl (fun n (a,k) => add n (div (mul a (pow x (k+1))) (k+1))) 0

def value (cs : List Nat) (x : Nat) : Nat :=
  cs.zipIdx.foldl (fun n (a,k) => add n (mul a (pow x k))) 0

/-- H/(X−τ), starting with the constant coefficient. -/
def coeffF (τ : Nat) : List Nat :=
  let c3 := sub (mul 42 τ) 84
  let c2 := add 56 (mul τ c3)
  let c1 := sub (mul τ c2) 14
  let c0 := add 1 (mul τ c1)
  [c0,c1,c2,c3,42]

/-- b(s) Λ′(s) for the fixed Lobatto measure and Λ=(X−1)H.
One division-free nodal numerator before the ordinary integral. -/
def massTimesDerivative (s : Nat) : Nat :=
  let c4 := sub (mul 42 s) 126
  let c3 := add 140 (mul s c4)
  let c2 := sub (mul s c3) 70
  let c1 := add 15 (mul s c2)
  let c0 := sub (mul s c1) 1
  integral [c0,c1,c2,c3,c4,42] 1

def fixedK (u w r : Nat) : Option (Nat × Nat × Nat) :=
  let dW := mul 6 (sub u (mul 2 w))
  let dR := mul 6 (add3 (mul 4 (mul r (add (pow u 2) (pow w 2))))
    (sub 0 (mul 13 (mul r (mul u w)))) (mul (mul u w) (add u w)))
  let nR := mul3 (pow r 3) (sub (mul 2 u) w)
    (add (sub (mul 3 (pow r 2)) (mul3 5 r (add u w))) (mul3 10 u w))
  if unit dW && unit dR && unit (sub (mul 2 u) w) then
    some (div (sub 0 (pow u 3)) 6, div (mul (pow w 3) (sub (mul 2 u) w)) dW, div nR dR)
  else none

def lateClock (u w r : Nat) : Nat :=
  let den := mul 6 (pow (sub u w) 2)
  let num := add (sub (mul 10 (mul r (add (pow u 2) (pow w 2))))
    (mul 25 (mul r (mul u w)))) (mul (mul u w) (add u w))
  div num den

def tap (a b c d j x : Nat) : Option Nat :=
  let den := mul 60 (mul (mul (sub j a) (sub j b)) (mul (sub j c) (sub j d)))
  let z := div (primitive60 a b c d x) den
  if unit den && unit z then some z else none

def phaseGood (qCore : Bool) (τ ξ y z sy sz headSum Sξ : Nat) : Bool :=
  let d := mul 36 (sub y ξ)
  let hy := div (mul (pow ξ 2) (pow y 3)) d
  let γ := div (pow ξ 3) 6
  let α := div (mul 3 (mul (sub y ξ) (sub y (mul 2 ξ)))) (pow ξ 2)
  let s := mul γ (mul (sub y (div ξ 2)) sy)
  let before := if qCore then
    sub (mul α (mul (H ξ) hy)) (mul s (sub ξ τ))
  else
    sub (mul α (mul hy headSum)) (mul s Sξ)
  let after := sub
    (mul 36 (mul (sub ξ y) (mul (sub y (mul 2 z)) (mul sz hy))))
    (mul (pow ξ 2) (mul (pow z 3) (mul (sub (mul 2 y) z) sy)))
  unit d && unit hy && unit (pow ξ 2) && unit sy && unit sz && before != 0 && after != 0

def typesGood (qCore : Bool) (τ q x : Nat) : Bool :=
  let ξ := if qCore then q else τ
  let a := if qCore then τ else q
  match tap 0 ξ 1 x a x, tap 0 ξ a x 1 x, tap 0 a 1 x ξ x with
  | some Sa, some S1, some Sξ =>
    let sa := if qCore then sub (div (integral (coeffF τ) x) Sa) (value (coeffF τ) τ)
      else div (sub 0 (H a)) (sub a τ)
    let s1 := div (sub 0 1) (sub 1 τ)
    let headSum := add (mul Sa sa) (mul S1 s1)
    unit q && unit (H q) && unit (sub 1 τ) && unit (sub q τ) &&
      phaseGood qCore τ ξ a 1 sa s1 headSum Sξ &&
      phaseGood qCore τ ξ 1 a s1 sa headSum Sξ
  | _, _, _ => false

/-- On two singleton receiver blocks the normalized dirty tap ratio
pins the exceptional reflected clock; a third singleton must match. -/
def barycentricCase (u w r X τR : Nat) (E : Nat → Nat) : Bool :=
  let singles := [u,w,r].filter (fun t => t != τR)
  match singles with
  | s::t::rest =>
    let den := sub (E s) (E t)
    let qR := div (sub (mul (E s) s) (mul (E t) t)) den
    let expected := mul (E s) (sub s qR)
    if !(unit den) then false else
    if rest.any (fun z => mul (E z) (sub z qR) != expected) then true else
    if τR=1 ∨ τR=X then false else
    let Z := lateClock u w r
    let τ := sub 1 τR
    let q := sub 1 qR
    let x := sub 1 X
    !(fixed.contains qR) && qR != 0 && Z != 0 && Z != qR && Z != τR &&
      typesGood true τ q x && (if τR=u then true else typesGood false τ q x)
  | _ => false

def distinct4 (u w r X : Nat) : Bool := distinct3 u w r && X != u && X != w && X != r

def nonconstCase (u w r X : Nat) : Bool :=
  if distinct4 u w r X then
    match fixedK u w r with
    | none => false
    | some (ku,kw,kr) =>
      let E := fun z => mul (massTimesDerivative z) (if z=u then ku else if z=w then kw else kr)
      unit (mul 6 (pow (sub u w) 2)) && [u,w,r].all (fun z => unit (E z)) &&
        fixed.all (fun τR => barycentricCase u w r X τR E)
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3500000 in
theorem all_corrected_nonconstant_cuts :
    interior.all (fun u => interior.all (fun w => interior.all (fun r =>
      interior.all (nonconstCase u w r)))) = true := by decide

end RKResearch.Certified.Graded.PaidOneOffRepairScalar
