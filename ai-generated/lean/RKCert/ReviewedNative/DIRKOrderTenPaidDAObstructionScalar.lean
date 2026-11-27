module

public import RKCert.ReviewedNative.DIRKOrderTenPaidOneOffRepairScalar

@[expose] public section

/-! # Uniform fixed-clock obstruction from the genuinely paid DA row

After the infinite-field bridge has removed the common U-column shift,
the exact three regular moment systems involve only ordered fixed Lobatto
roots. This module evaluates their affine second-difference obstruction
modulo the splitting prime 419. -/
namespace RKResearch.Certified.Graded.PaidDAObstructionScalar

open ConstantOneOffScalar

def isDistinct3 (u w r : Nat) : Bool :=
  (u != w) && (u != r) && (w != r)

def m1 (s : Nat) : Nat := div (pow s 2) 2
def m2 (s k : Nat) : Nat := sub (div (pow s 3) 3) k
def m3 (u s k : Nat) : Nat := sub (div (pow s 4) 4) (mul (add u (div u 2)) k)

def tap2 (t a S₁ S₂ : Nat) : Nat :=
  div (sub S₂ (mul a S₁)) (mul t (sub t a))

def tap3 (t a b S₁ S₂ S₃ : Nat) : Nat :=
  div (add (sub S₃ (mul (add a b) S₂)) (mul (mul a b) S₁))
    (mul (mul t (sub t a)) (sub t b))

def guardFactor (u w r : Nat) : Nat :=
  add (mul r (sub (add (pow u 2) (pow w 2)) (mul 4 (mul u w))))
    (mul (mul u w) (add u w))

def denR (u w r : Nat) : Nat :=
  add (mul r (sub (mul 4 (add (pow u 2) (pow w 2))) (mul 13 (mul u w))))
    (mul (mul u w) (add u w))

def numR (u w r : Nat) : Nat :=
  add (sub (mul 3 (pow r 2)) (mul (mul 5 r) (add u w))) (mul 10 (mul u w))

def defect (u w r kU kW kR : Nat) : Nat :=
  let ru := div u 2
  let aWU := tap2 u w (m1 w) (m2 w kW)
  let aWW := tap2 w u (m1 w) (m2 w kW)
  let rw := div (add (mul kU aWU) (mul kW aWW)) kW
  let aRU := tap3 u w r (m1 r) (m2 r kR) (m3 u r kR)
  let aRW := tap3 w u r (m1 r) (m2 r kR) (m3 u r kR)
  let aRR := tap3 r u w (m1 r) (m2 r kR) (m3 u r kR)
  let rr := div (add (add (mul kU aRU) (mul kW aRW)) (mul kR aRR)) kR
  add (add (mul (sub w r) ru) (mul (sub r u) rw)) (mul (sub u w) rr)

def signedSquare (u w r : Nat) : Nat :=
  let numerator := mul (sub 0 3) (mul (mul (sub r u) (sub r w))
    (mul (sub u w) (pow (guardFactor u w r) 2)))
  let den := mul (mul (sub u (mul 2 w)) (sub (mul 2 u) w)) (mul (numR u w r) (denR u w r))
  div numerator den

def checkTriple (u w r : Nat) : Bool :=
  if isDistinct3 u w r then
    match PaidOneOffRepairScalar.fixedK u w r with
    | none => false
    | some (kU,kW,kR) =>
      let δ := defect u w r kU kW kR
      [u,w,r,sub u w,sub u r,sub w r,kU,kW,kR,sub u (mul 2 w),sub (mul 2 u) w,
        guardFactor u w r,denR u w r,numR u w r,δ].all unit &&
        δ == signedSquare u w r
  else true

theorem all_fixed_da_defects :
    interior.all (fun u => interior.all (fun w => interior.all (checkTriple u w))) = true := by decide

end RKResearch.Certified.Graded.PaidDAObstructionScalar
