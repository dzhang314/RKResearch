module

public import RKCert.ReviewedNative.DIRKOrderTenPaidDAObstructionScalar

@[expose] public section

/-! # Fixed interior clean duplicate: two exact aggregate DA checks

At the repeated clock the columns are aggregated before applying the
affine DA and B5 reads. No signed-opposite assumption on that duplicated
ordinary mass is made. This module checks the resulting fixed scalars. -/
namespace RKResearch.Certified.Graded.InvisibleInteriorDuplicateScalar

open ConstantOneOffScalar
open PaidDAObstructionScalar (tap2 tap3 signedSquare isDistinct3)

def tri (x y z : Nat) : Nat := mul (mul x y) z

def Kquartic (V U : Nat) : Nat := tri V (sub V U) (sub V (div U 2))

def dLast (V U : Nat) : Nat :=
  div (sub 0 (pow U 3)) (tri 6 V (sub V U))

def mRatio (a b : Nat) : Nat :=
  sub (sub (mul 4 (pow a 2)) (tri 5 a b)) (mul 5 (pow b 2))

def mLast (V U : Nat) : Nat :=
  div (tri V (sub U V) (mRatio U V)) 5

def rowLast (V U dU : Nat) : Nat :=
  add (div V 2) (div (sub (div (pow U 2) 2) (mul V dU)) U)

def nodalNumerator (s a b : Nat) : Nat :=
  mul (pow s 3) (add (sub (mul 3 (pow s 2)) (tri 5 (add a b) s)) (tri 10 a b))

def oneLater (U W V : Nat) : Bool :=
  let K := Kquartic V U
  let dU := dLast V U
  let mU := mLast V U
  let dV := div (mul (pow V 3) (sub V (mul 2 U))) (mul 12 K)
  let sU := div (sub 0 (pow V 3)) (tri 6 U (sub U V))
  let mV := div (mul (pow V 3) (mRatio V U)) (mul 30 dV)
  let qU := rowLast V U dU
  let diagonal := sub (sub (div V 2) (div (mul U sU) V)) dV
  let qV := add (add (div V 2) diagonal) (div (mul dU sU) dV)
  let mW := add mU (div (mul (sub mV mU) (sub W U)) (sub V U))
  let den := sub mW (mul (add (add U W) V) K)
  let dW := div (nodalNumerator W U V) (mul 60 den)
  let r1 := div (pow W 2) 2
  let r2 := div (pow W 3) 3
  let r3 := add (div (pow W 4) 4) (mul K dW)
  let aU := tap3 U W V r1 r2 r3
  let aW := tap3 W U V r1 r2 r3
  let tV := tap3 V U W r1 r2 r3
  let qW := add (add aW (div (mul dU aU) dW))
    (add (div V 2) (mul dV (sub (div tV dW) 1)))
  let err := sub (mul (sub V U) (sub qW qU)) (mul (sub W U) (sub qV qU))
  [K,dU,dV,den,dW,err].all unit && err == sub 0 (signedSquare U V W)

def twoLater (U W V : Nat) : Bool :=
  let K := Kquartic V U
  let dU := dLast V U
  let dW := div (mul (pow W 3) (sub (mul 2 U) W))
    (mul (tri 6 V (sub V U)) (sub U (mul 2 W)))
  let mU := mLast V U
  let slopeDen := mul 5 (sub (mul 2 U) W)
  let slope := div (tri (mul 3 V) (sub U V) (pow (sub U W) 2)) slopeDen
  let mV := add mU (mul slope (sub V U))
  let den := sub mV (mul (add (add U W) V) K)
  let dV := div (nodalNumerator V U W) (mul 60 den)
  let qU := rowLast V U dU
  let r1 := sub (div (pow W 2) 2) (mul V dW)
  let r2 := sub (div (pow W 3) 3) (mul (pow V 2) dW)
  let aWU := tap2 U W r1 r2
  let aWW := tap2 W U r1 r2
  let qW := add (div V 2) (add (div (mul dU aWU) dW) aWW)
  let n1 := div (pow V 2) 2
  let n2 := div (pow V 3) 3
  let n3 := add (div (pow V 4) 4) (mul K dV)
  let aU := tap3 U W V n1 n2 n3
  let aW := tap3 W U V n1 n2 n3
  let tV := tap3 V U W n1 n2 n3
  let qV := add (add (div V 2) (sub tV dV)) (div (add (mul dU aU) (mul dW aW)) dV)
  let err := sub (mul (sub W U) (sub qV qU)) (mul (sub V U) (sub qW qU))
  [K,dU,dW,slopeDen,sub U (mul 2 W),den,dV,err].all unit && err == sub 0 (signedSquare U W V)

def checks (U W V : Nat) : Bool :=
  if isDistinct3 U W V then
    [U,W,V,sub U W,sub U V,sub W V,sub V (mul 2 U)].all unit &&
    oneLater U W V && twoLater U W V
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem all_interior_duplicate_gates :
    interior.all (fun U => interior.all (fun W => interior.all (checks U W))) = true := by decide

end RKResearch.Certified.Graded.InvisibleInteriorDuplicateScalar
