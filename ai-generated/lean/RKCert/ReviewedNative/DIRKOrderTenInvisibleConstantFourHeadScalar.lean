module

public import RKCert.ReviewedNative.DIRKOrderTenConstantOneOffScalar

@[expose] public section

/-! # Exact four-head late-cut and early-regular pole gates

The companion mathematical proof supplies literal order and rank
bridges. These finite gates do not claim to exclude the whole chart. -/
namespace RKResearch.Certified.Graded.InvisibleConstantFourHeadScalar

open ConstantOneOffScalar

def tri (a b c : Nat) : Nat := mul (mul a b) c

def primitive3 (U V t : Nat) : Nat :=
  mul (pow t 2) (add (sub (mul 3 (pow t 2)) (tri 4 (add U V) t)) (tri 6 U V))

def primitive4 (U V t : Nat) : Nat :=
  mul (pow t 3) (add (sub (mul 12 (pow t 2)) (tri 15 (add U V) t)) (tri 20 U V))

def ratio (U V t : Nat) : Nat := div (primitive4 U V t) (mul 5 (primitive3 U V t))

def lateGhostGate (U V W : Nat) : Bool :=
  if distinct3 U V W then
    let rU := ratio U V U
    let rV := ratio U V V
    let rW := ratio U V W
    [sub V (mul 2 U),sub U (mul 2 V),primitive3 U V U,primitive3 U V V,
      primitive3 U V W].all unit &&
    mul (sub V U) (sub rW rU) != mul (sub W U) (sub rV rU)
  else true

theorem all_late_ghost_cutoffs :
    interior.all (fun U => interior.all (fun V => interior.all (lateGhostGate U V))) = true := by decide

def poleNumerator (r : Nat) : Nat :=
  mul (mul 2 r)
    (add (sub (add (sub (mul 378 (pow r 4)) (mul 945 (pow r 3)))
      (mul 840 (pow r 2))) (mul 315 r)) 40)

def poleDenominator (r : Nat) : Nat :=
  add (sub (add (sub (mul 2079 (pow r 4)) (mul 5040 (pow r 3)))
    (mul 4200 (pow r 2))) (mul 1400 r)) 150

def earlyGate (r : Nat) : Bool :=
  let a := poleDenominator r
  let b := poleNumerator r
  unit r && unit a &&
  (0::fixed).all (fun t =>
    unit (sub b (mul a t)) &&
    unit (add (sub (mul 10 (pow t 2)) (tri 12 r t)) (mul 3 (pow r 2))))

theorem all_first_five_pole_guards : interior.all earlyGate = true := by decide

end RKResearch.Certified.Graded.InvisibleConstantFourHeadScalar
