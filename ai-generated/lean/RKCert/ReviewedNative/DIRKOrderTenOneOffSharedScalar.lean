module

public import Init

@[expose] public section

/-! # Fixed-clock separators for active nonconstant one-off DIRK10

The case partition and tableau transport are mathematical in the
companion note. All residue computations below are independent of
unknown weights, tableau coefficients, and defect sizes. -/
namespace RKResearch.Certified.Graded.OneOffSharedScalar

abbrev p : Nat := 227

def add (a b : Nat) : Nat := (a+b)%p
def sub (a b : Nat) : Nat := (a%p+p-b%p)%p
def mul (a b : Nat) : Nat := (a*b)%p
def pow (a k : Nat) : Nat := a^k%p
def inv (a : Nat) : Nat := pow a (p-2)
def div (a b : Nat) : Nat := mul a (inv b)
def unit (a : Nat) : Bool := mul a (inv a) == 1

def interior : List Nat := [24,51,177,204]

def jacobi (x : Nat) : Nat :=
  add (sub (add (sub (mul 42 (pow x 4)) (mul 84 (pow x 3))) (mul 56 (pow x 2))) (mul 14 x)) 1

def H (x : Nat) : Nat := mul x (jacobi x)

theorem jacobi_roots : (List.range p).filter (fun x => jacobi x == 0) = interior := by decide

theorem paid_divisor_guards : [2,3,4,5,6,36,60].all unit = true := by decide

/-- Two nonzero earlier donor labels would require 5a(x−a)=x².
The unknown donor has already been eliminated by the sum condition. -/
def twoDonorGuard (a x : Nat) : Bool :=
  if a=x then true else mul 5 (mul a (sub x a)) != pow x 2

theorem fixed_pair_guards :
    (1::interior).all (fun a => (1::interior).all (twoDonorGuard a)) = true := by decide

/-- Physical latest ordinary donor clock x, and fixed exceptional
clocks 1 and τ. The remaining exceptional clock is the only off-site. -/
def soleOff (τ x : Nat) : Option Nat :=
  let s := add τ 1
  let d := add (sub (mul 3 (pow x 2)) (mul 5 (mul s x))) (mul 10 τ)
  let n := mul x (add (sub (mul 2 (pow x 2)) (mul 3 (mul s x))) (mul 5 τ))
  if unit d then some (div n d) else none

/-- 60 times the primitive of product of the four other nodal factors. -/
def primitive60 (a b c d x : Nat) : Nat :=
  let s₁ := add (add a b) (add c d)
  let s₂ := add (add (mul a b) (mul c d)) (mul (add a b) (add c d))
  let s₃ := add (mul (mul a b) (add c d)) (mul (mul c d) (add a b))
  let s₄ := mul (mul a b) (mul c d)
  add (sub (add (sub (mul 12 (pow x 5)) (mul 15 (mul s₁ (pow x 4))))
    (mul 20 (mul s₂ (pow x 3)))) (mul 30 (mul s₃ (pow x 2)))) (mul 60 (mul s₄ x))

def tap (a b c d j x : Nat) : Option Nat :=
  let den := mul 60 (mul (mul (sub j a) (sub j b)) (mul (sub j c) (sub j d)))
  let z := div (primitive60 a b c d x) den
  if unit den && unit z then some z else none

/-- Polynomial F=H/(X−τ) at a fixed interior root by monic division. -/
def coeffF (τ : Nat) : List Nat :=
  let f₃ := sub (mul 42 τ) 84
  let f₂ := add 56 (mul τ f₃)
  let f₁ := sub (mul τ f₂) 14
  let f₀ := add 1 (mul τ f₁)
  [f₀,f₁,f₂,f₃,42]

def evalF (τ x : Nat) : Nat :=
  (coeffF τ).zipIdx.foldl (fun n (a,k) => add n (mul a (pow x k))) 0

def integralF (τ x : Nat) : Nat :=
  (coeffF τ).zipIdx.foldl (fun n (a,k) => add n (div (mul a (pow x (k+1))) (k+1))) 0

/-- Tests for the two timings of the first changed core row, for a
specified order of the two head debuts. True means neither timing works. -/
def phaseGood (qCore : Bool) (τ ξ y z sy sz headSum Sξ : Nat) : Bool :=
  let d := mul 36 (sub y ξ)
  let sn := div (mul (pow ξ 2) (pow y 3)) d
  let γ := div (pow ξ 3) 6
  let α := div (mul 3 (mul (sub y ξ) (sub y (mul 2 ξ)))) (pow ξ 2)
  let s := mul γ (mul (sub y (div ξ 2)) sy)
  let before := if qCore then
    sub (mul α (mul (H ξ) sn)) (mul s (sub ξ τ))
  else
    sub (mul α (mul sn headSum)) (mul s Sξ)
  let after := sub
    (mul 36 (mul (sub ξ y) (mul (sub y (mul 2 z)) (mul sz sn))))
    (mul (pow ξ 2) (mul (pow z 3) (mul (sub (mul 2 y) z) sy)))
  unit d && unit sn && unit (pow ξ 2) && unit sy && unit sz && before != 0 && after != 0

/-- The off clock is either the core or a head. In both cases τ,x are
fixed distinct interior clocks. A failed guard is a rejected test. -/
def tupleGood (qCore : Bool) (τ x : Nat) : Bool :=
  match soleOff τ x with
  | none => false
  | some q =>
    let ξ := if qCore then q else τ
    let a := if qCore then τ else q
    match tap 0 ξ 1 x a x, tap 0 ξ a x 1 x, tap 0 a 1 x ξ x with
    | some Sa, some S1, some Sξ =>
      let sa := if qCore then sub (div (integralF τ x) Sa) (evalF τ τ)
        else div (sub 0 (H a)) (sub a τ)
      let s1 := div (sub 0 1) (sub 1 τ)
      let headSum := add (mul Sa sa) (mul S1 s1)
      unit q && unit (H q) && unit (sub 1 τ) && unit (sub q τ) &&
        phaseGood qCore τ ξ a 1 sa s1 headSum Sξ &&
        phaseGood qCore τ ξ 1 a s1 sa headSum Sξ
    | _, _, _ => false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem all_off_core_cuts :
    interior.all (fun τ => interior.all (fun x => if τ=x then true else tupleGood true τ x)) = true := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem all_off_head_cuts :
    interior.all (fun τ => interior.all (fun x => if τ=x then true else tupleGood false τ x)) = true := by
  decide

end RKResearch.Certified.Graded.OneOffSharedScalar
