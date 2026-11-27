module

public import Init

@[expose] public section

/-! # Fixed-clock certificate for the active constant one-off DIRK10 case

The actual-tableau reductions are mathematical in the companion note.
Only fixed clock roots and their computed exceptional label are reduced. -/
namespace RKResearch.Certified.Graded.ConstantOneOffScalar

abbrev p : Nat := 419

def add (a b : Nat) : Nat := (a+b)%p
def sub (a b : Nat) : Nat := (a%p+p-b%p)%p
def mul (a b : Nat) : Nat := (a*b)%p
def pow (a k : Nat) : Nat := a^k%p
def inv (a : Nat) : Nat := mul (pow a 208) (pow a 209)
def div (a b : Nat) : Nat := mul a (inv b)
def unit (a : Nat) : Bool := mul a (inv a) == 1

def interior : List Nat := [67,141,279,353]
def fixed : List Nat := 1::interior

def jacobi (x : Nat) : Nat :=
  add (sub (add (sub (mul 42 (pow x 4)) (mul 84 (pow x 3))) (mul 56 (pow x 2))) (mul 14 x)) 1

theorem jacobi_roots : (List.range p).filter (fun x => jacobi x == 0) = interior := by decide

theorem primitive_denominator_units : [2,3,4,5,6,12,60].all unit=true := by decide

def paired (a b u : Nat) : Nat :=
  sub (mul u (sub (sub (mul 4 (mul a b)) (pow a 2)) (pow b 2))) (mul (mul a b) (add a b))

def distinct3 (a b u : Nat) : Bool := a != b && a != u && b != u

theorem fixed_triples_no_pair_cut :
    fixed.all (fun a => fixed.all (fun b => fixed.all (fun u =>
      if distinct3 a b u then paired a b u != 0 else true))) = true := by decide

/-- Vanishing of the third exterior head and the primitive read at u
would make this linear solve for the sole off label. -/
def thirdZeroGuard (a u : Nat) : Bool :=
  if a=u then true else
    let d := sub (mul 6 a) (mul 4 u)
    let q := div (mul u (sub (mul 4 a) (mul 3 u))) d
    unit d && paired a q u != 0

theorem fixed_pairs_no_zero_third_head :
    fixed.all (fun a => fixed.all (thirdZeroGuard a)) = true := by decide

def twoDonorGuard (a x : Nat) : Bool :=
  if a=x then true else mul 5 (mul a (sub x a)) != pow x 2

theorem fixed_pairs_no_two_donors :
    fixed.all (fun a => fixed.all (twoDonorGuard a)) = true := by decide

def soleOff (τ x : Nat) : Option Nat :=
  let s := add τ 1
  let d := add (sub (mul 3 (pow x 2)) (mul 5 (mul s x))) (mul 10 τ)
  let n := mul x (add (sub (mul 2 (pow x 2)) (mul 3 (mul s x))) (mul 5 τ))
  if unit d then some (div n d) else none

/-- 60 times the actual primitive at x of the four other donor nodes. -/
def primitive60 (a b c d x : Nat) : Nat :=
  let s₁ := add (add a b) (add c d)
  let s₂ := add (add (mul a b) (mul c d)) (mul (add a b) (add c d))
  let s₃ := add (mul (mul a b) (add c d)) (mul (mul c d) (add a b))
  let s₄ := mul (mul a b) (mul c d)
  add (sub (add (sub (mul 12 (pow x 5)) (mul 15 (mul s₁ (pow x 4))))
    (mul 20 (mul s₂ (pow x 3)))) (mul 30 (mul s₃ (pow x 2)))) (mul 60 (mul s₄ x))

def tapGuard (a b c d j x : Nat) : Bool :=
  let den := mul 60 (mul (mul (sub j a) (sub j b)) (mul (sub j c) (sub j d)))
  unit den && primitive60 a b c d x != 0

/-- Once the early dirty tap is killed, q is fixed by the nodal
quintic. All three heads must be present, but no order can pass the cut. -/
def firstRegularGuard (τ x : Nat) : Bool :=
  if τ=x then true else
  match soleOff τ x with
  | none => false
  | some q =>
    let heads := [1,τ,q]
    tapGuard 0 τ 1 x q x && tapGuard 0 q 1 x τ x && tapGuard 0 q τ x 1 x &&
      heads.all (fun a => heads.all (fun b => heads.all (fun u =>
        if distinct3 a b u then paired a b u != 0 else true)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem all_first_regular_cuts :
    interior.all (fun τ => interior.all (firstRegularGuard τ)) = true := by decide

end RKResearch.Certified.Graded.ConstantOneOffScalar
