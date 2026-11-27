module

public import Init

@[expose] public section

/-! # Fixed-clock finite checks for the one-dirty-clock DIRK10 branch

This module certifies the scalar residues only. The actual-tableau
paired cut and characteristic-zero reduction are in the companion note. -/
namespace RKResearch.Certified.Graded.OneClockScalar

abbrev p : Nat := 227

def modAdd (a b : Nat) : Nat := (a+b)%p
def modSub (a b : Nat) : Nat := (a%p+p-b%p)%p
def modMul (a b : Nat) : Nat := (a*b)%p
def modPow (a k : Nat) : Nat := a^k%p

def jacobiFour (x : Nat) : Nat :=
  modAdd (modSub (modAdd (modSub (modMul 42 (modPow x 4))
    (modMul 84 (modPow x 3))) (modMul 56 (modPow x 2))) (modMul 14 x)) 1

def interior : List Nat := [24,51,177,204]
def nonzeroLobatto : List Nat := interior ++ [1]

def pairCut (a b u : Nat) : Nat :=
  modSub (modMul u (modSub (modSub (modMul 4 (modMul a b)) (modPow a 2)) (modPow b 2)))
    (modMul (modMul a b) (modAdd a b))

def distinctTriple (a b u : Nat) : Bool := a != b && a != u && b != u

def tupleNonzero (a b u : Nat) : Bool :=
  if distinctTriple a b u then pairCut a b u != 0 else true

theorem jacobiFour_roots : (List.range p).filter (fun x => jacobiFour x == 0) = interior := by decide

theorem all_lobatto_triples :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (tupleNonzero a b))) = true := by
  decide

/-- Endpoint-inclusive five moments on only two earlier nonzero donor
clocks force the degree-two Jacobi relation: a+b=x and 5ab=x². -/
def degreeFiveTwoDonor (a b x : Nat) : Bool :=
  modAdd a b == x && modMul 5 (modMul a b) == modPow x 2

theorem all_lobatto_two_donor_tests :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (fun x =>
      if distinctTriple a b x then !(degreeFiveTwoDonor a b x) else true))) = true := by
  decide

/-- The quartic primitive denominator (after removing its nonzero
x³ factor) for solving one off-Lobatto head label. -/
def twoDonorDenominator (a b x : Nat) : Nat :=
  modAdd (modSub (modMul 10 (modMul a b)) (modMul 5 (modMul (modAdd a b) x)))
    (modMul 3 (modPow x 2))

theorem all_lobatto_three_label_denominators :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (fun x =>
      if distinctTriple a b x then twoDonorDenominator a b x != 0 else true))) = true := by
  decide

/-- 60 times the primitive of X(X-a)(X-b)(X-c)(X-x) at x.
All four values in this check are fixed distinct nonzero clock labels. -/
def degreeFiveThreeDonor (a b c x : Nat) : Nat :=
  let s₁ := modAdd (modAdd a b) c
  let s₂ := modAdd (modAdd (modMul a b) (modMul a c)) (modMul b c)
  let s₃ := modMul (modMul a b) c
  modMul (modPow x 3)
    (modAdd
      (modSub
        (modSub (modMul 3 (modMul s₁ (modPow x 2))) (modMul 2 (modPow x 3)))
        (modMul 5 (modMul s₂ x)))
      (modMul 10 s₃))

def distinctQuartet (a b c x : Nat) : Bool :=
  distinctTriple a b c && x != a && x != b && x != c

theorem all_lobatto_three_donor_tests :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (fun c =>
      nonzeroLobatto.all (fun x => if distinctQuartet a b c x then degreeFiveThreeDonor a b c x != 0 else true)))) = true := by
  decide

/-- No pair of distinct fixed clocks can be completed to the two-donor
Jacobi rule by a single unknown numerical clock. -/
def pairGuard (a x : Nat) : Bool :=
  if a=x then true else modMul 5 (modMul a (modSub x a)) != modPow x 2

theorem all_lobatto_two_label_guards :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (pairGuard a)) = true := by decide

def soleOffClock (a b x : Nat) : Nat :=
  let num := modMul x
    (modAdd (modSub (modMul 2 (modPow x 2)) (modMul 3 (modMul (modAdd a b) x)))
      (modMul 5 (modMul a b)))
  modMul num (modPow (twoDonorDenominator a b x) (p-2))

/-- 60 times the degree-four primitive of the remaining receiver/donor
nodes when one of the five physical clock masses is tested in isolation. -/
def quarticPrimitive60 (a b c d x : Nat) : Nat :=
  let s₁ := modAdd (modAdd a b) (modAdd c d)
  let s₂ := modAdd (modAdd (modMul a b) (modMul c d)) (modMul (modAdd a b) (modAdd c d))
  let s₃ := modAdd (modMul (modMul a b) (modAdd c d)) (modMul (modMul c d) (modAdd a b))
  let s₄ := modMul (modMul a b) (modMul c d)
  modAdd
    (modSub
      (modAdd
        (modSub (modMul 12 (modPow x 5)) (modMul 15 (modMul s₁ (modPow x 4))))
        (modMul 20 (modMul s₂ (modPow x 3))))
      (modMul 30 (modMul s₃ (modPow x 2))))
    (modMul 60 (modMul s₄ x))

def allFiveTapsNonzero (a b x : Nat) : Bool :=
  if distinctTriple a b x then
    let q := soleOffClock a b x
    let D := twoDonorDenominator a b x
    modMul D (modPow D (p-2)) == 1 &&
      quarticPrimitive60 a b q x x != 0 && quarticPrimitive60 0 b q x x != 0 &&
      quarticPrimitive60 0 a q x x != 0 && quarticPrimitive60 0 a b x x != 0 &&
      quarticPrimitive60 0 a b q x != 0
  else true

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem all_lobatto_one_off_five_taps :
    nonzeroLobatto.all (fun a => nonzeroLobatto.all (fun b => nonzeroLobatto.all (allFiveTapsNonzero a b))) = true := by
  decide

end RKResearch.Certified.Graded.OneClockScalar
