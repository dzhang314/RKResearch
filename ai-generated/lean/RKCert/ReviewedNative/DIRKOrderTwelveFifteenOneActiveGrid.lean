import Lean

/-! Core coefficient checks for the conditional fixed-grid one-label branch. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.OneActiveGrid

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def p : Nat := 1013
def add (a b : Nat) : Nat := (a+b) % p
def neg (a : Nat) : Nat := (p-a%p)%p
def sub (a b : Nat) : Nat := add a (neg b)
def mul (a b : Nat) : Nat := a*b%p
def res (n : Int) : Nat := (n % Int.ofNat p).toNat

def d6 : List Int := [-42,840,-5040,12600,-13860,5544]
def inner : List Nat := [347,468,507,546,667]
def live : List Nat := inner ++ [1]

def horner (as : List Nat) (x : Nat) : Nat :=
  as.foldr (fun a q => add a (mul x q)) 0

def radauPair (a b : Nat) : Nat :=
  add (sub (mul 10 (mul b b)) (mul 12 (mul a b))) (mul 3 (mul a a))

def nodalTriple (a b u : Nat) : Nat :=
  add (sub (mul 3 (mul u u)) (mul 5 (mul (add a b) u))) (mul 10 (mul a b))

def checkPairs : Bool :=
  live.all fun a => live.all fun b => a == b || radauPair a b != 0

def checkTriples : Bool :=
  live.all fun a => live.all fun b => live.all fun u =>
    a == b || a == u || b == u || nodalTriple a b u != 0

theorem primeTrialDivision :
    (List.range 30).all (fun i => p % (i+2) != 0) = true := by decide +kernel

theorem split :
    (d6.map res).getLast? = some 479 ∧
    (List.range p).filter (fun x => horner (d6.map res) x == 0) = inner ∧
    (0 :: live).Nodup := by decide +kernel

theorem noRadauRatio : checkPairs = true := by decide +kernel
theorem noNodalTriple : checkTriples = true := by decide +kernel

#print axioms primeTrialDivision
#print axioms split
#print axioms noRadauRatio
#print axioms noNodalTriple

end RKResearch.Certified.Graded.OrderTwelveFifteen.OneActiveGrid
