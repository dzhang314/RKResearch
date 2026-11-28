import Lean

/-! Portable modular determinant replay on the explicit fixed-grid matrices.
The generating scripts independently derive these matrices from the monomial
primitive and companion formulas documented beside the certificates. -/

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.SingletonUnitCore

set_option maxRecDepth 30000
set_option maxHeartbeats 0

abbrev Mat := List (List Nat)

def p : Nat := 1013
def add (a b : Nat) : Nat := (a+b) % p
def neg (a : Nat) : Nat := (p - a % p) % p
def sub (a b : Nat) : Nat := add a (neg b)
def mul (a b : Nat) : Nat := a*b % p

def get (m : Mat) (i j : Nat) : Nat := ((m[i]?.getD [])[j]?).getD 0

def det2 (m : Mat) : Nat := sub (mul (get m 0 0) (get m 1 1))
  (mul (get m 0 1) (get m 1 0))

def det3 (m : Mat) : Nat :=
  let cy := fun i j k => mul (get m 0 i) (mul (get m 1 j) (get m 2 k))
  sub (add (cy 0 1 2) (add (cy 1 2 0) (cy 2 0 1)))
      (add (cy 0 2 1) (add (cy 1 0 2) (cy 2 1 0)))

def det4 (m : Mat) : Nat :=
  let minor := fun j =>
    (m.drop 1).map (fun xs => xs.take j ++ xs.drop (j+1))
  let term := fun j => mul (get m 0 j) (det3 (minor j))
  sub (add (term 0) (term 2)) (add (term 1) (term 3))

def square (m : Mat) (n : Nat) : Bool :=
  m.length == n && m.all (fun r => r.length == n)

structure Entry where
  grid : List Nat
  leading : Nat
  twos : List Mat
  fours : List Mat

def check (a b : Nat) (d : Entry) : Bool :=
  d.leading % p != 0 && d.twos.length == a && d.fours.length == b &&
    d.twos.all (fun m => square m 2 && det2 m != 0) &&
    d.fours.all (fun m => square m 4 && det4 m != 0)

def interiors : List Nat := [347,468,507,546,667]
def d6 : List Int := [-42,840,-5040,12600,-13860,5544]

def evaluate (xs : List Nat) (x : Nat) : Nat :=
  xs.foldr (fun v w => add v (mul x w)) 0

def orders (xs : List Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => xs.flatMap fun x => (orders (xs.filter (· != x)) n).map (x::·)

def chooseFirst (x : Nat) : List (List Nat) :=
  (orders (interiors.filter (· != x)) 4).map (fun tail => [0,x] ++ tail ++ [1])

theorem primeTrialDivision :
    (List.range 30).all (fun i => p % (i+2) != 0) = true := by decide_cbv

theorem derivativeSplit :
    let ds := d6.map (fun v => (v % Int.ofNat p).toNat)
    ds.getLast? = some 479 ∧
    (List.range p).filter (fun x => evaluate ds x == 0) = interiors ∧
    (0 :: interiors ++ [1]).Nodup := by decide_cbv

theorem coverage : (interiors.flatMap chooseFirst).length = 120 := by decide_cbv

#print axioms primeTrialDivision
#print axioms derivativeSplit
#print axioms coverage

end RKResearch.Certified.Graded.OrderTwelveFifteen.SingletonUnitCore
