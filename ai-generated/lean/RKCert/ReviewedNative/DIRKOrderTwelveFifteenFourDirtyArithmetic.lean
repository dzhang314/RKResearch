import Lean

/-! Core exact arithmetic for the four-noncancelling cubic fibers on the
15-stage C(2), f₅ = 3 DIRK12 equality face. -/

namespace RKResearch.Certified.Graded.OrderTwelveFifteen.FourDirtyArithmetic

set_option maxRecDepth 20000
set_option maxHeartbeats 0

def prime : Nat := 43
def interiors : List Nat := [2,9,22,35,42]
def negative (x : Nat) := (prime - x % prime) % prime
def subMod (x y : Nat) := (x + negative y) % prime

def addPoly (x y : List Nat) : List Nat :=
  match x, y with
  | [], ys => ys
  | xs, [] => xs
  | a::as, b::bs => ((a+b) % prime)::addPoly as bs

def mulPoly (x y : List Nat) : List Nat :=
  match x with
  | [] => []
  | a::as => addPoly (y.map fun b => a*b % prime) (0::mulPoly as y)

def evaluate (f : List Nat) (x : Nat) : Nat :=
  f.foldr (fun a t => (a + x*t) % prime) 0

def hull (points : List Nat) : List Nat :=
  points.foldr (fun x f => mulPoly [negative x,1] f) [1]

def inverseSmall (n : Nat) : Nat :=
  ([0,1,22,29,11,26,36,37,27,24,13,4,18] : List Nat)[n]?.getD 0

def primitive (f : List Nat) : List Nat :=
  0 :: ((List.range f.length).map fun j => (f[j]?.getD 0) * inverseSmall (j+1) % prime)

def integral (f : List Nat) (a b : Nat) : Nat :=
  subMod (evaluate (primitive f) b) (evaluate (primitive f) a)

def tapRow (u : Nat) : List Nat :=
  let grid := 0::interiors
  grid.map fun z => integral (hull (grid.filter (· != z))) 0 u

def twoMomentDet (u d : Nat) : Nat :=
  let f := hull [0,u,d]
  let a := integral f 0 u
  let b := integral (0::f) 0 u
  let c := integral (0::0::f) 0 u
  subMod (a*c) (b*b)

def twoMomentRow (u : Nat) : List Nat :=
  (interiors.filter (· != u)).map (twoMomentDet u)

def onelineProfile (h : List Nat) (a b : Nat) : List Nat :=
  mulPoly h [integral (0::h) a b, negative (integral h a b)]

def crossed (u : Nat) (fwd bwd : List Nat) : Nat :=
  let f := onelineProfile (hull (0::u::fwd)) 0 u
  let g := onelineProfile (hull (1::u::bwd)) u 1
  integral (mulPoly (primitive f) g) 0 1

def selectPairs (l : List Nat) : List (List Nat) :=
  match l with
  | [] => []
  | a::as => (as.map fun b => [a,b]) ++ selectPairs as

def crossedRow (u : Nat) : List Nat :=
  let dirty := interiors.filter (· != u)
  (selectPairs dirty).map fun pair => crossed u pair (dirty.filter fun x => !pair.contains x)

def d6 : List Int := [-42,840,-5040,12600,-13860,5544]
def d6Residue : List Nat := d6.map fun c => (c % Int.ofNat prime).toNat

theorem modulusChecks :
    ((List.range 5).map (·+2)).all (fun n => prime % n != 0) = true ∧
    ((List.range 12).map (·+1)).all (fun n => n * inverseSmall n % prime == 1) = true := by decide

theorem gridChecks :
    d6Residue = [1,23,34,1,29,40] ∧
    (List.range prime).filter (fun x => evaluate d6Residue x == 0) = interiors ∧
    (interiors.map (fun x => subMod 1 x)).reverse = interiors ∧
    interiors.Nodup := by decide

theorem taps2 : tapRow 2 = [14,11,5,2,15,39] := by decide_cbv
theorem taps9 : tapRow 9 = [40,11,8,9,3,15] := by decide_cbv
theorem taps22 : tapRow 22 = [30,26,41,20,2,10] := by decide_cbv
theorem taps35 : tapRow 35 = [40,26,14,8,12,29] := by decide_cbv
theorem taps42 : tapRow 42 = [14,14,20,6,16,16] := by decide_cbv

theorem determinants2 : twoMomentRow 2 = [3,9,10,39] := by decide_cbv
theorem determinants9 : twoMomentRow 9 = [4,10,7,32] := by decide_cbv
theorem determinants22 : twoMomentRow 22 = [19,37,20,16] := by decide_cbv
theorem determinants35 : twoMomentRow 35 = [9,8,21,5] := by decide_cbv
theorem determinants42 : twoMomentRow 42 = [1,9,22,16] := by decide_cbv

theorem crossed2 : crossedRow 2 = [24,14,3,33,24,22] := by decide_cbv
theorem crossed9 : crossedRow 9 = [30,37,9,18,35,18] := by decide_cbv
theorem crossed22 : crossedRow 22 = [2,7,33,33,21,37] := by decide_cbv
theorem crossed35 : crossedRow 35 = [30,37,18,9,35,18] := by decide_cbv
theorem crossed42 : crossedRow 42 = [24,14,33,3,24,22] := by decide_cbv

theorem allTapNumerators :
    (interiors.flatMap tapRow).length = 30 ∧
    (interiors.flatMap tapRow).all (· != 0) = true := by
  simp [interiors, taps2, taps9, taps22, taps35, taps42, List.flatMap_cons]

theorem allMomentDeterminants :
    (interiors.flatMap twoMomentRow).length = 20 ∧
    (interiors.flatMap twoMomentRow).all (· != 0) = true := by
  simp [interiors, determinants2, determinants9, determinants22, determinants35,
    determinants42, List.flatMap_cons]

theorem allCrossedIntegrals :
    (interiors.flatMap crossedRow).length = 30 ∧
    (interiors.flatMap crossedRow).all (· != 0) = true := by
  simp [interiors, crossed2, crossed9, crossed22, crossed35, crossed42, List.flatMap_cons]

#print axioms modulusChecks
#print axioms gridChecks
#print axioms allTapNumerators
#print axioms allMomentDeterminants
#print axioms allCrossedIntegrals

end RKResearch.Certified.Graded.OrderTwelveFifteen.FourDirtyArithmetic
