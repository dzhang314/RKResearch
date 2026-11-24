module
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fin.VecNotation

@[expose] public section

/-! # Previously recorded split-prime Radau arithmetic
Only the documented seven-node grid is evaluated; this is modular
arithmetic, not a characteristic-zero nonvanishing theorem. -/
namespace RKCert.FixedPolynomial.Radau77569

theorem prime : Nat.Prime 77569 := by norm_num

instance : Fact (Nat.Prime 77569) := ⟨prime⟩

abbrev F := ZMod 77569

def leftRoots : Fin 7 → F := ![1183,3060,5614,14945,34802,41996,58713]
def leftGrid : Fin 8 → F := ![0,1183,3060,5614,14945,34802,41996,58713]
def rightRoots (i : Fin 7) : F := 1-leftRoots i

def reproducer (x : F) : F :=
  -51480*x^7+192192*x^6-288288*x^5+221760*x^4-92400*x^3+20160*x^2-2016*x+64

def diffReproducer (x : F) : F :=
  (-51480*7)*x^6+(192192*6)*x^5-(288288*5)*x^4+(221760*4)*x^3-
    (92400*3)*x^2+(20160*2)*x-2016

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2500000 in
theorem root_table :
    (∀ i : Fin 7, reproducer (leftRoots i)=0 ∧ diffReproducer (leftRoots i)≠0) ∧
      Function.Injective leftGrid := by
  unfold Function.Injective
  decide

/-- Primitive numerator multiplied by lcm(1,…,7)=420. -/
def momentThree (j : ℕ) (u a b c : F) : F :=
  ((420/(j+4):ℕ):F)*u^(j+4) - ((420/(j+3):ℕ):F)*(a+b+c)*u^(j+3)
    + ((420/(j+2):ℕ):F)*(a*b+a*c+b*c)*u^(j+2) - ((420/(j+1):ℕ):F)*a*b*c*u^(j+1)

def threeGram (u a b c : F) : F :=
  momentThree 1 u a b c*momentThree 3 u a b c-(momentThree 2 u a b c)^2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem left_three_gram :
    ∀ (i : Fin 7) (a b c : Fin 8), a<b → b<c →
      a≠i.succ → b≠i.succ → c≠i.succ →
      threeGram (leftRoots i) (leftGrid a) (leftGrid b) (leftGrid c)≠0 := by decide

def timesLinear (r : F) (xs : List F) : List F :=
  List.zipWith (·+·) ((xs.map fun a => -r*a)++[0]) (0::xs)

def selected (mask : Fin 128) : List (Fin 7) :=
  (List.finRange 7).filter (fun j => mask.val.testBit j.val)

def rightFactorCoefficients (mask : Fin 128) : List F :=
  (selected mask).foldl (fun c i => timesLinear (rightRoots i) c) [1]

def coeffMoment (j : ℕ) (u : F) (cs : List F) : F :=
  (cs.zipIdx.map (fun (a,i) => ((420/(i+j+1):ℕ):F)*a*u^(i+j+1))).sum

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem right_omitted_moment :
    ∀ (u : Fin 7) (mask : Fin 128), mask.val.testBit u.val=false →
      (selected mask).length≤4 →
      coeffMoment 1 (rightRoots u) (rightFactorCoefficients mask)≠0 := by decide

end RKCert.FixedPolynomial.Radau77569
