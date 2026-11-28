import Lean

/-! Scalar and exact arithmetic for the two-ended Jacobi doubling obstruction. -/
namespace RKResearch.ERK11TwoCarrierJacobiGate

open Lean.Grind
variable {K : Type} [Field K] [IsCharP K 0]
set_option linter.unusedSectionVars false

def j4 (x : K) := 42*x^4-84*x^3+56*x^2-14*x+1
def j5 (x : K) := 132*x^5-330*x^4+300*x^3-120*x^2+20*x-1
def doubleP (x : K) :=
  1386*x^8-8316*x^7+20496*x^6-27090*x^5+20973*x^4-9720*x^3+2632*x^2-384*x+24

theorem reflection (x : K) : j4 (1-x)=j4 x ∧ j5 (1-x)= -j5 x := by
  unfold j4 j5
  constructor <;> grind

theorem doubling (x : K) :
    8*(j5 x * j4 (x/2) - j5 (x/2) * j4 x) = x*doubleP x := by
  unfold j4 j5 doubleP
  grind

theorem oneApart (a : K) :
    j5 a*j4 (a-1)-j5 (a-1)*j4 a =
      2*(2772*(a-1)^8-3528*(a-1)^6+1212*(a-1)^4-104*(a-1)^2+1) := by
  unfold j4 j5
  grind

set_option maxRecDepth 30000
set_option maxHeartbeats 0

def a4 : List Int := [1,-14,56,-84,42]
def a5 : List Int := [-1,20,-120,300,-330,132]
def aq : List Int := [24,-384,2632,-9720,20973,-27090,20496,-8316,1386]

def term (a : List Int) (i : Nat) : Int := a[i]?.getD 0
def eval (a : List Int) (x : Int) : Int := a.foldr (fun v r => v+x*r) 0

def wmoment (a : List Int) (j : Nat) : Int :=
    a.zipIdx.foldl (fun z (v,i) =>
      z+v*((27720:Int)/(Int.ofNat (i+j+2)*Int.ofNat (i+j+3)))) 0

theorem moments : ∀ j : Fin 4, wmoment a4 j.val=0 ∧ wmoment a5 j.val=0 := by decide

def bezout (s : Int) (i j : Nat) : Int :=
  let a := term aq
  let b := fun k => term a5 k + s*term a4 k
  (List.range (min i j+1)).foldl (fun p k =>
    let h := i+j+1-k
    if h < 9 then p+(a h*b k-a k*b h) else p) 0

def matrix (s : Int) : List (List Int) :=
  (List.range 8).map (fun i => (List.range 8).map (bezout s i))

def determinant : Nat → List (List Int) → Int → Option Int
  | 0, _, _ => some 1
  | 1, mat, _ => some (term (mat.headD []) 0)
  | n+2, mat, prev =>
    match mat.zipIdx.find? (fun (r,_) => term r 0 != 0) with
    | none => some 0
    | some (pivot,i) =>
      let p := term pivot 0
      let new := (mat.eraseIdx i).map (fun row =>
        List.zipWith (fun x y => p*x-term row 0*y) row.tail pivot.tail)
      if prev == 0 || !(new.all (fun row => row.all (fun a => a % prev == 0)))
      then none
      else ((determinant (n+1) (new.map (fun row => row.map (· / prev))) p).map
        (fun val => if i%2==0 then val else -val))

def v : List Int :=
  [31138569,-150701166,211271046,-114018492,78459211,-15432746,7089124,72404556,17849034]
def vR : List Int := v.zipIdx.map (fun (c,i) => if i%2==0 then c else -c)

theorem determinantSamples : ∀ s : Fin 9,
    let z := Int.ofNat s.val
    determinant 8 (matrix z) 1 = some (14575336896282624*eval v z) := by decide

def add (a b : List Int) : List Int :=
  (List.range (max a.length b.length)).map (fun i => term a i+term b i)
def mul (a b : List Int) : List Int :=
  (List.range (a.length+b.length-1)).map (fun k =>
    (List.range (k+1)).foldl (fun s i => s+term a i*term b (k-i)) 0)
def red (a : List Int) : List Int := a.map (· % 13)

theorem degreePreserved :
    red v = [7,8,12,10,12,9,3,3,8] ∧
    red vR = [7,5,12,3,12,4,3,10,8] := by decide

theorem residueBezout :
    red (add (mul [1,4,3,7,11,4,6,10] v)
             (mul [1,9,3,6,11,9,6,3] vR)) =
             1::List.replicate 15 0 := by decide

end RKResearch.ERK11TwoCarrierJacobiGate
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.reflection
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.doubling
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.oneApart
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.moments
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.determinantSamples
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.degreePreserved
#print axioms RKResearch.ERK11TwoCarrierJacobiGate.residueBezout
