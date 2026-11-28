import Lean.Elab.Tactic.Omega

/-! Portable exact coefficient-prime certificate for the fixed-quartic
obstruction to an identically zero fifth ordinary clock condition. -/
namespace RKResearch.Certified.Graded.OrderTwelveFifteen.FifthOrdinaryCore

def pStar (x : Nat) : Int :=
  let a := Int.ofNat x
  (((99*a-165)*a+90)*a-18)*a+1

def pStarDeriv (x : Nat) : Int :=
  let a := Int.ofNat x
  ((396*a-495)*a+180)*a-18

def L₆d (x : Nat) : Int :=
  let a := Int.ofNat x
  ((((5544*a-13860)*a+12600)*a-5040)*a+840)*a-42

def twoClock (x y : Nat) : Int :=
  let a := Int.ofNat x
  let b := Int.ofNat y
  a^4*(2*b-a)*L₆d y-b^3*(2*b*b-6*a*b+5*a*a)*L₆d x

def roots : List Nat := [24,36,47,65]

theorem primeTrial : (List.range 7).all (fun i => 73 % (i+2) != 0) = true :=
  by decide +kernel

theorem completeRoots :
    (List.range 73).filter (fun a => pStar a % 73 == 0) = roots :=
  by decide +kernel

theorem unitGuards :
    roots.all (fun a => a != 0 && pStarDeriv a % 73 != 0 && L₆d a % 73 != 0) = true :=
  by decide +kernel

theorem distinctPairs :
    roots.all (fun a => roots.all (fun b => (a == b) || twoClock a b % 73 != 0)) = true :=
  by decide +kernel

#print axioms primeTrial
#print axioms completeRoots
#print axioms unitGuards
#print axioms distinctPairs
end RKResearch.Certified.Graded.OrderTwelveFifteen.FifthOrdinaryCore
