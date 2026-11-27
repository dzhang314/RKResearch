import Std

namespace RKResearch.Certified.RationalERKEndpointSixMod11

/-- Synthetic division by X-x, in descending coefficient order. -/
def synthetic (x : Nat) : List Nat → Nat → List Nat × Nat
  | [], a => ([],a)
  | [t], a => ([],(t+x*a)%11)
  | t::u::rest, a =>
      let v := (t+x*a)%11
      let (q,r) := synthetic x (u::rest) v
      (v::q,r)

def strip (x : Nat) : Nat → List Nat → List Nat
  | 0, f => f
  | n+1, f =>
      if f.length ≤ 1 then f else
        let (q,r) := synthetic x f 0
        if r=0 then strip x n q else f

def split (p : List Nat) : Bool :=
  ((List.range 11).foldl (fun f x => strip x 4 f) p).length == 1

def cubic := [3,1,9,10]
def quartic (a : Nat) := [9,(4+3*a)%11,(1+a)%11,(8+9*a)%11,(1+10*a)%11]

theorem finite_pencil_not_split :
    ((List.range 11).all fun a => ! split (quartic a)) = true := by
  decide +kernel

theorem infinity_pencil_not_split : split cubic = false := by
  decide +kernel

end RKResearch.Certified.RationalERKEndpointSixMod11
