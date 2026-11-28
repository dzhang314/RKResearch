module

public import RKCert.ReviewedNative.DIRKOrderTwelveMidpointGhostCore

@[expose] public section

/-! Exact low forward arithmetic for the literal four hidden midpoint rows.

The grading is h, p*h, p^2*h, with no full-tableau premise. -/

namespace RKResearch.Certified.DIRK12MidpointGhost

def add3 (f : Fin 3 → Rat) : Rat := f 0 + f 1 + f 2

def lift (k : Nat) (i : Fin 4) : Rat := cubic i * clock i ^ k

def imageCoeff (k : Fin 2) (l : Fin 3) : Rat :=
  if k = 0 then
    if l = 0 then 25/12 else if l = 1 then -47/6 else 0
  else
    if l = 0 then 79/144 else if l = 1 then -35/18 else -1/2

/-- Scaled defects on entering powers 1, 2, 3, 4. -/
def primitiveCoeff (m : Fin 4) (l : Fin 3) : Rat :=
  if m = 0 then 0
  else if m = 1 then if l = 0 then 3 else 0
  else if m = 2 then if l = 0 then -2 else if l = 1 then 14 else 0
  else if l = 0 then 91/24 else if l = 1 then -95/3 else 75

theorem cubic_literal (i : Fin 4) :
    cubic i = if i = 0 then 1/384 else if i = 1 then -1/162
              else if i = 2 then 4/3993 else -1/534 := by
  revert i
  decide +kernel

theorem action_lift :
    ∀ (k : Fin 2) (i : Fin 4), act (lift k.val) i =
      add3 (fun l => imageCoeff k l * lift l.val i) := by
  decide +kernel

theorem imageCoeff_zero :
    ∀ (k : Fin 2) (l : Fin 3), k.val+1 < l.val → imageCoeff k l = 0 := by
  decide +kernel

theorem primitive_lift :
    ∀ (m : Fin 4) (i : Fin 4),
    ((m.val+2 : Nat) : Rat) * act (fun j => clock j ^ (m.val+1)) i -
      clock i ^ (m.val+2) = add3 (fun l => primitiveCoeff m l * lift l.val i) := by
  decide +kernel

theorem primitiveCoeff_zero :
    ∀ (m : Fin 4) (l : Fin 3), m.val ≤ l.val → primitiveCoeff m l = 0 := by
  decide +kernel

theorem tap_annihilates :
    ∀ k : Fin 3, add4 (fun i => tap i * lift k.val i) = 0 := by
  decide +kernel

theorem first_diagonal : block 0 0 = 1/8 := by
  decide +kernel

end RKResearch.Certified.DIRK12MidpointGhost

#print axioms RKResearch.Certified.DIRK12MidpointGhost.action_lift
#print axioms RKResearch.Certified.DIRK12MidpointGhost.primitive_lift
#print axioms RKResearch.Certified.DIRK12MidpointGhost.tap_annihilates
