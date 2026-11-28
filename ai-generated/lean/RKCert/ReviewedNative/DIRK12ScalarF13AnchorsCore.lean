/-! Core arithmetic for the canonical F13 scalar moment weights. -/
namespace RKResearch.Certified.DIRK12ScalarF13Anchors

def inverses : List Nat := [1,7,9,10,8,11,2,5,3,4,6,12]
def rho (a : Nat) : Nat :=
  ((List.range 12).zip inverses).foldl (fun t ij => (t+ij.2*a^(ij.1+1)) % 13) 0
def residueTable : List Nat := [0,0,7,8,0,6,4,3,4,6,0,8,7]
def anchoredCount (theta : Nat) : Nat :=
  ((List.range 13).filter (fun a => a == 0 || a == 1 || (theta + rho a) % 13 != 0)).length
def moment (theta : Nat) (j : Nat) : Nat :=
  ((List.range 13).foldl (fun s a => (s + a^j * (theta + rho a)) % 13) 0)

theorem residue_literal : ∀ a : Fin 13, rho a.val = residueTable[a.val]! := by
  decide

theorem anchor_count : ∀ theta : Fin 13, 11 ≤ anchoredCount theta.val := by
  decide

theorem anchor_count_there_is_equality : anchoredCount 0 = 11 := by
  decide

theorem finite_moments : ∀ j : Fin 12, moment 0 j.val = inverses[j.val]! := by
  decide

end RKResearch.Certified.DIRK12ScalarF13Anchors

#print axioms RKResearch.Certified.DIRK12ScalarF13Anchors.residue_literal
#print axioms RKResearch.Certified.DIRK12ScalarF13Anchors.anchor_count
#print axioms RKResearch.Certified.DIRK12ScalarF13Anchors.anchor_count_there_is_equality
#print axioms RKResearch.Certified.DIRK12ScalarF13Anchors.finite_moments
