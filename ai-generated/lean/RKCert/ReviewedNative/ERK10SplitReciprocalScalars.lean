namespace RKResearch.Certified.ERK10SplitReciprocalScalars

theorem pivotDiscriminantBracket :
    (28558112 : Nat)^2 < 815565802526596 ∧
      815565802526596 < (28558113 : Nat)^2 := by decide

theorem nonlinearCubicProjectiveModThirteen :
    ∀ a b : Fin 13, (a ≠ 0 ∨ b ≠ 0) →
      (2*a.val^3 + 5*a.val^2*b.val + 12*a.val*b.val^2 + b.val^3) % 13
        ≠ 0 := by decide

end RKResearch.Certified.ERK10SplitReciprocalScalars

#print axioms RKResearch.Certified.ERK10SplitReciprocalScalars.pivotDiscriminantBracket
#print axioms RKResearch.Certified.ERK10SplitReciprocalScalars.nonlinearCubicProjectiveModThirteen

namespace RKResearch.Certified.ERK10SplitReciprocalScalars

def residueMinorZero : List Nat :=
  [17,27,17,2,18,12,11,14,23,12,5,12,24,23,5,16,25,
   20,20,6,21,11,25,0,26,16,12,17,14,13,19,8,27]

def residueMinorSix : List Nat :=
  [28,2,5,12,2,16,19,16,2,0,4,16,14,6,12,14,27,24,
   19,4,11,22,14,25,18,12,25,3,15,14,18,19,20,0,0,0]

def eval29 (cs : List Nat) (a : Nat) : Nat :=
  cs.foldl (fun x c => (x*a+c)%29) 0

theorem residueTwoMinorFinite :
    ∀ a : Fin 29, eval29 residueMinorZero a.val ≠ 0 ∨
                  eval29 residueMinorSix a.val ≠ 0 := by decide

theorem residueMinorInfinity : residueMinorSix.headD 0 = 28 := by decide

theorem pivotProjectiveModTwentyNine :
    ∀ a b : Fin 29, (a ≠ 0 ∨ b ≠ 0) →
      (21*a.val^2+22*a.val*b.val+19*b.val^2)%29 ≠ 0 := by decide

end RKResearch.Certified.ERK10SplitReciprocalScalars

#print axioms RKResearch.Certified.ERK10SplitReciprocalScalars.residueTwoMinorFinite
#print axioms RKResearch.Certified.ERK10SplitReciprocalScalars.residueMinorInfinity
#print axioms RKResearch.Certified.ERK10SplitReciprocalScalars.pivotProjectiveModTwentyNine
