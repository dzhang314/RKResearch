import Lean

/-! Cleared linear and duplicate-row gates for the invisible-ghost fifth contact. -/
namespace RKResearch.ERK10SingleGhostFifthRowGate
open Lean.Grind
set_option linter.unusedSectionVars false
variable {K : Type} [Field K] [IsCharP K 0]

theorem quarticCalibrates (r : K) (hr : r ≠ 0) :
    (9/8:K)-(3/2:K)^4/4+(r*(9/8:K))/(8*r)=0 := by
  grind

theorem clearedRelation (R a d y : K)
    (quad : 2*R+2*a+3*d=y^2)
    (cubic : 8*R+12*a+27*d=4*y^3)
    (quartic : 4*R+9*a+27*d=2*y^4) :
    2*R=y^2*(2*y-3)^2 := by
  calc
    2*R = 9*(2*R+2*a+3*d)-3*(8*R+12*a+27*d)+2*(4*R+9*a+27*d) := by grind
    _ = 9*y^2-3*(4*y^3)+2*(2*y^4) := by rw [quad,cubic,quartic]
    _ = y^2*(2*y-3)^2 := by grind

theorem incomingList (th r a d y A51 : K)
    (quad : 2*(th*r)+2*a+3*d=y^2)
    (cubic : 8*(th*r)+12*a+27*d=4*y^3)
    (quartic : 4*(th*r)+9*a+27*d=2*y^4)
    (singleClock : r=0 ∨ y=1)
    (rowSum : A51+r+a+d=y) :
    (y=0 ∧ A51=0 ∧ r=0 ∧ a=0 ∧ d=0) ∨
    (2*y=3 ∧ 8*A51=3 ∧ r=0 ∧ 8*a=9 ∧ d=0) ∨
    (y=1 ∧ A51+r=1 ∧ 2*(th*r)=1 ∧ a=0 ∧ d=0) := by
  have h := clearedRelation (th*r) a d y quad cubic quartic
  have sd : 9*d=4*y^3-6*y^2+4*(th*r) := by
    calc
      9*d = (8*(th*r)+12*a+27*d)-6*(2*(th*r)+2*a+3*d)+4*(th*r) := by grind
      _ = _ := by rw [quad,cubic]
  have sa : 2*a=y^2-2*(th*r)-3*d := by grind
  clear quad cubic quartic
  rcases singleClock with hzero | hone
  · subst r
    have hprod : y^2*(2*y-3)^2=0 := by grind
    have hfactor : y=0 ∨ 2*y-3=0 := by
      by_cases hy : y=0
      · exact Or.inl hy
      · exact Or.inr (by grind)
    rcases hfactor with hy | hp
    · subst y
      have hd : d=0 := by grind
      have ha : a=0 := by grind
      exact Or.inl (by grind)
    · have hy : y=(3/2:K) := by grind
      subst y
      have hd : d=0 := by grind
      have ha : 8*a=9 := by grind
      exact Or.inr (Or.inl (by grind))
  · subst y
    have hR : 2*(th*r)=1 := by grind
    have hd : d=0 := by grind
    have ha : a=0 := by grind
    exact Or.inr (Or.inr (by grind))

theorem fifthDuplicate (th r a d y A51 r3 A31 : K) (thLive : th ≠ 0)
    (third : 2*(th*r3)=1) (thirdSum : A31+r3=1)
    (quad : 2*(th*r)+2*a+3*d=y^2)
    (cubic : 8*(th*r)+12*a+27*d=4*y^3)
    (quartic : 4*(th*r)+9*a+27*d=2*y^4)
    (singleClock : r=0 ∨ y=1)
    (rowSum : A51+r+a+d=y) :
    (y=0 ∧ A51=0 ∧ r=0 ∧ a=0 ∧ d=0) ∨
    (2*y=3 ∧ 8*A51=3 ∧ r=0 ∧ 8*a=9 ∧ d=0) ∨
    (y=1 ∧ A51=A31 ∧ r=r3 ∧ a=0 ∧ d=0) := by
  rcases incomingList th r a d y A51 quad cubic quartic singleClock rowSum with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · rcases h with ⟨hy,hsum,hp,ha,hd⟩
    have rEq : r=r3 := by grind
    have firstEq : A51=A31 := by grind
    exact Or.inr (Or.inr ⟨hy,firstEq,rEq,ha,hd⟩)

end RKResearch.ERK10SingleGhostFifthRowGate
#print axioms RKResearch.ERK10SingleGhostFifthRowGate.quarticCalibrates
#print axioms RKResearch.ERK10SingleGhostFifthRowGate.clearedRelation
#print axioms RKResearch.ERK10SingleGhostFifthRowGate.incomingList
#print axioms RKResearch.ERK10SingleGhostFifthRowGate.fifthDuplicate
