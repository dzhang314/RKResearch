module
import RKCert.ReviewedNative.DIRK12MidpointOpeningFourthPhysical

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointForward.Opening
open RKResearch.Certified.DIRK12MidpointGhost RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval

theorem auditFourthKernel (x : ℝ) (hx : Encloses xBox x) (hx0 : realX x=0) :
    let y := yOf x
    let t := tOf x
    J 0 x y t=rAt x t*J 0 x y 1+kAt x t*J 1 x y 1 ∧
    J 1 x y t=rAt x t*J 1 x y 1+kAt x t*(J 2 x y 1-eps x) :=
  fourth_kernel_payment hx hx0

theorem auditPhysicalRowEight (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hx0 : realX x=0) :
    let P := fourFeed x f L
    (∀ j : Fin 4, P.tableau (visible 3) (visible (Fin.castAdd 6 j)) =
      (1/2:ℝ)*fullCardinals4 x (yOf x) (tOf x) (fourthTargetReads x) j) ∧
    P.tableau (visible 3) (visible 3)=0 ∧
    (∀ m : Fin 4, DualSupport12.forward P.tableau (m.val+1) (visible 3)=0) ∧
    DualSupport12.forward P.tableau 5 (visible 3)=
      6*(1/2:ℝ)^6*kAt x (tOf x)*(eps x+(excess:ℝ)) := by
  refine ⟨fun j => row8_actual_entry x f L j hx hx0,row8_zero_diagonal x f L,
    row8_paid x f L hx hx0,?_⟩
  simpa using row8_actual x f L hx hx0 4

theorem auditFourthRemainder (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hx0 : realX x=0) (tail : FourthRemainder x f L) :
    (fourFeed x f L).LiveBudget := four_opening_budget x f L hx hx0 tail

#print axioms auditFourthKernel
#print axioms auditPhysicalRowEight
#print axioms auditFourthRemainder
