module
import RKCert.ReviewedNative.DIRK12MidpointOpeningThirdPhysical

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointForward.Opening
open RKResearch.Certified.DIRK12MidpointGhost RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval

theorem auditRealOpeningG3 (x : ℝ) (hx0 : realX x=0) :
    g3 x (yOf x)=0 := g3_real_zero hx0

theorem auditPhysicalRowSeven (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hx0 : realX x=0) :
    let P := threeFeed x f L
    (∀ m : Fin 4, DualSupport12.forward P.tableau (m.val+1) (visible 2)=0) ∧
    DualSupport12.forward P.tableau 5 (visible 2)=
      6*(1/2:ℝ)^6*kY x (yOf x)*(eps x+(excess:ℝ)) := by
  refine ⟨row7_paid x f L hx hx0,?_⟩
  simpa using row7_actual x f L hx hx0 4

theorem auditThirdRemainder (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hx0 : realX x=0) (tail : ThirdRemainder x f L) :
    (threeFeed x f L).LiveBudget := three_opening_budget x f L hx hx0 tail

#print axioms auditRealOpeningG3
#print axioms auditPhysicalRowSeven
#print axioms auditThirdRemainder
