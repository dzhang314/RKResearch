module
import RKCert.ReviewedNative.DIRK12MidpointOpeningFifth

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointForward.Opening
open RKResearch.Certified.DIRK12MidpointGhost RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval

theorem auditFifthCardinalGuard (x f : ℝ) (hx : Encloses xBox x) (hf : Encloses fBox f) :
    Function.Injective (fifthNodes x f) ∧ (∀ i, fifthNodes x f i≠0) := ⟨fifth_distinct hx hf,fifth_nonzero hx hf⟩

theorem auditPhysicalRowNine (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) :
    let P := fiveFeed x f L
    (∀ i : Fin 5, P.tableau (visible 4) (visible (Fin.castAdd 5 i))=
      (1/2:ℝ)*fifthCoeffs x f i) ∧
    (∀ m : Fin 4, DualSupport12.forward P.tableau (m.val+1) (visible 4)=0) ∧
    DualSupport12.forward P.tableau 5 (visible 4)=6*(1/2:ℝ)^6*kAt x (2*f)*(eps x+(excess:ℝ)) := by
  refine ⟨row9_actual_entry x f L,row9_paid x f L hx hf,?_⟩
  simpa using row9_actual x f L hx hf 4

theorem auditFifthRemainder (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0)
    (tail : FifthRemainder x f L) :
    (fiveFeed x f L).LiveBudget :=
  five_opening_budget x f L hx hf hx0 tail

#print axioms auditFifthCardinalGuard
#print axioms auditPhysicalRowNine
#print axioms auditFifthRemainder
