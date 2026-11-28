module
import RKCert.ReviewedNative.DIRK12MidpointOpeningSecond

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointForward.Opening
open RKResearch.Certified.DIRK12MidpointGhost RKResearch.Certified.DirectedRatBox
open RKResearch.Certified.DIRK12MidpointRealInterval

theorem auditFittedOpeningModes (x : ℝ) (hx : Encloses xBox x) :
    let y := yOf x
    db x≠0 ∧ dc x y≠0 ∧ P0 x*Q0 y-Q0 x*P0 y≠0 ∧
    R (alpha x y) (mu x y) 1=1 ∧ R (alpha x y) (mu x y) x=rX x ∧
    R (alpha x y) (mu x y) y=rY x y ∧ K (nu x) x=kX x := by
  obtain ⟨hd,hc,hD,hq,hqy,hxy⟩ := guarded_modes hx
  exact ⟨hd,hc,hD,modes_fit x (yOf x) hq hqy hxy⟩

theorem auditPhysicalRowSix (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ) (hx : Encloses xBox x) :
    let P := openingFeed x f L
    P.tableau (visible 1) (visible 0)=(1/2:ℝ)*ell0 x ∧
    P.tableau (visible 1) (visible 1)=(1/2:ℝ)*ell1 x ∧
    (∀ m : Fin 4, DualSupport12.forward P.tableau (m.val+1) (visible 1)=0) ∧
    DualSupport12.forward P.tableau 5 (visible 1)=6*(1/2:ℝ)^6*kX x*(eps x+(excess:ℝ)) := by
  obtain ⟨a,b⟩ := literal_row6_entries x f L
  refine ⟨a,b,row6_paid x f L hx,?_⟩
  simpa using row6_actual x f L hx 4

theorem auditOpeningPrimitiveRemainder (x f : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (tail : OpeningRemainder x f L) (j : Nat) (hj : j<5) :
    DualSupport12.forward (openingFeed x f L).tableau j ∈ forwardBand ℝ (j+1) :=
  real_opening_fw_primitive x f L hx hf hx0 hf0 tail j hj

#print axioms auditFittedOpeningModes
#print axioms auditPhysicalRowSix
#print axioms auditOpeningPrimitiveRemainder
