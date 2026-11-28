import Mathlib.Tactic.Ring.Basic

namespace RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointScale

variable {K : Type*} [CommRing K]

theorem low_scale_difference (H a b : K) :
    ((a-2)*H*(H-b)-2*H+a+b)-((b-2)*H*(H-a)-2*H+a+b) =
      (a-b)*H*(H-2) := by
  ring1

theorem lost_partner_forces_zero (P Q a : K)
    (h₁ : P*a+Q=0) (h₂ : Q*a+P-2*Q=0) :
    P*(1+2*a-a^2)=0 := by
  calc
    _ = (Q*a+P-2*Q)-(a-2)*(P*a+Q) := by ring1
    _ = 0 := by rw [h₁,h₂]; ring1

theorem transfer_partner_defect (P Q a : K) :
    let D := P*a+Q
    let N := (2-a)*Q-P
    D^2+2*N*D-N^2=(Q^2-P*(P-2*Q))*(1+2*a-a^2) := by
  dsimp
  ring1

end RKResearch.Certified.SDIRKEightDirtySevenBothSingletonBothTwoSDisjointScale
