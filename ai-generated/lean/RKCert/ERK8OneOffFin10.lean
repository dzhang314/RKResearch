module

public import RKCert.ERK8OneOffEndgame

@[expose] public section

/-! Literal exact-width one-off entrypoint. It deliberately consumes the
public activated midpoint and is not a stage-floor theorem. -/
namespace RKResearch.Certified.Graded.OneOff.Eight

open RKResearch Reverse

variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Source candidate for the *one-off branch only* of exact width ten. -/
theorem erk8_one_off_exclusion (ha : ∀ i j, i≤j → A i j=0)
    (ho : RKResearch.HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    (off : (offKnots A).card=1) : False := by
  obtain ⟨a,d,i,j,D,R,rk,mEq⟩ := physicalPrefix_of_horizon ha ho mid off
  exact finish ha ho mid rk mEq D R

end RKResearch.Certified.Graded.OneOff.Eight
