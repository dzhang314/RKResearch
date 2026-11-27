module
public import RKCert.ReviewedNative.ERK8PaidArithmetic

public import RKCert.ReviewedNative.ERK8PaidOneOffEndgame

@[expose] public section

/-! Literal exact-width one-off entrypoint. It deliberately consumes the
public activated midpoint and is not a stage-floor theorem. -/
namespace RKResearch.Certified.Graded.OneOff.PaidProof.Eight

open RKResearch Reverse

variable {K : Type*} [Field K] [EightUnits K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}

/-- Paid proof for the one-off branch of exact width ten. -/
theorem erk8_one_off_exclusion (ha : ∀ i j, i≤j → A i j=0)
    (ho : RKResearch.HasOrder 8 A b) (mid : ERKEvenHorizon A b 4)
    (off : (offKnots A).card=1) : False := by
  obtain ⟨a,d,i,j,D,R,rk,mEq⟩ := physicalPrefix_of_horizon ha ho mid off
  exact finish ha ho mid rk mEq D R

end RKResearch.Certified.Graded.OneOff.PaidProof.Eight

namespace RKResearch.Certified.Graded.OneOff.EightPaid

open RKResearch ERK8PaidField

variable {K : Type*} [Field K]
variable {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10→K}

/-- The literal ten-stage one-off branch is impossible in every field.
The 8! unit and actual horizon are both earned from the reviewed order. -/
theorem no_order8_one_off
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder 8 A b)
    (off : (OneOff.offKnots A).card=1) : False := by
  letI : PaidProof.EightUnits K := PaidProof.eightUnits_of_order ho
  exact PaidProof.Eight.erk8_one_off_exclusion ha ho
    (order8_paid_even_horizon ha ho) off

end RKResearch.Certified.Graded.OneOff.EightPaid

#print axioms RKResearch.Certified.Graded.OneOff.EightPaid.no_order8_one_off
