import RKCert.ReviewedNative.FiveLadderThirteen
import RKCert.ReviewedNative.PaidStageAppend

open scoped BigOperators Matrix
open RKResearch.Certified

set_option autoImplicit false

example {K : Type*} [Field K] [CharZero K] (g a b : K) (w : Fin 7 → K)
    (h : ∀ j : ℕ, j ≤ 12 →
      (∑ i, w i * (FiveLadderThirteen.nodes g a b i)^j) = 1/(((j+1 : ℕ)):K)) :
    False := FiveLadderThirteen.no_seven_site_ladder g a b w h

example {K ι : Type*} [Fintype ι] [Field K] [CharZero K]
    {A : Matrix ι ι K} {v : ι → K} {x γ : K} {q : ℕ}
    (hq : 1 ≤ q) (h : TwoDonorDense.PaidShiftedJet A v x γ q) :
    TwoDonorDense.PureAt (TwoDonorDense.appendStage A v γ) (Sum.inr PUnit.unit) (q+1) :=
  TwoDonorDense.paid_append_pure hq h

#print axioms FiveLadderThirteen.no_seven_site_ladder
#print axioms TwoDonorDense.paid_append_pure
#print axioms TwoDonorDense.residual_row_payment
