module

public import RKCert.ReviewedNative.ERK13NativeWidth19Assembly
public import RKCert.ReviewedNative.ERK13NativeMarkedLobattoDispatch

public section

/-! # The sole remaining early cut in the Lean order-thirteen proof -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst

open RKResearch

/-- The actual degree-six escape is impossible in either of its radii. -/
theorem earlyMarkedObstruction13_five (K : Type*) [Field K] [CharZero K] :
    EarlyMarkedObstruction13 K 5 :=
  fun ha ho chart _ => chart.degree_six_impossible ha ho

/-- Only the degree-seven marked escape remains as an input to the
characteristic-zero stage bound. -/
theorem twenty_le_of_order_thirteen_of_degree_seven_cut {K : Type*} [Field K] [CharZero K]
    (earlySix : EarlyMarkedObstruction13 K 6)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 13 A b) : 20 ≤ s :=
  twenty_le_of_order_thirteen_of_early_cuts (earlyMarkedObstruction13_five K) earlySix ha ho

end RKResearch.Certified.Graded.ERK13NativeFirst
