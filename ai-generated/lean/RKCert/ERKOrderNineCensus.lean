module

public import RKCert.ERKOrderNineHighOff
public import RKCert.ERKOrderNineSixOff
public import RKCert.ERKOrderNineFiveOnFiveOff

@[expose] public section

/-! # Exact remaining order-nine finite cases -/
namespace RKCert.Paired
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- For a literal order-nine twelve-stage explicit tableau over an
ordered field, the remaining possibilities are a single defective
abscissa or a five-off/six-on two-curve chart. This is a reduction
and claims no numerical promotion. -/
theorem order9_actual_remaining_census {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card=1 ∨
      ((supportedNodes A (qdef A)).card=5 ∧ (onNodes A).card=6) := by
  have low := order9_reduced_off_count_chart ha ho
  dsimp only at low
  have high := order9_no_eight_or_more_off ha ho
  have h6 := order9_no_six_off ha ho
  have h7 := RKCert.FixedFactor.order9_no_seven_off ha ho
  have h : (supportedNodes A (qdef A)).card=1 ∨ (supportedNodes A (qdef A)).card=5 := by omega
  exact h.imp_right fun hn => ⟨hn,order9_five_off_forces_six_on ha ho hn⟩

end RKCert.Paired
