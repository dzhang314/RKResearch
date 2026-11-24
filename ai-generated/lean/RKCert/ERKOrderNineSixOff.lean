module

public import RKCert.ERKOrderNineSixSix
public import RKCert.OrderNineSixOffFiveOn

@[expose] public section

namespace RKCert.Paired
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- A strict order-nine, twelve-stage tableau over an ordered field
never has six distinct defective abscissas. -/
theorem order9_no_six_off {A : Fin 12 → Fin 12 → K} {b : Vec K 12}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 9) :
    (supportedNodes A (qdef A)).card≠6 := by
  intro hN
  exact order9_no_six_off_six_on ha ho hN (RKCert.FixedFactor.order9_six_off_forces_six_on ha ho hN)

end RKCert.Paired
