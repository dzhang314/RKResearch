module
public import RKResearch.OrderConditions
public import Mathlib.Algebra.Order.Field.Basic
import RKCert.ReviewedOrderBridge
import RKCert.ExplicitOrderFifteen

public section

namespace RKResearch.Certified

/-- An explicit Runge–Kutta tableau of order at least fifteen has at
least twenty-three stages over any ordered field. -/
theorem explicit_order_fifteen_at_least_twenty_three {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] {s : ℕ}
    {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j : Fin s, i ≤ j → A i j = 0)
    (ho : RKResearch.HasOrder 15 A b) : 23 ≤ s :=
  RKCert.explicit_order_fifteen_at_least_twenty_three ha
    ((RKCert.ReviewedOrderBridge.hasOrder_iff A b 15).mp ho)

end RKResearch.Certified
