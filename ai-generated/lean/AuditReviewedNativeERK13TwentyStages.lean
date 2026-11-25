module

import RKCert.ReviewedNative.ERK13NativeTwentyStages

open RKResearch
open RKResearch.Certified.Graded.ERK13NativeFirst

example {K : Type*} [Field K] [CharZero K]
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (hA : ∀ i j, i ≤ j → A i j = 0) (h : HasOrder 13 A b) : 20 ≤ s :=
  twenty_le_of_order_thirteen hA h

#print axioms twenty_le_of_order_thirteen
