import RKCert.ReviewedNative.ERKOrder16WeakHead

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKResearch.Certified.ERK16
open RKCert.Endpoint.WeightedClock RKCert.OneEscape

#print axioms paid_clock_core_le_carrier
#print axioms width24_seed_rows_ge_fifteen
#print axioms width24_twice_paid_F5_le_carrier
#print axioms width24_two_paid_core_rank
#print axioms width24_seven_not_all_hidden
#print axioms width24_ordinary_weak_head
#print axioms width24_weak_five_ports_of_ordinary_head

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b : Fin 24 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7) :
    ∃ (U : Submodule K (Fin 24 → K)) (w : Fin 24 → K) (Q P : K[X]),
      Width24OrdinaryWeakHead A b U w Q P :=
  width24_ordinary_weak_head ha ho seven
