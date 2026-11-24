import RKCert.ReviewedNative.ERKOrder16WeakFiveCensus

open RKResearch Module Polynomial
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.Reverse.Thin RKResearch.Certified.ERK16
open RKCert.Endpoint.WeightedClock RKCert.OneEscape

#print axioms complement_supported_of_stage_restriction
#print axioms quadratic_seed_double_rows
#print axioms weak_seven_tree_restriction
#print axioms weak_seven_support_switch
#print axioms weak_fifteen_quadratic_sites
#print axioms width24_weak_five_census

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 24) (Fin 24) K} {b w : Fin 24 → K} {Q P : K[X]}
    {U : Submodule K (Fin 24 → K)}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 16 A b)
    (seven : finrank K (zeroSpace A 7) = 7)
    (H : FlatClockHead A 5 2 2 U w) (core : U ≤ width24WeakFiveCarrier A b)
    (five : 5 ≤ (weightedSites (reflectedClock A) (reverseContrast A b Q P)).card)
    (qd : Q.natDegree ≤ 4) (pd : P.natDegree ≤ 3)
    (qFit : ∀ i, quadraticSeed A b i * w i = Q.eval (reflectedClock A i) * quadraticSeed A b i)
    (pFit : ∀ i, reflectedClock A i * b i * w i = P.eval (reflectedClock A i) * quadraticSeed A b i) :
    ∃ (q : K[X]) (ι : Fin 5 → Fin 24) (Z : K[X]), q ≠ 0 ∧ WeakFiveInnerPorts A b q Q P Z ι := by
  have C := (width24_weak_five_census ha ho seven H core five qd pd qFit pFit).2.2.2.2.2
  exact width24_weak_five_ports_of_chart ha ho C
