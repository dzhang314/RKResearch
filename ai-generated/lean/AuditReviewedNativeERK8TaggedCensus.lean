module

import RKCert.ReviewedNative.ERKOrderEightTaggedCensus

open RKResearch
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.MultiOff
open RKResearch.Certified.Graded.ERKTaggedHorizon (cleanKnots)

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 8 A b) :
    ERKEvenHorizon A b 4 ∧ ((offKnots A).card = 1 ∨ (offKnots A).card = 4) :=
  order8_native_one_or_four_with_horizon ha ho

example {K : Type*} [Field K] [CharZero K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : RKResearch.HasOrder 8 A b) :
    ERKEvenHorizon A b 4 ∧
      ((offKnots A).card = 1 ∨ (offKnots A).card = 4 ∧ (cleanKnots A).card = 5) :=
  order8_native_tagged_census ha ho

#print axioms RKResearch.Certified.Graded.MultiOff.order8_native_even_horizon
#print axioms RKResearch.Certified.Graded.MultiOff.order8_native_tagged_census
#print axioms RKResearch.Certified.Graded.MultiOff.order8_native_one_or_four_with_horizon
