module

import RKCert.ERK8OneOffFin10

namespace RKResearch.Certified.Graded.OneOff.Eight.Audit

open RKResearch Module Reverse

/-- Required literal branch target. The Horizon and actual one-off knot
count are the only branch inputs beyond strictness and reviewed order. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : RKResearch.HasOrder 8 A b)
    (mid : Reverse.ERKEvenHorizon A b 4) (off : (OneOff.offKnots A).card=1) : False :=
  Eight.erk8_one_off_exclusion ha ho mid off

/-- Separately type the chart result: no propagated assumption about
physical placement or the grade-five profile is supplied by the caller. -/
example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : RKResearch.HasOrder 8 A b)
    (mid : Reverse.ERKEvenHorizon A b 4) (off : (OneOff.offKnots A).card=1) :
    ∃ (a d : K) (i j : Fin 10), OneOff.GlobalNormal A a d i j ∧ Eight.PhysicalPrefix A a d ∧
      finrank K (treeSpace A 5)=9 ∧ LinearMap.range (Eight.shortProfileMap A)=treeSpace A 5 :=
  Eight.physicalPrefix_of_horizon ha ho mid off

#print axioms earnedNormal
#print axioms terminalDefectZero
#print axioms gradeFiveCap
#print axioms firstFour
#print axioms fifthFeature
#print axioms zero_F5_low_top_kernel
#print axioms zero_F5_poly_le_three
#print axioms low_relation_zero
#print axioms defectsSeparate
#print axioms shortProfileFull
#print axioms noCausalClockContrast
#print axioms sixthRow
#print axioms physicalPrefix_of_horizon
#print axioms causalJV
#print axioms terminalPolynomial
#print axioms terminalProfile
#print axioms cleanW
#print axioms seventhAlternative
#print axioms curveClockTrap
#print axioms finish
#print axioms erk8_one_off_exclusion

end RKResearch.Certified.Graded.OneOff.Eight.Audit
