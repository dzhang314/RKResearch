module

import RKCert.ReviewedNative.ERKOrderEightFourOffPhysicalPlacement

open RKResearch
open RKResearch.Certified.Graded
open RKResearch.Certified.Graded.OneOff
open RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.Graded.FourOffPhysical
open Polynomial

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (hFour : (offKnots A).card = 4) :
    ∃ (P : K[X]) (i h : Fin 10), Placement A b P i h :=
  physical_placement_of_order8_four_off ha ho hFour

example {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {A : Matrix (Fin 10) (Fin 10) K} {b : Fin 10 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 8 A b)
    (hFour : (offKnots A).card = 4) :
    (∃ i : Fin 10, i<8 ∧ SameTag A i 8 ∧
      ∀ {u v : Fin 10}, u<v → SameTag A u v → u=i ∧ v=8) ∧
    g A 6=0 ∧ g A 7=0 ∧ g A 9=0 ∧
    ∃ h : Fin 10, (h=4 ∨ h=5) ∧ g A h=0 ∧ nodes A h≠0 ∧
      ∀ l : Fin 10, l<h → g A l=0 → l=0 := by
  obtain ⟨P,i,h,D⟩ := physical_placement_of_order8_four_off ha ho hFour
  exact ⟨⟨i,D.repeatAtEight.before,D.repeatAtEight.same,D.repeatAtEight.unique⟩,
    D.cleanSix,D.cleanSeven,D.cleanNine,h,D.firstAtFourOrFive,D.firstClean,D.firstClockNe,
    D.noEarlierNonzeroClean⟩

#print axioms RKResearch.Certified.Graded.FourOffPhysical.rankData_of_order8_four_off
#print axioms RKResearch.Certified.Graded.FourOffPhysical.repeatAtEight_of_rankData
#print axioms RKResearch.Certified.Graded.FourOffPhysical.row6_clean
#print axioms RKResearch.Certified.Graded.FourOffPhysical.physical_placement_of_order8_four_off
