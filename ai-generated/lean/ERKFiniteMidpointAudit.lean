import RKCert.ERKFiniteStaircase

open RKCert RKCert.Paired RKCert.Paired.FiniteMidpoint

#check saturated
#check midpoint_noninvariant
#check head_chart
#check margin
#check even_terminal_column
#check even_last_zero
#check ReverseHull.reverse_primitive_annih_six
#check ReverseHull.three_failed_of_five_moments
#check finite_reverse_gain
#check band_staircase

#print axioms saturated
#print axioms midpoint_noninvariant
#print axioms head_chart
#print axioms margin
#print axioms even_terminal_column
#print axioms even_last_zero
#print axioms ReverseHull.reverse_primitive_annih_six
#print axioms ReverseHull.three_failed_of_five_moments
#print axioms finite_reverse_gain
#print axioms band_staircase

example {A : Fin 23 → Fin 23 → ℚ} {b : Fin 23 → ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 16) :
    Module.finrank ℚ (zeroSpace A 8) = 8 :=
  (saturated (q := 8) (ε := 0) ha ho (by decide) (by decide) (by decide)).fRank 8 (by decide) (by decide)

example {A : Fin 25 → Fin 25 → ℚ} {b : Fin 25 → ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 17) :
    Module.finrank ℚ (treeSpace A 8) = 17 :=
  (saturated (q := 8) (ε := 1) ha ho (by decide) (by decide) (by decide)).eMid

example {A : Fin 26 → Fin 26 → ℚ} {b : Fin 26 → ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 18) :
    b (Fin.last 25) ≠ 0 :=
  (saturated (q := 9) (ε := 0) ha ho (by decide) (by decide) (by decide)).lastLive

example {A : Fin 28 → Fin 28 → ℚ} {b : Fin 28 → ℚ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b 19) :
    Module.finrank ℚ (treeSpace A 8) = 17 :=
  (saturated (q := 9) (ε := 1) ha ho (by decide) (by decide) (by decide)).ePrev

