module

public import RKCert.ERKFinitePackets

@[expose] public section

/-! # Explicit rational midpoint mesh and ghost packets
Each exported decoder uses only exact small rational linear combinations.
The root-polynomial coefficients agree with the published ratio-gate inputs.
-/
namespace RKCert.Paired.FiniteMidpoint
open RKCert.Paired RKCert.Endpoint Polynomial
variable {K:Type*} [Field K]
set_option maxHeartbeats 8000000
-- These exact generated row reductions deliberately use a uniform tactic script.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false

noncomputable def dx3 : K[X] := from11 ![0, -20, 180, -420, 280, 0, 0, 0, 0, 0, 0]
theorem dx3_coeff (i:ℕ) (h:i<11) :
    (dx3:K[X]).coeff i=(![0, -20, 180, -420, 280, 0, 0, 0, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx3_degree [CharZero K] : (dx3:K[X]).natDegree=4 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx3_coeff i h]
      interval_cases i <;> rfl
    · unfold dx3
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx3_coeff 4 (by decide)]
    norm_num

noncomputable def dx4 : K[X] := from11 ![0, 30, -420, 1680, -2520, 1260, 0, 0, 0, 0, 0]
theorem dx4_coeff (i:ℕ) (h:i<11) :
    (dx4:K[X]).coeff i=(![0, 30, -420, 1680, -2520, 1260, 0, 0, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx4_degree [CharZero K] : (dx4:K[X]).natDegree=5 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx4_coeff i h]
      interval_cases i <;> rfl
    · unfold dx4
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx4_coeff 5 (by decide)]
    norm_num

noncomputable def odd5 : K[X] := from11 ![0, -6, 105, -560, 1260, -1260, 462, 0, 0, 0, 0]
theorem odd5_coeff (i:ℕ) (h:i<11) :
    (odd5:K[X]).coeff i=(![0, -6, 105, -560, 1260, -1260, 462, 0, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem odd5_degree [CharZero K] : (odd5:K[X]).natDegree=6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [odd5_coeff i h]
      interval_cases i <;> rfl
    · unfold odd5
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [odd5_coeff 6 (by decide)]
    norm_num

noncomputable def odd6 : K[X] := from11 ![0, 7, -168, 1260, -4200, 6930, -5544, 1716, 0, 0, 0]
theorem odd6_coeff (i:ℕ) (h:i<11) :
    (odd6:K[X]).coeff i=(![0, 7, -168, 1260, -4200, 6930, -5544, 1716, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem odd6_degree [CharZero K] : (odd6:K[X]).natDegree=7 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [odd6_coeff i h]
      interval_cases i <;> rfl
    · unfold odd6
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [odd6_coeff 7 (by decide)]
    norm_num

variable [CharZero K]

theorem mesh13Full_decode (P:K[X]) (hdegree:P.natDegree≤7)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 6,scalarMoment P k.val=0) :
    ∃ t:K, P=t • odd6 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have m0 := h 0
  rw [scalarMoment_11 P d10] at m0
  change moment a 1 0=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10] at m1
  change moment a 1 1=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10] at m2
  change moment a 1 2=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10] at m3
  change moment a 1 3=0 at m3
  have m4 := h 4
  rw [scalarMoment_11 P d10] at m4
  change moment a 1 4=0 at m4
  have m5 := h 5
  rw [scalarMoment_11 P d10] at m5
  change moment a 1 5=0 at m5
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 n8 n9 n10
  let a7 := a 7
  let t:K := (1 / 1716) * a7
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(7 / 1716) * a7 := by linear_combination (-42) * h0 + 882 * m0 + (-11760) * m1 + 52920 * m2 + (-105840) * m3 + 97020 * m4 + (-33264) * m5 + (2 / 143) * n8 + (21 / 715) * n9 + (7 / 143) * n10
  have e2 : a 2=(-14 / 143) * a7 := by linear_combination 420 * h0 + (-11760) * m0 + 176400 * m1 + (-846720) * m2 + 1764000 * m3 + (-1663200) * m4 + 582120 * m5 + (-140 / 429) * n8 + (-96 / 143) * n9 + (-315 / 286) * n10
  have e3 : a 3=(105 / 143) * a7 := by linear_combination (-1680) * h0 + 52920 * m0 + (-846720) * m1 + 4233600 * m2 + (-9072000) * m3 + 8731800 * m4 + (-3104640) * m5 + (336 / 143) * n8 + (672 / 143) * n9 + (1080 / 143) * n10
  have e4 : a 4=(-350 / 143) * a7 := by linear_combination 3150 * h0 + (-105840) * m0 + 1764000 * m1 + (-9072000) * m2 + 19845000 * m3 + (-19404000) * m4 + 6985440 * m5 + (-1050 / 143) * n8 + (-2016 / 143) * n9 + (-3150 / 143) * n10
  have e5 : a 5=(105 / 26) * a7 := by linear_combination (-2772) * h0 + 97020 * m0 + (-1663200) * m1 + 8731800 * m2 + (-19404000) * m3 + 19209960 * m4 + (-6985440) * m5 + (140 / 13) * n8 + (252 / 13) * n9 + (378 / 13) * n10
  have e6 : a 6=(-42 / 13) * a7 := by linear_combination 924 * h0 + (-33264) * m0 + 582120 * m1 + (-3104640) * m2 + 6985440 * m3 + (-6985440) * m4 + 2561328 * m5 + (-84 / 13) * n8 + (-672 / 65) * n9 + (-189 / 13) * n10
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 7, -168, 1260, -4200, 6930, -5544, 1716, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a7]
      try dsimp [a7] at e0
      linear_combination e0
    · change a 1=t * (7:K)
      dsimp [t, a7]
      try dsimp [a7] at e1
      linear_combination e1
    · change a 2=t * (-168:K)
      dsimp [t, a7]
      try dsimp [a7] at e2
      linear_combination e2
    · change a 3=t * (1260:K)
      dsimp [t, a7]
      try dsimp [a7] at e3
      linear_combination e3
    · change a 4=t * (-4200:K)
      dsimp [t, a7]
      try dsimp [a7] at e4
      linear_combination e4
    · change a 5=t * (6930:K)
      dsimp [t, a7]
      try dsimp [a7] at e5
      linear_combination e5
    · change a 6=t * (-5544:K)
      dsimp [t, a7]
      try dsimp [a7] at e6
      linear_combination e6
    · change a 7=t * (1716:K)
      dsimp [t, a7]
      ring
    · change a 8=t * (0:K)
      dsimp [t, a7]
      try dsimp [a7] at e8
      linear_combination e8
    · change a 9=t * (0:K)
      dsimp [t, a7]
      try dsimp [a7] at e9
      linear_combination e9
    · change a 10=t * (0:K)
      dsimp [t, a7]
      try dsimp [a7] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • odd6 := by
      rw [hvec]
      unfold odd6 from11
      simp only [map_smul]

theorem mesh13Prefix_decode (P:K[X]) (hdegree:P.natDegree≤7)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 5,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx5+u • dx6 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have m0 := h 0
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m0
  change moment a 1 0-moment a 1 1=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m1
  change moment a 1 1-moment a 1 2=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m2
  change moment a 1 2-moment a 1 3=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m3
  change moment a 1 3-moment a 1 4=0 at m3
  have m4 := h 4
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m4
  change moment a 1 4-moment a 1 5=0 at m4
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 n8 n9 n10
  let a6 := a 6
  let a7 := a 7
  let t:K := (1 / 5544) * a6 + (1 / 1848) * a7
  let u:K := (1 / 24024) * a7
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 132) * a6 + (-35 / 1716) * a7 := by linear_combination (-35) * h0 + 630 * m0 + (-6720) * m1 + 22680 * m2 + (-30240) * m3 + 13860 * m4 + (-5 / 143) * n8 + (-7 / 143) * n9 + (-35 / 572) * n10
  have e2 : a 2=(5 / 33) * a6 + (56 / 143) * a7 := by linear_combination 280 * h0 + (-6720) * m0 + 81480 * m1 + (-294840) * m2 + 410760 * m3 + (-194040) * m4 + (280 / 429) * n8 + (128 / 143) * n9 + (315 / 286) * n10
  have e3 : a 3=(-10 / 11) * a6 + (-315 / 143) * a7 := by linear_combination (-840) * h0 + 22680 * m0 + (-294840) * m1 + 1116360 * m2 + (-1605240) * m3 + 776160 * m4 + (-504 / 143) * n8 + (-672 / 143) * n9 + (-810 / 143) * n10
  have e4 : a 4=(25 / 11) * a6 + (700 / 143) * a7 := by linear_combination 1050 * h0 + (-30240) * m0 + 410760 * m1 + (-1605240) * m2 + 2363760 * m3 + (-1164240) * m4 + (1050 / 143) * n8 + (1344 / 143) * n9 + (1575 / 143) * n10
  have e5 : a 5=(-5 / 2) * a6 + (-105 / 26) * a7 := by linear_combination (-462) * h0 + 13860 * m0 + (-194040) * m1 + 776160 * m2 + (-1164240) * m3 + 582120 * m4 + (-70 / 13) * n8 + (-84 / 13) * n9 + (-189 / 26) * n10
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -42, 840, -5040, 12600, -13860, 5544, 0, 0, 0, 0]+u • ![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e0
      linear_combination e0
    · change a 1=t * (-42:K) + u * (56:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e1
      linear_combination e1
    · change a 2=t * (840:K) + u * (-1512:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e2
      linear_combination e2
    · change a 3=t * (-5040:K) + u * (12600:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e3
      linear_combination e3
    · change a 4=t * (12600:K) + u * (-46200:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e4
      linear_combination e4
    · change a 5=t * (-13860:K) + u * (83160:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e5
      linear_combination e5
    · change a 6=t * (5544:K) + u * (-72072:K)
      dsimp [t, u, a6, a7]
      ring
    · change a 7=t * (0:K) + u * (24024:K)
      dsimp [t, u, a6, a7]
      ring
    · change a 8=t * (0:K) + u * (0:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e8
      linear_combination e8
    · change a 9=t * (0:K) + u * (0:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e9
      linear_combination e9
    · change a 10=t * (0:K) + u * (0:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e10
      linear_combination e10
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx5+u • dx6 := by
      rw [hvec]
      unfold dx5 dx6 from11
      simp only [map_add,map_smul]

theorem ghost13Full_decode (P:K[X]) (hdegree:P.natDegree≤6)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 5,scalarMoment P k.val=0) :
    ∃ t:K, P=t • odd5 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have m0 := h 0
  rw [scalarMoment_11 P d10] at m0
  change moment a 1 0=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10] at m1
  change moment a 1 1=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10] at m2
  change moment a 1 2=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10] at m3
  change moment a 1 3=0 at m3
  have m4 := h 4
  rw [scalarMoment_11 P d10] at m4
  change moment a 1 4=0 at m4
  have n7 : a 7=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 n7 n8 n9 n10
  let a6 := a 6
  let t:K := (1 / 462) * a6
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 77) * a6 := by linear_combination (-30) * h0 + 450 * m0 + (-4200) * m1 + 12600 * m2 + (-15120) * m3 + 6300 * m4 + (-5 / 132) * n7 + (-10 / 143) * n8 + (-15 / 143) * n9 + (-20 / 143) * n10
  have e2 : a 2=(5 / 22) * a6 := by linear_combination 210 * h0 + (-4200) * m0 + 44100 * m1 + (-141120) * m2 + 176400 * m3 + (-75600) * m4 + (7 / 11) * n7 + (490 / 429) * n8 + (240 / 143) * n9 + (315 / 143) * n10
  have e3 : a 3=(-40 / 33) * a6 := by linear_combination (-560) * h0 + 12600 * m0 + (-141120) * m1 + 470400 * m2 + (-604800) * m3 + 264600 * m4 + (-35 / 11) * n7 + (-784 / 143) * n8 + (-1120 / 143) * n9 + (-1440 / 143) * n10
  have e4 : a 4=(30 / 11) * a6 := by linear_combination 630 * h0 + (-15120) * m0 + 176400 * m1 + (-604800) * m2 + 793800 * m3 + (-352800) * m4 + (70 / 11) * n7 + (1470 / 143) * n8 + (2016 / 143) * n9 + (2520 / 143) * n10
  have e5 : a 5=(-30 / 11) * a6 := by linear_combination (-252) * h0 + 6300 * m0 + (-75600) * m1 + 264600 * m2 + (-352800) * m3 + 158760 * m4 + (-105 / 22) * n7 + (-980 / 143) * n8 + (-1260 / 143) * n9 + (-1512 / 143) * n10
  have e7 : a 7=0 := by linear_combination 1 * n7
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -6, 105, -560, 1260, -1260, 462, 0, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a6]
      try dsimp [a6] at e0
      linear_combination e0
    · change a 1=t * (-6:K)
      dsimp [t, a6]
      try dsimp [a6] at e1
      linear_combination e1
    · change a 2=t * (105:K)
      dsimp [t, a6]
      try dsimp [a6] at e2
      linear_combination e2
    · change a 3=t * (-560:K)
      dsimp [t, a6]
      try dsimp [a6] at e3
      linear_combination e3
    · change a 4=t * (1260:K)
      dsimp [t, a6]
      try dsimp [a6] at e4
      linear_combination e4
    · change a 5=t * (-1260:K)
      dsimp [t, a6]
      try dsimp [a6] at e5
      linear_combination e5
    · change a 6=t * (462:K)
      dsimp [t, a6]
      ring
    · change a 7=t * (0:K)
      dsimp [t, a6]
      try dsimp [a6] at e7
      linear_combination e7
    · change a 8=t * (0:K)
      dsimp [t, a6]
      try dsimp [a6] at e8
      linear_combination e8
    · change a 9=t * (0:K)
      dsimp [t, a6]
      try dsimp [a6] at e9
      linear_combination e9
    · change a 10=t * (0:K)
      dsimp [t, a6]
      try dsimp [a6] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • odd5 := by
      rw [hvec]
      unfold odd5 from11
      simp only [map_smul]

theorem ghost13Prefix_decode (P:K[X]) (hdegree:P.natDegree≤6)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 4,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx4+u • dx5 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have m0 := h 0
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m0
  change moment a 1 0-moment a 1 1=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m1
  change moment a 1 1-moment a 1 2=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m2
  change moment a 1 2-moment a 1 3=0 at m2
  have m3 := h 3
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m3
  change moment a 1 3-moment a 1 4=0 at m3
  have n7 : a 7=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 n7 n8 n9 n10
  let a5 := a 5
  let a6 := a 6
  let t:K := (1 / 1260) * a5 + (1 / 504) * a6
  let u:K := (1 / 5544) * a6
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 42) * a5 + (4 / 77) * a6 := by linear_combination (-24) * h0 + 300 * m0 + (-2100) * m1 + 4200 * m2 + (-2520) * m3 + (5 / 66) * n7 + (40 / 429) * n8 + (15 / 143) * n9 + (16 / 143) * n10
  have e2 : a 2=(-1 / 3) * a5 + (-15 / 22) * a6 := by linear_combination 126 * h0 + (-2100) * m0 + 16800 * m1 + (-36120) * m2 + 22680 * m3 + (-21 / 22) * n7 + (-490 / 429) * n8 + (-180 / 143) * n9 + (-189 / 143) * n10
  have e3 : a 3=(4 / 3) * a5 + (80 / 33) * a6 := by linear_combination (-224) * h0 + 4200 * m0 + (-36120) * m1 + 81480 * m2 + (-52920) * m3 + (35 / 11) * n7 + (1568 / 429) * n8 + (560 / 143) * n9 + (576 / 143) * n10
  have e4 : a 4=(-2) * a5 + (-30 / 11) * a6 := by linear_combination 126 * h0 + (-2520) * m0 + 22680 * m1 + (-52920) * m2 + 35280 * m3 + (-35 / 11) * n7 + (-490 / 143) * n8 + (-504 / 143) * n9 + (-504 / 143) * n10
  have e7 : a 7=0 := by linear_combination 1 * n7
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 30, -420, 1680, -2520, 1260, 0, 0, 0, 0, 0]+u • ![0, -42, 840, -5040, 12600, -13860, 5544, 0, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e0
      linear_combination e0
    · change a 1=t * (30:K) + u * (-42:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e1
      linear_combination e1
    · change a 2=t * (-420:K) + u * (840:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e2
      linear_combination e2
    · change a 3=t * (1680:K) + u * (-5040:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e3
      linear_combination e3
    · change a 4=t * (-2520:K) + u * (12600:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e4
      linear_combination e4
    · change a 5=t * (1260:K) + u * (-13860:K)
      dsimp [t, u, a5, a6]
      ring
    · change a 6=t * (0:K) + u * (5544:K)
      dsimp [t, u, a5, a6]
      ring
    · change a 7=t * (0:K) + u * (0:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e7
      linear_combination e7
    · change a 8=t * (0:K) + u * (0:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e8
      linear_combination e8
    · change a 9=t * (0:K) + u * (0:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e9
      linear_combination e9
    · change a 10=t * (0:K) + u * (0:K)
      dsimp [t, u, a5, a6]
      try dsimp [a5, a6] at e10
      linear_combination e10
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx4+u • dx5 := by
      rw [hvec]
      unfold dx4 dx5 from11
      simp only [map_add,map_smul]

theorem ghost13Alias_decode (P:K[X]) (hdegree:P.natDegree≤5)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 3,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx3+u • dx4 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have m0 := h 0
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m0
  change moment a 1 0-moment a 1 1=0 at m0
  have m1 := h 1
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m1
  change moment a 1 1-moment a 1 2=0 at m1
  have m2 := h 2
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m2
  change moment a 1 2-moment a 1 3=0 at m2
  have n6 : a 6=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n7 : a 7=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 n6 n7 n8 n9 n10
  let a4 := a 4
  let a5 := a 5
  let t:K := (1 / 280) * a4 + (1 / 140) * a5
  let u:K := (1 / 1260) * a5
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 14) * a4 + (-5 / 42) * a5 := by linear_combination (-15) * h0 + 120 * m0 + (-480) * m1 + 420 * m2 + (-1 / 7) * n6 + (-5 / 33) * n7 + (-5 / 33) * n8 + (-21 / 143) * n9 + (-20 / 143) * n10
  have e2 : a 2=(9 / 14) * a4 + (20 / 21) * a5 := by linear_combination 45 * h0 + (-480) * m0 + 2220 * m1 + (-2100) * m2 + (15 / 14) * n6 + (12 / 11) * n7 + (35 / 33) * n8 + (144 / 143) * n9 + (135 / 143) * n10
  have e3 : a 3=(-3 / 2) * a4 + (-5 / 3) * a5 := by linear_combination (-35) * h0 + 420 * m0 + (-2100) * m1 + 2100 * m2 + (-5 / 3) * n6 + (-35 / 22) * n7 + (-49 / 33) * n8 + (-196 / 143) * n9 + (-180 / 143) * n10
  have e6 : a 6=0 := by linear_combination 1 * n6
  have e7 : a 7=0 := by linear_combination 1 * n7
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -20, 180, -420, 280, 0, 0, 0, 0, 0, 0]+u • ![0, 30, -420, 1680, -2520, 1260, 0, 0, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e0
      linear_combination e0
    · change a 1=t * (-20:K) + u * (30:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e1
      linear_combination e1
    · change a 2=t * (180:K) + u * (-420:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e2
      linear_combination e2
    · change a 3=t * (-420:K) + u * (1680:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e3
      linear_combination e3
    · change a 4=t * (280:K) + u * (-2520:K)
      dsimp [t, u, a4, a5]
      ring
    · change a 5=t * (0:K) + u * (1260:K)
      dsimp [t, u, a4, a5]
      ring
    · change a 6=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e6
      linear_combination e6
    · change a 7=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e7
      linear_combination e7
    · change a 8=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e8
      linear_combination e8
    · change a 9=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e9
      linear_combination e9
    · change a 10=t * (0:K) + u * (0:K)
      dsimp [t, u, a4, a5]
      try dsimp [a4, a5] at e10
      linear_combination e10
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx3+u • dx4 := by
      rw [hvec]
      unfold dx3 dx4 from11
      simp only [map_add,map_smul]

end RKCert.Paired.FiniteMidpoint
