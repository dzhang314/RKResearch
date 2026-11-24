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

noncomputable def even4 : K[X] := from11 ![0, 30, -450, 2100, -4200, 3780, -1260, 0, 0, 0, 0]
theorem even4_coeff (i:ℕ) (h:i<11) :
    (even4:K[X]).coeff i=(![0, 30, -450, 2100, -4200, 3780, -1260, 0, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem even4_degree [CharZero K] : (even4:K[X]).natDegree=6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [even4_coeff i h]
      interval_cases i <;> rfl
    · unfold even4
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [even4_coeff 6 (by decide)]
    norm_num

noncomputable def even5 : K[X] := from11 ![0, -42, 882, -5880, 17640, -26460, 19404, -5544, 0, 0, 0]
theorem even5_coeff (i:ℕ) (h:i<11) :
    (even5:K[X]).coeff i=(![0, -42, 882, -5880, 17640, -26460, 19404, -5544, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem even5_degree [CharZero K] : (even5:K[X]).natDegree=7 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [even5_coeff i h]
      interval_cases i <;> rfl
    · unfold even5
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [even5_coeff 7 (by decide)]
    norm_num

variable [CharZero K]

theorem meshEven7_decode (P:K[X]) (hdegree:P.natDegree≤8)
    (hzero:P.coeff 0=0) (hone:P.eval 1=0)
    (h:∀ k:Fin 6,scalarMoment P k.val=0) :
    ∃ t:K, P=t • even6 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have h1 : (∑ i,a i)=0 := (eval_one_11 P d10).symm.trans hone
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
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at h1 m0 m1 m2 m3 m4 m5 n9 n10
  let a8 := a 8
  let t:K := (-1 / 24024) * a8
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 429) * a8 := by linear_combination (-49) * h0 + 7 * h1 + 1176 * m0 + (-17640) * m1 + 88200 * m2 + (-194040) * m3 + 194040 * m4 + (-72072) * m5 + (-7 / 715) * n9 + (-7 / 286) * n10
  have e2 : a 2=(28 / 429) * a8 := by linear_combination 588 * h0 + (-168) * h1 + (-18816) * m0 + 317520 * m1 + (-1693440) * m2 + 3880800 * m3 + (-3991680) * m4 + 1513512 * m5 + (192 / 715) * n9 + (189 / 286) * n10
  have e3 : a 3=(-84 / 143) * a8 := by linear_combination (-2940) * h0 + 1260 * h1 + 105840 * m0 + (-1905120) * m1 + 10584000 * m2 + (-24948000) * m3 + 26195400 * m4 + (-10090080) * m5 + (-336 / 143) * n9 + (-810 / 143) * n10
  have e4 : a 4=(350 / 143) * a8 := by linear_combination 7350 * h0 + (-4200) * h1 + (-282240) * m0 + 5292000 * m1 + (-30240000) * m2 + 72765000 * m3 + (-77616000) * m4 + 30270240 * m5 + (1344 / 143) * n9 + (3150 / 143) * n10
  have e5 : a 5=(-70 / 13) * a8 := by linear_combination (-9702) * h0 + 6930 * h1 + 388080 * m0 + (-7484400) * m1 + 43659000 * m2 + (-106722000) * m3 + 115259760 * m4 + (-45405360) * m5 + (-252 / 13) * n9 + (-567 / 13) * n10
  have e6 : a 6=(84 / 13) * a8 := by linear_combination 6468 * h0 + (-5544) * h1 + (-266112) * m0 + 5239080 * m1 + (-31046400) * m2 + 76839840 * m3 + (-83825280) * m4 + 33297264 * m5 + (1344 / 65) * n9 + (567 / 13) * n10
  have e7 : a 7=(-4) * a8 := by linear_combination (-1716) * h0 + 1716 * h1 + 72072 * m0 + (-1441440) * m1 + 8648640 * m2 + (-21621600) * m3 + 23783760 * m4 + (-9513504) * m5 + (-48 / 5) * n9 + (-18) * n10
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 56, -1568, 14112, -58800, 129360, -155232, 96096, -24024, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a8]
      try dsimp [a8] at e0
      linear_combination e0
    · change a 1=t * (56:K)
      dsimp [t, a8]
      try dsimp [a8] at e1
      linear_combination e1
    · change a 2=t * (-1568:K)
      dsimp [t, a8]
      try dsimp [a8] at e2
      linear_combination e2
    · change a 3=t * (14112:K)
      dsimp [t, a8]
      try dsimp [a8] at e3
      linear_combination e3
    · change a 4=t * (-58800:K)
      dsimp [t, a8]
      try dsimp [a8] at e4
      linear_combination e4
    · change a 5=t * (129360:K)
      dsimp [t, a8]
      try dsimp [a8] at e5
      linear_combination e5
    · change a 6=t * (-155232:K)
      dsimp [t, a8]
      try dsimp [a8] at e6
      linear_combination e6
    · change a 7=t * (96096:K)
      dsimp [t, a8]
      try dsimp [a8] at e7
      linear_combination e7
    · change a 8=t * (-24024:K)
      dsimp [t, a8]
      ring
    · change a 9=t * (0:K)
      dsimp [t, a8]
      try dsimp [a8] at e9
      linear_combination e9
    · change a 10=t * (0:K)
      dsimp [t, a8]
      try dsimp [a8] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • even6 := by
      rw [hvec]
      unfold even6 from11
      simp only [map_smul]

theorem ghostEven7_decode (P:K[X]) (hdegree:P.natDegree≤7)
    (hzero:P.coeff 0=0) (hone:P.eval 1=0)
    (h:∀ k:Fin 4,scalarMoment P k.val=0) :
    ∃ t u:K, P=t • even4+u • even5 := by
  let a : Fin 11→K := fun i=>P.coeff i.val
  have d10 : P.natDegree≤10 := hdegree.trans (by decide)
  have h0 : a 0=0 := hzero
  have h1 : (∑ i,a i)=0 := (eval_one_11 P d10).symm.trans hone
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
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at h1 m0 m1 m2 m3 n8 n9 n10
  let a6 := a 6
  let a7 := a 7
  let t:K := (-1 / 1260) * a6 + (-1 / 360) * a7
  let u:K := (-1 / 5544) * a7
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 42) * a6 + (-5 / 66) * a7 := by linear_combination (-25) * h0 + 5 * h1 + 300 * m0 + (-2100) * m1 + 4200 * m2 + (-2520) * m3 + (-5 / 33) * n8 + (-35 / 143) * n9 + (-50 / 143) * n10
  have e2 : a 2=(5 / 14) * a6 + (12 / 11) * a7 := by linear_combination 150 * h0 + (-60) * h1 + (-2400) * m0 + 18900 * m1 + (-40320) * m2 + 25200 * m3 + (70 / 33) * n8 + (480 / 143) * n9 + (675 / 143) * n10
  have e3 : a 3=(-5 / 3) * a6 + (-105 / 22) * a7 := by linear_combination (-350) * h0 + 210 * h1 + 6300 * m0 + (-52920) * m1 + 117600 * m2 + (-75600) * m3 + (-98 / 11) * n8 + (-1960 / 143) * n9 + (-2700 / 143) * n10
  have e4 : a 4=(10 / 3) * a6 + (280 / 33) * a7 := by linear_combination 350 * h0 + (-280) * h1 + (-6720) * m0 + 58800 * m1 + (-134400) * m2 + 88200 * m3 + (490 / 33) * n8 + (3136 / 143) * n9 + (4200 / 143) * n10
  have e5 : a 5=(-3) * a6 + (-63 / 11) * a7 := by linear_combination (-126) * h0 + 126 * h1 + 2520 * m0 + (-22680) * m1 + 52920 * m2 + (-35280) * m3 + (-98 / 11) * n8 + (-1764 / 143) * n9 + (-2268 / 143) * n10
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 30, -450, 2100, -4200, 3780, -1260, 0, 0, 0, 0]+u • ![0, -42, 882, -5880, 17640, -26460, 19404, -5544, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e0
      linear_combination e0
    · change a 1=t * (30:K) + u * (-42:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e1
      linear_combination e1
    · change a 2=t * (-450:K) + u * (882:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e2
      linear_combination e2
    · change a 3=t * (2100:K) + u * (-5880:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e3
      linear_combination e3
    · change a 4=t * (-4200:K) + u * (17640:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e4
      linear_combination e4
    · change a 5=t * (3780:K) + u * (-26460:K)
      dsimp [t, u, a6, a7]
      try dsimp [a6, a7] at e5
      linear_combination e5
    · change a 6=t * (-1260:K) + u * (19404:K)
      dsimp [t, u, a6, a7]
      ring
    · change a 7=t * (0:K) + u * (-5544:K)
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
    _ = t • even4+u • even5 := by
      rw [hvec]
      unfold even4 even5 from11
      simp only [map_add,map_smul]

theorem terminalEven7_decode (P:K[X]) (hdegree:P.natDegree≤7)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 6,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t:K, P=t • dx6 := by
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
  have m5 := h 5
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m5
  change moment a 1 5-moment a 1 6=0 at m5
  have n8 : a 8=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 n8 n9 n10
  let a7 := a 7
  let t:K := (1 / 24024) * a7
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 429) * a7 := by linear_combination (-48) * h0 + 1176 * m0 + (-17640) * m1 + 88200 * m2 + (-194040) * m3 + 194040 * m4 + (-72072) * m5 + (16 / 2145) * n8 + (21 / 1430) * n9 + (56 / 2431) * n10
  have e2 : a 2=(-9 / 143) * a7 := by linear_combination 540 * h0 + (-17640) * m0 + 299880 * m1 + (-1605240) * m2 + 3686760 * m3 + (-3797640) * m4 + 1441440 * m5 + (-28 / 143) * n8 + (-54 / 143) * n9 + (-2835 / 4862) * n10
  have e3 : a 3=(75 / 143) * a7 := by linear_combination (-2400) * h0 + 88200 * m0 + (-1605240) * m1 + 8978760 * m2 + (-21261240) * m3 + 22397760 * m4 + (-8648640) * m5 + (224 / 143) * n8 + (420 / 143) * n9 + (10800 / 2431) * n10
  have e4 : a 4=(-25 / 13) * a7 := by linear_combination 4950 * h0 + (-194040) * m0 + 3686760 * m1 + (-21261240) * m2 + 51503760 * m3 + (-55218240) * m4 + 21621600 * m5 + (-70 / 13) * n8 + (-126 / 13) * n9 + (-3150 / 221) * n10
  have e5 : a 5=(45 / 13) * a7 := by linear_combination (-4752) * h0 + 194040 * m0 + (-3797640) * m1 + 22397760 * m2 + (-55218240) * m3 + 60041520 * m4 + (-23783760) * m5 + (112 / 13) * n8 + (189 / 13) * n9 + (4536 / 221) * n10
  have e6 : a 6=(-3) * a7 := by linear_combination 1716 * h0 + (-72072) * m0 + 1441440 * m1 + (-8648640) * m2 + 21621600 * m3 + (-23783760) * m4 + 9513504 * m5 + (-28 / 5) * n8 + (-42 / 5) * n9 + (-189 / 17) * n10
  have e8 : a 8=0 := by linear_combination 1 * n8
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a7]
      try dsimp [a7] at e0
      linear_combination e0
    · change a 1=t * (56:K)
      dsimp [t, a7]
      try dsimp [a7] at e1
      linear_combination e1
    · change a 2=t * (-1512:K)
      dsimp [t, a7]
      try dsimp [a7] at e2
      linear_combination e2
    · change a 3=t * (12600:K)
      dsimp [t, a7]
      try dsimp [a7] at e3
      linear_combination e3
    · change a 4=t * (-46200:K)
      dsimp [t, a7]
      try dsimp [a7] at e4
      linear_combination e4
    · change a 5=t * (83160:K)
      dsimp [t, a7]
      try dsimp [a7] at e5
      linear_combination e5
    · change a 6=t * (-72072:K)
      dsimp [t, a7]
      try dsimp [a7] at e6
      linear_combination e6
    · change a 7=t * (24024:K)
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
    _ = t • dx6 := by
      rw [hvec]
      unfold dx6 from11
      simp only [map_smul]

end RKCert.Paired.FiniteMidpoint
