module

public import RKCert.ERKPhysicalContrasts
public import RKCert.FixedKnotCases
public import RKCert.FreeQuasiGate
public import Mathlib.Data.Fin.VecNotation

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

noncomputable def from11 (a:Fin 11→K) : K[X] := by classical exact ofFn 11 a
theorem from11_coeff (a:Fin 11→K) {i:ℕ} (h:i<11) :
    (from11 a).coeff i=a ⟨i,h⟩ := by classical exact ofFn_coeff_eq_val_of_lt a h
theorem from11_coeff_hi (a:Fin 11→K) {i:ℕ} (h : 11 ≤ i) :
    (from11 a).coeff i=0 := by classical exact ofFn_coeff_eq_zero_of_ge a h

theorem from11_exact (P:K[X]) (h:P.natDegree≤10) :
    from11 (fun i=>P.coeff i.val)=P := by
  classical
  exact ofFn_comp_toFn_eq_id_of_natDegree_lt (by omega)

noncomputable def scalarMoment [CharZero K] (P:K[X]) (k:ℕ) := (Paired.primitive (X^k*P)).eval 1

theorem scalarMoment_11 [CharZero K] (P:K[X]) (h:P.natDegree≤10) (k:ℕ) :
    scalarMoment P k=moment (fun i:Fin 11=>P.coeff i.val) 1 k := by
  classical
  have e:=primitive_monomial_moment (fun i:Fin 11=>P.coeff i.val) (1:K) k
  change (Paired.primitive (X^k*from11 (fun i=>P.coeff i.val))).eval 1=_
    at e
  rw [from11_exact P h] at e
  exact e

theorem eval_one_11 (P:K[X]) (h:P.natDegree≤10) :
    P.eval 1=∑ i:Fin 11,P.coeff i.val := by
  classical
  conv_lhs => rw [←from11_exact P h,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  simp

noncomputable def dx5 : K[X] := from11 ![0, -42, 840, -5040, 12600, -13860, 5544, 0, 0, 0, 0]
theorem dx5_coeff (i:ℕ) (h:i<11) :
    (dx5:K[X]).coeff i=(![0, -42, 840, -5040, 12600, -13860, 5544, 0, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx5_degree [CharZero K] : (dx5:K[X]).natDegree=6 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx5_coeff i h]
      interval_cases i <;> rfl
    · unfold dx5
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx5_coeff 6 (by decide)]
    norm_num

noncomputable def dx6 : K[X] := from11 ![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0]
theorem dx6_coeff (i:ℕ) (h:i<11) :
    (dx6:K[X]).coeff i=(![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx6_degree [CharZero K] : (dx6:K[X]).natDegree=7 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx6_coeff i h]
      interval_cases i <;> rfl
    · unfold dx6
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx6_coeff 7 (by decide)]
    norm_num

noncomputable def dx7 : K[X] := from11 ![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0]
theorem dx7_coeff (i:ℕ) (h:i<11) :
    (dx7:K[X]).coeff i=(![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx7_degree [CharZero K] : (dx7:K[X]).natDegree=8 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx7_coeff i h]
      interval_cases i <;> rfl
    · unfold dx7
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx7_coeff 8 (by decide)]
    norm_num

noncomputable def dx8 : K[X] := from11 ![0, 90, -3960, 55440, -360360, 1261260, -2522520, 2882880, -1750320, 437580, 0]
theorem dx8_coeff (i:ℕ) (h:i<11) :
    (dx8:K[X]).coeff i=(![0, 90, -3960, 55440, -360360, 1261260, -2522520, 2882880, -1750320, 437580, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx8_degree [CharZero K] : (dx8:K[X]).natDegree=9 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx8_coeff i h]
      interval_cases i <;> rfl
    · unfold dx8
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx8_coeff 9 (by decide)]
    norm_num

noncomputable def dx9 : K[X] := from11 ![0, -110, 5940, -102960, 840840, -3783780, 10090080, -16336320, 15752880, -8314020, 1847560]
theorem dx9_coeff (i:ℕ) (h:i<11) :
    (dx9:K[X]).coeff i=(![0, -110, 5940, -102960, 840840, -3783780, 10090080, -16336320, 15752880, -8314020, 1847560] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem dx9_degree [CharZero K] : (dx9:K[X]).natDegree=10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [dx9_coeff i h]
      interval_cases i <;> rfl
    · unfold dx9
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [dx9_coeff 10 (by decide)]
    norm_num

noncomputable def even6 : K[X] := from11 ![0, 56, -1568, 14112, -58800, 129360, -155232, 96096, -24024, 0, 0]
theorem even6_coeff (i:ℕ) (h:i<11) :
    (even6:K[X]).coeff i=(![0, 56, -1568, 14112, -58800, 129360, -155232, 96096, -24024, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem even6_degree [CharZero K] : (even6:K[X]).natDegree=8 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [even6_coeff i h]
      interval_cases i <;> rfl
    · unfold even6
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [even6_coeff 8 (by decide)]
    norm_num

noncomputable def even7 : K[X] := from11 ![0, -72, 2592, -30240, 166320, -498960, 864864, -864864, 463320, -102960, 0]
theorem even7_coeff (i:ℕ) (h:i<11) :
    (even7:K[X]).coeff i=(![0, -72, 2592, -30240, 166320, -498960, 864864, -864864, 463320, -102960, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem even7_degree [CharZero K] : (even7:K[X]).natDegree=9 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [even7_coeff i h]
      interval_cases i <;> rfl
    · unfold even7
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [even7_coeff 9 (by decide)]
    norm_num

noncomputable def even8 : K[X] := from11 ![0, 90, -4050, 59400, -415800, 1621620, -3783780, 5405400, -4633200, 2187900, -437580]
theorem even8_coeff (i:ℕ) (h:i<11) :
    (even8:K[X]).coeff i=(![0, 90, -4050, 59400, -415800, 1621620, -3783780, 5405400, -4633200, 2187900, -437580] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem even8_degree [CharZero K] : (even8:K[X]).natDegree=10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [even8_coeff i h]
      interval_cases i <;> rfl
    · unfold even8
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [even8_coeff 10 (by decide)]
    norm_num

noncomputable def odd7 : K[X] := from11 ![0, -8, 252, -2520, 11550, -27720, 36036, -24024, 6435, 0, 0]
theorem odd7_coeff (i:ℕ) (h:i<11) :
    (odd7:K[X]).coeff i=(![0, -8, 252, -2520, 11550, -27720, 36036, -24024, 6435, 0, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem odd7_degree [CharZero K] : (odd7:K[X]).natDegree=8 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [odd7_coeff i h]
      interval_cases i <;> rfl
    · unfold odd7
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [odd7_coeff 8 (by decide)]
    norm_num

noncomputable def odd8 : K[X] := from11 ![0, 9, -360, 4620, -27720, 90090, -168168, 180180, -102960, 24310, 0]
theorem odd8_coeff (i:ℕ) (h:i<11) :
    (odd8:K[X]).coeff i=(![0, 9, -360, 4620, -27720, 90090, -168168, 180180, -102960, 24310, 0] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem odd8_degree [CharZero K] : (odd8:K[X]).natDegree=9 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [odd8_coeff i h]
      interval_cases i <;> rfl
    · unfold odd8
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [odd8_coeff 9 (by decide)]
    norm_num

noncomputable def odd9 : K[X] := from11 ![0, -10, 495, -7920, 60060, -252252, 630630, -960960, 875160, -437580, 92378]
theorem odd9_coeff (i:ℕ) (h:i<11) :
    (odd9:K[X]).coeff i=(![0, -10, 495, -7920, 60060, -252252, 630630, -960960, 875160, -437580, 92378] : Fin 11→K) ⟨i,h⟩ := from11_coeff _ h
theorem odd9_degree [CharZero K] : (odd9:K[X]).natDegree=10 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro i hi
    by_cases h:i<11
    · rw [odd9_coeff i h]
      interval_cases i <;> rfl
    · unfold odd9
      exact from11_coeff_hi _ (show 11 ≤ i by omega)
  · rw [odd9_coeff 10 (by decide)]
    norm_num

theorem dx7_eval (x:K) : (dx7:K[X]).eval x=x*jacDerivative7 x := by
  classical
  rw [dx7,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative7,jacDerivative8,lobatto9,rightWeight8]
  ring

theorem dx8_eval (x:K) : (dx8:K[X]).eval x=x*jacDerivative8 x := by
  classical
  rw [dx8,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative7,jacDerivative8,lobatto9,rightWeight8]
  ring

theorem even7_eval (x:K) : (even7:K[X]).eval x=(-72:K)*x*lobatto9 x := by
  classical
  rw [even7,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative7,jacDerivative8,lobatto9,rightWeight8]
  ring

theorem odd8_eval (x:K) : (odd8:K[X]).eval x=x*rightWeight8 x := by
  classical
  rw [odd8,from11,ofFn_eq_sum_monomial,eval_finsetSum]
  norm_num [Fin.sum_univ_succ,jacDerivative7,jacDerivative8,lobatto9,rightWeight8]
  ring

variable [CharZero K]

theorem meshEven8_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) (hone:P.eval 1=0)
    (h:∀ k:Fin 7,scalarMoment P k.val=0) :
    ∃ t:K, P=t • even7 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at h1 m0 m1 m2 m3 m4 m5 m6 n10
  let a9 := a 9
  let t:K := (-1 / 102960) * a9
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 1430) * a9 := by linear_combination (-64) * h0 + (-8) * h1 + 2016 * m0 + (-40320) * m1 + 277200 * m2 + (-887040) * m3 + 1441440 * m4 + (-1153152) * m5 + 360360 * m6 + (8 / 2431) * n10
  have e2 : a 2=(-18 / 715) * a9 := by linear_combination 1008 * h0 + 252 * h1 + (-42336) * m0 + 952560 * m1 + (-6985440) * m2 + 23284800 * m3 + (-38918880) * m4 + 31783752 * m5 + (-10090080) * m6 + (-567 / 4862) * n10
  have e3 : a 3=(42 / 143) * a9 := by linear_combination (-6720) * h0 + (-2520) * h1 + 317520 * m0 + (-7620480) * m1 + 58212000 * m2 + (-199584000) * m3 + 340540200 * m4 + (-282522240) * m5 + 90810720 * m6 + (3240 / 2431) * n10
  have e4 : a 4=(-21 / 13) * a9 := by linear_combination 23100 * h0 + 11550 * h1 + (-1164240) * m0 + 29106000 * m1 + (-228690000) * m2 + 800415000 * m3 + (-1387386000) * m4 + 1165404240 * m5 + (-378378000) * m6 + (-1575 / 221) * n10
  have e5 : a 5=(63 / 13) * a9 := by linear_combination (-44352) * h0 + (-27720) * h1 + 2328480 * m0 + (-59875200) * m1 + 480249000 * m2 + (-1707552000) * m3 + 2996753760 * m4 + (-2542700160) * m5 + 832431600 * m6 + (4536 / 221) * n10
  have e6 : a 6=(-42 / 5) * a9 := by linear_combination 48048 * h0 + 36036 * h1 + (-2594592) * m0 + 68108040 * m1 + (-554954400) * m2 + 1997835840 * m3 + (-3541618080) * m4 + 3030051024 * m5 + (-998917920) * m6 + (-567 / 17) * n10
  have e7 : a 7=(42 / 5) * a9 := by linear_combination (-27456) * h0 + (-24024) * h1 + 1513512 * m0 + (-40360320) * m1 + 332972640 * m2 + (-1210809600) * m3 + 2164322160 * m4 + (-1864646784) * m5 + 618377760 * m6 + (504 / 17) * n10
  have e8 : a 8=(-9 / 2) * a9 := by linear_combination 6435 * h0 + 6435 * h1 + (-360360) * m0 + 9729720 * m1 + (-81081000) * m2 + 297297000 * m3 + (-535134600) * m4 + 463783320 * m5 + (-154594440) * m6 + (-405 / 34) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -72, 2592, -30240, 166320, -498960, 864864, -864864, 463320, -102960, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e0
      linear_combination e0
    · change a 1=t * (-72:K)
      dsimp [t, a9]
      try dsimp [a9] at e1
      linear_combination e1
    · change a 2=t * (2592:K)
      dsimp [t, a9]
      try dsimp [a9] at e2
      linear_combination e2
    · change a 3=t * (-30240:K)
      dsimp [t, a9]
      try dsimp [a9] at e3
      linear_combination e3
    · change a 4=t * (166320:K)
      dsimp [t, a9]
      try dsimp [a9] at e4
      linear_combination e4
    · change a 5=t * (-498960:K)
      dsimp [t, a9]
      try dsimp [a9] at e5
      linear_combination e5
    · change a 6=t * (864864:K)
      dsimp [t, a9]
      try dsimp [a9] at e6
      linear_combination e6
    · change a 7=t * (-864864:K)
      dsimp [t, a9]
      try dsimp [a9] at e7
      linear_combination e7
    · change a 8=t * (463320:K)
      dsimp [t, a9]
      try dsimp [a9] at e8
      linear_combination e8
    · change a 9=t * (-102960:K)
      dsimp [t, a9]
      ring
    · change a 10=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • even7 := by
      rw [hvec]
      unfold even7 from11
      simp only [map_smul]

theorem meshEven9_decode (P:K[X]) (hdegree:P.natDegree≤10)
    (hzero:P.coeff 0=0) (hone:P.eval 1=0)
    (h:∀ k:Fin 8,scalarMoment P k.val=0) :
    ∃ t:K, P=t • even8 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10] at m7
  change moment a 1 7=0 at m7
  norm_num [moment, Fin.sum_univ_succ] at h1 m0 m1 m2 m3 m4 m5 m6 m7
  let a10 := a 10
  let t:K := (-1 / 437580) * a10
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 4862) * a10 := by linear_combination (-81) * h0 + 9 * h1 + 3240 * m0 + (-83160) * m1 + 748440 * m2 + (-3243240) * m3 + 7567560 * m4 + (-9729720) * m5 + 6486480 * m6 + (-1750320) * m7
  have e2 : a 2=(45 / 4862) * a10 := by linear_combination 1620 * h0 + (-360) * h1 + (-86400) * m0 + 2494800 * m1 + (-23950080) * m2 + 108108000 * m3 + (-259459200) * m4 + 340540200 * m5 + (-230630400) * m6 + 63011520 * m7
  have e3 : a 3=(-30 / 221) * a10 := by linear_combination (-13860) * h0 + 4620 * h1 + 831600 * m0 + (-25613280) * m1 + 256132800 * m2 + (-1189188000) * m3 + 2913510600 * m4 + (-3884680800) * m5 + 2663781120 * m6 + (-735134400) * m7
  have e4 : a 4=(210 / 221) * a10 := by linear_combination 62370 * h0 + (-27720) * h1 + (-3991680) * m0 + 128066400 * m1 + (-1317254400) * m2 + 6243237000 * m3 + (-15538723200) * m4 + 20977276320 * m5 + (-14529715200) * m6 + 4043239200 * m7
  have e5 : a 5=(-63 / 17) * a10 := by linear_combination (-162162) * h0 + 90090 * h1 + 10810800 * m0 + (-356756400) * m1 + 3745942200 * m2 + (-18036018000) * m3 + 45450765360 * m4 + (-61978316400) * m5 + 43286443200 * m6 + (-12129717600) * m7
  have e6 : a 6=(147 / 17) * a10 := by linear_combination 252252 * h0 + (-168168) * h1 + (-17297280) * m0 + 582702120 * m1 + (-6215489280) * m2 + 30300510240 * m3 + (-77128571520) * m4 + 106051785840 * m5 + (-74585871360) * m6 + 21024843840 * m7
  have e7 : a 7=(-210 / 17) * a10 := by linear_combination (-231660) * h0 + 180180 * h1 + 16216200 * m0 + (-554954400) * m1 + 5993507520 * m2 + (-29513484000) * m3 + 75751275600 * m4 + (-104886381600) * m5 + 74205331200 * m6 + (-21024843840) * m7
  have e8 : a 8=(180 / 17) * a10 := by linear_combination 115830 * h0 + (-102960) * h1 + (-8236800) * m0 + 285405120 * m1 + (-3113510400) * m2 + 15459444000 * m3 + (-39956716800) * m4 + 55653998400 * m5 + (-39576176640) * m6 + 11263309200 * m7
  have e9 : a 9=(-5) * a10 := by linear_combination (-24310) * h0 + 24310 * h1 + 1750320 * m0 + (-61261200) * m1 + 673873200 * m2 + (-3369366000) * m3 + 8760351600 * m4 + (-12264492240) * m5 + 8760351600 * m6 + (-2502957600) * m7
  have hvec : a=t • ![0, 90, -4050, 59400, -415800, 1621620, -3783780, 5405400, -4633200, 2187900, -437580] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a10]
      try dsimp [a10] at e0
      linear_combination e0
    · change a 1=t * (90:K)
      dsimp [t, a10]
      try dsimp [a10] at e1
      linear_combination e1
    · change a 2=t * (-4050:K)
      dsimp [t, a10]
      try dsimp [a10] at e2
      linear_combination e2
    · change a 3=t * (59400:K)
      dsimp [t, a10]
      try dsimp [a10] at e3
      linear_combination e3
    · change a 4=t * (-415800:K)
      dsimp [t, a10]
      try dsimp [a10] at e4
      linear_combination e4
    · change a 5=t * (1621620:K)
      dsimp [t, a10]
      try dsimp [a10] at e5
      linear_combination e5
    · change a 6=t * (-3783780:K)
      dsimp [t, a10]
      try dsimp [a10] at e6
      linear_combination e6
    · change a 7=t * (5405400:K)
      dsimp [t, a10]
      try dsimp [a10] at e7
      linear_combination e7
    · change a 8=t * (-4633200:K)
      dsimp [t, a10]
      try dsimp [a10] at e8
      linear_combination e8
    · change a 9=t * (2187900:K)
      dsimp [t, a10]
      try dsimp [a10] at e9
      linear_combination e9
    · change a 10=t * (-437580:K)
      dsimp [t, a10]
      ring
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • even8 := by
      rw [hvec]
      unfold even8 from11
      simp only [map_smul]

theorem meshFull8_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 8,scalarMoment P k.val=0) :
    ∃ t:K, P=t • odd8 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10] at m7
  change moment a 1 7=0 at m7
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 m7 n10
  let a9 := a 9
  let t:K := (1 / 24310) * a9
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(9 / 24310) * a9 := by linear_combination (-72) * h0 + 2592 * m0 + (-60480) * m1 + 498960 * m2 + (-1995840) * m3 + 4324320 * m4 + (-5189184) * m5 + 3243240 * m6 + (-823680) * m7 + (4 / 2431) * n10
  have e2 : a 2=(-36 / 2431) * a9 := by linear_combination 1260 * h0 + (-60480) * m0 + 1587600 * m1 + (-13970880) * m2 + 58212000 * m3 + (-129729600) * m4 + 158918760 * m5 + (-100900800) * m6 + 25945920 * m7 + (-315 / 4862) * n10
  have e3 : a 3=(42 / 221) * a9 := by linear_combination (-9240) * h0 + 498960 * m0 + (-13970880) * m1 + 128066400 * m2 + (-548856000) * m3 + 1248647400 * m4 + (-1553872320) * m5 + 998917920 * m6 + (-259459200) * m7 + (180 / 221) * n10
  have e4 : a 4=(-252 / 221) * a9 := by linear_combination 34650 * h0 + (-1995840) * m0 + 58212000 * m1 + (-548856000) * m2 + 2401245000 * m3 + (-5549544000) * m4 + 6992425440 * m5 + (-4540536000) * m6 + 1189188000 * m7 + (-1050 / 221) * n10
  have e5 : a 5=(63 / 17) * a9 := by linear_combination (-72072) * h0 + 4324320 * m0 + (-129729600) * m1 + 1248647400 * m2 + (-5549544000) * m3 + 12985932960 * m4 + (-16527551040) * m5 + 10821610800 * m6 + (-2854051200) * m7 + (252 / 17) * n10
  have e6 : a 6=(-588 / 85) * a9 := by linear_combination 84084 * h0 + (-5189184) * m0 + 158918760 * m1 + (-1553872320) * m2 + 6992425440 * m3 + (-16527551040) * m4 + 21210357168 * m5 + (-13984850880) * m6 + 3710266560 * m7 + (-441 / 17) * n10
  have e7 : a 7=(126 / 17) * a9 := by linear_combination (-51480) * h0 + 3243240 * m0 + (-100900800) * m1 + 998917920 * m2 + (-4540536000) * m3 + 10821610800 * m4 + (-13984850880) * m5 + 9275666400 * m6 + (-2473511040) * m7 + (420 / 17) * n10
  have e8 : a 8=(-72 / 17) * a9 := by linear_combination 12870 * h0 + (-823680) * m0 + 25945920 * m1 + (-259459200) * m2 + 1189188000 * m3 + (-2854051200) * m4 + 3710266560 * m5 + (-2473511040) * m6 + 662547600 * m7 + (-180 / 17) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 9, -360, 4620, -27720, 90090, -168168, 180180, -102960, 24310, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e0
      linear_combination e0
    · change a 1=t * (9:K)
      dsimp [t, a9]
      try dsimp [a9] at e1
      linear_combination e1
    · change a 2=t * (-360:K)
      dsimp [t, a9]
      try dsimp [a9] at e2
      linear_combination e2
    · change a 3=t * (4620:K)
      dsimp [t, a9]
      try dsimp [a9] at e3
      linear_combination e3
    · change a 4=t * (-27720:K)
      dsimp [t, a9]
      try dsimp [a9] at e4
      linear_combination e4
    · change a 5=t * (90090:K)
      dsimp [t, a9]
      try dsimp [a9] at e5
      linear_combination e5
    · change a 6=t * (-168168:K)
      dsimp [t, a9]
      try dsimp [a9] at e6
      linear_combination e6
    · change a 7=t * (180180:K)
      dsimp [t, a9]
      try dsimp [a9] at e7
      linear_combination e7
    · change a 8=t * (-102960:K)
      dsimp [t, a9]
      try dsimp [a9] at e8
      linear_combination e8
    · change a 9=t * (24310:K)
      dsimp [t, a9]
      ring
    · change a 10=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • odd8 := by
      rw [hvec]
      unfold odd8 from11
      simp only [map_smul]

theorem meshFull9_decode (P:K[X]) (hdegree:P.natDegree≤10)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 9,scalarMoment P k.val=0) :
    ∃ t:K, P=t • odd9 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10] at m7
  change moment a 1 7=0 at m7
  have m8 := h 8
  rw [scalarMoment_11 P d10] at m8
  change moment a 1 8=0 at m8
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 m7 m8
  let a10 := a 10
  let t:K := (1 / 92378) * a10
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-5 / 46189) * a10 := by linear_combination (-90) * h0 + 4050 * m0 + (-118800) * m1 + 1247400 * m2 + (-6486480) * m3 + 18918900 * m4 + (-32432400) * m5 + 32432400 * m6 + (-17503200) * m7 + 3938220 * m8
  have e2 : a 2=(45 / 8398) * a10 := by linear_combination 1980 * h0 + (-118800) * m0 + 3920400 * m1 + (-43908480) * m2 + 237837600 * m3 + (-713512800) * m4 + 1248647400 * m5 + (-1268467200) * m6 + 693126720 * m7 + (-157528800) * m8
  have e3 : a 3=(-360 / 4199) * a10 := by linear_combination (-18480) * h0 + 1247400 * m0 + (-43908480) * m1 + 512265600 * m2 + (-2854051200) * m3 + 8740531800 * m4 + (-15538723200) * m5 + 15982686720 * m6 + (-8821612800) * m7 + 2021619600 * m8
  have e4 : a 4=(210 / 323) * a10 := by linear_combination 90090 * h0 + (-6486480) * m0 + 237837600 * m1 + (-2854051200) * m2 + 16232416200 * m3 + (-50500850400) * m4 + 90901530720 * m5 + (-94443148800) * m6 + 52562109600 * m7 + (-12129717600) * m8
  have e5 : a 5=(-882 / 323) * a10 := by linear_combination (-252252) * h0 + 18918900 * m0 + (-713512800) * m1 + 8740531800 * m2 + (-50500850400) * m3 + 159077678760 * m4 + (-289232143200) * m5 + 303005102400 * m6 + (-169816046400) * m7 + 39421582200 * m8
  have e6 : a 6=(2205 / 323) * a10 := by linear_combination 420420 * h0 + (-32432400) * m0 + 1248647400 * m1 + (-15538723200) * m2 + 90901530720 * m3 + (-289232143200) * m4 + 530258929200 * m5 + (-559394035200) * m6 + 315372657600 * m7 + (-73586953440) * m8
  have e7 : a 7=(-3360 / 323) * a10 := by linear_combination (-411840) * h0 + 32432400 * m0 + (-1268467200) * m1 + 15982686720 * m2 + (-94443148800) * m3 + 303005102400 * m4 + (-559394035200) * m5 + 593642649600 * m6 + (-336397501440) * m7 + 78843164400 * m8
  have e8 : a 8=(180 / 19) * a10 := by linear_combination 218790 * h0 + (-17503200) * m0 + 693126720 * m1 + (-8821612800) * m2 + 52562109600 * m3 + (-169816046400) * m4 + 315372657600 * m5 + (-336397501440) * m6 + 191476256400 * m7 + (-45053236800) * m8
  have e9 : a 9=(-90 / 19) * a10 := by linear_combination (-48620) * h0 + 3938220 * m0 + (-157528800) * m1 + 2021619600 * m2 + (-12129717600) * m3 + 39421582200 * m4 + (-73586953440) * m5 + 78843164400 * m6 + (-45053236800) * m7 + 10637569800 * m8
  have hvec : a=t • ![0, -10, 495, -7920, 60060, -252252, 630630, -960960, 875160, -437580, 92378] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a10]
      try dsimp [a10] at e0
      linear_combination e0
    · change a 1=t * (-10:K)
      dsimp [t, a10]
      try dsimp [a10] at e1
      linear_combination e1
    · change a 2=t * (495:K)
      dsimp [t, a10]
      try dsimp [a10] at e2
      linear_combination e2
    · change a 3=t * (-7920:K)
      dsimp [t, a10]
      try dsimp [a10] at e3
      linear_combination e3
    · change a 4=t * (60060:K)
      dsimp [t, a10]
      try dsimp [a10] at e4
      linear_combination e4
    · change a 5=t * (-252252:K)
      dsimp [t, a10]
      try dsimp [a10] at e5
      linear_combination e5
    · change a 6=t * (630630:K)
      dsimp [t, a10]
      try dsimp [a10] at e6
      linear_combination e6
    · change a 7=t * (-960960:K)
      dsimp [t, a10]
      try dsimp [a10] at e7
      linear_combination e7
    · change a 8=t * (875160:K)
      dsimp [t, a10]
      try dsimp [a10] at e8
      linear_combination e8
    · change a 9=t * (-437580:K)
      dsimp [t, a10]
      try dsimp [a10] at e9
      linear_combination e9
    · change a 10=t * (92378:K)
      dsimp [t, a10]
      ring
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • odd9 := by
      rw [hvec]
      unfold odd9 from11
      simp only [map_smul]

theorem meshPrefix8_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 7,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx7+u • dx8 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m6
  change moment a 1 6-moment a 1 7=0 at m6
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 n10
  let a8 := a 8
  let a9 := a 9
  let t:K := (1 / 102960) * a8 + (1 / 25740) * a9
  let u:K := (1 / 437580) * a9
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 1430) * a8 + (-63 / 24310) * a9 := by linear_combination (-63) * h0 + 2016 * m0 + (-40320) * m1 + 277200 * m2 + (-887040) * m3 + 1441440 * m4 + (-1153152) * m5 + 360360 * m6 + (-14 / 2431) * n10
  have e2 : a 2=(7 / 286) * a8 + (216 / 2431) * a9 := by linear_combination 945 * h0 + (-40320) * m0 + 912240 * m1 + (-6708240) * m2 + 22397760 * m3 + (-37477440) * m4 + 30630600 * m5 + (-9729720) * m6 + (945 / 4862) * n10
  have e3 : a 3=(-7 / 26) * a8 + (-210 / 221) * a9 := by linear_combination (-5775) * h0 + 277200 * m0 + (-6708240) * m1 + 51503760 * m2 + (-177186240) * m3 + 303062760 * m4 + (-251891640) * m5 + 81081000 * m6 + (-450 / 221) * n10
  have e4 : a 4=(35 / 26) * a8 + (1008 / 221) * a9 := by linear_combination 17325 * h0 + (-887040) * m0 + 22397760 * m1 + (-177186240) * m2 + 623228760 * m3 + (-1084323240) * m4 + 913512600 * m5 + (-297297000) * m6 + (2100 / 221) * n10
  have e5 : a 5=(-7 / 2) * a8 + (-189 / 17) * a9 := by linear_combination (-27027) * h0 + 1441440 * m0 + (-37477440) * m1 + 303062760 * m2 + (-1084323240) * m3 + 1912430520 * m4 + (-1629187560) * m5 + 535134600 * m6 + (-378 / 17) * n10
  have e6 : a 6=(49 / 10) * a8 + (1176 / 85) * a9 := by linear_combination 21021 * h0 + (-1153152) * m0 + 30630600 * m1 + (-251891640) * m2 + 913512600 * m3 + (-1629187560) * m4 + 1400863464 * m5 + (-463783320) * m6 + (441 / 17) * n10
  have e7 : a 7=(-7 / 2) * a8 + (-126 / 17) * a9 := by linear_combination (-6435) * h0 + 360360 * m0 + (-9729720) * m1 + 81081000 * m2 + (-297297000) * m3 + 535134600 * m4 + (-463783320) * m5 + 154594440 * m6 + (-210 / 17) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0]+u • ![0, 90, -3960, 55440, -360360, 1261260, -2522520, 2882880, -1750320, 437580, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e0
      linear_combination e0
    · change a 1=t * (-72:K) + u * (90:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e1
      linear_combination e1
    · change a 2=t * (2520:K) + u * (-3960:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e2
      linear_combination e2
    · change a 3=t * (-27720:K) + u * (55440:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e3
      linear_combination e3
    · change a 4=t * (138600:K) + u * (-360360:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e4
      linear_combination e4
    · change a 5=t * (-360360:K) + u * (1261260:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e5
      linear_combination e5
    · change a 6=t * (504504:K) + u * (-2522520:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e6
      linear_combination e6
    · change a 7=t * (-360360:K) + u * (2882880:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e7
      linear_combination e7
    · change a 8=t * (102960:K) + u * (-1750320:K)
      dsimp [t, u, a8, a9]
      ring
    · change a 9=t * (0:K) + u * (437580:K)
      dsimp [t, u, a8, a9]
      ring
    · change a 10=t * (0:K) + u * (0:K)
      dsimp [t, u, a8, a9]
      try dsimp [a8, a9] at e10
      linear_combination e10
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx7+u • dx8 := by
      rw [hvec]
      unfold dx7 dx8 from11
      simp only [map_add,map_smul]

theorem meshPrefix9_decode (P:K[X]) (hdegree:P.natDegree≤10)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 8,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx8+u • dx9 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m6
  change moment a 1 6-moment a 1 7=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m7
  change moment a 1 7-moment a 1 8=0 at m7
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 m7
  let a9 := a 9
  let a10 := a 10
  let t:K := (1 / 437580) * a9 + (1 / 97240) * a10
  let u:K := (1 / 1847560) * a10
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 4862) * a9 + (40 / 46189) * a10 := by linear_combination (-80) * h0 + 3240 * m0 + (-83160) * m1 + 748440 * m2 + (-3243240) * m3 + 7567560 * m4 + (-9729720) * m5 + 6486480 * m6 + (-1750320) * m7
  have e2 : a 2=(-2 / 221) * a9 + (-315 / 8398) * a10 := by linear_combination 1540 * h0 + (-83160) * m0 + 2411640 * m1 + (-23201640) * m2 + 104864760 * m3 + (-251891640) * m4 + 330810480 * m5 + (-224143920) * m6 + 61261200 * m7
  have e3 : a 3=(28 / 221) * a9 + (2160 / 4199) * a10 := by linear_combination (-12320) * h0 + 748440 * m0 + (-23201640) * m1 + 232931160 * m2 + (-1084323240) * m3 + 2661618960 * m4 + (-3553870320) * m5 + 2439637200 * m6 + (-673873200) * m7
  have e4 : a 4=(-14 / 17) * a9 + (-1050 / 323) * a10 := by linear_combination 50050 * h0 + (-3243240) * m0 + 104864760 * m1 + (-1084323240) * m2 + 5158913760 * m3 + (-12877104240) * m4 + 17423406000 * m5 + (-12090078000) * m6 + 3369366000 * m7
  have e5 : a 5=(49 / 17) * a9 + (3528 / 323) * a10 := by linear_combination (-112112) * h0 + 7567560 * m0 + (-251891640) * m1 + 2661618960 * m2 + (-12877104240) * m3 + 32573661120 * m4 + (-44554910400) * m5 + 31196365200 * m6 + (-8760351600) * m7
  have e6 : a 6=(-98 / 17) * a9 + (-6615 / 323) * a10 := by linear_combination 140140 * h0 + (-9729720) * m0 + 330810480 * m1 + (-3553870320) * m2 + 17423406000 * m3 + (-44554910400) * m4 + 61496875440 * m5 + (-43389506160) * m6 + 12264492240 * m7
  have e7 : a 7=(112 / 17) * a9 + (6720 / 323) * a10 := by linear_combination (-91520) * h0 + 6486480 * m0 + (-224143920) * m1 + 2439637200 * m2 + (-12090078000) * m3 + 31196365200 * m4 + (-43389506160) * m5 + 30815825040 * m6 + (-8760351600) * m7
  have e8 : a 8=(-4) * a9 + (-180 / 19) * a10 := by linear_combination 24310 * h0 + (-1750320) * m0 + 61261200 * m1 + (-673873200) * m2 + 3369366000 * m3 + (-8760351600) * m4 + 12264492240 * m5 + (-8760351600) * m6 + 2502957600 * m7
  have hvec : a=t • ![0, 90, -3960, 55440, -360360, 1261260, -2522520, 2882880, -1750320, 437580, 0]+u • ![0, -110, 5940, -102960, 840840, -3783780, 10090080, -16336320, 15752880, -8314020, 1847560] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e0
      linear_combination e0
    · change a 1=t * (90:K) + u * (-110:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e1
      linear_combination e1
    · change a 2=t * (-3960:K) + u * (5940:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e2
      linear_combination e2
    · change a 3=t * (55440:K) + u * (-102960:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e3
      linear_combination e3
    · change a 4=t * (-360360:K) + u * (840840:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e4
      linear_combination e4
    · change a 5=t * (1261260:K) + u * (-3783780:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e5
      linear_combination e5
    · change a 6=t * (-2522520:K) + u * (10090080:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e6
      linear_combination e6
    · change a 7=t * (2882880:K) + u * (-16336320:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e7
      linear_combination e7
    · change a 8=t * (-1750320:K) + u * (15752880:K)
      dsimp [t, u, a9, a10]
      try dsimp [a9, a10] at e8
      linear_combination e8
    · change a 9=t * (437580:K) + u * (-8314020:K)
      dsimp [t, u, a9, a10]
      ring
    · change a 10=t * (0:K) + u * (1847560:K)
      dsimp [t, u, a9, a10]
      ring
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx8+u • dx9 := by
      rw [hvec]
      unfold dx8 dx9 from11
      simp only [map_add,map_smul]

theorem ghostEven8_decode (P:K[X]) (hdegree:P.natDegree≤8)
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

theorem ghostEven9_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) (hone:P.eval 1=0)
    (h:∀ k:Fin 8,scalarMoment P k.val=0) :
    P=0 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10] at m7
  change moment a 1 7=0 at m7
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at h1 m0 m1 m2 m3 m4 m5 m6 m7 n10
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=0 := by linear_combination (-81) * h0 + 9 * h1 + 3240 * m0 + (-83160) * m1 + 748440 * m2 + (-3243240) * m3 + 7567560 * m4 + (-9729720) * m5 + 6486480 * m6 + (-1750320) * m7 + (-1 / 4862) * n10
  have e2 : a 2=0 := by linear_combination 1620 * h0 + (-360) * h1 + (-86400) * m0 + 2494800 * m1 + (-23950080) * m2 + 108108000 * m3 + (-259459200) * m4 + 340540200 * m5 + (-230630400) * m6 + 63011520 * m7 + (45 / 4862) * n10
  have e3 : a 3=0 := by linear_combination (-13860) * h0 + 4620 * h1 + 831600 * m0 + (-25613280) * m1 + 256132800 * m2 + (-1189188000) * m3 + 2913510600 * m4 + (-3884680800) * m5 + 2663781120 * m6 + (-735134400) * m7 + (-30 / 221) * n10
  have e4 : a 4=0 := by linear_combination 62370 * h0 + (-27720) * h1 + (-3991680) * m0 + 128066400 * m1 + (-1317254400) * m2 + 6243237000 * m3 + (-15538723200) * m4 + 20977276320 * m5 + (-14529715200) * m6 + 4043239200 * m7 + (210 / 221) * n10
  have e5 : a 5=0 := by linear_combination (-162162) * h0 + 90090 * h1 + 10810800 * m0 + (-356756400) * m1 + 3745942200 * m2 + (-18036018000) * m3 + 45450765360 * m4 + (-61978316400) * m5 + 43286443200 * m6 + (-12129717600) * m7 + (-63 / 17) * n10
  have e6 : a 6=0 := by linear_combination 252252 * h0 + (-168168) * h1 + (-17297280) * m0 + 582702120 * m1 + (-6215489280) * m2 + 30300510240 * m3 + (-77128571520) * m4 + 106051785840 * m5 + (-74585871360) * m6 + 21024843840 * m7 + (147 / 17) * n10
  have e7 : a 7=0 := by linear_combination (-231660) * h0 + 180180 * h1 + 16216200 * m0 + (-554954400) * m1 + 5993507520 * m2 + (-29513484000) * m3 + 75751275600 * m4 + (-104886381600) * m5 + 74205331200 * m6 + (-21024843840) * m7 + (-210 / 17) * n10
  have e8 : a 8=0 := by linear_combination 115830 * h0 + (-102960) * h1 + (-8236800) * m0 + 285405120 * m1 + (-3113510400) * m2 + 15459444000 * m3 + (-39956716800) * m4 + 55653998400 * m5 + (-39576176640) * m6 + 11263309200 * m7 + (180 / 17) * n10
  have e9 : a 9=0 := by linear_combination (-24310) * h0 + 24310 * h1 + 1750320 * m0 + (-61261200) * m1 + 673873200 * m2 + (-3369366000) * m3 + 8760351600 * m4 + (-12264492240) * m5 + 8760351600 * m6 + (-2502957600) * m7 + (-5) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=0 := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
  have e : from11 a=P := from11_exact P d10
  classical
  rw [←e,hvec]
  unfold from11
  exact map_zero _

theorem ghostFull8_decode (P:K[X]) (hdegree:P.natDegree≤8)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 7,scalarMoment P k.val=0) :
    ∃ t:K, P=t • odd7 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 n9 n10
  let a8 := a 8
  let t:K := (1 / 6435) * a8
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-8 / 6435) * a8 := by linear_combination (-56) * h0 + 1568 * m0 + (-28224) * m1 + 176400 * m2 + (-517440) * m3 + 776160 * m4 + (-576576) * m5 + 168168 * m6 + (-7 / 1430) * n9 + (-28 / 2431) * n10
  have e2 : a 2=(28 / 715) * a8 := by linear_combination 756 * h0 + (-28224) * m0 + 571536 * m1 + (-3810240) * m2 + 11642400 * m3 + (-17962560) * m4 + 13621608 * m5 + (-4036032) * m6 + (108 / 715) * n9 + (1701 / 4862) * n10
  have e3 : a 3=(-56 / 143) * a8 := by linear_combination (-4200) * h0 + 176400 * m0 + (-3810240) * m1 + 26460000 * m2 + (-83160000) * m3 + 130977000 * m4 + (-100900800) * m5 + 30270240 * m6 + (-210 / 143) * n9 + (-8100 / 2431) * n10
  have e4 : a 4=(70 / 39) * a8 := by linear_combination 11550 * h0 + (-517440) * m0 + 11642400 * m1 + (-83160000) * m2 + 266805000 * m3 + (-426888000) * m4 + 332972640 * m5 + (-100900800) * m6 + (84 / 13) * n9 + (3150 / 221) * n10
  have e5 : a 5=(-56 / 13) * a8 := by linear_combination (-16632) * h0 + 776160 * m0 + (-17962560) * m1 + 130977000 * m2 + (-426888000) * m3 + 691558560 * m4 + (-544864320) * m5 + 166486320 * m6 + (-189 / 13) * n9 + (-6804 / 221) * n10
  have e6 : a 6=(28 / 5) * a8 := by linear_combination 12012 * h0 + (-576576) * m0 + 13621608 * m1 + (-100900800) * m2 + 332972640 * m3 + (-544864320) * m4 + 432864432 * m5 + (-133189056) * m6 + (84 / 5) * n9 + (567 / 17) * n10
  have e7 : a 7=(-56 / 15) * a8 := by linear_combination (-3432) * h0 + 168168 * m0 + (-4036032) * m1 + 30270240 * m2 + (-100900800) * m3 + 166486320 * m4 + (-133189056) * m5 + 41225184 * m6 + (-42 / 5) * n9 + (-252 / 17) * n10
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -8, 252, -2520, 11550, -27720, 36036, -24024, 6435, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a8]
      try dsimp [a8] at e0
      linear_combination e0
    · change a 1=t * (-8:K)
      dsimp [t, a8]
      try dsimp [a8] at e1
      linear_combination e1
    · change a 2=t * (252:K)
      dsimp [t, a8]
      try dsimp [a8] at e2
      linear_combination e2
    · change a 3=t * (-2520:K)
      dsimp [t, a8]
      try dsimp [a8] at e3
      linear_combination e3
    · change a 4=t * (11550:K)
      dsimp [t, a8]
      try dsimp [a8] at e4
      linear_combination e4
    · change a 5=t * (-27720:K)
      dsimp [t, a8]
      try dsimp [a8] at e5
      linear_combination e5
    · change a 6=t * (36036:K)
      dsimp [t, a8]
      try dsimp [a8] at e6
      linear_combination e6
    · change a 7=t * (-24024:K)
      dsimp [t, a8]
      try dsimp [a8] at e7
      linear_combination e7
    · change a 8=t * (6435:K)
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
    _ = t • odd7 := by
      rw [hvec]
      unfold odd7 from11
      simp only [map_smul]

theorem ghostFull9_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 9,scalarMoment P k.val=0) :
    P=0 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10] at m6
  change moment a 1 6=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10] at m7
  change moment a 1 7=0 at m7
  have m8 := h 8
  rw [scalarMoment_11 P d10] at m8
  change moment a 1 8=0 at m8
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 m7 m8 n10
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=0 := by linear_combination (-90) * h0 + 4050 * m0 + (-118800) * m1 + 1247400 * m2 + (-6486480) * m3 + 18918900 * m4 + (-32432400) * m5 + 32432400 * m6 + (-17503200) * m7 + 3938220 * m8 + (-5 / 46189) * n10
  have e2 : a 2=0 := by linear_combination 1980 * h0 + (-118800) * m0 + 3920400 * m1 + (-43908480) * m2 + 237837600 * m3 + (-713512800) * m4 + 1248647400 * m5 + (-1268467200) * m6 + 693126720 * m7 + (-157528800) * m8 + (45 / 8398) * n10
  have e3 : a 3=0 := by linear_combination (-18480) * h0 + 1247400 * m0 + (-43908480) * m1 + 512265600 * m2 + (-2854051200) * m3 + 8740531800 * m4 + (-15538723200) * m5 + 15982686720 * m6 + (-8821612800) * m7 + 2021619600 * m8 + (-360 / 4199) * n10
  have e4 : a 4=0 := by linear_combination 90090 * h0 + (-6486480) * m0 + 237837600 * m1 + (-2854051200) * m2 + 16232416200 * m3 + (-50500850400) * m4 + 90901530720 * m5 + (-94443148800) * m6 + 52562109600 * m7 + (-12129717600) * m8 + (210 / 323) * n10
  have e5 : a 5=0 := by linear_combination (-252252) * h0 + 18918900 * m0 + (-713512800) * m1 + 8740531800 * m2 + (-50500850400) * m3 + 159077678760 * m4 + (-289232143200) * m5 + 303005102400 * m6 + (-169816046400) * m7 + 39421582200 * m8 + (-882 / 323) * n10
  have e6 : a 6=0 := by linear_combination 420420 * h0 + (-32432400) * m0 + 1248647400 * m1 + (-15538723200) * m2 + 90901530720 * m3 + (-289232143200) * m4 + 530258929200 * m5 + (-559394035200) * m6 + 315372657600 * m7 + (-73586953440) * m8 + (2205 / 323) * n10
  have e7 : a 7=0 := by linear_combination (-411840) * h0 + 32432400 * m0 + (-1268467200) * m1 + 15982686720 * m2 + (-94443148800) * m3 + 303005102400 * m4 + (-559394035200) * m5 + 593642649600 * m6 + (-336397501440) * m7 + 78843164400 * m8 + (-3360 / 323) * n10
  have e8 : a 8=0 := by linear_combination 218790 * h0 + (-17503200) * m0 + 693126720 * m1 + (-8821612800) * m2 + 52562109600 * m3 + (-169816046400) * m4 + 315372657600 * m5 + (-336397501440) * m6 + 191476256400 * m7 + (-45053236800) * m8 + (180 / 19) * n10
  have e9 : a 9=0 := by linear_combination (-48620) * h0 + 3938220 * m0 + (-157528800) * m1 + 2021619600 * m2 + (-12129717600) * m3 + 39421582200 * m4 + (-73586953440) * m5 + 78843164400 * m6 + (-45053236800) * m7 + 10637569800 * m8 + (-90 / 19) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=0 := by
    funext i
    fin_cases i
    · exact e0
    · exact e1
    · exact e2
    · exact e3
    · exact e4
    · exact e5
    · exact e6
    · exact e7
    · exact e8
    · exact e9
    · exact e10
  have e : from11 a=P := from11_exact P d10
  classical
  rw [←e,hvec]
  unfold from11
  exact map_zero _

theorem ghostPrefix8_decode (P:K[X]) (hdegree:P.natDegree≤8)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 6,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t u:K, P=t • dx6+u • dx7 := by
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
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 n9 n10
  let a7 := a 7
  let a8 := a 8
  let t:K := (1 / 24024) * a7 + (1 / 6864) * a8
  let u:K := (1 / 102960) * a8
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 429) * a7 + (16 / 2145) * a8 := by linear_combination (-48) * h0 + 1176 * m0 + (-17640) * m1 + 88200 * m2 + (-194040) * m3 + 194040 * m4 + (-72072) * m5 + (21 / 1430) * n9 + (56 / 2431) * n10
  have e2 : a 2=(-9 / 143) * a7 + (-28 / 143) * a8 := by linear_combination 540 * h0 + (-17640) * m0 + 299880 * m1 + (-1605240) * m2 + 3686760 * m3 + (-3797640) * m4 + 1441440 * m5 + (-54 / 143) * n9 + (-2835 / 4862) * n10
  have e3 : a 3=(75 / 143) * a7 + (224 / 143) * a8 := by linear_combination (-2400) * h0 + 88200 * m0 + (-1605240) * m1 + 8978760 * m2 + (-21261240) * m3 + 22397760 * m4 + (-8648640) * m5 + (420 / 143) * n9 + (10800 / 2431) * n10
  have e4 : a 4=(-25 / 13) * a7 + (-70 / 13) * a8 := by linear_combination 4950 * h0 + (-194040) * m0 + 3686760 * m1 + (-21261240) * m2 + 51503760 * m3 + (-55218240) * m4 + 21621600 * m5 + (-126 / 13) * n9 + (-3150 / 221) * n10
  have e5 : a 5=(45 / 13) * a7 + (112 / 13) * a8 := by linear_combination (-4752) * h0 + 194040 * m0 + (-3797640) * m1 + 22397760 * m2 + (-55218240) * m3 + 60041520 * m4 + (-23783760) * m5 + (189 / 13) * n9 + (4536 / 221) * n10
  have e6 : a 6=(-3) * a7 + (-28 / 5) * a8 := by linear_combination 1716 * h0 + (-72072) * m0 + 1441440 * m1 + (-8648640) * m2 + 21621600 * m3 + (-23783760) * m4 + 9513504 * m5 + (-42 / 5) * n9 + (-189 / 17) * n10
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 56, -1512, 12600, -46200, 83160, -72072, 24024, 0, 0, 0]+u • ![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K) + u * (0:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e0
      linear_combination e0
    · change a 1=t * (56:K) + u * (-72:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e1
      linear_combination e1
    · change a 2=t * (-1512:K) + u * (2520:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e2
      linear_combination e2
    · change a 3=t * (12600:K) + u * (-27720:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e3
      linear_combination e3
    · change a 4=t * (-46200:K) + u * (138600:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e4
      linear_combination e4
    · change a 5=t * (83160:K) + u * (-360360:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e5
      linear_combination e5
    · change a 6=t * (-72072:K) + u * (504504:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e6
      linear_combination e6
    · change a 7=t * (24024:K) + u * (-360360:K)
      dsimp [t, u, a7, a8]
      ring
    · change a 8=t * (0:K) + u * (102960:K)
      dsimp [t, u, a7, a8]
      ring
    · change a 9=t * (0:K) + u * (0:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e9
      linear_combination e9
    · change a 10=t * (0:K) + u * (0:K)
      dsimp [t, u, a7, a8]
      try dsimp [a7, a8] at e10
      linear_combination e10
  refine ⟨t, u,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx6+u • dx7 := by
      rw [hvec]
      unfold dx6 dx7 from11
      simp only [map_add,map_smul]

theorem ghostPrefix9_decode (P:K[X]) (hdegree:P.natDegree≤9)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 8,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t:K, P=t • dx8 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m6
  change moment a 1 6-moment a 1 7=0 at m6
  have m7 := h 7
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m7
  change moment a 1 7-moment a 1 8=0 at m7
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 m7 n10
  let a9 := a 9
  let t:K := (1 / 437580) * a9
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(1 / 4862) * a9 := by linear_combination (-80) * h0 + 3240 * m0 + (-83160) * m1 + 748440 * m2 + (-3243240) * m3 + 7567560 * m4 + (-9729720) * m5 + 6486480 * m6 + (-1750320) * m7 + (40 / 46189) * n10
  have e2 : a 2=(-2 / 221) * a9 := by linear_combination 1540 * h0 + (-83160) * m0 + 2411640 * m1 + (-23201640) * m2 + 104864760 * m3 + (-251891640) * m4 + 330810480 * m5 + (-224143920) * m6 + 61261200 * m7 + (-315 / 8398) * n10
  have e3 : a 3=(28 / 221) * a9 := by linear_combination (-12320) * h0 + 748440 * m0 + (-23201640) * m1 + 232931160 * m2 + (-1084323240) * m3 + 2661618960 * m4 + (-3553870320) * m5 + 2439637200 * m6 + (-673873200) * m7 + (2160 / 4199) * n10
  have e4 : a 4=(-14 / 17) * a9 := by linear_combination 50050 * h0 + (-3243240) * m0 + 104864760 * m1 + (-1084323240) * m2 + 5158913760 * m3 + (-12877104240) * m4 + 17423406000 * m5 + (-12090078000) * m6 + 3369366000 * m7 + (-1050 / 323) * n10
  have e5 : a 5=(49 / 17) * a9 := by linear_combination (-112112) * h0 + 7567560 * m0 + (-251891640) * m1 + 2661618960 * m2 + (-12877104240) * m3 + 32573661120 * m4 + (-44554910400) * m5 + 31196365200 * m6 + (-8760351600) * m7 + (3528 / 323) * n10
  have e6 : a 6=(-98 / 17) * a9 := by linear_combination 140140 * h0 + (-9729720) * m0 + 330810480 * m1 + (-3553870320) * m2 + 17423406000 * m3 + (-44554910400) * m4 + 61496875440 * m5 + (-43389506160) * m6 + 12264492240 * m7 + (-6615 / 323) * n10
  have e7 : a 7=(112 / 17) * a9 := by linear_combination (-91520) * h0 + 6486480 * m0 + (-224143920) * m1 + 2439637200 * m2 + (-12090078000) * m3 + 31196365200 * m4 + (-43389506160) * m5 + 30815825040 * m6 + (-8760351600) * m7 + (6720 / 323) * n10
  have e8 : a 8=(-4) * a9 := by linear_combination 24310 * h0 + (-1750320) * m0 + 61261200 * m1 + (-673873200) * m2 + 3369366000 * m3 + (-8760351600) * m4 + 12264492240 * m5 + (-8760351600) * m6 + 2502957600 * m7 + (-180 / 19) * n10
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, 90, -3960, 55440, -360360, 1261260, -2522520, 2882880, -1750320, 437580, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e0
      linear_combination e0
    · change a 1=t * (90:K)
      dsimp [t, a9]
      try dsimp [a9] at e1
      linear_combination e1
    · change a 2=t * (-3960:K)
      dsimp [t, a9]
      try dsimp [a9] at e2
      linear_combination e2
    · change a 3=t * (55440:K)
      dsimp [t, a9]
      try dsimp [a9] at e3
      linear_combination e3
    · change a 4=t * (-360360:K)
      dsimp [t, a9]
      try dsimp [a9] at e4
      linear_combination e4
    · change a 5=t * (1261260:K)
      dsimp [t, a9]
      try dsimp [a9] at e5
      linear_combination e5
    · change a 6=t * (-2522520:K)
      dsimp [t, a9]
      try dsimp [a9] at e6
      linear_combination e6
    · change a 7=t * (2882880:K)
      dsimp [t, a9]
      try dsimp [a9] at e7
      linear_combination e7
    · change a 8=t * (-1750320:K)
      dsimp [t, a9]
      try dsimp [a9] at e8
      linear_combination e8
    · change a 9=t * (437580:K)
      dsimp [t, a9]
      ring
    · change a 10=t * (0:K)
      dsimp [t, a9]
      try dsimp [a9] at e10
      linear_combination e10
  refine ⟨t,?_⟩
  classical
  calc
    P = from11 a := (from11_exact P d10).symm
    _ = t • dx8 := by
      rw [hvec]
      unfold dx8 from11
      simp only [map_smul]

theorem ghostAlias8_decode (P:K[X]) (hdegree:P.natDegree≤7)
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

theorem ghostAlias9_decode (P:K[X]) (hdegree:P.natDegree≤8)
    (hzero:P.coeff 0=0) 
    (h:∀ k:Fin 7,scalarMoment P k.val-scalarMoment P (k.val+1)=0) :
    ∃ t:K, P=t • dx7 := by
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
  have m6 := h 6
  rw [scalarMoment_11 P d10,scalarMoment_11 P d10] at m6
  change moment a 1 6-moment a 1 7=0 at m6
  have n9 : a 9=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  have n10 : a 10=0 := coeff_eq_zero_of_natDegree_lt (by omega)
  norm_num [moment, Fin.sum_univ_succ] at m0 m1 m2 m3 m4 m5 m6 n9 n10
  let a8 := a 8
  let t:K := (1 / 102960) * a8
  have e0 : a 0=0 := by linear_combination 1 * h0
  have e1 : a 1=(-1 / 1430) * a8 := by linear_combination (-63) * h0 + 2016 * m0 + (-40320) * m1 + 277200 * m2 + (-887040) * m3 + 1441440 * m4 + (-1153152) * m5 + 360360 * m6 + (-63 / 24310) * n9 + (-14 / 2431) * n10
  have e2 : a 2=(7 / 286) * a8 := by linear_combination 945 * h0 + (-40320) * m0 + 912240 * m1 + (-6708240) * m2 + 22397760 * m3 + (-37477440) * m4 + 30630600 * m5 + (-9729720) * m6 + (216 / 2431) * n9 + (945 / 4862) * n10
  have e3 : a 3=(-7 / 26) * a8 := by linear_combination (-5775) * h0 + 277200 * m0 + (-6708240) * m1 + 51503760 * m2 + (-177186240) * m3 + 303062760 * m4 + (-251891640) * m5 + 81081000 * m6 + (-210 / 221) * n9 + (-450 / 221) * n10
  have e4 : a 4=(35 / 26) * a8 := by linear_combination 17325 * h0 + (-887040) * m0 + 22397760 * m1 + (-177186240) * m2 + 623228760 * m3 + (-1084323240) * m4 + 913512600 * m5 + (-297297000) * m6 + (1008 / 221) * n9 + (2100 / 221) * n10
  have e5 : a 5=(-7 / 2) * a8 := by linear_combination (-27027) * h0 + 1441440 * m0 + (-37477440) * m1 + 303062760 * m2 + (-1084323240) * m3 + 1912430520 * m4 + (-1629187560) * m5 + 535134600 * m6 + (-189 / 17) * n9 + (-378 / 17) * n10
  have e6 : a 6=(49 / 10) * a8 := by linear_combination 21021 * h0 + (-1153152) * m0 + 30630600 * m1 + (-251891640) * m2 + 913512600 * m3 + (-1629187560) * m4 + 1400863464 * m5 + (-463783320) * m6 + (1176 / 85) * n9 + (441 / 17) * n10
  have e7 : a 7=(-7 / 2) * a8 := by linear_combination (-6435) * h0 + 360360 * m0 + (-9729720) * m1 + 81081000 * m2 + (-297297000) * m3 + 535134600 * m4 + (-463783320) * m5 + 154594440 * m6 + (-126 / 17) * n9 + (-210 / 17) * n10
  have e9 : a 9=0 := by linear_combination 1 * n9
  have e10 : a 10=0 := by linear_combination 1 * n10
  have hvec : a=t • ![0, -72, 2520, -27720, 138600, -360360, 504504, -360360, 102960, 0, 0] := by
    funext i
    fin_cases i
    · change a 0=t * (0:K)
      dsimp [t, a8]
      try dsimp [a8] at e0
      linear_combination e0
    · change a 1=t * (-72:K)
      dsimp [t, a8]
      try dsimp [a8] at e1
      linear_combination e1
    · change a 2=t * (2520:K)
      dsimp [t, a8]
      try dsimp [a8] at e2
      linear_combination e2
    · change a 3=t * (-27720:K)
      dsimp [t, a8]
      try dsimp [a8] at e3
      linear_combination e3
    · change a 4=t * (138600:K)
      dsimp [t, a8]
      try dsimp [a8] at e4
      linear_combination e4
    · change a 5=t * (-360360:K)
      dsimp [t, a8]
      try dsimp [a8] at e5
      linear_combination e5
    · change a 6=t * (504504:K)
      dsimp [t, a8]
      try dsimp [a8] at e6
      linear_combination e6
    · change a 7=t * (-360360:K)
      dsimp [t, a8]
      try dsimp [a8] at e7
      linear_combination e7
    · change a 8=t * (102960:K)
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
    _ = t • dx7 := by
      rw [hvec]
      unfold dx7 from11
      simp only [map_smul]

end RKCert.Paired.FiniteMidpoint
