module
public import RKCert.ERKFinitePackets
@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

theorem shiftEven8
    (aᵢ0 : K) (bᵢ0 : K) (tᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • even6) - (bᵢ0 • even6) = tᵢ0 • even7)
    : aᵢ0=0 := by
  have q1 : (-56) * bᵢ0 + 72 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • even6) - (bᵢ0 • even6)):K[X]).coeff (0+1)=((tᵢ0 • even7):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even6_coeff 0 (by decide), even6_coeff 1 (by decide)] at raw
    try simp only [even7_coeff 0 (by decide), even7_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : 56 * aᵢ0 + 1568 * bᵢ0 + (-2592) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • even6) - (bᵢ0 • even6)):K[X]).coeff (1+1)=((tᵢ0 • even7):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even6_coeff 1 (by decide), even6_coeff 2 (by decide)] at raw
    try simp only [even7_coeff 1 (by decide), even7_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : (-1568) * aᵢ0 + (-14112) * bᵢ0 + 30240 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • even6) - (bᵢ0 • even6)):K[X]).coeff (2+1)=((tᵢ0 • even7):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even6_coeff 2 (by decide), even6_coeff 3 (by decide)] at raw
    try simp only [even7_coeff 2 (by decide), even7_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (-6 / 7) * q1 + (-3 / 56) * q2 + (-1 / 392) * q3
  exact z0

theorem shiftFull8
    (aᵢ0 : K) (bᵢ0 : K) (tᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • odd7) - (bᵢ0 • odd7) = tᵢ0 • odd8)
    : aᵢ0=0 := by
  have q1 : 8 * bᵢ0 + (-9) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • odd7) - (bᵢ0 • odd7)):K[X]).coeff (0+1)=((tᵢ0 • odd8):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd7_coeff 0 (by decide), odd7_coeff 1 (by decide)] at raw
    try simp only [odd8_coeff 0 (by decide), odd8_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : (-8) * aᵢ0 + (-252) * bᵢ0 + 360 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • odd7) - (bᵢ0 • odd7)):K[X]).coeff (1+1)=((tᵢ0 • odd8):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd7_coeff 1 (by decide), odd7_coeff 2 (by decide)] at raw
    try simp only [odd8_coeff 1 (by decide), odd8_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : 252 * aᵢ0 + 2520 * bᵢ0 + (-4620) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • odd7) - (bᵢ0 • odd7)):K[X]).coeff (2+1)=((tᵢ0 • odd8):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd7_coeff 2 (by decide), odd7_coeff 3 (by decide)] at raw
    try simp only [odd8_coeff 2 (by decide), odd8_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (45 / 7) * q1 + (5 / 14) * q2 + (3 / 196) * q3
  exact z0

theorem shiftPrefix8
    (aᵢ0 aᵢ1 : K) (bᵢ0 bᵢ1 : K) (cᵢ0 cᵢ1 : K) (tᵢ0 tᵢ1 : K) (uᵢ0 uᵢ1 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx6 + aᵢ1 • dx7) - (bᵢ0 • dx6 + bᵢ1 • dx7) = tᵢ0 • dx7 + tᵢ1 • dx8)
    (h1 : (X:K[X]) * (bᵢ0 • dx6 + bᵢ1 • dx7) - (cᵢ0 • dx6 + cᵢ1 • dx7) = uᵢ0 • dx7 + uᵢ1 • dx8)
    : aᵢ0=0 ∧ aᵢ1=0 := by
  have q1 : (-56) * bᵢ0 + 72 * bᵢ1 + 72 * tᵢ0 + (-90) * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx6 + aᵢ1 • dx7) - (bᵢ0 • dx6 + bᵢ1 • dx7)):K[X]).coeff (0+1)=((tᵢ0 • dx7 + tᵢ1 • dx8):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    try simp only [dx7_coeff 0 (by decide), dx7_coeff 1 (by decide)] at raw
    try simp only [dx8_coeff 0 (by decide), dx8_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : 56 * aᵢ0 + (-72) * aᵢ1 + 1512 * bᵢ0 + (-2520) * bᵢ1 + (-2520) * tᵢ0 + 3960 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx6 + aᵢ1 • dx7) - (bᵢ0 • dx6 + bᵢ1 • dx7)):K[X]).coeff (1+1)=((tᵢ0 • dx7 + tᵢ1 • dx8):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    try simp only [dx7_coeff 1 (by decide), dx7_coeff 2 (by decide)] at raw
    try simp only [dx8_coeff 1 (by decide), dx8_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : (-1512) * aᵢ0 + 2520 * aᵢ1 + (-12600) * bᵢ0 + 27720 * bᵢ1 + 27720 * tᵢ0 + (-55440) * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx6 + aᵢ1 • dx7) - (bᵢ0 • dx6 + bᵢ1 • dx7)):K[X]).coeff (2+1)=((tᵢ0 • dx7 + tᵢ1 • dx8):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    try simp only [dx7_coeff 2 (by decide), dx7_coeff 3 (by decide)] at raw
    try simp only [dx8_coeff 2 (by decide), dx8_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q4 : 12600 * aᵢ0 + (-27720) * aᵢ1 + 46200 * bᵢ0 + (-138600) * bᵢ1 + (-138600) * tᵢ0 + 360360 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h0
    change ((X * (aᵢ0 • dx6 + aᵢ1 • dx7) - (bᵢ0 • dx6 + bᵢ1 • dx7)):K[X]).coeff (3+1)=((tᵢ0 • dx7 + tᵢ1 • dx8):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    try simp only [dx7_coeff 3 (by decide), dx7_coeff 4 (by decide)] at raw
    try simp only [dx8_coeff 3 (by decide), dx8_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q12 : (-56) * cᵢ0 + 72 * cᵢ1 + 72 * uᵢ0 + (-90) * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h1
    change ((X * (bᵢ0 • dx6 + bᵢ1 • dx7) - (cᵢ0 • dx6 + cᵢ1 • dx7)):K[X]).coeff (0+1)=((uᵢ0 • dx7 + uᵢ1 • dx8):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    try simp only [dx7_coeff 0 (by decide), dx7_coeff 1 (by decide)] at raw
    try simp only [dx8_coeff 0 (by decide), dx8_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q13 : 56 * bᵢ0 + (-72) * bᵢ1 + 1512 * cᵢ0 + (-2520) * cᵢ1 + (-2520) * uᵢ0 + 3960 * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h1
    change ((X * (bᵢ0 • dx6 + bᵢ1 • dx7) - (cᵢ0 • dx6 + cᵢ1 • dx7)):K[X]).coeff (1+1)=((uᵢ0 • dx7 + uᵢ1 • dx8):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    try simp only [dx7_coeff 1 (by decide), dx7_coeff 2 (by decide)] at raw
    try simp only [dx8_coeff 1 (by decide), dx8_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q14 : (-1512) * bᵢ0 + 2520 * bᵢ1 + (-12600) * cᵢ0 + 27720 * cᵢ1 + 27720 * uᵢ0 + (-55440) * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h1
    change ((X * (bᵢ0 • dx6 + bᵢ1 • dx7) - (cᵢ0 • dx6 + cᵢ1 • dx7)):K[X]).coeff (2+1)=((uᵢ0 • dx7 + uᵢ1 • dx8):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    try simp only [dx7_coeff 2 (by decide), dx7_coeff 3 (by decide)] at raw
    try simp only [dx8_coeff 2 (by decide), dx8_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q15 : 12600 * bᵢ0 + (-27720) * bᵢ1 + 46200 * cᵢ0 + (-138600) * cᵢ1 + (-138600) * uᵢ0 + 360360 * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h1
    change ((X * (bᵢ0 • dx6 + bᵢ1 • dx7) - (cᵢ0 • dx6 + cᵢ1 • dx7)):K[X]).coeff (3+1)=((uᵢ0 • dx7 + uᵢ1 • dx8):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    try simp only [dx7_coeff 3 (by decide), dx7_coeff 4 (by decide)] at raw
    try simp only [dx8_coeff 3 (by decide), dx8_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (-165 / 112) * q1 + (-55 / 448) * q2 + (-33 / 3136) * q3 + (-1 / 1568) * q4
  have z1 : aᵢ1=0 := by linear_combination (605 / 1008) * q1 + (11 / 448) * q2 + (1 / 3136) * q3 + (-1 / 14112) * q4 + (-935 / 168) * q12 + (-935 / 2016) * q13 + (-187 / 4704) * q14 + (-17 / 7056) * q15
  exact ⟨z0,z1⟩

theorem shiftPrefix9
    (aᵢ0 : K) (bᵢ0 : K) (tᵢ0 tᵢ1 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx8) - (bᵢ0 • dx8) = tᵢ0 • dx8 + tᵢ1 • dx9)
    : aᵢ0=0 := by
  have q1 : (-90) * bᵢ0 + (-90) * tᵢ0 + 110 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx8) - (bᵢ0 • dx8)):K[X]).coeff (0+1)=((tᵢ0 • dx8 + tᵢ1 • dx9):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx8_coeff 0 (by decide), dx8_coeff 1 (by decide)] at raw
    try simp only [dx9_coeff 0 (by decide), dx9_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : 90 * aᵢ0 + 3960 * bᵢ0 + 3960 * tᵢ0 + (-5940) * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx8) - (bᵢ0 • dx8)):K[X]).coeff (1+1)=((tᵢ0 • dx8 + tᵢ1 • dx9):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx8_coeff 1 (by decide), dx8_coeff 2 (by decide)] at raw
    try simp only [dx9_coeff 1 (by decide), dx9_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : (-3960) * aᵢ0 + (-55440) * bᵢ0 + (-55440) * tᵢ0 + 102960 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx8) - (bᵢ0 • dx8)):K[X]).coeff (2+1)=((tᵢ0 • dx8 + tᵢ1 • dx9):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx8_coeff 2 (by decide), dx8_coeff 3 (by decide)] at raw
    try simp only [dx9_coeff 2 (by decide), dx9_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (-11 / 15) * q1 + (-4 / 135) * q2 + (-1 / 1080) * q3
  exact z0

theorem shiftAlias8
    (aᵢ0 aᵢ1 : K) (bᵢ0 bᵢ1 : K) (cᵢ0 cᵢ1 : K) (tᵢ0 : K) (uᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx5 + aᵢ1 • dx6) - (bᵢ0 • dx5 + bᵢ1 • dx6) = tᵢ0 • dx7)
    (h1 : (X:K[X]) * (bᵢ0 • dx5 + bᵢ1 • dx6) - (cᵢ0 • dx5 + cᵢ1 • dx6) = uᵢ0 • dx7)
    : aᵢ0=0 ∧ aᵢ1=0 := by
  have q1 : 42 * bᵢ0 + (-56) * bᵢ1 + 72 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx5 + aᵢ1 • dx6) - (bᵢ0 • dx5 + bᵢ1 • dx6)):K[X]).coeff (0+1)=((tᵢ0 • dx7):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    try simp only [dx7_coeff 0 (by decide), dx7_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : (-42) * aᵢ0 + 56 * aᵢ1 + (-840) * bᵢ0 + 1512 * bᵢ1 + (-2520) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx5 + aᵢ1 • dx6) - (bᵢ0 • dx5 + bᵢ1 • dx6)):K[X]).coeff (1+1)=((tᵢ0 • dx7):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    try simp only [dx7_coeff 1 (by decide), dx7_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : 840 * aᵢ0 + (-1512) * aᵢ1 + 5040 * bᵢ0 + (-12600) * bᵢ1 + 27720 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx5 + aᵢ1 • dx6) - (bᵢ0 • dx5 + bᵢ1 • dx6)):K[X]).coeff (2+1)=((tᵢ0 • dx7):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    try simp only [dx7_coeff 2 (by decide), dx7_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q4 : (-5040) * aᵢ0 + 12600 * aᵢ1 + (-12600) * bᵢ0 + 46200 * bᵢ1 + (-138600) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h0
    change ((X * (aᵢ0 • dx5 + aᵢ1 • dx6) - (bᵢ0 • dx5 + bᵢ1 • dx6)):K[X]).coeff (3+1)=((tᵢ0 • dx7):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    try simp only [dx7_coeff 3 (by decide), dx7_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q12 : 42 * cᵢ0 + (-56) * cᵢ1 + 72 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h1
    change ((X * (bᵢ0 • dx5 + bᵢ1 • dx6) - (cᵢ0 • dx5 + cᵢ1 • dx6)):K[X]).coeff (0+1)=((uᵢ0 • dx7):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    try simp only [dx7_coeff 0 (by decide), dx7_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q13 : (-42) * bᵢ0 + 56 * bᵢ1 + (-840) * cᵢ0 + 1512 * cᵢ1 + (-2520) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h1
    change ((X * (bᵢ0 • dx5 + bᵢ1 • dx6) - (cᵢ0 • dx5 + cᵢ1 • dx6)):K[X]).coeff (1+1)=((uᵢ0 • dx7):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    try simp only [dx7_coeff 1 (by decide), dx7_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q14 : 840 * bᵢ0 + (-1512) * bᵢ1 + 5040 * cᵢ0 + (-12600) * cᵢ1 + 27720 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h1
    change ((X * (bᵢ0 • dx5 + bᵢ1 • dx6) - (cᵢ0 • dx5 + cᵢ1 • dx6)):K[X]).coeff (2+1)=((uᵢ0 • dx7):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    try simp only [dx7_coeff 2 (by decide), dx7_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q15 : (-5040) * bᵢ0 + 12600 * bᵢ1 + (-12600) * cᵢ0 + 46200 * cᵢ1 + (-138600) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h1
    change ((X * (bᵢ0 • dx5 + bᵢ1 • dx6) - (cᵢ0 • dx5 + cᵢ1 • dx6)):K[X]).coeff (3+1)=((uᵢ0 • dx7):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    try simp only [dx7_coeff 3 (by decide), dx7_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (10 / 7) * q1 + (15 / 98) * q2 + (5 / 294) * q3 + (1 / 735) * q4
  have z1 : aᵢ1=0 := by linear_combination (-45 / 56) * q1 + (-5 / 98) * q2 + (-1 / 392) * q3 + (75 / 14) * q12 + (225 / 392) * q13 + (25 / 392) * q14 + (1 / 196) * q15
  exact ⟨z0,z1⟩

theorem shiftAlias9
    (aᵢ0 : K) (bᵢ0 : K) (tᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx7) - (bᵢ0 • dx7) = tᵢ0 • dx8)
    : aᵢ0=0 := by
  have q1 : 72 * bᵢ0 + (-90) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx7) - (bᵢ0 • dx7)):K[X]).coeff (0+1)=((tᵢ0 • dx8):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx7_coeff 0 (by decide), dx7_coeff 1 (by decide)] at raw
    try simp only [dx8_coeff 0 (by decide), dx8_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : (-72) * aᵢ0 + (-2520) * bᵢ0 + 3960 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx7) - (bᵢ0 • dx7)):K[X]).coeff (1+1)=((tᵢ0 • dx8):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx7_coeff 1 (by decide), dx7_coeff 2 (by decide)] at raw
    try simp only [dx8_coeff 1 (by decide), dx8_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : 2520 * aᵢ0 + 27720 * bᵢ0 + (-55440) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx7) - (bᵢ0 • dx7)):K[X]).coeff (2+1)=((tᵢ0 • dx8):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx7_coeff 2 (by decide), dx7_coeff 3 (by decide)] at raw
    try simp only [dx8_coeff 2 (by decide), dx8_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (55 / 72) * q1 + (11 / 288) * q2 + (1 / 672) * q3
  exact z0

end RKCert.Paired.FiniteMidpoint
