module
public import RKCert.ERKOrderedQ7Packets
@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

theorem shiftEven7
    (aᵢ0 aᵢ1 : K) (bᵢ0 bᵢ1 : K) (cᵢ0 cᵢ1 : K) (tᵢ0 : K) (uᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • even4 + aᵢ1 • even5) - (bᵢ0 • even4 + bᵢ1 • even5) = tᵢ0 • even6)
    (h1 : (X:K[X]) * (bᵢ0 • even4 + bᵢ1 • even5) - (cᵢ0 • even4 + cᵢ1 • even5) = uᵢ0 • even6)
    : aᵢ0=0 ∧ aᵢ1=0 := by
  have q1 : (-30) * bᵢ0 + 42 * bᵢ1 + (-56) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • even4 + aᵢ1 • even5) - (bᵢ0 • even4 + bᵢ1 • even5)):K[X]).coeff (0+1)=((tᵢ0 • even6):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 0 (by decide), even4_coeff 1 (by decide)] at raw
    try simp only [even5_coeff 0 (by decide), even5_coeff 1 (by decide)] at raw
    try simp only [even6_coeff 0 (by decide), even6_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : 30 * aᵢ0 + (-42) * aᵢ1 + 450 * bᵢ0 + (-882) * bᵢ1 + 1568 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • even4 + aᵢ1 • even5) - (bᵢ0 • even4 + bᵢ1 • even5)):K[X]).coeff (1+1)=((tᵢ0 • even6):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 1 (by decide), even4_coeff 2 (by decide)] at raw
    try simp only [even5_coeff 1 (by decide), even5_coeff 2 (by decide)] at raw
    try simp only [even6_coeff 1 (by decide), even6_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : (-450) * aᵢ0 + 882 * aᵢ1 + (-2100) * bᵢ0 + 5880 * bᵢ1 + (-14112) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • even4 + aᵢ1 • even5) - (bᵢ0 • even4 + bᵢ1 • even5)):K[X]).coeff (2+1)=((tᵢ0 • even6):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 2 (by decide), even4_coeff 3 (by decide)] at raw
    try simp only [even5_coeff 2 (by decide), even5_coeff 3 (by decide)] at raw
    try simp only [even6_coeff 2 (by decide), even6_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q4 : 2100 * aᵢ0 + (-5880) * aᵢ1 + 4200 * bᵢ0 + (-17640) * bᵢ1 + 58800 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h0
    change ((X * (aᵢ0 • even4 + aᵢ1 • even5) - (bᵢ0 • even4 + bᵢ1 • even5)):K[X]).coeff (3+1)=((tᵢ0 • even6):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 3 (by decide), even4_coeff 4 (by decide)] at raw
    try simp only [even5_coeff 3 (by decide), even5_coeff 4 (by decide)] at raw
    try simp only [even6_coeff 3 (by decide), even6_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q12 : (-30) * cᵢ0 + 42 * cᵢ1 + (-56) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h1
    change ((X * (bᵢ0 • even4 + bᵢ1 • even5) - (cᵢ0 • even4 + cᵢ1 • even5)):K[X]).coeff (0+1)=((uᵢ0 • even6):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 0 (by decide), even4_coeff 1 (by decide)] at raw
    try simp only [even5_coeff 0 (by decide), even5_coeff 1 (by decide)] at raw
    try simp only [even6_coeff 0 (by decide), even6_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q13 : 30 * bᵢ0 + (-42) * bᵢ1 + 450 * cᵢ0 + (-882) * cᵢ1 + 1568 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h1
    change ((X * (bᵢ0 • even4 + bᵢ1 • even5) - (cᵢ0 • even4 + cᵢ1 • even5)):K[X]).coeff (1+1)=((uᵢ0 • even6):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 1 (by decide), even4_coeff 2 (by decide)] at raw
    try simp only [even5_coeff 1 (by decide), even5_coeff 2 (by decide)] at raw
    try simp only [even6_coeff 1 (by decide), even6_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q14 : (-450) * bᵢ0 + 882 * bᵢ1 + (-2100) * cᵢ0 + 5880 * cᵢ1 + (-14112) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h1
    change ((X * (bᵢ0 • even4 + bᵢ1 • even5) - (cᵢ0 • even4 + cᵢ1 • even5)):K[X]).coeff (2+1)=((uᵢ0 • even6):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 2 (by decide), even4_coeff 3 (by decide)] at raw
    try simp only [even5_coeff 2 (by decide), even5_coeff 3 (by decide)] at raw
    try simp only [even6_coeff 2 (by decide), even6_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q15 : 2100 * bᵢ0 + (-5880) * bᵢ1 + 4200 * cᵢ0 + (-17640) * cᵢ1 + 58800 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h1
    change ((X * (bᵢ0 • even4 + bᵢ1 • even5) - (cᵢ0 • even4 + cᵢ1 • even5)):K[X]).coeff (3+1)=((uᵢ0 • even6):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [even4_coeff 3 (by decide), even4_coeff 4 (by decide)] at raw
    try simp only [even5_coeff 3 (by decide), even5_coeff 4 (by decide)] at raw
    try simp only [even6_coeff 3 (by decide), even6_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (-49 / 30) * q1 + (-7 / 30) * q2 + (-1 / 30) * q3 + (-1 / 300) * q4
  have z1 : aᵢ1=0 := by linear_combination (7 / 6) * q1 + (23 / 210) * q2 + (1 / 105) * q3 + (1 / 2100) * q4 + (-91 / 15) * q12 + (-13 / 15) * q13 + (-13 / 105) * q14 + (-13 / 1050) * q15
  exact ⟨z0,z1⟩

end RKCert.Paired.FiniteMidpoint
