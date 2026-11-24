module
public import RKCert.ERKOrder13Packets
@[expose] public section
namespace RKCert.Paired.FiniteMidpoint
open Polynomial
variable {K : Type*} [Field K] [CharZero K]
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

theorem shift13Full
    (aᵢ0 : K) (bᵢ0 : K) (tᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • odd5) - (bᵢ0 • odd5) = tᵢ0 • odd6)
    : aᵢ0=0 := by
  have q1 : 6 * bᵢ0 + (-7) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • odd5) - (bᵢ0 • odd5)):K[X]).coeff (0+1)=((tᵢ0 • odd6):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd5_coeff 0 (by decide), odd5_coeff 1 (by decide)] at raw
    try simp only [odd6_coeff 0 (by decide), odd6_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : (-6) * aᵢ0 + (-105) * bᵢ0 + 168 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • odd5) - (bᵢ0 • odd5)):K[X]).coeff (1+1)=((tᵢ0 • odd6):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd5_coeff 1 (by decide), odd5_coeff 2 (by decide)] at raw
    try simp only [odd6_coeff 1 (by decide), odd6_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : 105 * aᵢ0 + 560 * bᵢ0 + (-1260) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • odd5) - (bᵢ0 • odd5)):K[X]).coeff (2+1)=((tᵢ0 • odd6):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [odd5_coeff 2 (by decide), odd5_coeff 3 (by decide)] at raw
    try simp only [odd6_coeff 2 (by decide), odd6_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (28 / 5) * q1 + (8 / 15) * q2 + (1 / 25) * q3
  exact z0

theorem shift13Prefix
    (aᵢ0 aᵢ1 : K) (bᵢ0 bᵢ1 : K) (cᵢ0 cᵢ1 : K) (tᵢ0 tᵢ1 : K) (uᵢ0 uᵢ1 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx4 + aᵢ1 • dx5) - (bᵢ0 • dx4 + bᵢ1 • dx5) = tᵢ0 • dx5 + tᵢ1 • dx6)
    (h1 : (X:K[X]) * (bᵢ0 • dx4 + bᵢ1 • dx5) - (cᵢ0 • dx4 + cᵢ1 • dx5) = uᵢ0 • dx5 + uᵢ1 • dx6)
    : aᵢ0=0 ∧ aᵢ1=0 := by
  have q1 : (-30) * bᵢ0 + 42 * bᵢ1 + 42 * tᵢ0 + (-56) * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx4 + aᵢ1 • dx5) - (bᵢ0 • dx4 + bᵢ1 • dx5)):K[X]).coeff (0+1)=((tᵢ0 • dx5 + tᵢ1 • dx6):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 0 (by decide), dx4_coeff 1 (by decide)] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : 30 * aᵢ0 + (-42) * aᵢ1 + 420 * bᵢ0 + (-840) * bᵢ1 + (-840) * tᵢ0 + 1512 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx4 + aᵢ1 • dx5) - (bᵢ0 • dx4 + bᵢ1 • dx5)):K[X]).coeff (1+1)=((tᵢ0 • dx5 + tᵢ1 • dx6):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 1 (by decide), dx4_coeff 2 (by decide)] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : (-420) * aᵢ0 + 840 * aᵢ1 + (-1680) * bᵢ0 + 5040 * bᵢ1 + 5040 * tᵢ0 + (-12600) * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx4 + aᵢ1 • dx5) - (bᵢ0 • dx4 + bᵢ1 • dx5)):K[X]).coeff (2+1)=((tᵢ0 • dx5 + tᵢ1 • dx6):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 2 (by decide), dx4_coeff 3 (by decide)] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q4 : 1680 * aᵢ0 + (-5040) * aᵢ1 + 2520 * bᵢ0 + (-12600) * bᵢ1 + (-12600) * tᵢ0 + 46200 * tᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h0
    change ((X * (aᵢ0 • dx4 + aᵢ1 • dx5) - (bᵢ0 • dx4 + bᵢ1 • dx5)):K[X]).coeff (3+1)=((tᵢ0 • dx5 + tᵢ1 • dx6):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 3 (by decide), dx4_coeff 4 (by decide)] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q12 : (-30) * cᵢ0 + 42 * cᵢ1 + 42 * uᵢ0 + (-56) * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h1
    change ((X * (bᵢ0 • dx4 + bᵢ1 • dx5) - (cᵢ0 • dx4 + cᵢ1 • dx5)):K[X]).coeff (0+1)=((uᵢ0 • dx5 + uᵢ1 • dx6):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 0 (by decide), dx4_coeff 1 (by decide)] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    try simp only [dx6_coeff 0 (by decide), dx6_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q13 : 30 * bᵢ0 + (-42) * bᵢ1 + 420 * cᵢ0 + (-840) * cᵢ1 + (-840) * uᵢ0 + 1512 * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h1
    change ((X * (bᵢ0 • dx4 + bᵢ1 • dx5) - (cᵢ0 • dx4 + cᵢ1 • dx5)):K[X]).coeff (1+1)=((uᵢ0 • dx5 + uᵢ1 • dx6):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 1 (by decide), dx4_coeff 2 (by decide)] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    try simp only [dx6_coeff 1 (by decide), dx6_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q14 : (-420) * bᵢ0 + 840 * bᵢ1 + (-1680) * cᵢ0 + 5040 * cᵢ1 + 5040 * uᵢ0 + (-12600) * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h1
    change ((X * (bᵢ0 • dx4 + bᵢ1 • dx5) - (cᵢ0 • dx4 + cᵢ1 • dx5)):K[X]).coeff (2+1)=((uᵢ0 • dx5 + uᵢ1 • dx6):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 2 (by decide), dx4_coeff 3 (by decide)] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    try simp only [dx6_coeff 2 (by decide), dx6_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q15 : 1680 * bᵢ0 + (-5040) * bᵢ1 + 2520 * cᵢ0 + (-12600) * cᵢ1 + (-12600) * uᵢ0 + 46200 * uᵢ1 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h1
    change ((X * (bᵢ0 • dx4 + bᵢ1 • dx5) - (cᵢ0 • dx4 + cᵢ1 • dx5)):K[X]).coeff (3+1)=((uᵢ0 • dx5 + uᵢ1 • dx6):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx4_coeff 3 (by decide), dx4_coeff 4 (by decide)] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    try simp only [dx6_coeff 3 (by decide), dx6_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (-7 / 5) * q1 + (-1 / 5) * q2 + (-3 / 100) * q3 + (-1 / 300) * q4
  have z1 : aᵢ1=0 := by linear_combination (37 / 35) * q1 + (1 / 10) * q2 + (19 / 2100) * q3 + (1 / 2100) * q4 + (-26 / 5) * q12 + (-26 / 35) * q13 + (-39 / 350) * q14 + (-13 / 1050) * q15
  exact ⟨z0,z1⟩

theorem shift13Alias
    (aᵢ0 aᵢ1 : K) (bᵢ0 bᵢ1 : K) (cᵢ0 cᵢ1 : K) (tᵢ0 : K) (uᵢ0 : K)
    (h0 : (X:K[X]) * (aᵢ0 • dx3 + aᵢ1 • dx4) - (bᵢ0 • dx3 + bᵢ1 • dx4) = tᵢ0 • dx5)
    (h1 : (X:K[X]) * (bᵢ0 • dx3 + bᵢ1 • dx4) - (cᵢ0 • dx3 + cᵢ1 • dx4) = uᵢ0 • dx5)
    : aᵢ0=0 ∧ aᵢ1=0 := by
  have q1 : 20 * bᵢ0 + (-30) * bᵢ1 + 42 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h0
    change ((X * (aᵢ0 • dx3 + aᵢ1 • dx4) - (bᵢ0 • dx3 + bᵢ1 • dx4)):K[X]).coeff (0+1)=((tᵢ0 • dx5):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 0 (by decide), dx3_coeff 1 (by decide)] at raw
    try simp only [dx4_coeff 0 (by decide), dx4_coeff 1 (by decide)] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q2 : (-20) * aᵢ0 + 30 * aᵢ1 + (-180) * bᵢ0 + 420 * bᵢ1 + (-840) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h0
    change ((X * (aᵢ0 • dx3 + aᵢ1 • dx4) - (bᵢ0 • dx3 + bᵢ1 • dx4)):K[X]).coeff (1+1)=((tᵢ0 • dx5):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 1 (by decide), dx3_coeff 2 (by decide)] at raw
    try simp only [dx4_coeff 1 (by decide), dx4_coeff 2 (by decide)] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q3 : 180 * aᵢ0 + (-420) * aᵢ1 + 420 * bᵢ0 + (-1680) * bᵢ1 + 5040 * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h0
    change ((X * (aᵢ0 • dx3 + aᵢ1 • dx4) - (bᵢ0 • dx3 + bᵢ1 • dx4)):K[X]).coeff (2+1)=((tᵢ0 • dx5):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 2 (by decide), dx3_coeff 3 (by decide)] at raw
    try simp only [dx4_coeff 2 (by decide), dx4_coeff 3 (by decide)] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q4 : (-420) * aᵢ0 + 1680 * aᵢ1 + (-280) * bᵢ0 + 2520 * bᵢ1 + (-12600) * tᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h0
    change ((X * (aᵢ0 • dx3 + aᵢ1 • dx4) - (bᵢ0 • dx3 + bᵢ1 • dx4)):K[X]).coeff (3+1)=((tᵢ0 • dx5):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 3 (by decide), dx3_coeff 4 (by decide)] at raw
    try simp only [dx4_coeff 3 (by decide), dx4_coeff 4 (by decide)] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q12 : 20 * cᵢ0 + (-30) * cᵢ1 + 42 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 1) h1
    change ((X * (bᵢ0 • dx3 + bᵢ1 • dx4) - (cᵢ0 • dx3 + cᵢ1 • dx4)):K[X]).coeff (0+1)=((uᵢ0 • dx5):K[X]).coeff 1 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 0 (by decide), dx3_coeff 1 (by decide)] at raw
    try simp only [dx4_coeff 0 (by decide), dx4_coeff 1 (by decide)] at raw
    try simp only [dx5_coeff 0 (by decide), dx5_coeff 1 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q13 : (-20) * bᵢ0 + 30 * bᵢ1 + (-180) * cᵢ0 + 420 * cᵢ1 + (-840) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 2) h1
    change ((X * (bᵢ0 • dx3 + bᵢ1 • dx4) - (cᵢ0 • dx3 + cᵢ1 • dx4)):K[X]).coeff (1+1)=((uᵢ0 • dx5):K[X]).coeff 2 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 1 (by decide), dx3_coeff 2 (by decide)] at raw
    try simp only [dx4_coeff 1 (by decide), dx4_coeff 2 (by decide)] at raw
    try simp only [dx5_coeff 1 (by decide), dx5_coeff 2 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q14 : 180 * bᵢ0 + (-420) * bᵢ1 + 420 * cᵢ0 + (-1680) * cᵢ1 + 5040 * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 3) h1
    change ((X * (bᵢ0 • dx3 + bᵢ1 • dx4) - (cᵢ0 • dx3 + cᵢ1 • dx4)):K[X]).coeff (2+1)=((uᵢ0 • dx5):K[X]).coeff 3 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 2 (by decide), dx3_coeff 3 (by decide)] at raw
    try simp only [dx4_coeff 2 (by decide), dx4_coeff 3 (by decide)] at raw
    try simp only [dx5_coeff 2 (by decide), dx5_coeff 3 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have q15 : (-420) * bᵢ0 + 1680 * bᵢ1 + (-280) * cᵢ0 + 2520 * cᵢ1 + (-12600) * uᵢ0 = 0 := by
    have raw := congrArg (fun P:K[X]=>P.coeff 4) h1
    change ((X * (bᵢ0 • dx3 + bᵢ1 • dx4) - (cᵢ0 • dx3 + cᵢ1 • dx4)):K[X]).coeff (3+1)=((uᵢ0 • dx5):K[X]).coeff 4 at raw
    simp only [coeff_sub, coeff_X_mul, coeff_add, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul] at raw
    try simp only [dx3_coeff 3 (by decide), dx3_coeff 4 (by decide)] at raw
    try simp only [dx4_coeff 3 (by decide), dx4_coeff 4 (by decide)] at raw
    try simp only [dx5_coeff 3 (by decide), dx5_coeff 4 (by decide)] at raw
    have rz := sub_eq_zero.mpr raw
    convert rz using 1 <;> (try norm_num; ring)
  have z0 : aᵢ0=0 := by linear_combination (7 / 5) * q1 + (7 / 25) * q2 + (3 / 50) * q3 + (1 / 100) * q4
  have z1 : aᵢ1=0 := by linear_combination (-7 / 5) * q1 + (-1 / 5) * q2 + (-3 / 100) * q3 + (-1 / 300) * q4 + (77 / 15) * q12 + (77 / 75) * q13 + (11 / 50) * q14 + (11 / 300) * q15
  exact ⟨z0,z1⟩

end RKCert.Paired.FiniteMidpoint
