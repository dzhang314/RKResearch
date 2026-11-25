module

public import RKCert.ReviewedNative.WeakFiveThreeInteriorDetGridReplay
public import RKCert.ReviewedNative.WeakFiveThreeInteriorBernsteinRows
public import Mathlib.Algebra.BigOperators.Ring.List
public import Mathlib.Algebra.Ring.Rat

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Denominator-cleared executable strip coefficients and soundness

Every nonunit edge is checked at both defect endpoints. The common positive
factor is 105 · 8192^7 · (2^depth)^7 times the normalized defect denominator.
No rational sign checks are presumed by the mathematical consumer.
-/
namespace RKCert.ReviewedNative.ThreeInteriorPencil

open Polynomial RKCert.ReviewedNative.PolynomialCertificate
open RKCert.ReviewedNative.PolynomialCertificate.WeakFiveCells
open scoped Polynomial BigOperators

def clearedPowerTerm (a : ℕ × ℕ × ℤ) (den si xn k : ℕ) : ℤ :=
  a.2.2 * (xn:ℤ)^a.2.1 * (8192:ℤ)^(7-a.2.1) * (den:ℤ)^(7-a.1) *
    (si:ℤ)^(a.1-k) * (a.1.choose k : ℤ)

def clearedPower {N : ℕ} (T : SparseDetTemplate N) (den si xn k : ℕ) : ℤ :=
  (T.terms.map fun a => clearedPowerTerm a den si xn k).sum

def bernWeightZ (k j : ℕ) : ℕ := k.choose j * (105 / Nat.choose 7 j)

def clearedBernstein {N : ℕ} (T : SparseDetTemplate N) (den si xn k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range 8, clearedPower T den si xn j * (bernWeightZ k j : ℤ)

def rawSL (r : ThreeInteriorCell) : ℚ := (r.rect.xIndex:ℚ) / ((2^r.rect.xDepth:ℕ):ℚ)
def rawSU (r : ThreeInteriorCell) : ℚ := ((r.rect.xIndex+1:ℕ):ℚ) / ((2^r.rect.xDepth:ℕ):ℚ)
def rawJL (r : ThreeInteriorCell) : ℚ := (r.rect.yIndex:ℚ) / ((2^r.rect.yDepth:ℕ):ℚ)
def rawJU (r : ThreeInteriorCell) : ℚ := ((r.rect.yIndex+1:ℕ):ℚ) / ((2^r.rect.yDepth:ℕ):ℚ)

def templateLower (s : ℚ) : ℚ := -publishedTemplate7.value s 0 / publishedTemplate6.value s 0
def templateUpper (s : ℚ) : ℚ := -publishedTemplate7.value s 1 / publishedTemplate6.value s 1

def templateDefect (r : ThreeInteriorCell) : Bool → ℚ
  | false => mix (templateLower (rawSU r)) (templateUpper (rawSL r)) (rawJL r)
  | true => mix (templateLower (rawSL r)) (templateUpper (rawSU r)) (rawJU r)

def combineStripZ (sign : ℤ) (δ : ℚ) (b7 b6 : ℤ) : ℤ :=
  sign*((δ.den:ℤ)*b7+δ.num*b6)

def clearedSignedEdge (r : ThreeInteriorCell) (upper : Bool) (i : Fin 7)
    (bias : Bool) (k : Fin 8) : ℤ :=
  let den := 2 ^ r.rect.xDepth
  let si := r.rect.xIndex
  let xn := edgeNumerator r upper i
  combineStripZ (edgeSense upper i) (templateDefect r bias)
    (clearedBernstein publishedTemplate7 den si xn k.val)
    (clearedBernstein publishedTemplate6 den si xn k.val)

private theorem pow_scale {a : ℚ} (an : a ≠ 0) {i : ℕ} (ib : i ≤ 7) :
    a^7*(a⁻¹)^i = a^(7-i) := by
  have sh : a^7 = a^(7-i)*a^i := by rw [← pow_add,Nat.sub_add_cancel ib]
  rw [sh,inv_pow,mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ an),mul_one]

private theorem affine_cast_pullback (den si : ℕ) :
    C ((((si+1:ℕ):ℚ)/(den:ℚ))-(si:ℚ)/(den:ℚ))*X+C ((si:ℚ)/(den:ℚ)) =
      C ((den:ℚ)⁻¹)*(X+C (si:ℚ)) := by
  have sub : (((si+1:ℕ):ℚ)/(den:ℚ))-(si:ℚ)/(den:ℚ) = (den:ℚ)⁻¹ := by
    rw [Nat.cast_add,Nat.cast_one,← sub_div]
    simp [one_div]
  have c : (den:ℚ)⁻¹*(si:ℚ) = (si:ℚ)/(den:ℚ) := by rw [div_eq_mul_inv,mul_comm]
  rw [sub,mul_add,← C_mul,c]

noncomputable def sparsePulled {N : ℕ} (T : SparseDetTemplate N) (den si xn : ℕ) : ℚ[X] :=
  intervalPullback (T.densitySlice ((xn:ℚ)/8192)) ((si:ℚ)/(den:ℚ)) (((si+1:ℕ):ℚ)/(den:ℚ))

private theorem sparsePulled_coeff {N : ℕ} (T : SparseDetTemplate N) (den si xn k : ℕ) :
    (sparsePulled T den si xn).coeff k =
      (T.terms.map fun a => (a.2.2:ℚ)*((xn:ℚ)/8192)^a.2.1*((den:ℚ)⁻¹)^a.1 *
        ((si:ℚ)^(a.1-k)*(a.1.choose k:ℚ))).sum := by
  let L : ℚ[X] := C ((den:ℚ)⁻¹)*(X+C (si:ℚ))
  unfold sparsePulled intervalPullback
  rw [affine_cast_pullback]
  change ((Polynomial.compRingHom L) (T.densitySlice ((xn:ℚ)/8192))).coeff k = _
  rw [SparseDetTemplate.densitySlice,map_list_sum,List.map_map, coeff_list_sum_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a _
  simp only [Function.comp_apply,Polynomial.coe_compRingHom_apply,mul_comp,C_comp,
    pow_comp,X_comp,L,mul_pow,← C_pow,← mul_assoc,← C_mul,coeff_C_mul,
    coeff_X_add_C_pow]

def powerFactor (den : ℕ) : ℚ := (8192:ℚ)^7*(den:ℚ)^7
def bernFactor (den : ℕ) : ℚ := 105*powerFactor den

private theorem term_clear {a : ℕ × ℕ × ℤ} {den si xn k : ℕ} (dp : den > 0)
    (a7 : a.1 ≤ 7) (b7 : a.2.1 ≤ 7) :
    (clearedPowerTerm a den si xn k : ℚ) = powerFactor den *
      ((a.2.2:ℚ)*((xn:ℚ)/8192)^a.2.1*((den:ℚ)⁻¹)^a.1 *
        ((si:ℚ)^(a.1-k)*(a.1.choose k:ℚ))) := by
  have sx : (8192:ℚ)^7*((xn:ℚ)/8192)^a.2.1 = (xn:ℚ)^a.2.1*(8192:ℚ)^(7-a.2.1) := by
    rw [div_eq_mul_inv,mul_pow]
    calc
      (8192:ℚ)^7*((xn:ℚ)^a.2.1*((8192:ℚ)⁻¹)^a.2.1) =
          (xn:ℚ)^a.2.1*((8192:ℚ)^7*((8192:ℚ)⁻¹)^a.2.1) := by ring
      _ = _ := by rw [pow_scale (by decide : (8192:ℚ) ≠ 0) b7]
  have sy := pow_scale (a := (den:ℚ)) (Nat.cast_ne_zero.mpr dp.ne') a7
  simp only [clearedPowerTerm,Int.cast_mul,Int.cast_pow,Int.cast_natCast,Int.cast_ofNat]
  calc
    (a.2.2:ℚ)*(xn:ℚ)^a.2.1*(8192:ℚ)^(7-a.2.1)*(den:ℚ)^(7-a.1)*
        (si:ℚ)^(a.1-k)*(a.1.choose k:ℚ) =
      (a.2.2:ℚ)*((xn:ℚ)^a.2.1*(8192:ℚ)^(7-a.2.1))*(den:ℚ)^(7-a.1)*
        ((si:ℚ)^(a.1-k)*(a.1.choose k:ℚ)) := by ring
    _ = _ := by rw [← sx,← sy]; unfold powerFactor; ring

private theorem power_cast {N : ℕ} (T : SparseDetTemplate N) (N7 : N ≤ 7)
    (den si xn k : ℕ) (dp : den > 0) :
    (clearedPower T den si xn k : ℚ) = powerFactor den*(sparsePulled T den si xn).coeff k := by
  rw [sparsePulled_coeff,← List.sum_map_mul_left]
  unfold clearedPower
  change (Int.castRingHom ℚ) ((T.terms.map _).sum) = _
  rw [map_list_sum,List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro a ha
  exact term_clear dp ((T.bounded a ha).1.trans N7) ((T.bounded a ha).2.trans N7)

private theorem bern_den_dvd (k : Fin 8) : Nat.choose 7 k.val ∣ 105 := by
  fin_cases k <;> decide

theorem clearedBernstein_cast {N : ℕ} (T : SparseDetTemplate N) (N7 : N ≤ 7)
    (den si xn k : ℕ) (dp : den > 0) :
    (clearedBernstein T den si xn k : ℚ) =
      bernFactor den * bernsteinCoeff (sparsePulled T den si xn) 7 k := by
  unfold clearedBernstein bernFactor bernsteinCoeff
  change (Int.castRingHom ℚ) _ = _
  rw [map_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  let i : Fin 8 := ⟨j,Finset.mem_range.mp hj⟩
  have divides : Nat.choose 7 j ∣ 105 := bern_den_dvd i
  have cast_div : ((105 / Nat.choose 7 j : ℕ) : ℚ) =
      (105 : ℚ) / (Nat.choose 7 j : ℚ) := Nat.cast_div_charZero divides
  simp only [Int.coe_castRingHom, Int.cast_mul, Int.cast_natCast, bernWeightZ, Nat.cast_mul,
    power_cast T N7 den si xn j dp]
  rw [cast_div]
  ring

private theorem bern_add (P Q : ℚ[X]) (k : ℕ) :
    bernsteinCoeff (P+Q) 7 k = bernsteinCoeff P 7 k + bernsteinCoeff Q 7 k := by
  simp only [bernsteinCoeff,coeff_add,add_mul,Finset.sum_add_distrib]

private theorem bern_C_mul (a : ℚ) (P : ℚ[X]) (k : ℕ) :
    bernsteinCoeff (C a*P) 7 k = a*bernsteinCoeff P 7 k := by
  simp only [bernsteinCoeff,coeff_C_mul,mul_assoc,Finset.mul_sum]

theorem templateDefect_correct (r : ThreeInteriorCell) (bias : Bool) :
    templateDefect r bias = (cellDefectEnd r bias : ℚ) := by
  have a (s : ℚ) : templateLower s = compactLower s := by
    unfold templateLower
    rw [publishedTemplate6.uniform_rat publishedGrid6,publishedTemplate7.uniform_rat publishedGrid7,
      compactLower_det]
  have b (s : ℚ) : templateUpper s = compactUpper s := by
    unfold templateUpper
    rw [publishedTemplate6.uniform_rat publishedGrid6,publishedTemplate7.uniform_rat publishedGrid7,
      compactUpper_det]
  cases bias
  · simp only [templateDefect,cellDefectEnd,defectBoxLow,a,b] <;> rfl
  · simp only [templateDefect,cellDefectEnd,defectBoxHigh,a,b] <;> rfl

theorem semantic_signed_coefficient (r : ThreeInteriorCell) (upper : Bool) (i : Fin 7)
    (bias : Bool) (k : Fin 8) :
    finiteStripCoefficient r upper i bias k = (edgeSense upper i : ℚ)*
      (bernsteinCoeff (sparsePulled publishedTemplate7 (2^r.rect.xDepth) r.rect.xIndex
          (edgeNumerator r upper i)) 7 k.val +
       templateDefect r bias *
        bernsteinCoeff (sparsePulled publishedTemplate6 (2^r.rect.xDepth) r.rect.xIndex
          (edgeNumerator r upper i)) 7 k.val) := by
  rw [templateDefect_correct]
  unfold finiteStripCoefficient signedDensityPencil densityRootPencil sparsePulled
  have a (n : ℕ) (T : SparseDetTemplate n) (h : SparseDetGrid n T) :
      densityDeterminant n (edgePoint r upper i : ℚ) =
        T.densitySlice ((edgeNumerator r upper i:ℚ)/8192) :=
    (T.densitySlice_eq_rat h ((edgeNumerator r upper i:ℚ)/8192)).symm
  rw [a 7 publishedTemplate7 publishedGrid7,a 6 publishedTemplate6 publishedGrid6]
  unfold intervalPullback
  simp only [mul_comp,C_comp,add_comp,bern_C_mul,bern_add] <;> rfl

theorem clearedSignedEdge_cast (r : ThreeInteriorCell) (upper : Bool) (i : Fin 7)
    (bias : Bool) (k : Fin 8) :
    (clearedSignedEdge r upper i bias k : ℚ) =
      (bernFactor (2^r.rect.xDepth)*((templateDefect r bias).den:ℚ)) *
        finiteStripCoefficient r upper i bias k := by
  let d := 2^r.rect.xDepth
  let δ := templateDefect r bias
  have dpos : 0 < d := pow_pos (by decide) _
  have nz : (δ.den:ℚ) ≠ 0 := Nat.cast_ne_zero.mpr δ.den_nz
  have numerator : (δ.num:ℚ) = δ*(δ.den:ℚ) := (div_eq_iff nz).mp (Rat.num_div_den δ)
  unfold clearedSignedEdge combineStripZ
  simp only [Int.cast_mul,Int.cast_add,Int.cast_natCast]
  rw [clearedBernstein_cast publishedTemplate7 le_rfl _ _ _ _ dpos,
    clearedBernstein_cast publishedTemplate6 (by decide) _ _ _ _ dpos, semantic_signed_coefficient]
  change _ = _
  rw [numerator]
  ring

theorem clearedSignedEdge_sound (r : ThreeInteriorCell) (upper : Bool) (i : Fin 7)
    (bias : Bool) (k : Fin 8) (hp : 0 < clearedSignedEdge r upper i bias k) :
    0 < finiteStripCoefficient r upper i bias k := by
  have e : 0 < (clearedSignedEdge r upper i bias k : ℚ) := by exact_mod_cast hp
  rw [clearedSignedEdge_cast] at e
  have pd : 0 < (2:ℕ)^r.rect.xDepth := pow_pos (by decide) _
  have denominator : (0:ℚ) < (templateDefect r bias).den :=
    Nat.cast_pos.mpr (templateDefect r bias).den_pos
  have pp : 0 < bernFactor (2^r.rect.xDepth)*((templateDefect r bias).den:ℚ) := by
    unfold bernFactor powerFactor
    exact mul_pos (mul_pos (by decide) (mul_pos (pow_pos (by decide) _) (pow_pos (Nat.cast_pos.mpr pd) _)))
      denominator
  exact (mul_pos_iff_of_pos_left pp).mp e

end RKCert.ReviewedNative.ThreeInteriorPencil
