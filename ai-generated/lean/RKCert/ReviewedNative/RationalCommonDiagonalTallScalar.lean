module

public import RKCert.ReviewedNative.MonicFractionRootPrime
public import RKCert.ReviewedNative.PrimeFactorialDenominators
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Tactic.Ring

@[expose] public section

/-! # The cleared tall-moment polynomial has no rational root in degree at least two

The integer polynomial has leading coefficient one and all other coefficients
divisible by two consecutive integers' product. An odd prime divisor then
forces the root to be a prime-divisible integer. After dividing by the
constant coefficient, the valuation argument contradicts cancellation. -/

namespace RKResearch.Certified

open Polynomial
open scoped BigOperators Polynomial

/-- The scalar in the native common-diagonal tall-tree identity. -/
def commonDiagonalTallBinomial {K : Type*} [Field K] (m : ℕ) (x : K) : K :=
  ∑ k ∈ Finset.range (m + 1),
    (m.choose k : K) * (-x) ^ (m - k) / ((k + 1).factorial : K)

/-- The normalized series, with powers indexed in increasing order.
The argument is the negative reciprocal of a nonzero physical diagonal. -/
def commonDiagonalTallNormalized {K : Type*} [Field K] (m : ℕ) (y : K) : K :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : K) * y ^ j / ((j + 1).factorial : K)

theorem commonDiagonalTallBinomial_eq_pow_mul_normalized_of_ne_zero
    {K : Type*} [Field K] (m : ℕ) {x : K} (hx : x ≠ 0) :
    commonDiagonalTallBinomial m x =
      (-x) ^ m * commonDiagonalTallNormalized m ((-x)⁻¹) := by
  unfold commonDiagonalTallBinomial commonDiagonalTallNormalized
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have h : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [pow_sub₀ (-x) (neg_ne_zero.mpr hx) h, ← inv_pow]
  simp only [div_eq_mul_inv] <;> ring

theorem commonDiagonalTallBinomial_at_zero {K : Type*} [Field K] (m : ℕ) :
    commonDiagonalTallBinomial m (0 : K) = 1 / ((m + 1).factorial : K) := by
  unfold commonDiagonalTallBinomial
  rw [Finset.sum_range_succ]
  have h : (∑ j ∈ Finset.range m,
      (m.choose j : K) * (- (0 : K)) ^ (m - j) / ((j + 1).factorial : K)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' : m - j ≠ 0 := Nat.ne_of_gt (Nat.sub_pos_of_lt (Finset.mem_range.mp hj))
    simp [zero_pow hj']
  rw [h]
  simp

/-- Integer coefficients of the cleared tall-moment polynomial, on `j ≤ m`.
The factorial quotient is exact in this range. -/
def commonDiagonalTallCoeff (m j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (m - j) * ((m.choose j * ((m + 1).factorial / (j + 1).factorial) : ℕ) : ℤ)

/-- The signed normalized series cleared by `(-1)^m * (m+1)!`.
Its variable is the reciprocal diagonal, not the diagonal itself. -/
noncomputable def commonDiagonalTallPolynomial (m : ℕ) : ℤ[X] :=
  ∑ j ∈ Finset.range (m + 1), C (commonDiagonalTallCoeff m j) * X ^ j

theorem coeff_commonDiagonalTallPolynomial (m j : ℕ) :
    (commonDiagonalTallPolynomial m).coeff j =
      if j ≤ m then commonDiagonalTallCoeff m j else 0 := by
  rw [commonDiagonalTallPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff]

theorem commonDiagonalTallPolynomial_monic_degree (m : ℕ) :
    (commonDiagonalTallPolynomial m).Monic ∧ (commonDiagonalTallPolynomial m).natDegree = m := by
  have hDeg : (commonDiagonalTallPolynomial m).natDegree ≤ m := by
    rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero]
    intro j hj
    have h : m < j := WithBot.coe_lt_coe.mp hj
    simp [coeff_commonDiagonalTallPolynomial, not_le.mpr h]
  have hCoeff : (commonDiagonalTallPolynomial m).coeff m = 1 := by
    simp [coeff_commonDiagonalTallPolynomial, commonDiagonalTallCoeff,
      Nat.div_self (Nat.factorial_pos (m + 1))]
  exact ⟨monic_of_natDegree_le_of_coeff_eq_one m hDeg hCoeff,
    natDegree_eq_of_le_of_coeff_ne_zero hDeg (hCoeff ▸ one_ne_zero)⟩

/-- The only nonleading coefficient whose factorial ratio by itself does
not supply both adjacent factors is just below the leading coefficient;
its binomial factor supplies the missing `m`. -/
theorem mul_succ_dvd_commonDiagonalTallCoeff {m j : ℕ} (hj : j < m) :
    ((m * (m + 1) : ℕ) : ℤ) ∣ commonDiagonalTallCoeff m j := by
  unfold commonDiagonalTallCoeff
  apply dvd_mul_of_dvd_right
  apply Int.natCast_dvd_natCast.mpr
  by_cases h : j + 1 = m
  · subst m
    have hrat : (j + 1 + 1).factorial / (j + 1).factorial = j + 1 + 1 := by
      rw [Nat.factorial_succ (j + 1), Nat.mul_div_cancel _ (Nat.factorial_pos (j + 1))]
    simpa only [Nat.choose_succ_self_right, hrat] using dvd_refl ((j + 1) * (j + 1 + 1))
  cases m with
  | zero => omega
  | succ m =>
    have hf : (j + 1).factorial ∣ m.factorial := Nat.factorial_dvd_factorial (by omega)
    have hs : (m + 1 + 1).factorial = ((m + 1) * (m + 1 + 1)) * m.factorial := by
      rw [Nat.factorial_succ (m + 1), Nat.factorial_succ m]
      ac_rfl
    change (m + 1) * (m + 1 + 1) ∣ (m + 1).choose j *
      ((m + 1 + 1).factorial / (j + 1).factorial)
    rw [hs, Nat.mul_div_assoc _ hf]
    exact dvd_mul_of_dvd_right (Nat.dvd_mul_right _ _) _

/-- For `m ≥ 2`, the odd one of `m,m+1` exceeds one and has an odd prime divisor. -/
theorem exists_odd_prime_dvd_mul_succ {m : ℕ} (hm : 2 ≤ m) :
    ∃ q : ℕ, q.Prime ∧ 2 < q ∧ q ∣ m * (m + 1) := by
  let v := if m % 2 = 0 then m + 1 else m
  have hv1 : v ≠ 1 := by
    dsimp [v]
    split <;> omega
  have hv2 : ¬ 2 ∣ v := by
    rw [Nat.dvd_iff_mod_eq_zero]
    dsimp [v]
    split <;> omega
  have hv : v ∣ m * (m + 1) := by
    dsimp [v]
    split
    · exact Nat.dvd_mul_left _ _
    · exact Nat.dvd_mul_right _ _
  obtain ⟨q, hq, hqv⟩ := Nat.exists_prime_and_dvd hv1
  have hqne : q ≠ 2 := fun h => hv2 (h ▸ hqv)
  have hqle := hq.two_le
  exact ⟨q, hq, by omega, hqv.trans hv⟩

theorem aeval_commonDiagonalTallPolynomial (m : ℕ) (x : ℚ) :
    aeval x (commonDiagonalTallPolynomial m) =
      (-1 : ℚ) ^ m * ((m + 1).factorial : ℚ) * commonDiagonalTallNormalized m (-x) := by
  simp only [commonDiagonalTallPolynomial, commonDiagonalTallNormalized, aeval_def,
    eval₂_finsetSum, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hsign : (-1 : ℚ) ^ m * (-1 : ℚ) ^ j = (-1 : ℚ) ^ (m - j) := calc
    (-1 : ℚ) ^ m * (-1 : ℚ) ^ j =
      (-1 : ℚ) ^ (m - j + j) * (-1 : ℚ) ^ j := by rw [Nat.sub_add_cancel hj']
    _ = (-1 : ℚ) ^ (m - j) * ((-1 : ℚ) * (-1 : ℚ)) ^ j := by
      rw [pow_add, mul_pow, mul_assoc]
    _ = _ := by simp
  change (commonDiagonalTallCoeff m j : ℚ) * x ^ j = _
  have hfd : (j + 1).factorial ∣ (m + 1).factorial :=
    Nat.factorial_dvd_factorial (Nat.succ_le_succ hj')
  simp only [commonDiagonalTallCoeff, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast, Nat.cast_mul, Nat.cast_div_charZero hfd]
  rw [show -x = (-1 : ℚ) * x by simp, mul_pow, ← hsign]
  simp only [div_eq_mul_inv] <;> ring

/-- A rational reciprocal diagonal is ruled out arithmetically, not
by enumerating residues and not by reducing the tableau’s entries. -/
theorem commonDiagonalTallPolynomial_no_rat_root {m : ℕ} (hm : 2 ≤ m) (x : ℚ) :
    aeval x (commonDiagonalTallPolynomial m) ≠ 0 := by
  intro hx
  obtain ⟨q, hq, hqodd, hqdiv⟩ := exists_odd_prime_dvd_mul_succ hm
  letI : Fact q.Prime := ⟨hq⟩
  have hP := commonDiagonalTallPolynomial_monic_degree m
  have hcoeff (j : ℕ) (hj : j < (commonDiagonalTallPolynomial m).natDegree) :
      (q : ℤ) ∣ (commonDiagonalTallPolynomial m).coeff j := by
    rw [hP.2] at hj
    rw [coeff_commonDiagonalTallPolynomial, if_pos hj.le]
    exact (Int.natCast_dvd_natCast.mpr hqdiv).trans (mul_succ_dvd_commonDiagonalTallCoeff hj)
  obtain ⟨z, hz, hzd⟩ :=
    exists_integer_dvd_of_monic_aeval_eq_zero (Nat.prime_iff_prime_int.mp hq) hP.1 hcoeff hx
  change x = (z : ℚ) at hz
  have hS (j : ℕ) (hj : j ∈ (Finset.range (m + 1)).erase 0) : 0 < j :=
    Nat.pos_of_ne_zero (Finset.mem_erase.mp hj).1
  have hn := one_add_factorial_power_sum_ne_zero_of_dvd hqodd
    ((Finset.range (m + 1)).erase 0) hS (fun j => (m.choose j : ℤ)) (dvd_neg.mpr hzd)
  have hseries : commonDiagonalTallNormalized m (-(z : ℚ)) ≠ 0 := by
    unfold commonDiagonalTallNormalized
    rw [← Finset.add_sum_erase _ _ (show 0 ∈ Finset.range (m + 1) by simp)]
    simpa only [Int.cast_natCast, Int.cast_neg, Nat.choose_zero_right, Nat.cast_one,
      pow_zero, Nat.zero_add, Nat.factorial_one, mul_one, div_one] using hn
  rw [hz, aeval_commonDiagonalTallPolynomial] at hx
  have hsign : (-1 : ℚ) ^ m ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
  have hfac : ((m + 1).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  exact (mul_ne_zero (mul_ne_zero hsign hfac) hseries) hx

/-- The scalar from the reviewed native tall-tree constraint cannot
vanish at a rational diagonal in degree at least two. -/
theorem commonDiagonalTallBinomial_ne_zero {m : ℕ} (hm : 2 ≤ m) (x : ℚ) :
    commonDiagonalTallBinomial m x ≠ 0 := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [commonDiagonalTallBinomial_at_zero]
    exact one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
  rw [commonDiagonalTallBinomial_eq_pow_mul_normalized_of_ne_zero m hx]
  refine mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr hx)) ?_
  intro hz
  apply commonDiagonalTallPolynomial_no_rat_root hm (x⁻¹)
  have hz' : commonDiagonalTallNormalized m (-(x⁻¹)) = 0 := by
    simpa only [inv_neg] using hz
  rw [aeval_commonDiagonalTallPolynomial, hz', mul_zero]

end RKResearch.Certified
