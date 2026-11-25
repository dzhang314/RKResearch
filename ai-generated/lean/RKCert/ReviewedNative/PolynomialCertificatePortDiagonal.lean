module
import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import RKCert.ReviewedNative.PolynomialCertificateBox
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic

import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # A common-stop diagonal with exact homogeneous Bernstein coefficients

Different copies of the stop are not enclosed as independent variables.
The two homogeneous coordinates have the same values in every factor.
For a degree-n polynomial the coefficient here equals choose(n,j) times
its usual Bernstein coefficient. No division by a binomial appears. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open scoped BigOperators

section Ring

variable {R : Type*} [CommRing R]

/-- Evaluate the weighted product recursively on a prescribed monomial
functional. At the uniform moment functional this is the actual port. -/
def portRec (mu : ℕ → R) (d : R) : List R → ℕ → R
  | [] => mu
  | r :: rs => fun e => d * portRec mu d rs (e + 1) - r * portRec mu d rs e

def shiftCoeff (f : ℕ → R) : ℕ → R
  | 0 => 0
  | k + 1 => f k

/-- Collect equal powers of the common two endpoint weights before
checking any signs. Coefficients outside 0..n vanish. -/
def diagonalCoeff (mu : ℕ → R) (l u : R) : List R → ℕ → ℕ → R
  | [] => fun e j => if j = 0 then mu e else 0
  | r :: rs => fun e j =>
      (l * diagonalCoeff mu l u rs (e + 1) j - r * diagonalCoeff mu l u rs e j) +
      shiftCoeff (fun k =>
        u * diagonalCoeff mu l u rs (e + 1) k - r * diagonalCoeff mu l u rs e k) j

theorem diagonalCoeff_zero_of_lt (mu : ℕ → R) (l u : R) (rs : List R)
    (e j : ℕ) (h : rs.length < j) : diagonalCoeff mu l u rs e j = 0 := by
  induction rs generalizing e j with
  | nil => have hj : j ≠ 0 := by simpa using Nat.ne_of_gt h
           simp [diagonalCoeff, hj]
  | cons r rs ih =>
    cases j with
    | zero => simp at h
    | succ k =>
      have hk : rs.length < k := by simpa using h
      have hk' : rs.length < k + 1 := Nat.lt.step hk
      simp only [diagonalCoeff, shiftCoeff, ih _ _ hk, ih _ _ hk', mul_zero, sub_zero, add_zero]

def homogeneousValue (n : ℕ) (f : ℕ → R) (a b : R) : R :=
  ∑ j ∈ Finset.range (n + 1), f j * a ^ (n - j) * b ^ j

private theorem hv_add (n : ℕ) (f g : ℕ → R) (a b : R) :
    homogeneousValue n (fun j => f j + g j) a b =
      homogeneousValue n f a b + homogeneousValue n g a b := by
  simp only [homogeneousValue, add_mul, Finset.sum_add_distrib]

private theorem hv_sub (n : ℕ) (f g : ℕ → R) (a b : R) :
    homogeneousValue n (fun j => f j - g j) a b =
      homogeneousValue n f a b - homogeneousValue n g a b := by
  simp only [homogeneousValue, sub_mul, Finset.sum_sub_distrib]

private theorem hv_mul (n : ℕ) (z : R) (f : ℕ → R) (a b : R) :
    homogeneousValue n (fun j => z * f j) a b = z * homogeneousValue n f a b := by
  simp only [homogeneousValue, Finset.mul_sum, mul_assoc]

private theorem hv_extend (n : ℕ) (f : ℕ → R) (hf : f (n + 1) = 0) (a b : R) :
    homogeneousValue (n + 1) f a b = a * homogeneousValue n f a b := by
  unfold homogeneousValue
  rw [Finset.sum_range_succ, hf, zero_mul, zero_mul, add_zero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  have he : n + 1 - j = n - j + 1 := by omega
  rw [he, pow_succ]
  ring

private theorem hv_shift (n : ℕ) (f : ℕ → R) (a b : R) :
    homogeneousValue (n + 1) (shiftCoeff f) a b = b * homogeneousValue n f a b := by
  unfold homogeneousValue
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [shiftCoeff, zero_mul, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  have he : n + 1 - (j + 1) = n - j := by omega
  simp only [he, pow_succ]
  ring

theorem portRec_eq_diagonal (mu : ℕ → R) (l u t : R) (rs : List R) (e : ℕ) :
    portRec mu ((1 - t) * l + t * u) rs e =
      homogeneousValue rs.length (diagonalCoeff mu l u rs e) (1 - t) t := by
  induction rs generalizing e with
  | nil => simp [portRec, diagonalCoeff, homogeneousValue]
  | cons r rs ih =>
      let P := diagonalCoeff mu l u rs (e + 1)
      let Q := diagonalCoeff mu l u rs e
      have zeroL : l * P (rs.length + 1) - r * Q (rs.length + 1) = 0 := by
        simp only [P, Q, diagonalCoeff_zero_of_lt mu l u rs _ _ (Nat.lt_succ_self _),
          mul_zero, sub_zero]
      change ((1 - t) * l + t * u) * portRec mu _ rs (e + 1) - r * portRec mu _ rs e =
        homogeneousValue (rs.length + 1) (fun j =>
          (l * P j - r * Q j) + shiftCoeff (fun k => u * P k - r * Q k) j) _ _
      rw [ih (e + 1), ih e, hv_add, hv_extend _ _ zeroL, hv_shift]
      simp only [hv_sub, hv_mul, P, Q]
      ring

theorem portRec_scale_moments (mu : ℕ → R) (z d : R) (rs : List R) (e : ℕ) :
    portRec (fun j => z * mu j) d rs e = z * portRec mu d rs e := by
  induction rs generalizing e with
  | nil => rfl
  | cons r rs ih => simp only [portRec, ih]; ring

theorem portRec_scale_factors (mu : ℕ → R) (z d : R) (rs : List R) (e : ℕ) :
    portRec mu (z * d) (rs.map (fun r => z * r)) e = z ^ rs.length * portRec mu d rs e := by
  induction rs generalizing e with
  | nil => simp [portRec]
  | cons r rs ih => simp only [List.map_cons, List.length_cons, pow_succ, portRec, ih]; ring

theorem portRec_congr_moments (mu nu : ℕ → R) (d : R) (rs : List R) (e : ℕ)
    (h : ∀ j, e ≤ j → j ≤ e + rs.length → mu j = nu j) : portRec mu d rs e = portRec nu d rs e := by
  induction rs generalizing e with
  | nil => exact h e le_rfl (by simp)
  | cons r rs ih =>
    have hh (j : ℕ) (a : e + 1 ≤ j) (b : j ≤ e + 1 + rs.length) : mu j = nu j :=
      h j (by omega) (by simpa only [List.length_cons] using (show j ≤ e + (rs.length + 1) by omega))
    have hl (j : ℕ) (a : e ≤ j) (b : j ≤ e + rs.length) : mu j = nu j :=
      h j a (by simp only [List.length_cons]; omega)
    simp only [portRec, ih _ hh, ih _ hl]

end Ring

section Ordered

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Strictly positive grouped coefficients give strict positivity even
at t=0 or t=1; only one of the endpoint monomials has to be positive. -/
theorem homogeneousValue_pos (n : ℕ) (f : ℕ → K) {t : K} (ht : t ∈ Set.Icc 0 1)
    (hf : ∀ j ≤ n, 0 < f j) : 0 < homogeneousValue n f (1 - t) t := by
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (mul_nonneg (hf j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).le
      (pow_nonneg (sub_nonneg.mpr ht.2) _)) (pow_nonneg ht.1 _)
  · by_cases h : t = 0
    · refine ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
      simpa [h] using hf 0 (Nat.zero_le _)
    · refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
      have hp : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm h)
      simpa using mul_pos (hf n le_rfl) (pow_pos hp n)

def signedValue (positive : Bool) (z : K) : K := if positive then z else -z

theorem signed_portRec_pos_of_coeff (mu : ℕ → K) (l u : K) (rs : List K) (e : ℕ)
    (positive : Bool) {d : K} (hd : d ∈ Set.Icc l u)
    (h : ∀ j ≤ rs.length, 0 < signedValue positive (diagonalCoeff mu l u rs e j)) :
    0 < signedValue positive (portRec mu d rs e) := by
  obtain ⟨t, ht, hdt⟩ := exists_unit_mix hd
  change d = (1 - t) * l + t * u at hdt
  rw [hdt, portRec_eq_diagonal]
  cases positive with
  | true => exact homogeneousValue_pos _ _ ht h
  | false =>
      have hp := homogeneousValue_pos rs.length (fun j => -(diagonalCoeff mu l u rs e j)) ht h
      simpa only [signedValue, Bool.false_eq_true, if_false, homogeneousValue, neg_mul,
        Finset.sum_neg_distrib] using hp

end Ordered

end RKCert.ReviewedNative.PolynomialCertificate
