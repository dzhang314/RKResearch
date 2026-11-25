module

public import RKCert.ReviewedNative.PolynomialCertificateBox
public import Mathlib.RingTheory.Polynomial.Bernstein
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Algebraic Bernstein interval and box certificates

The conversion from power coefficients is proved explicitly. A certificate
can therefore consist of finitely many coefficient inequalities, rather than
an assumed identity at every point of the interval. -/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped BigOperators Polynomial

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def bernsteinWeight (n j : ℕ) (x : K) : K :=
  (bernsteinPolynomial K n j).eval x

theorem bernsteinWeight_formula (n j : ℕ) (x : K) :
    bernsteinWeight n j x = (n.choose j : K) * x ^ j * (1 - x) ^ (n - j) := by
  simp [bernsteinWeight, bernsteinPolynomial, mul_assoc]

theorem bernsteinWeight_nonneg (n j : ℕ) {x : K} (hx : x ∈ Set.Icc 0 1) :
    0 ≤ bernsteinWeight n j x := by
  rw [bernsteinWeight_formula]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hx.1 _))
    (pow_nonneg (sub_nonneg.mpr hx.2) _)

theorem sum_bernsteinWeight (n : ℕ) (x : K) :
    (∑ j ∈ Finset.range (n + 1), bernsteinWeight n j x) = 1 := by
  unfold bernsteinWeight
  rw [← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

private theorem exists_bernsteinWeight_pos (n : ℕ) {x : K} (hx : x ∈ Set.Icc 0 1) :
    ∃ j ∈ Finset.range (n + 1), 0 < bernsteinWeight n j x := by
  by_cases h : x = 0
  · subst x
    refine ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ _), ?_⟩
    simp [bernsteinWeight, bernsteinPolynomial.eval_at_0]
  · have hp : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm h)
    refine ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), ?_⟩
    simpa [bernsteinWeight_formula] using (pow_pos hp n)

/-- The binomial conversion for one monomial. The interval condition is
only needed for the signs below, not for this identity. -/
theorem sum_choose_bernstein_eq_pow {n k : ℕ} (hk : k ≤ n) (x : K) :
    (∑ j ∈ Finset.range (n + 1),
      ((j.choose k : K) / (n.choose k : K)) * bernsteinWeight n j x) = x ^ k := by
  let f (j : ℕ) := ((j.choose k : K) / (n.choose k : K)) * bernsteinWeight n j x
  change (∑ j ∈ Finset.range (n + 1), f j) = x ^ k
  have hsize : n + 1 = k + (n - k + 1) := by omega
  have hfirst : (∑ j ∈ Finset.range k, f j) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [f, Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hj)]
  have hden : (n.choose k : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Nat.choose_pos hk))
  have hshift (j : ℕ) : f (k + j) = x ^ k * bernsteinWeight (n - k) j x := by
    have hsub : n - (k + j) = n - k - j := by omega
    have hkj : k + j - k = j := by omega
    have hon : n.choose (k + j) * (k + j).choose k =
        n.choose k * (n - k).choose j := by
      simpa only [hkj] using
        (Nat.choose_mul (n := n) (k := k + j) (s := k) (by omega))
    have hcast :
        (n.choose (k + j) : K) * ((k + j).choose k : K) =
          (n.choose k : K) * ((n - k).choose j : K) := by
      exact_mod_cast hon
    calc
      f (k + j) =
          ((n.choose (k + j) : K) * ((k + j).choose k : K)) / (n.choose k : K) *
            (x ^ k * x ^ j * (1 - x) ^ (n - k - j)) := by
        simp only [f, bernsteinWeight_formula, pow_add, hsub]
        ring
      _ = x ^ k * bernsteinWeight (n - k) j x := by
        rw [hcast, bernsteinWeight_formula]
        field_simp [hden] <;> ring
  calc
    (∑ j ∈ Finset.range (n + 1), f j) =
        (∑ j ∈ Finset.range k, f j) +
          ∑ j ∈ Finset.range (n - k + 1), f (k + j) := by
      rw [hsize, Finset.sum_range_add]
    _ = x ^ k * ∑ j ∈ Finset.range (n - k + 1), bernsteinWeight (n - k) j x := by
      rw [hfirst, zero_add, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => hshift j
    _ = x ^ k := by rw [sum_bernsteinWeight, mul_one]

/-- Exact degree-n Bernstein coefficient for a polynomial of degree at most n. -/
def bernsteinCoeff (p : K[X]) (n j : ℕ) : K :=
  ∑ k ∈ Finset.range (n + 1), p.coeff k * ((j.choose k : K) / (n.choose k : K))

theorem eval_eq_bernstein_sum (p : K[X]) {n : ℕ} (hd : p.natDegree ≤ n) (x : K) :
    p.eval x =
      ∑ j ∈ Finset.range (n + 1), bernsteinCoeff p n j * bernsteinWeight n j x := by
  calc
    p.eval x = ∑ k ∈ Finset.range (n + 1), p.coeff k * x ^ k :=
      Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hd) x
    _ = ∑ k ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1),
          (p.coeff k * ((j.choose k : K) / (n.choose k : K))) * bernsteinWeight n j x := by
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      rw [← sum_choose_bernstein_eq_pow hkn x, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
    _ = _ := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [bernsteinCoeff, Finset.sum_mul]

theorem eval_mem_Icc_of_bernsteinCoeff {p : K[X]} {n : ℕ} (hd : p.natDegree ≤ n)
    {x a b : K} (hx : x ∈ Set.Icc 0 1)
    (hcoeff : ∀ j ≤ n, bernsteinCoeff p n j ∈ Set.Icc a b) :
    p.eval x ∈ Set.Icc a b := by
  rw [eval_eq_bernstein_sum p hd x]
  constructor
  · calc
      a = ∑ j ∈ Finset.range (n + 1), a * bernsteinWeight n j x := by
        rw [← Finset.mul_sum, sum_bernsteinWeight, mul_one]
      _ ≤ _ := Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_right (hcoeff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).1
          (bernsteinWeight_nonneg n j hx)
  · calc
      _ ≤ ∑ j ∈ Finset.range (n + 1), b * bernsteinWeight n j x :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right (hcoeff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).2
            (bernsteinWeight_nonneg n j hx)
      _ = b := by rw [← Finset.mul_sum, sum_bernsteinWeight, mul_one]

theorem lt_eval_of_bernsteinCoeff {p : K[X]} {n : ℕ} (hd : p.natDegree ≤ n)
    {x a : K} (hx : x ∈ Set.Icc 0 1)
    (hcoeff : ∀ j ≤ n, a < bernsteinCoeff p n j) : a < p.eval x := by
  have hpos : 0 < ∑ j ∈ Finset.range (n + 1),
      (bernsteinCoeff p n j - a) * bernsteinWeight n j x := by
    apply Finset.sum_pos'
    · intro j hj
      exact mul_nonneg
        (sub_nonneg.mpr (hcoeff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))).le)
        (bernsteinWeight_nonneg n j hx)
    · obtain ⟨j, hj, hp⟩ := exists_bernsteinWeight_pos n hx
      exact ⟨j, hj, mul_pos
        (sub_pos.mpr (hcoeff j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hp⟩
  have heq : (∑ j ∈ Finset.range (n + 1),
      (bernsteinCoeff p n j - a) * bernsteinWeight n j x) = p.eval x - a := by
    rw [eval_eq_bernstein_sum p hd x]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_bernsteinWeight, mul_one]
  rw [heq] at hpos
  exact sub_pos.mp hpos

/-- Pull an interval back to the unit interval, allowing equal endpoints. -/
def intervalPullback (p : K[X]) (l u : K) : K[X] :=
  p.comp (C (u - l) * X + C l)

theorem natDegree_intervalPullback_le (p : K[X]) (l u : K) :
    (intervalPullback p l u).natDegree ≤ p.natDegree := by
  have hh : (C (u - l) * X + C l).natDegree ≤ 1 :=
    natDegree_add_le_of_le ((natDegree_C_mul_le _ _).trans natDegree_X.le)
      ((natDegree_C l).trans_le (Nat.zero_le 1))
  calc
    _ ≤ p.natDegree * (C (u - l) * X + C l).natDegree := natDegree_comp_le
    _ ≤ p.natDegree * 1 := Nat.mul_le_mul_left _ hh
    _ = _ := mul_one _

theorem eval_intervalPullback (p : K[X]) (l u t : K) :
    (intervalPullback p l u).eval t = p.eval (mix l u t) := by
  simp only [intervalPullback, Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X]
  congr 1
  unfold mix
  ring

theorem interval_lt_eval_of_bernsteinCoeff {p : K[X]} {n : ℕ} (hd : p.natDegree ≤ n)
    {l u x a : K} (hx : x ∈ Set.Icc l u)
    (hcoeff : ∀ j ≤ n, a < bernsteinCoeff (intervalPullback p l u) n j) :
    a < p.eval x := by
  obtain ⟨t, ht, heq⟩ := exists_unit_mix hx
  have hh := lt_eval_of_bernsteinCoeff ((natDegree_intervalPullback_le p l u).trans hd) ht hcoeff
  rwa [eval_intervalPullback, ← heq] at hh

theorem interval_eval_mem_Icc_of_bernsteinCoeff {p : K[X]} {n : ℕ}
    (hd : p.natDegree ≤ n) {l u x a b : K} (hx : x ∈ Set.Icc l u)
    (hcoeff : ∀ j ≤ n, bernsteinCoeff (intervalPullback p l u) n j ∈ Set.Icc a b) :
    p.eval x ∈ Set.Icc a b := by
  obtain ⟨t, ht, heq⟩ := exists_unit_mix hx
  have hh := eval_mem_Icc_of_bernsteinCoeff ((natDegree_intervalPullback_le p l u).trans hd)
    ht hcoeff
  rwa [eval_intervalPullback, ← heq] at hh

/-- Compose the two certificate consumers: check finitely many Bernstein
coefficients at every factor vertex, then conclude over the full box and
the independent univariate interval. -/
theorem box_interval_lt_eval_of_bernstein_vertices {m n : ℕ}
    {p : (Fin m → K) → K[X]}
    (haff : ∀ t, SeparatelyAffine (fun r => (p r).eval t))
    {l u x : Fin m → K} (hx : ∀ i, x i ∈ Set.Icc (l i) (u i))
    {L U t a : K} (ht : t ∈ Set.Icc L U)
    (hdeg : ∀ e : Fin m → Bool, (p (vertex l u e)).natDegree ≤ n)
    (hcert : ∀ (e : Fin m → Bool) (j : ℕ), j ≤ n →
      a < bernsteinCoeff (intervalPullback (p (vertex l u e)) L U) n j) :
    a < (p x).eval t := by
  apply box_of_vertices (haff t) hx (mixClosed_strictLower a)
  intro e
  exact interval_lt_eval_of_bernsteinCoeff (hdeg e) ht (hcert e)

/-- A polynomial specialization of the general linear-product producer.
The final functional can be the formal integral, a moment or a coefficient. -/
theorem separatelyAffine_polynomial_sub_C {m : ℕ} (L : K[X] →ₗ[K] K)
    (body : K[X]) (g : Fin m → K[X]) :
    SeparatelyAffine (fun r => L (body * ∏ i, (g i - C (r i)))) := by
  refine separatelyAffine_linearMap_product L body
    (fun (i : Fin m) (r : K) => g i - C r) ?_
  intro i a b t
  simp only [Polynomial.smul_eq_C_mul, mix, map_add, map_sub, map_mul, map_one]
  ring

end

end RKCert.ReviewedNative.PolynomialCertificate
