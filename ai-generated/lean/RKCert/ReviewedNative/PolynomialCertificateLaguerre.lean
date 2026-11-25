module

public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Data.Fintype.Card

import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section

/-! # An ordered-field Laguerre cut, from split factors

This leaf concerns the original split polynomial, not an unproved claim
that its derivatives split in the base field. No division by evaluation
values, distinct-root hypothesis, analytic Rolle theorem or real closure
is used. The first three Taylor coefficients are the Hasse coefficients,
so twice the last one is the second derivative value.
-/

namespace RKCert.ReviewedNative.PolynomialCertificate

open Polynomial
open scoped Polynomial

noncomputable section

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Signed degree-normalized Laguerre expression for three Hasse coefficients. -/
def laguerreForm (n a b c : K) : K :=
  (n - 1) * b ^ 2 - (2 * n) * (a * c)

/-- Clearing a *positive* old degree gives a perfect square plus the old
form times a nonnegative scalar. Multiplication by the new linear factor
changes the low coefficients as shown. This also works at a root. -/
theorem laguerreForm_linear_step {n a b c : K} (hn : 0 < n)
    (ih : 0 ≤ laguerreForm n a b c) (u : K) :
    0 ≤ laguerreForm (n + 1) (u * a) (a + u * b) (b + u * c) := by
  refine nonneg_of_mul_nonneg_right (a := n) ?_ hn
  calc
    0 ≤ (n * a - u * b) ^ 2 + (n + 1) * u ^ 2 * laguerreForm n a b c :=
      add_nonneg (sq_nonneg _)
        (mul_nonneg (mul_nonneg (add_nonneg hn.le zero_le_one) (sq_nonneg _)) ih)
    _ = n * laguerreForm (n + 1) (u * a) (a + u * b) (b + u * c) := by
      unfold laguerreForm
      ring

/-- The form applied to the three low coefficients of a polynomial. -/
def coeffLaguerreForm (n : K) (q : K[X]) : K :=
  laguerreForm n (q.coeff 0) (q.coeff 1) (q.coeff 2)

private theorem coeffLaguerreForm_linear {n : K} (hn : 0 < n)
    (q : K[X]) (ih : 0 ≤ coeffLaguerreForm n q) (u : K) :
    0 ≤ coeffLaguerreForm (n + 1) ((X + C u) * q) := by
  have c₀ : ((X + C u) * q).coeff 0 = u * q.coeff 0 := by
    rw [add_mul, coeff_add, coeff_X_mul_zero, coeff_C_mul, zero_add]
  have c₁ : ((X + C u) * q).coeff 1 = q.coeff 0 + u * q.coeff 1 := by
    rw [add_mul, coeff_add, coeff_C_mul]
    exact congrArg (fun v => v + u * q.coeff 1) (coeff_X_mul q 0)
  have c₂ : ((X + C u) * q).coeff 2 = q.coeff 1 + u * q.coeff 2 := by
    rw [add_mul, coeff_add, coeff_C_mul]
    exact congrArg (fun v => v + u * q.coeff 2) (coeff_X_mul q 1)
  rw [coeffLaguerreForm, c₀, c₁, c₂]
  exact laguerreForm_linear_step hn ih u

theorem coeffLaguerreForm_C_mul (n d : K) (q : K[X]) :
    coeffLaguerreForm n (C d * q) = d ^ 2 * coeffLaguerreForm n q := by
  simp only [coeffLaguerreForm, laguerreForm, coeff_C_mul]
  ring

/-- Actual product of a multiset of linear factors, with its true factor
count. The singleton case avoids division by zero in the induction. -/
theorem laguerre_nonneg_root_product (rs : Multiset K) :
    0 ≤ coeffLaguerreForm (rs.card : K) ((rs.map (fun r => X - C r)).prod) := by
  induction rs using Multiset.induction_on with
  | empty => simp [coeffLaguerreForm, laguerreForm, coeff_one]
  | cons r rs ih =>
      by_cases h : rs = 0
      · subst rs
        simp [coeffLaguerreForm, laguerreForm, coeff_sub, coeff_X, coeff_C]
      · have hn : 0 < (rs.card : K) := Nat.cast_pos.mpr (Multiset.card_pos.mpr h)
        have step := coeffLaguerreForm_linear hn _ ih (-r)
        simpa only [Multiset.card_cons, Nat.cast_add_one, Multiset.map_cons,
          Multiset.prod_cons, C_neg, sub_eq_add_neg] using step

theorem laguerre_nonneg_of_splits {p : K[X]} (h : p.Splits) :
    0 ≤ coeffLaguerreForm (p.natDegree : K) p := by
  rw [h.natDegree_eq_card_roots]
  calc
    0 ≤ coeffLaguerreForm (p.roots.card : K)
        (C p.leadingCoeff * (p.roots.map (fun r => X - C r)).prod) := by
      rw [coeffLaguerreForm_C_mul]
      exact mul_nonneg (sq_nonneg _) (laguerre_nonneg_root_product _)
    _ = coeffLaguerreForm (p.roots.card : K) p :=
      congrArg (coeffLaguerreForm (p.roots.card : K)) h.eq_prod_roots.symm

/-- Universal split-polynomial inequality at every field point. -/
theorem laguerre_taylor_nonneg_of_splits {p : K[X]} (h : p.Splits) (x : K) :
    0 ≤ coeffLaguerreForm (p.natDegree : K) (p.taylor x) := by
  simpa only [Polynomial.natDegree_taylor] using laguerre_nonneg_of_splits (h.taylor x)

/-- A full-degree injective tuple of actual roots supplies the split
hypothesis; no roots away from the actual parameters need to exist. -/
theorem splits_of_full_site_tuple {n : ℕ} {p : K[X]} (hp : p ≠ 0)
    (hd : p.natDegree = n) {β : Fin n → K} (hi : Function.Injective β)
    (hr : ∀ i, p.IsRoot (β i)) : p.Splits := by
  classical
  let S : Finset K := Finset.univ.image β
  have hcard : S.card = n := by
    change (Finset.univ.image β).card = n
    rw [Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  have hs : ∀ y ∈ S, p.eval y = 0 := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hr i
  have hroots : p.roots = S.val := Polynomial.roots_eq_of_natDegree_le_card_of_ne_zero
    hs (le_of_eq (hd.trans hcard.symm)) hp
  apply Polynomial.splits_iff_card_roots.mpr
  calc
    p.roots.card = S.card := congrArg Multiset.card hroots
    _ = p.natDegree := hcard.trans hd.symm

/-- Four-corner minimum for the product of two arbitrary closed intervals. -/
def intervalProdLower (l u v w : K) : K :=
  min (min (l * v) (u * v)) (min (l * w) (u * w))

private theorem min_mul_le_of_mem {l u a : K} (ha : a ∈ Set.Icc l u) (v : K) :
    min (l * v) (u * v) ≤ a * v := by
  rcases le_total 0 v with hv | hv
  · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right ha.1 hv)
  · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right ha.2 hv)

theorem intervalProdLower_le {l u v w a c : K}
    (ha : a ∈ Set.Icc l u) (hc : c ∈ Set.Icc v w) : intervalProdLower l u v w ≤ a * c := by
  rcases le_total 0 a with h | h
  · exact (min_le_left _ _).trans ((min_mul_le_of_mem ha v).trans (mul_le_mul_of_nonneg_left hc.1 h))
  · exact (min_le_right _ _).trans ((min_mul_le_of_mem ha w).trans (mul_le_mul_of_nonpos_left hc.2 h))

theorem sq_le_endpoint_max {l u b : K} (hb : b ∈ Set.Icc l u) :
    b ^ 2 ≤ max (l ^ 2) (u ^ 2) := by
  rcases le_total 0 b with h | h
  · exact (pow_le_pow_left₀ h hb.2 2).trans (le_max_right _ _)
  · have hs := pow_le_pow_left₀ (neg_nonneg.mpr h) (neg_le_neg hb.1) 2
    simp only [neg_sq] at hs
    exact hs.trans (le_max_left _ _)

/-- This matches the exact strict test on the rational interval table;
its degree is the degree of the polynomial actually being tested. -/
def LaguerreIntervalCut (n : ℕ) (l₀ u₀ l₁ u₁ l₂ u₂ : K) : Prop :=
  ((n : K) - 1) * max (l₁ ^ 2) (u₁ ^ 2) <
    (2 * (n : K)) * intervalProdLower l₀ u₀ l₂ u₂

theorem not_splits_of_laguerre_interval {p : K[X]} {n : ℕ}
    (hd : p.natDegree = n) (hn : 1 ≤ n) (x : K) {l₀ u₀ l₁ u₁ l₂ u₂ : K}
    (h₀ : (p.taylor x).coeff 0 ∈ Set.Icc l₀ u₀)
    (h₁ : (p.taylor x).coeff 1 ∈ Set.Icc l₁ u₁)
    (h₂ : (p.taylor x).coeff 2 ∈ Set.Icc l₂ u₂)
    (cut : LaguerreIntervalCut n l₀ u₀ l₁ u₁ l₂ u₂) : ¬p.Splits := by
  intro hs
  have hbase := laguerre_taylor_nonneg_of_splits hs x
  rw [hd] at hbase
  have lower : (2 * (n : K)) * ((p.taylor x).coeff 0 * (p.taylor x).coeff 2) ≤
      ((n : K) - 1) * ((p.taylor x).coeff 1) ^ 2 := sub_nonneg.mp hbase
  have hcast : (1 : K) ≤ (n : K) := by exact_mod_cast hn
  have hleft := mul_le_mul_of_nonneg_left (sq_le_endpoint_max h₁) (sub_nonneg.mpr hcast)
  have hn0 : (0 : K) ≤ 2 * (n : K) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hright := mul_le_mul_of_nonneg_left (intervalProdLower_le h₀ h₂) hn0
  exact (not_lt_of_ge lower) ((hleft.trans_lt cut).trans_le hright)

/-- The table compiler may clear denominators by one common nonzero
factor for all three coefficients. The scalar need not be positive. -/
theorem not_splits_of_scaled_laguerre_interval {p : K[X]} {n : ℕ}
    (hd : p.natDegree = n) (hn : 1 ≤ n) (x : K) {s : K} (hs : s ≠ 0)
    {l₀ u₀ l₁ u₁ l₂ u₂ : K}
    (h₀ : s * (p.taylor x).coeff 0 ∈ Set.Icc l₀ u₀)
    (h₁ : s * (p.taylor x).coeff 1 ∈ Set.Icc l₁ u₁)
    (h₂ : s * (p.taylor x).coeff 2 ∈ Set.Icc l₂ u₂)
    (cut : LaguerreIntervalCut n l₀ u₀ l₁ u₁ l₂ u₂) : ¬p.Splits := by
  have hdeg : (C s * p).natDegree = n := (Polynomial.natDegree_C_mul hs).trans hd
  have hc (j : ℕ) : ((C s * p).taylor x).coeff j = s * (p.taylor x).coeff j := by
    rw [taylor_mul, taylor_C, coeff_C_mul]
  exact fun hsplit => not_splits_of_laguerre_interval hdeg hn x
    ((hc 0).symm ▸ h₀) ((hc 1).symm ▸ h₁) ((hc 2).symm ▸ h₂) cut (hsplit.C_mul s)

/-- Cast the entire *finite comparison*, including all minima and maxima,
not a result sampled at rational parameter points. -/
theorem laguerreIntervalCut_ratCast {n : ℕ} {l₀ u₀ l₁ u₁ l₂ u₂ : ℚ}
    (h : LaguerreIntervalCut n l₀ u₀ l₁ u₁ l₂ u₂) :
    LaguerreIntervalCut n (l₀ : K) (u₀ : K) (l₁ : K) (u₁ : K) (l₂ : K) (u₂ : K) := by
  unfold LaguerreIntervalCut intervalProdLower at *
  have hh := (Rat.cast_lt (K := K)).2 h
  simpa [pow_two] using hh

end

end RKCert.ReviewedNative.PolynomialCertificate
