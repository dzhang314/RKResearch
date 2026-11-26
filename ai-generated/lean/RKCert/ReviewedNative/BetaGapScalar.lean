module

public import RKCert.ReviewedNative.FiniteCauchy
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Eval.Degree
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! A finite scalar beta-moment support bound, without a tableau,
a characteristic-zero hypothesis, or distinctness of the measured nodes. -/
namespace RKResearch.Certified.Graded.BetaGapScalar

open Polynomial
open scoped BigOperators Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The endpoint sum eliminates coefficient zero; the remaining square
test is exactly the existing finite Cauchy kernel. -/
theorem betaCoefficients_zero {d r : ℕ} (positive : 0 < d)
    (paid : ∀ n : ℕ, 0 < n → n ≤ d + 2 * r + 1 → (n : K) ≠ 0)
    (a : Fin (r + 2) → K) (endpoint : (∑ j : Fin (r + 2), a j) = 0)
    (test : ∀ i : Fin (r + 1),
      (∑ j : Fin (r + 2), a j / ((d + i.val + j.val : ℕ) : K)) = 0) :
    a = 0 := by
  let den (i : Fin (r + 1)) (j : Fin (r + 2)) : K := ((d + i.val + j.val : ℕ) : K)
  have dn (i : Fin (r + 1)) (j : Fin (r + 2)) : den i j ≠ 0 := by
    have hi := i.isLt
    have hj := j.isLt
    exact paid (d + i.val + j.val) (by omega) (by omega)
  have term (i : Fin (r + 1)) (j : Fin (r + 2)) :
      (j.val : K) * a j / den i j =
        a j - ((d + i.val : ℕ) : K) * (a j / den i j) := by
    let t : K := ((d + i.val : ℕ) : K)
    have num : (j.val : K) = den i j - t := by
      change (j.val : K) = ((d + i.val + j.val : ℕ) : K) - ((d + i.val : ℕ) : K)
      rw [Nat.cast_add (d + i.val) j.val, add_sub_cancel_left]
    calc
      _ = (den i j - t) * a j / den i j :=
        congrArg (fun z : K => z * a j / den i j) num
      _ = den i j * a j / den i j - t * a j / den i j := by
        rw [sub_mul, sub_div]
      _ = _ := by rw [mul_div_cancel_left₀ _ (dn i j), mul_div_assoc]
  have weighted (i : Fin (r + 1)) :
      (∑ j : Fin (r + 2), (j.val : K) * a j / den i j) = 0 := by
    have ti : (∑ j : Fin (r + 2), a j / den i j) = 0 := test i
    calc
      _ = ∑ j : Fin (r + 2), (a j - ((d + i.val : ℕ) : K) * (a j / den i j)) :=
        Finset.sum_congr rfl (fun j _ => term i j)
      _ = 0 := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, endpoint, ti, mul_zero, sub_zero]
  let x : Fin (r + 1) → K := fun i => (i.val : K)
  let y : Fin (r + 1) → K := fun j => ((d + 1 : ℕ) : K) + (j.val : K)
  let a' : Fin (r + 1) → K := fun j => ((j.val + 1 : ℕ) : K) * a j.succ
  have apart {u v : ℕ} (lt : u < v) (bound : v < r + 1) :
      (u : K) ≠ (v : K) := by
    intro e
    have un := paid (v - u) (by omega) (by omega)
    exact un (by rw [Nat.cast_sub lt.le, e, sub_self])
  have hx : Function.Injective x := by
    intro i j e
    change (i.val : K) = (j.val : K) at e
    apply Fin.ext
    rcases lt_trichotomy i.val j.val with h | h | h
    · exact (apart h j.isLt e).elim
    · exact h
    · exact (apart h i.isLt e.symm).elim
  have hy : Function.Injective y := by
    intro i j e
    change ((d + 1 : ℕ) : K) + x i = ((d + 1 : ℕ) : K) + x j at e
    exact hx (add_left_cancel e)
  have hden (i j : Fin (r + 1)) : x i + y j = den i j.succ := by
    simp only [x, y, den, Fin.val_succ, ← Nat.cast_add]
    congr 1
    omega
  have hxy (i j : Fin (r + 1)) : x i + y j ≠ 0 := by
    rw [hden i j]
    exact dn i j.succ
  have rows (i : Fin (r + 1)) :
      (∑ j : Fin (r + 1), a' j / (x i + y j)) = 0 := by
    have e := weighted i
    rw [Fin.sum_univ_succ] at e
    simpa only [Fin.val_zero, Nat.cast_zero, zero_mul, zero_div, zero_add,
      a', hden, Fin.val_succ] using e
  have van := cauchy_kernel x y a' hx hy hxy rows
  have tail (j : Fin (r + 1)) : a j.succ = 0 := by
    have hj := j.isLt
    have un := paid (j.val + 1) (by omega) (by omega)
    have h : ((j.val + 1 : ℕ) : K) * a j.succ = 0 := van j
    exact (mul_eq_zero.mp h).resolve_left un
  have head : a 0 = 0 := by
    have e := endpoint
    rw [Fin.sum_univ_succ] at e
    simpa only [tail, Finset.sum_const_zero, add_zero] using e
  funext j
  change a j = 0
  exact Fin.cases (motive := fun j => a j = 0) head tail j

private theorem eval_fin_coeff (P : K[X]) {n : ℕ} (hp : P.natDegree < n) (v : K) :
    P.eval v = ∑ j : Fin n, P.coeff j.val * v ^ j.val := by
  exact (Polynomial.eval_eq_sum_range' hp v).trans
    (Fin.sum_univ_eq_sum_range (fun j => P.coeff j * v ^ j) n).symm

private theorem one_sub_X_reciprocal_coeff (P : K[X]) (m : ℕ) {r : ℕ}
    (hp : P.natDegree < r + 1) :
    (∑ j : Fin (r + 2), ((1 - X) * P).coeff j.val / ((m + j.val : ℕ) : K)) =
      ∑ j : Fin (r + 1), P.coeff j.val *
        (1 / ((m + j.val : ℕ) : K) - 1 / ((m + j.val + 1 : ℕ) : K)) := by
  have top : P.coeff (r + 1) = 0 := coeff_eq_zero_of_natDegree_lt hp
  have drop :
      (∑ j : Fin (r + 2), P.coeff j.val / ((m + j.val : ℕ) : K)) =
        ∑ j : Fin (r + 1), P.coeff j.val / ((m + j.val : ℕ) : K) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last, top, zero_div, add_zero]
  have shift :
      (∑ j : Fin (r + 2), (X * P).coeff j.val / ((m + j.val : ℕ) : K)) =
        ∑ j : Fin (r + 1), P.coeff j.val / ((m + j.val + 1 : ℕ) : K) := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, coeff_X_mul_zero, zero_div, zero_add,
      Fin.val_succ, coeff_X_mul, Nat.add_assoc]
  calc
    _ = (∑ j : Fin (r + 2), P.coeff j.val / ((m + j.val : ℕ) : K)) -
        (∑ j : Fin (r + 2), (X * P).coeff j.val / ((m + j.val : ℕ) : K)) := by
      simp only [sub_mul, one_mul, coeff_sub, sub_div, Finset.sum_sub_distrib]
    _ = _ := by
      rw [drop, shift, ← Finset.sum_sub_distrib]
      simp only [mul_sub, mul_one_div]

/-- The cleared beta moments force at least r+1 indices. The labels
need not be distinct, and no separate condition on the scalar normalization
is needed. Only the written finite casts must be nonzero. -/
theorem card_succ_le_of_cleared_beta_moments {ι : Type*} [Fintype ι]
    (x w : ι → K) (κ : K) {d r : ℕ} (positive : 0 < d)
    (paid : ∀ n : ℕ, 0 < n → n ≤ d + 2 * r + 1 → (n : K) ≠ 0)
    (moment : ∀ q : ℕ, q ≤ 2 * r →
      κ * ((d + q : ℕ) : K) * ((d + q + 1 : ℕ) : K) *
        (∑ s : ι, w s * x s ^ q) = 1) :
    r + 1 ≤ Fintype.card ι := by
  classical
  by_contra short
  have small : Fintype.card ι ≤ r := by omega
  let P : K[X] := ∏ s : ι, (X - C (x s))
  have pm : P.Monic := Polynomial.monic_prod_X_sub_C x (Finset.univ : Finset ι)
  have pdeg : P.natDegree ≤ r := by
    calc
      P.natDegree ≤ ∑ s : ι, (X - C (x s)).natDegree := natDegree_prod_le _ _
      _ = Fintype.card ι := by simp only [natDegree_X_sub_C, Finset.sum_const,
        nsmul_eq_mul, mul_one, Finset.card_univ, Nat.cast_id]
      _ ≤ r := small
  have pd : P.natDegree < r + 1 := by omega
  have root (s : ι) : P.eval (x s) = 0 := by
    unfold P
    rw [eval_prod]
    refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
    simp only [eval_sub, eval_X, eval_C, sub_self]
  let u : ι → K := fun s => κ * w s
  have normalized (q : ℕ) (hq : q ≤ 2 * r) :
      (∑ s : ι, u s * x s ^ q) =
        1 / ((d + q : ℕ) : K) - 1 / ((d + q + 1 : ℕ) : K) := by
    let l : K := ((d + q : ℕ) : K)
    let h : K := ((d + q + 1 : ℕ) : K)
    have nl : l ≠ 0 := paid (d + q) (by omega) (by omega)
    have nh : h ≠ 0 := paid (d + q + 1) (by omega) (by omega)
    have step : h - l = 1 := by
      change ((d + q + 1 : ℕ) : K) - ((d + q : ℕ) : K) = 1
      rw [Nat.cast_add (d + q) 1, Nat.cast_one, add_sub_cancel_left]
    have pull : (∑ s : ι, u s * x s ^ q) = κ * (∑ s : ι, w s * x s ^ q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _
      simp only [u, mul_assoc]
    have clear : (∑ s : ι, u s * x s ^ q) * (l * h) = 1 := by
      rw [pull]
      calc
        _ = κ * l * h * (∑ s : ι, w s * x s ^ q) := by ac_rfl
        _ = 1 := moment q hq
    change _ = 1 / l - 1 / h
    rw [div_sub_div 1 1 nl nh, one_mul, mul_one, step]
    exact (eq_div_iff (mul_ne_zero nl nh)).mpr clear
  have zeroTest (i : Fin (r + 1)) :
      (∑ j : Fin (r + 1), P.coeff j.val *
        (1 / ((d + i.val + j.val : ℕ) : K) -
          1 / ((d + i.val + j.val + 1 : ℕ) : K))) = 0 := by
    calc
      _ = ∑ j : Fin (r + 1), P.coeff j.val * (∑ s : ι, u s * x s ^ (i.val + j.val)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hi := i.isLt
        have hj := j.isLt
        have hq : i.val + j.val ≤ 2 * r := by omega
        simpa only [Nat.add_assoc] using
          congrArg (fun z : K => P.coeff j.val * z) (normalized _ hq).symm
      _ = ∑ s : ι, ∑ j : Fin (r + 1), P.coeff j.val * (u s * x s ^ (i.val + j.val)) := by
        simp_rw [Finset.mul_sum]
        exact Finset.sum_comm
      _ = ∑ s : ι, (u s * x s ^ i.val) * P.eval (x s) := by
        apply Finset.sum_congr rfl
        intro s _
        rw [eval_fin_coeff P pd, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [pow_add]
        ac_rfl
      _ = 0 := by simp only [root, mul_zero, Finset.sum_const_zero]
  let Q : K[X] := (1 - X) * P
  have qdeg : Q.natDegree < r + 2 := by
    have ld : ((1 - X : K[X]).natDegree) ≤ 1 :=
      (natDegree_sub_le _ _).trans (max_le (by simp) (by simp))
    exact (natDegree_mul_le_of_le ld pdeg).trans_lt (by omega)
  have qeval : Q.eval 1 = 0 := by
    simp only [Q, eval_mul, eval_sub, eval_one, eval_X, sub_self, zero_mul]
  let a : Fin (r + 2) → K := fun j => Q.coeff j.val
  have aSum : (∑ j : Fin (r + 2), a j) = 0 := by
    have e := eval_fin_coeff Q qdeg (1 : K)
    rw [qeval] at e
    simpa only [a, one_pow, mul_one] using e.symm
  have test (i : Fin (r + 1)) :
      (∑ j : Fin (r + 2), a j / ((d + i.val + j.val : ℕ) : K)) = 0 :=
    (one_sub_X_reciprocal_coeff P (d + i.val) pd).trans (zeroTest i)
  have van := betaCoefficients_zero positive paid a aSum test
  have qne : Q ≠ 0 := by
    have oneSub : (1 - X : K[X]) ≠ 0 := by
      rw [show (1 - X : K[X]) = -(X - C (1 : K)) by simp]
      exact neg_ne_zero.mpr (X_sub_C_ne_zero _)
    exact mul_ne_zero oneSub pm.ne_zero
  apply qne
  ext j
  rw [coeff_zero]
  by_cases hj : j < r + 2
  · exact congrFun van (⟨j, hj⟩ : Fin (r + 2))
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

end
end RKResearch.Certified.Graded.BetaGapScalar
