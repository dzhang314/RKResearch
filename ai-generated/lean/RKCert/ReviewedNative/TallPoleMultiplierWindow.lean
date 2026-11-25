module

public import RKCert.ReviewedNative.TallCharacteristicResponse

import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Finite tall coefficient windows for a supplied derivative multiplier

The proof consumes polynomial equalities and degree endpoints, not a
particular gcd implementation, a split field or any ordering. The last
right-hand coefficient is exactly the one that shifts the zero window
back by one index. -/

namespace RKResearch.Certified.TallFiniteResponse

open RKResearch Polynomial
open scoped Polynomial Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

abbrev expConvolution (Q : K[X]) (n : ℕ) : K :=
  convolution Q (exponentialCoeff K) n

/-- Minimal certificate for a backward zero window of length `d+1`.
Neither `V.coeff 0 ≠ 0` nor squarefreeness is needed by the consumer. -/
structure PoleMultiplier (Q : K[X]) (d : ℕ) (V B : K[X]) : Prop where
  mul_derivative : V*Q.derivative = B*Q
  v_degree : V.natDegree ≤ d
  sum_degree : (V+B).natDegree ≤ d
  sum_top : (V+B).coeff d ≠ 0

variable {Q V B : K[X]} {d : ℕ}

/-- Standard squarefree cofactor shape; includes the `d=0, B=0` case.
The producer may use divisibility or some other exact certificate. -/
theorem PoleMultiplier.of_boundary (hm : V*Q.derivative = B*Q)
    (hv : V.natDegree ≤ d) (hb : B.natDegree ≤ d)
    (ht : V.coeff d ≠ 0) (hb₀ : B.coeff d = 0) : PoleMultiplier Q d V B := by
  refine ⟨hm, hv, Polynomial.natDegree_add_le_of_degree_le hv hb, ?_⟩
  simpa only [Polynomial.coeff_add, hb₀, add_zero] using ht

private theorem expCoeff_succ_mul [CharZero K] (n : ℕ) :
    exponentialCoeff K (n+1) * ((n+1 : ℕ) : K) = exponentialCoeff K n := by
  have hsucc : ((n+1 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  have hfac : (n.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  unfold exponentialCoeff
  rw [Nat.factorial_succ, Nat.cast_mul]
  apply (eq_div_iff_mul_eq hfac).mpr
  rw [mul_assoc]
  exact div_mul_cancel₀ 1 (mul_ne_zero hsucc hfac)

/-- At coefficient `k` use the prefix through degree `k+1`, not `k`. -/
private theorem expPrefix_diff_dvd [CharZero K] (k : ℕ) :
    (X : K[X])^(k+1) ∣ («prefix» (exponentialCoeff K) (k+2)).derivative -
      «prefix» (exponentialCoeff K) (k+2) := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro i hi
  have hi₁ : i+1 < k+2 := by omega
  have hi₀ : i < k+2 := by omega
  rw [Polynomial.coeff_sub, Polynomial.coeff_derivative,
    coeff_prefix_lt (exponentialCoeff K) hi₁, coeff_prefix_lt (exponentialCoeff K) hi₀]
  apply sub_eq_zero.mpr
  simpa only [Nat.cast_succ] using (expCoeff_succ_mul (K := K) i)

/-- Only the indices through `d` can contribute once `d≤k`. -/
private theorem coeff_mul_of_left_degree (S F : K[X]) {d k : ℕ}
    (hd : S.natDegree ≤ d) (hk : d ≤ k) :
    (S*F).coeff k = ∑ i ∈ Finset.range (d+1), S.coeff i * F.coeff (k-i) := by
  calc
    (S*F).coeff k = ∑ ij ∈ Finset.antidiagonal k, S.coeff ij.1 * F.coeff ij.2 :=
      Polynomial.coeff_mul S F k
    _ = ∑ i ∈ Finset.range (k+1), S.coeff i * F.coeff (k-i) :=
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => S.coeff i * F.coeff j) k
    _ = ∑ i ∈ Finset.range (d+1), S.coeff i * F.coeff (k-i) := by
      symm
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hk))
      intro i _ hi
      have hlt : d < i := by simp only [Finset.mem_range] at hi; omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd.trans_lt hlt), zero_mul]

/-- From the `d+1` zeros starting at `j+1`, earn the preceding zero.
All natural subtractions on the proof side occur at legal indices. -/
theorem PoleMultiplier.backward [CharZero K] (h : PoleMultiplier Q d V B) (j : ℕ)
    (hw : ∀ i : ℕ, i ≤ d → expConvolution Q (j+1+i) = 0) :
    expConvolution Q j = 0 := by
  let k := j+d
  let U := «prefix» (exponentialCoeff K) (k+2)
  let F := Q*U
  have hdk : d ≤ k := by dsimp [k]; omega
  have hk : k = j+d := rfl
  have hpoly : V*F.derivative - (V+B)*F = (V*Q)*(U.derivative-U) := by
    change V*(Q*U).derivative - (V+B)*(Q*U) = (V*Q)*(U.derivative-U)
    calc
      V*(Q*U).derivative - (V+B)*(Q*U) =
          (V*Q.derivative)*U+(V*Q)*U.derivative-(V+B)*(Q*U) := by
        rw [Polynomial.derivative_mul]
        ring
      _ = _ := by rw [h.mul_derivative]; ring
  have hdiv : (X : K[X])^(k+1) ∣ V*F.derivative - (V+B)*F := by
    rw [hpoly]
    exact dvd_mul_of_dvd_right (expPrefix_diff_dvd (K := K) k) (V*Q)
  have hz := (Polynomial.X_pow_dvd_iff.mp hdiv) k (Nat.lt_succ_self k)
  rw [Polynomial.coeff_sub] at hz
  have hF {n : ℕ} (hn : n < k+2) : F.coeff n = expConvolution Q n :=
    coeff_mul_prefix Q (exponentialCoeff K) hn
  have hwin {n : ℕ} (hlo : j+1 ≤ n) (hhi : n ≤ k+1) : F.coeff n = 0 := by
    rw [hF (n := n) (by omega)]
    have hi : n-(j+1) ≤ d := by omega
    have he : j+1+(n-(j+1)) = n := by omega
    simpa only [he] using hw (n-(j+1)) hi
  have hleft : (V*F.derivative).coeff k = 0 := by
    rw [coeff_mul_of_left_degree V F.derivative h.v_degree hdk]
    apply Finset.sum_eq_zero
    intro i hi
    have hid : i ≤ d := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hlo : j+1 ≤ k-i+1 := by omega
    have hhi : k-i+1 ≤ k+1 := by omega
    simp only [Polynomial.coeff_derivative, hwin hlo hhi, zero_mul, mul_zero]
  have hright : ((V+B)*F).coeff k = (V+B).coeff d * F.coeff j := by
    rw [coeff_mul_of_left_degree (V+B) F h.sum_degree hdk, Finset.sum_range_succ]
    have hsmall : (∑ i ∈ Finset.range d, (V+B).coeff i * F.coeff (k-i)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hid : i < d := Finset.mem_range.mp hi
      have hlo : j+1 ≤ k-i := by omega
      have hhi : k-i ≤ k+1 := by omega
      rw [hwin hlo hhi, mul_zero]
    have he : k-d = j := by omega
    simp only [hsmall, zero_add, he]
  have hEq : (V*F.derivative).coeff k = ((V+B)*F).coeff k := sub_eq_zero.mp hz
  have hprod : (V+B).coeff d * F.coeff j = 0 := by rw [← hright, ← hEq, hleft]
  have hj : j < k+2 := by omega
  exact (hF hj).symm.trans ((mul_eq_zero.mp hprod).resolve_left h.sum_top)

private theorem expConvolution_at_zero (hQ : Q.coeff 0 = 1) : expConvolution Q 0 = 1 := by
  simp [expConvolution, convolution, exponentialCoeff, hQ]

/-- Normalization prevents a full `d+1` block at every natural index. -/
theorem PoleMultiplier.not_zero_window [CharZero K] (h : PoleMultiplier Q d V B)
    (hQ : Q.coeff 0 = 1) (n : ℕ) :
    ¬ (∀ i : ℕ, i ≤ d → expConvolution Q (n+i) = 0) := by
  induction n with
  | zero =>
    intro hw
    have hz : expConvolution Q 0 = 0 := hw 0 (Nat.zero_le d)
    exact one_ne_zero ((expConvolution_at_zero hQ).symm.trans hz)
  | succ n ih =>
    intro hw
    have hn : expConvolution Q n = 0 := h.backward n (fun i hi => hw i hi)
    apply ih
    intro i hi
    cases i with
    | zero => simpa only [Nat.add_zero] using hn
    | succ i =>
      have he : n+(i+1) = (n+1)+i := by omega
      change expConvolution Q (n+(i+1)) = 0
      rw [he]
      exact hw i (by omega)

theorem PoleMultiplier.order_le_num_add_of_coeff_prefix [CharZero K]
    (h : PoleMultiplier Q d V B) (hQ : Q.coeff 0 = 1)
    {P : K[X]} {p : ℕ} (hpaid : ∀ n : ℕ, n ≤ p → expConvolution Q n = P.coeff n) :
    p ≤ P.natDegree+d := by
  by_contra hp
  apply h.not_zero_window hQ (P.natDegree+1)
  intro i hi
  have hnp : P.natDegree+1+i ≤ p := by omega
  have hdeg : P.natDegree < P.natDegree+1+i := by omega
  exact (hpaid _ hnp).trans (Polynomial.coeff_eq_zero_of_natDegree_lt hdeg)

variable {s p : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {P : K[X]}

/-- Literal reviewed order; a scalar budget, not an order transfer to a
smaller tableau. No coprimality or splitting assumption enters. -/
theorem Fraction.order_le_num_add_of_multiplier [CharZero K] (hf : Fraction A b P Q)
    (hm : PoleMultiplier Q d V B) (ho : HasOrder p A b) : p ≤ P.natDegree+d :=
  hm.order_le_num_add_of_coeff_prefix hf.den_zero (paid_fraction_coeff ho hf)

end
end RKResearch.Certified.TallFiniteResponse
