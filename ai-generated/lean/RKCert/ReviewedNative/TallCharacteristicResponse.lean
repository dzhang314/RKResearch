module

public import RKCert.ReviewedNative.CommonDiagonalTallObstruction
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.Algebra.Polynomial.OfFn
public import Mathlib.Algebra.Polynomial.Splits
public import Mathlib.RingTheory.Coprime.Lemmas

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The reviewed tall response, using only finite coefficients

Cayley–Hamilton certifies the finite numerator. A rational pair is
identified by a polynomial cross-product equation. Each coefficient
conclusion uses only a finite prefix and cancellation of coprime
polynomials, not a separate formal-series object. -/

namespace RKResearch.Certified.TallFiniteResponse

open RKResearch Polynomial
open scoped Matrix Polynomial BigOperators

noncomputable section

variable {K : Type*} [Field K] {s p : ℕ}

def convolution (Q : K[X]) (u : ℕ → K) (n : ℕ) : K :=
  ∑ i ∈ Finset.range (n+1), Q.coeff i * u (n-i)

def exponentialCoeff (K : Type*) [Field K] (n : ℕ) : K :=
  1 / (n.factorial : K)

/-- Build just the requested finite prefix with the pinned Mathlib
coefficient-vector constructor. -/
def «prefix» (u : ℕ → K) (N : ℕ) : K[X] := by
  classical
  exact Polynomial.ofFn N (fun i => u i.val)

theorem coeff_prefix_lt (u : ℕ → K) {N n : ℕ} (hn : n < N) :
    («prefix» u N).coeff n = u n := by
  classical
  unfold «prefix»
  exact Polynomial.ofFn_coeff_eq_val_of_lt _ hn

theorem coeff_prefix_ge (u : ℕ → K) {N n : ℕ} (hn : N ≤ n) :
    («prefix» u N).coeff n = 0 := by
  classical
  unfold «prefix»
  exact Polynomial.ofFn_coeff_eq_zero_of_ge _ hn

theorem prefix_natDegree_lt (u : ℕ → K) {N : ℕ} (hN : 1 ≤ N) :
    («prefix» u N).natDegree < N := by
  classical
  unfold «prefix»
  exact Polynomial.ofFn_natDegree_lt hN _

theorem coeff_mul_prefix (Q : K[X]) (u : ℕ → K) {N n : ℕ} (hn : n < N) :
    (Q * «prefix» u N).coeff n = convolution Q u n := by
  rw [Polynomial.coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,convolution]
  exact Finset.sum_congr rfl fun i _ => by
    rw [coeff_prefix_lt u ((Nat.sub_le n i).trans_lt hn)]

abbrev moment (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (k : ℕ) : K :=
  b ⬝ᵥ (A^k *ᵥ 1)

/-- These are the scalar coefficients of the actual tall response:
1 in degree zero and the kth physical stage-power moment in degree k+1. -/
def responseCoeff (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) : ℕ → K
  | 0 => 1
  | k+1 => moment A b k

@[simp] theorem responseCoeff_zero (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    responseCoeff A b 0 = 1 := rfl

@[simp] theorem responseCoeff_succ (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (k : ℕ) :
    responseCoeff A b (k+1) = moment A b k := rfl

abbrev denominator (A : Matrix (Fin s) (Fin s) K) : K[X] := A.charpolyRev

def numerator (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) : K[X] :=
  «prefix» (convolution (denominator A) (responseCoeff A b)) (s+1)

theorem denominator_degree_le (A : Matrix (Fin s) (Fin s) K) : (denominator A).natDegree ≤ s := by
  rw [show denominator A = A.charpoly.reverse from (Matrix.reverse_charpoly A).symm]
  simpa only [Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin] using A.charpoly.reverse_natDegree_le

theorem denominator_coeff_zero (A : Matrix (Fin s) (Fin s) K) : (denominator A).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero,Matrix.eval_charpolyRev]

private theorem denominator_reverse_coeff (A : Matrix (Fin s) (Fin s) K) {i : ℕ} (hi : i ≤ s) :
    (denominator A).coeff i = A.charpoly.coeff (s-i) := by
  rw [show denominator A = A.charpoly.reverse from (Matrix.reverse_charpoly A).symm,
    Polynomial.coeff_reverse,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin,Polynomial.revAt_le hi]

/-- Read the usual Cayley–Hamilton identity through the physical
linear output after multiplication by an arbitrary power of A. -/
private theorem cayley_hamilton_moment_sum (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (n : ℕ) :
    (∑ j ∈ Finset.range (s+1), A.charpoly.coeff j * moment A b (n+j)) = 0 := by
  have hp : (∑ j ∈ Finset.range (s+1), A.charpoly.coeff j • A^j) = 0 := by
    simpa only [Polynomial.aeval_eq_sum_range,Matrix.charpoly_natDegree_eq_dim,Fintype.card_fin]
      using Matrix.aeval_self_charpoly A
  have h := congrArg (fun M : Matrix (Fin s) (Fin s) K => b ⬝ᵥ ((A^n*M) *ᵥ 1)) hp
  simpa only [Finset.mul_sum,Matrix.mul_smul,Matrix.sum_mulVec,Matrix.smul_mulVec,
    dotProduct_sum,dotProduct_smul,← pow_add,smul_eq_mul,mul_zero,Matrix.zero_mulVec,dotProduct_zero] using h

private theorem reversed_moment_sum (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (n : ℕ) (hn : s ≤ n) :
    (∑ i ∈ Finset.range (n+1), (denominator A).coeff i * moment A b (n-i)) = 0 := by
  have hsub : Finset.range (s+1) ⊆ Finset.range (n+1) := Finset.range_mono (by omega)
  have hout (i : ℕ) (hi : i ∈ Finset.range (n+1)) (hs : i ∉ Finset.range (s+1)) :
      (denominator A).coeff i * moment A b (n-i) = 0 := by
    have hsi : s < i := by simp only [Finset.mem_range] at hi hs; omega
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((denominator_degree_le A).trans_lt hsi),zero_mul]
  rw [← Finset.sum_subset hsub hout]
  calc
    (∑ i ∈ Finset.range (s+1), (denominator A).coeff i * moment A b (n-i)) =
        ∑ i ∈ Finset.range (s+1),
          A.charpoly.coeff (s+1-1-i) * moment A b (n-s+(s+1-1-i)) := by
      apply Finset.sum_congr rfl
      intro i hi
      have his : i ≤ s := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : n-i = n-s+(s-i) := by omega
      rw [denominator_reverse_coeff A his,he] <;> simp only [Nat.add_sub_cancel]
    _ = 0 := (Finset.sum_range_reflect
      (fun j => A.charpoly.coeff j * moment A b (n-s+j)) (s+1)).trans
      (cayley_hamilton_moment_sum A b (n-s))

theorem response_cutoff (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (n : ℕ) (hn : s < n) : convolution (denominator A) (responseCoeff A b) n = 0 := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hk : s ≤ k := by omega
  change convolution (denominator A) (responseCoeff A b) (k+1) = 0
  have hq : (denominator A).coeff (k+1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((denominator_degree_le A).trans_lt hn)
  unfold convolution
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self,responseCoeff_zero,hq,zero_mul,add_zero]
  calc
    (∑ i ∈ Finset.range (k+1), (denominator A).coeff i * responseCoeff A b (k+1-i)) =
        ∑ i ∈ Finset.range (k+1), (denominator A).coeff i * moment A b (k-i) := by
      apply Finset.sum_congr rfl
      intro i hi
      have his : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
      have he : k+1-i = (k-i)+1 := by omega
      rw [he,responseCoeff_succ]
    _ = 0 := reversed_moment_sum A b k hk

theorem numerator_coeff (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (n : ℕ) :
    (numerator A b).coeff n = convolution (denominator A) (responseCoeff A b) n := by
  unfold numerator
  by_cases hn : n < s+1
  · exact coeff_prefix_lt _ hn
  · rw [coeff_prefix_ge _ (Nat.le_of_not_gt hn)]
    exact (response_cutoff A b n (by omega)).symm

theorem numerator_degree_le (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    (numerator A b).natDegree ≤ s :=
  Nat.le_of_lt_succ (prefix_natDegree_lt _ (Nat.succ_le_succ (Nat.zero_le s)))

/-- The normalized rational representation is a finite algebraic
cross equality against the canonical characteristic pair. -/
structure Fraction (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (P Q : K[X]) : Prop where
  den_zero : Q.coeff 0 = 1
  cross : denominator A * P = Q * numerator A b

theorem physical_fraction (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    Fraction A b (numerator A b) (denominator A) :=
  ⟨denominator_coeff_zero A,rfl⟩

private theorem denominator_X_coprime (A : Matrix (Fin s) (Fin s) K) :
    IsCoprime (X : K[X]) (denominator A) := by
  have hd : (X : K[X]) ∣ denominator A - 1 := by
    exact Polynomial.X_dvd_iff.mpr (by simp [denominator_coeff_zero A])
  obtain ⟨g,hg⟩ := hd
  refine ⟨-g,1,?_⟩
  calc
    (-g)*X + 1*denominator A = denominator A-X*g := by ring
    _ = 1 := by rw [← hg]; ring

private theorem physical_prefix_dvd (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) (N : ℕ) :
    (X : K[X])^N ∣ denominator A * «prefix» (responseCoeff A b) N - numerator A b := by
  apply Polynomial.X_pow_dvd_iff.mpr
  intro n hn
  rw [Polynomial.coeff_sub,coeff_mul_prefix _ _ hn,numerator_coeff,sub_self]

theorem Fraction.prefix_dvd {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (h : Fraction A b P Q) (N : ℕ) :
    (X : K[X])^N ∣ Q * «prefix» (responseCoeff A b) N - P := by
  let R := «prefix» (responseCoeff A b) N
  have hc : IsCoprime ((X : K[X])^N) (denominator A) := (denominator_X_coprime A).pow_left
  apply hc.dvd_of_dvd_mul_left
  change (X : K[X])^N ∣ denominator A * (Q*R - P)
  have he : denominator A * (Q*R - P) = Q * (denominator A * R - numerator A b) := by
    simp only [mul_sub,h.cross,mul_left_comm (denominator A) Q R]
  rw [he]
  exact dvd_mul_of_dvd_right (physical_prefix_dvd A b N) Q

theorem Fraction.convolution_eq {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (h : Fraction A b P Q) (n : ℕ) :
    convolution Q (responseCoeff A b) n = P.coeff n := by
  have hx := (Polynomial.X_pow_dvd_iff.mp (h.prefix_dvd (n+1))) n (Nat.lt_succ_self n)
  rw [Polynomial.coeff_sub,coeff_mul_prefix _ _ (Nat.lt_succ_self n)] at hx
  exact sub_eq_zero.mp hx

theorem Fraction.num_zero {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (h : Fraction A b P Q) : P.coeff 0 = 1 := by
  simpa [convolution,h.den_zero] using (h.convolution_eq 0).symm

theorem denominator_eq_diag_product {A : Matrix (Fin s) (Fin s) K} (hA : A.IsLowerTriangular) :
    denominator A = ∏ i : Fin s, (1 - X * C (A i i)) := by
  let T : Matrix (Fin s) (Fin s) K[X] := 1 - (X : K[X]) • A.map C
  have ht : T.IsLowerTriangular := by
    intro i j hij
    have hlt : i < j := hij
    have hz : A i j = 0 := hA hlt
    simp only [T,Matrix.sub_apply,Matrix.one_apply_ne hlt.ne,Matrix.smul_apply,Matrix.map_apply,
      hz,map_zero,smul_zero,sub_zero]
  change T.det = _
  rw [Matrix.det_of_isLowerTriangular T ht]
  simp only [T,Matrix.sub_apply,Matrix.one_apply_eq,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul]

theorem denominator_splits {A : Matrix (Fin s) (Fin s) K} (hA : A.IsLowerTriangular) :
    (denominator A).Splits := by
  rw [denominator_eq_diag_product hA]
  apply Polynomial.Splits.prod
  intro i _
  apply Polynomial.Splits.of_natDegree_le_one
  have hp : (X*C (A i i)).natDegree ≤ 1 := Polynomial.natDegree_mul_le.trans (by simp)
  exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) hp)

theorem reduced_denominator_dvd {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (h : Fraction A b P Q) (hc : IsCoprime Q P) : Q ∣ denominator A := by
  apply hc.dvd_of_dvd_mul_left
  rw [mul_comm P,h.cross]
  exact dvd_mul_right _ _

theorem reduced_denominator_splits {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (hA : A.IsLowerTriangular) (h : Fraction A b P Q) (hc : IsCoprime Q P) :
    Q.Splits := (denominator_splits hA).of_dvd (by
      intro h0
      have hq := denominator_coeff_zero A
      rw [h0,Polynomial.coeff_zero] at hq
      exact zero_ne_one hq) (reduced_denominator_dvd h hc)

/-- Only the actual paid rooted tall trees are read, via the reviewed
stage-power identity. No order surrogate is assumed. -/
theorem paid_response_coeff {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ho : HasOrder p A b) (n : ℕ) (hn : n ≤ p) :
    responseCoeff A b n = exponentialCoeff K n := by
  cases n with
  | zero => simp [exponentialCoeff]
  | succ k => exact ho.tall_moment_eq_inv_factorial k hn

theorem paid_fraction_coeff {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    {P Q : K[X]} (ho : HasOrder p A b) (h : Fraction A b P Q)
    (n : ℕ) (hn : n ≤ p) : convolution Q (exponentialCoeff K) n = P.coeff n := by
  rw [← h.convolution_eq n]
  unfold convolution
  apply Finset.sum_congr rfl
  intro i _
  rw [paid_response_coeff ho (n-i) ((Nat.sub_le n i).trans hn)]

end
end RKResearch.Certified.TallFiniteResponse
