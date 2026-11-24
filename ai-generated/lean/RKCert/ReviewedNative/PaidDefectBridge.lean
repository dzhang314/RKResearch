module

public import RKCert.ReviewedNative.GradedColumns
public import Mathlib.Data.Matrix.Block
public import Mathlib.LinearAlgebra.Span.Basic

import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

@[expose] public section

/-! # Paid single-defect bridge on actual reviewed tree columns

The proof uses a span of one marked primitive seed followed by a finite
word of actual suffix actions. It assumes neither order of a donor nor
rank of a stage space. -/
namespace RKResearch.Certified.PaidDefectBridge

open RKResearch FiniteRootedTree
open RKResearch.Certified.Graded (mat diag row mat_apply diag_apply row_apply)
open scoped Matrix FiniteRootedTree

abbrev treeSize (t : FiniteRootedTree) : ℕ := t.order
abbrev treeGrade (t : FiniteRootedTree) : ℕ := treeSize t - 1
abbrev forestNat (t : FiniteRootedTree) : ℕ := t.forestFactorial
abbrev factorialNat (t : FiniteRootedTree) : ℕ := t.factorial

private theorem size_pos (t : FiniteRootedTree) : 0 < treeSize t :=
  t.order.pos

private theorem grade_succ (t : FiniteRootedTree) :
    treeGrade t + 1 = treeSize t := by
  have h := size_pos t
  change treeSize t - 1 + 1 = treeSize t
  omega

private theorem grade_join (u v : FiniteRootedTree) :
    treeGrade (u ◂ v) = treeGrade u + treeSize v := by
  have h := size_pos u
  have hsize : treeSize (u ◂ v) = treeSize u + treeSize v := by
    simp only [treeSize, FiniteRootedTree.order, PNat.add_coe]
  change treeSize (u ◂ v) - 1 = (treeSize u - 1) + treeSize v
  rw [hsize]
  omega

private theorem forest_join (u v : FiniteRootedTree) :
    forestNat (u ◂ v) = forestNat u * factorialNat v := by
  simp only [forestNat, factorialNat, FiniteRootedTree.forestFactorial,
    FiniteRootedTree.factorial, PNat.mul_coe]

private theorem factorial_size_forest (t : FiniteRootedTree) :
    factorialNat t = treeSize t * forestNat t := by
  simp only [factorialNat, treeSize, forestNat, FiniteRootedTree.factorial, PNat.mul_coe]

variable {K : Type*} [Field K] {F S : Type*} [Fintype F] [Fintype S]

/-- The scalar tree derivative profile, evaluated on the paid clocks. -/
def idealDerivative (ξ : S → K) (t : FiniteRootedTree) : S → K :=
  (forestNat t : K)⁻¹ • ξ ^ treeGrade t

/-- The corresponding zero-constant primitive profile on the paid clocks. -/
def idealPrimitive (ξ : S → K) (t : FiniteRootedTree) : S → K :=
  (factorialNat t : K)⁻¹ • ξ ^ treeSize t

private theorem idealDerivative_leaf (ξ : S → K) :
    idealDerivative ξ .leaf = 1 := by
  simp [idealDerivative, forestNat, treeGrade, treeSize]

private theorem idealDerivative_join (ξ : S → K) (u v : FiniteRootedTree) :
    idealDerivative ξ (u ◂ v) = idealDerivative ξ u * idealPrimitive ξ v := by
  funext i
  simp only [idealDerivative, idealPrimitive, forest_join, grade_join, Nat.cast_mul,
    mul_inv_rev, Pi.smul_apply, Pi.pow_apply, Pi.mul_apply, smul_eq_mul, pow_add]
  ac_rfl

/-- Prefix-to-suffix and suffix-to-suffix action are literal submatrices. -/
abbrev crossBlock (A : Matrix (F ⊕ S) (F ⊕ S) K) : Matrix S F K :=
  A.submatrix Sum.inr Sum.inl

abbrev suffixBlock (A : Matrix (F ⊕ S) (F ⊕ S) K) : Matrix S S K :=
  A.submatrix Sum.inr Sum.inr

private theorem suffix_mulVec (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (v : F ⊕ S → K) :
    (A *ᵥ v) ∘ Sum.inr =
      crossBlock A *ᵥ (v ∘ Sum.inl) + suffixBlock A *ᵥ (v ∘ Sum.inr) := by
  funext i
  change (∑ j : F ⊕ S, A (Sum.inr i) j * v j) =
    (∑ j : F, A (Sum.inr i) (Sum.inl j) * v (Sum.inl j)) +
    (∑ j : S, A (Sum.inr i) (Sum.inr j) * v (Sum.inr j))
  exact Fintype.sum_sum_type _

/-- The inhomogeneous part of a single actual primitive error. -/
def primitiveSeed (A : Matrix (F ⊕ S) (F ⊕ S) K) (ξ : S → K)
    (t : FiniteRootedTree) : S → K :=
  crossBlock A *ᵥ (Φ t A ∘ Sum.inl) +
    suffixBlock A *ᵥ idealDerivative ξ t - idealPrimitive ξ t

def derivativeError (A : Matrix (F ⊕ S) (F ⊕ S) K) (ξ : S → K)
    (t : FiniteRootedTree) : S → K :=
  (Φ t A ∘ Sum.inr) - idealDerivative ξ t

def primitiveError (A : Matrix (F ⊕ S) (F ⊕ S) K) (ξ : S → K)
    (t : FiniteRootedTree) : S → K :=
  ((A *ᵥ Φ t A) ∘ Sum.inr) - idealPrimitive ξ t

private theorem primitiveError_eq (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (ξ : S → K) (t : FiniteRootedTree) :
    primitiveError A ξ t =
      mat (suffixBlock A) (derivativeError A ξ t) + primitiveSeed A ξ t := by
  rw [primitiveError, suffix_mulVec, derivativeError, map_sub, primitiveSeed]
  simp only [mat_apply]
  abel

private theorem derivativeError_join (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (ξ : S → K) (u v : FiniteRootedTree) :
    derivativeError A ξ (u ◂ v) =
      idealDerivative ξ u * primitiveError A ξ v +
        derivativeError A ξ u * idealPrimitive ξ v +
        derivativeError A ξ u * primitiveError A ξ v := by
  funext i
  simp only [derivativeError, primitiveError, idealDerivative_join, Φ, Function.comp_apply,
    Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  ring

inductive Letter where
  | transport
  | clock

def letterMap (T : Matrix S S K) (ξ : S → K) :
    Letter → (S → K) →ₗ[K] (S → K)
  | .transport => mat T
  | .clock => diag ξ

/-- A word acts with its head on the outside. -/
def wordMap (T : Matrix S S K) (ξ : S → K) :
    List Letter → (S → K) →ₗ[K] (S → K)
  | [] => LinearMap.id
  | c :: W => (letterMap T ξ c).comp (wordMap T ξ W)

section Span

variable (T : Matrix S S K) (ξ : S → K)
    (z : FiniteRootedTree → S → K) (q : ℕ)

/-- All single-seed words whose total primitive grade is at most the budget. -/
def wordGenerators (k : ℕ) : Set (S → K) :=
  {v | ∃ (t : FiniteRootedTree) (W : List Letter),
    q < treeSize t ∧ W.length + treeSize t ≤ k ∧ v = wordMap T ξ W (z t)}

abbrev paidSpan (k : ℕ) : Submodule K (S → K) :=
  Submodule.span K (wordGenerators T ξ z q k)

private theorem paidSpan_mono {k l : ℕ} (h : k ≤ l) :
    paidSpan T ξ z q k ≤ paidSpan T ξ z q l := by
  apply Submodule.span_mono
  rintro _ ⟨t,W,ht,hW,rfl⟩
  exact ⟨t,W,ht,hW.trans h,rfl⟩

private theorem paidSpan_low {k : ℕ} (hk : k ≤ q) :
    paidSpan T ξ z q k = ⊥ := by
  apply le_antisymm _ bot_le
  apply Submodule.span_le.2
  rintro _ ⟨t,W,ht,hW,rfl⟩
  have hf : False := by omega
  exact hf.elim

private theorem eq_zero_of_mem_low {k : ℕ} {v : S → K}
    (hk : k ≤ q) (h : v ∈ paidSpan T ξ z q k) : v = 0 := by
  rw [paidSpan_low T ξ z q hk, Submodule.mem_bot] at h
  exact h

private theorem letter_mem_paidSpan (c : Letter) {k : ℕ} {v : S → K}
    (hv : v ∈ paidSpan T ξ z q k) :
    letterMap T ξ c v ∈ paidSpan T ξ z q (k + 1) := by
  have hmap :
      (paidSpan T ξ z q k).map (letterMap T ξ c) ≤ paidSpan T ξ z q (k + 1) := by
    apply (Submodule.map_span_le (letterMap T ξ c) (wordGenerators T ξ z q k)
      (paidSpan T ξ z q (k + 1))).2
    rintro _ ⟨t,W,ht,hW,rfl⟩
    apply Submodule.subset_span
    have hw' : (c :: W).length + treeSize t ≤ k + 1 := by
      simp only [List.length_cons]
      omega
    exact ⟨t,c :: W,ht,hw',rfl⟩
  exact hmap (Submodule.mem_map_of_mem hv)

private theorem clockPow_mem_paidSpan {k : ℕ} {v : S → K}
    (hv : v ∈ paidSpan T ξ z q k) (m : ℕ) :
    ξ ^ m * v ∈ paidSpan T ξ z q (k + m) := by
  induction m with
  | zero => simpa only [pow_zero, one_mul, Nat.add_zero] using hv
  | succ m ih =>
    have h := letter_mem_paidSpan T ξ z q .clock ih
    change ξ * (ξ ^ m * v) ∈ paidSpan T ξ z q (k + m + 1) at h
    simpa only [pow_succ', mul_assoc, Nat.add_succ] using h

private theorem scaledClockPow_mem_paidSpan {k : ℕ} {v : S → K}
    (hv : v ∈ paidSpan T ξ z q k) (m : ℕ) (a : K) :
    (a • ξ ^ m) * v ∈ paidSpan T ξ z q (k + m) := by
  have e : (a • ξ ^ m) * v = a • (ξ ^ m * v) := by
    funext i
    simp only [Pi.smul_apply, Pi.mul_apply, smul_eq_mul, mul_assoc]
  rw [e]
  exact (paidSpan T ξ z q (k + m)).smul_mem a
    (clockPow_mem_paidSpan T ξ z q hv m)

end Span

abbrev actualPaidSpan (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (ξ : S → K) (q k : ℕ) : Submodule K (S → K) :=
  paidSpan (suffixBlock A) ξ (primitiveSeed A ξ) q k

private theorem primitiveError_mem (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (ξ : S → K) {q p : ℕ}
    (hzero : ∀ t, treeSize t ≤ q → treeSize t < p → primitiveSeed A ξ t = 0)
    (t : FiniteRootedTree) (ht : treeSize t < p)
    (h : derivativeError A ξ t ∈ actualPaidSpan A ξ q (treeGrade t)) :
    primitiveError A ξ t ∈ actualPaidSpan A ξ q (treeSize t) := by
  have hx : mat (suffixBlock A) (derivativeError A ξ t) ∈
      actualPaidSpan A ξ q (treeSize t) := by
    simpa only [letterMap, grade_succ] using
      (letter_mem_paidSpan (suffixBlock A) ξ (primitiveSeed A ξ) q .transport h)
  have hz : primitiveSeed A ξ t ∈ actualPaidSpan A ξ q (treeSize t) := by
    by_cases hs : q < treeSize t
    · apply Submodule.subset_span
      exact ⟨t,[],hs,by simp,rfl⟩
    · rw [hzero t (by omega) ht]
      exact (actualPaidSpan A ξ q (treeSize t)).zero_mem
  rw [primitiveError_eq]
  exact (actualPaidSpan A ξ q (treeSize t)).add_mem hx hz

/-- Below collision grade every actual suffix tree error is a linear
combination of eligible one-seed words. No output order is assumed. -/
theorem derivativeError_mem_paidSpan (A : Matrix (F ⊕ S) (F ⊕ S) K)
    (ξ : S → K) {q p : ℕ} (hgap : p - 1 < 2 * (q + 1))
    (hzero : ∀ t, treeSize t ≤ q → treeSize t < p → primitiveSeed A ξ t = 0)
    (t : FiniteRootedTree) (ht : treeGrade t < p) :
    derivativeError A ξ t ∈ actualPaidSpan A ξ q (treeGrade t) := by
  revert ht
  induction t with
  | leaf =>
    intro _
    have e : derivativeError A ξ .leaf = 0 := by
      funext i
      simp only [derivativeError, idealDerivative_leaf, Φ, Function.comp_apply,
        Pi.one_apply, Pi.sub_apply, sub_self, Pi.zero_apply]
    rw [e]
    exact (actualPaidSpan A ξ q (treeGrade .leaf)).zero_mem
  | butcherProduct u v hu hv =>
    intro ht
    have h : treeGrade u + treeSize v < p := by simpa only [grade_join] using ht
    have hvg := grade_succ v
    have hu' := hu (show treeGrade u < p by omega)
    have hv' := hv (show treeGrade v < p by omega)
    have hprim := primitiveError_mem A ξ hzero v (by omega) hv'
    have hcross : derivativeError A ξ u * primitiveError A ξ v = 0 := by
      by_cases low : treeGrade u ≤ q
      · have e := eq_zero_of_mem_low (suffixBlock A) ξ (primitiveSeed A ξ) q low hu'
        rw [e, zero_mul]
      · have low' : treeSize v ≤ q := by omega
        have e := eq_zero_of_mem_low (suffixBlock A) ξ (primitiveSeed A ξ) q low' hprim
        rw [e, mul_zero]
    have hleft : idealDerivative ξ u * primitiveError A ξ v ∈
        actualPaidSpan A ξ q (treeGrade u + treeSize v) := by
      have hh := scaledClockPow_mem_paidSpan (suffixBlock A) ξ (primitiveSeed A ξ) q
        hprim (treeGrade u) ((forestNat u : K)⁻¹)
      simpa only [idealDerivative, Nat.add_comm (treeSize v) (treeGrade u)] using hh
    have hright : derivativeError A ξ u * idealPrimitive ξ v ∈
        actualPaidSpan A ξ q (treeGrade u + treeSize v) := by
      rw [mul_comm]
      exact scaledClockPow_mem_paidSpan (suffixBlock A) ξ (primitiveSeed A ξ) q
        hu' (treeSize v) ((factorialNat v : K)⁻¹)
    rw [derivativeError_join, hcross, add_zero, grade_join]
    exact (actualPaidSpan A ξ q (treeGrade u + treeSize v)).add_mem hleft hright

private theorem dotProduct_suffix (w : S → K) (v : F ⊕ S → K) :
    (Sum.elim (0 : F → K) w) ⬝ᵥ v = row w (v ∘ Sum.inr) := by
  simp only [row_apply, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_add, Function.comp_apply]

private theorem idealDerivative_paid [CharZero K] {p : ℕ}
    (w ξ : S → K) (hquad : HasQuadratureOrder p w ξ)
    (t : FiniteRootedTree) (ht : treeGrade t < p) :
    (factorialNat t : K) * row w (idealDerivative ξ t) = 1 := by
  have h := hquad (treeGrade t) ht
  have hsize : (treeSize t : K) * (w ⬝ᵥ ξ ^ treeGrade t) = 1 := by
    simpa only [Nat.succ_eq_add_one, grade_succ] using h
  have hn : forestNat t ≠ 0 := ne_of_gt t.forestFactorial.pos
  have hz : (forestNat t : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [idealDerivative, map_smul, factorial_size_forest, Nat.cast_mul]
  simp only [row_apply, smul_eq_mul]
  calc
    _ = ((treeSize t : K) * ((forestNat t : K) * (forestNat t : K)⁻¹)) *
        (w ⬝ᵥ ξ ^ treeGrade t) := by ring
    _ = 1 := by rw [mul_inv_cancel₀ hz, mul_one, hsize]

/-- Exact ordinary reviewed order from actual scalar quadrature and paid
single-primitive cancellations. Prefix weights are zero; no conditions
are imposed on the prefix diagonal, spectra, or stage-space ranks. -/
theorem hasOrder_of_paid_defect_words [CharZero K] {p q : ℕ}
    (A : Matrix (F ⊕ S) (F ⊕ S) K) (w ξ : S → K)
    (hgap : p - 1 < 2 * (q + 1))
    (hquad : HasQuadratureOrder p w ξ)
    (hzero : ∀ t, treeSize t ≤ q → treeSize t < p → primitiveSeed A ξ t = 0)
    (hpaid : ∀ (t : FiniteRootedTree) (W : List Letter), q < treeSize t →
      W.length + treeSize t < p →
      row w (wordMap (suffixBlock A) ξ W (primitiveSeed A ξ t)) = 0) :
    HasOrder p A (Sum.elim (0 : F → K) w) := by
  have paid : actualPaidSpan A ξ q (p - 1) ≤ LinearMap.ker (row w) := by
    apply Submodule.span_le.2
    rintro _ ⟨t,W,ht,hW,rfl⟩
    have hs := size_pos t
    exact LinearMap.mem_ker.2 (hpaid t W ht (by omega))
  intro t ht
  have hn : treeSize t ≤ p := ht
  have hd : treeGrade t < p := by have hs := grade_succ t; omega
  have hm := derivativeError_mem_paidSpan A ξ hgap hzero t hd
  have hm' := paidSpan_mono (suffixBlock A) ξ (primitiveSeed A ξ) q
    (show treeGrade t ≤ p - 1 by omega) hm
  have hz : row w (derivativeError A ξ t) = 0 := LinearMap.mem_ker.1 (paid hm')
  have hrow : row w (Φ t A ∘ Sum.inr) = row w (idealDerivative ξ t) := by
    simpa only [derivativeError, map_sub, sub_eq_zero] using hz
  rw [dotProduct_suffix, hrow]
  exact idealDerivative_paid w ξ hquad t hd

end RKResearch.Certified.PaidDefectBridge
