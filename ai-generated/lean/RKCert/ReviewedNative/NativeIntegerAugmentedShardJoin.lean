module

public import RKCert.ReviewedNative.NativeIntegerAugmentedTopPay
import Init.Data.List.FinRange

@[expose] public section

/-! Proof-only assembly for checked, disjoint finite key windows.
This module contains no tableau, coefficients, or order-specific constants. -/
namespace RKResearch.Certified.NativeIntegerAugmentedShardJoin

open NativeIntegerSpanClearing NativeIntegerAugmentedChecker NativeIntegerAugmentedTopPay

/-- An actual index is covered only when it lies in this half-open interval. -/
def Slice {r : ℕ} (test : Fin r → Bool) (lo hi : ℕ) : Prop :=
  ∀ i : Fin r, lo ≤ i.val → i.val < hi → test i = true

def blockIndex {r : ℕ} (lo len : ℕ) (bound : lo + len ≤ r) (j : Fin len) : Fin r :=
  ⟨lo + j.val, by have hj := j.isLt; omega⟩

/-- The only integer calculations here are inside the passed test. -/
def checkBlock {r : ℕ} (test : Fin r → Bool) (lo len : ℕ) (bound : lo + len ≤ r) : Bool :=
  checkIndices fun j => test (blockIndex lo len bound j)

theorem slice_of_checkBlock {r lo len : ℕ} {test : Fin r → Bool} (bound : lo + len ≤ r)
    (h : checkBlock test lo len bound = true) : Slice test lo (lo + len) := by
  intro i hi hj
  let j : Fin len := ⟨i.val - lo, by omega⟩
  have same : blockIndex lo len bound j = i := Fin.ext (by
    change lo + (i.val - lo) = i.val
    omega)
  change checkIndices (fun t => test (blockIndex lo len bound t)) = true at h
  have hit : test (blockIndex lo len bound j) = true := checkIndices_get h j
  rw [same] at hit
  exact hit

theorem slice_singleton {r : ℕ} {test : Fin r → Bool} (i : Fin r)
    (h : test i = true) : Slice test i.val (i.val + 1) := by
  intro j hj hb
  have same : j = i := Fin.ext (by omega)
  rw [same]
  exact h

theorem slice_concat {r lo mid hi : ℕ} {test : Fin r → Bool}
    (left : Slice test lo mid) (right : Slice test mid hi) : Slice test lo hi := by
  intro i h0 h1
  by_cases hm : i.val < mid
  · exact left i h0 hm
  · exact right i (Nat.le_of_not_lt hm) h1

/-- A frozen shard may compute with local byte-exact inputs. Transport uses
only equality of the tested statements at its actual indices. -/
theorem slice_congr {r lo hi : ℕ} {f g : Fin r → Bool}
    (eq : ∀ i : Fin r, lo ≤ i.val → i.val < hi → f i = g i)
    (h : Slice f lo hi) : Slice g lo hi := by
  intro i h0 h1
  rw [← eq i h0 h1]
  exact h i h0 h1

theorem checkIndices_of_points {r : ℕ} {test : Fin r → Bool}
    (h : ∀ i, test i = true) : checkIndices test = true := by
  change (List.finRange r).all test = true
  exact List.all_eq_true.mpr fun i _ => h i

theorem checkIndices_of_slice {r : ℕ} {test : Fin r → Bool}
    (h : Slice test 0 r) : checkIndices test = true :=
  checkIndices_of_points fun i => h i (Nat.zero_le _) i.isLt

theorem checkDegrees_of_points {p : ℕ} {test : ℕ → Bool}
    (h : ∀ n, 0 < n → n ≤ p → test n = true) : checkDegrees p test = true := by
  change (List.range p).all (fun n => test (n + 1)) = true
  apply List.all_eq_true.mpr
  intro n hn
  have hn' := List.mem_range.mp hn
  exact h (n + 1) (by omega) (by omega)

theorem actions_of_points {s p : ℕ} {act : ZVec s → ZVec s} {C : Candidate s}
    (h : ∀ l, 0 < l → l < p → ∀ j : Fin (C.rank l), checkAction act C l j = true) :
    checkActions act p C = true := by
  change checkDegrees (p - 1) (fun l => checkIndices (checkAction act C l)) = true
  apply checkDegrees_of_points
  intro l hl hb
  exact checkIndices_of_points (h l hl (by omega))

theorem products_of_points {s p : ℕ} {d : ℤ} {C : Candidate s}
    (h : ∀ k l, 0 < k → 0 < l → k + l ≤ p →
      ∀ (i : Fin (C.rank k)) (j : Fin (C.rank l)), checkProduct d C k l i j = true) :
    checkProducts d p C = true := by
  change checkDegrees p (fun k => checkDegrees (p - k) (fun l =>
    checkIndices (fun i => checkIndices (checkProduct d C k l i)))) = true
  apply checkDegrees_of_points
  intro k hk hkp
  apply checkDegrees_of_points
  intro l hl hlp
  apply checkIndices_of_points
  intro i
  exact checkIndices_of_points (h k l hk hl (by omega) i)

theorem payments_of_points {s p : ℕ} {out : ZVec s → ℤ} {e : ℤ} {C : Candidate s}
    (h : ∀ n, 0 < n → n ≤ p → ∀ i : Fin (C.rank n),
      checkPayment out e n (C.rows n i) = true) : checkPayments out e p C = true := by
  change checkDegrees p (fun n => checkIndices (fun i =>
    checkPayment out e n (C.rows n i))) = true
  apply checkDegrees_of_points
  intro n hn hb
  exact checkIndices_of_points (h n hn hb)

theorem top_of_points {s p : ℕ} {out : ZVec s → ℤ} {d e : ℤ} {C : Candidate s}
    (h : ∀ k l, 0 < k → 0 < l → k + l = p →
      ∀ (i : Fin (C.rank k)) (j : Fin (C.rank l)),
        checkPayment out e p (joinedZ d C k l i j) = true) :
    checkTopPayments out d e p C = true := by
  change checkDegrees (p - 1) (fun k => checkTopPair out d e p C k (p - k)) = true
  apply checkDegrees_of_points
  intro k hk hb
  change checkIndices (fun i : Fin (C.rank k) => checkIndices (fun j : Fin (C.rank (p - k)) =>
    checkPayment out e p (joinedZ d C k (p - k) i j))) = true
  apply checkIndices_of_points
  intro i
  exact checkIndices_of_points (h k (p - k) hk (by omega) (by omega) i)

/-- Only pointwise results about one unchanged candidate are supplied.
No theorem about its computed rank or source hash is an assumption. -/
structure DirectTopPoints {s : ℕ} (act : ZVec s → ZVec s) (out : ZVec s → ℤ)
    (d e : ℤ) (p : ℕ) (C : Candidate s) : Prop where
  order_gt_one : 1 < p
  scales : checkScales d e = true
  leaf : checkLeaf C = true
  actions : ∀ l, 0 < l → l < p → ∀ j : Fin (C.rank l), checkAction act C l j = true
  products : ∀ k l, 0 < k → 0 < l → k + l ≤ p - 1 →
    ∀ (i : Fin (C.rank k)) (j : Fin (C.rank l)), checkProduct d C k l i j = true
  payments : ∀ n, 0 < n → n ≤ p - 1 → ∀ i : Fin (C.rank n),
    checkPayment out e n (C.rows n i) = true
  top : ∀ k l, 0 < k → 0 < l → k + l = p →
    ∀ (i : Fin (C.rank k)) (j : Fin (C.rank l)),
      checkPayment out e p (joinedZ d C k l i j) = true

/-- The unsharded checker is proved true without reducing it on this data. -/
theorem checkDirectTop_of_points {s p : ℕ} {act : ZVec s → ZVec s} {out : ZVec s → ℤ}
    {d e : ℤ} {C : Candidate s} (h : DirectTopPoints act out d e p C) :
    checkDirectTop act out d e p C = true := by
  have hp : 1 < p := h.order_gt_one
  have hpd : decide (1 < p) = true := by simp [hp]
  exact (checkDirectTop_iff act out d e p C).mpr
    ⟨hpd, h.scales, h.leaf, actions_of_points h.actions, products_of_points h.products,
     payments_of_points h.payments, top_of_points h.top⟩

end RKResearch.Certified.NativeIntegerAugmentedShardJoin
