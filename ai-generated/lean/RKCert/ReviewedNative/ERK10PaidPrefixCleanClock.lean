module

public import RKResearch.ERK
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Fintype.Fin

@[expose] public section

/-! # A clean opening clock must survive before the first live suffix

No rooted polynomial necessity is assumed for arbitrary tableaux.
This is the algebraic gate consumed by constructions paying the two
stated strong suffix conditions with only one impure early starter. -/

namespace RKResearch.Certified.ERK10PaidPrefixCleanClock

open RKResearch
open scoped Matrix

theorem no_suffix_nonzero_of_only_impure
    {s : ℕ} {K : Type*} [Field K]
    {A : Matrix (Fin s) (Fin s) K} (hA : ERK A)
    (c d : Fin s → K) (e : Fin s) (k : ℕ)
    (hprefix : ∀ i : Fin s, i.val < k → i ≠ e → c i=0)
    (hsilent : ∀ i : Fin s, i ≠ e → d i=0)
    (hdefect : c e ≠ 0 → d e ≠ 0)
    (hc : ∀ i : Fin s, k ≤ i.val → (c i)^2 = 2*(A *ᵥ c) i)
    (hd : ∀ i : Fin s, k ≤ i.val → (A *ᵥ d) i=0)
    (i : Fin s) (hi : k ≤ i.val) :
    c i=0 := by
  have hs : ∀ j : Fin s, k ≤ j.val → A j e * c e=0 := by
    intro j hj
    by_cases ce : c e=0
    · simp [ce]
    have hm : (A *ᵥ d) j = A j e * d e := by
      rw [Matrix.mulVec_apply_eq_sum]
      apply Finset.sum_eq_single e
      · intro b hb hbe
        rw [hsilent b hbe,mul_zero]
      · simp
    have he := (mul_eq_zero.mp (hm.symm.trans (hd j hj))).resolve_right (hdefect ce)
    rw [he,zero_mul]
  have aux : ∀ n : ℕ, ∀ j : Fin s, j.val=n → k ≤ n → c j=0 := by
    intro n
    induction n using Nat.strong_induction_on
    next n ih =>
      intro j hj hk
      have hjk : k ≤ j.val := hj.symm ▸ hk
      have hm : (A *ᵥ c) j=0 := by
        rw [Matrix.mulVec_apply_eq_sum]
        apply Finset.sum_eq_zero
        intro b hb
        by_cases hbe : b=e
        · simpa [hbe] using hs j hjk
        by_cases hbj : j ≤ b
        · rw [hA hbj,zero_mul]
        have hlt : b.val < n := by
          rw [←hj]
          exact (show b < j from lt_of_not_ge hbj)
        by_cases hbk : b.val < k
        · rw [hprefix b hbk hbe,mul_zero]
        · rw [ih b.val hlt b rfl (Nat.le_of_not_gt hbk),mul_zero]
      have hq := hc j hjk
      rw [hm,mul_zero] at hq
      exact (mul_eq_zero.mp (by simpa [pow_two] using hq)).elim id id
  exact aux i.val i rfl hi

end RKResearch.Certified.ERK10PaidPrefixCleanClock

#print axioms RKResearch.Certified.ERK10PaidPrefixCleanClock.no_suffix_nonzero_of_only_impure
