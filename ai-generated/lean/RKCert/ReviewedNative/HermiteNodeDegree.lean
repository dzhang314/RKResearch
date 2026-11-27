module

public import Mathlib.Algebra.Polynomial.FieldDivision

@[expose] public section

/-! Multiplicity bound for the scalar primitive readings in the causal
clean-row argument. No ordering or characteristic-zero hypothesis is needed. -/

namespace RKCert.ReviewedNative.HermiteNodeDegree

open Polynomial

variable {K : Type*} [Field K]

theorem double_roots_card_le (p : K[X]) (S : Finset K) (hp : p ≠ 0)
    (h₀ : ∀ x ∈ S, p.IsRoot x) (h₁ : ∀ x ∈ S, p.derivative.IsRoot x) :
    2 * S.card ≤ p.natDegree := by
  classical
  have hs : S.val + S.val ≤ p.roots := by
    rw [Multiset.le_iff_count]
    intro x
    rw [Multiset.count_add]
    by_cases hx : x ∈ S
    · have hr : 1 < p.rootMultiplicity x :=
        (one_lt_rootMultiplicity_iff_isRoot hp).2 ⟨h₀ x hx, h₁ x hx⟩
      rw [Multiset.count_eq_one_of_mem S.nodup (show x ∈ S.val from hx), count_roots]
      exact hr
    · rw [Multiset.count_eq_zero.mpr (show x ∉ S.val from hx), zero_add]
      exact Nat.zero_le _
  have h := (Multiset.card_le_card hs).trans p.card_roots'
  simpa only [two_mul, Multiset.card_add, Finset.card] using h

/-- Two bounded-degree primitives that agree in value and first derivative
on the distinct set coincide. This includes positive characteristic. -/
theorem eq_of_hermite_read {p q : K[X]} {S : Finset K}
    (hp : p.natDegree < 2*S.card) (hq : q.natDegree < 2*S.card)
    (h₀ : ∀ x ∈ S, p.eval x = q.eval x)
    (h₁ : ∀ x ∈ S, p.derivative.eval x = q.derivative.eval x) :
    p = q := by
  by_contra h
  have hdeg := double_roots_card_le (p-q) S (sub_ne_zero.mpr h)
    (fun x hx => by rw [IsRoot, eval_sub, h₀ x hx, sub_self])
    (fun x hx => by rw [derivative_sub, IsRoot, eval_sub, h₁ x hx, sub_self])
  exact (not_le_of_gt ((natDegree_sub_le p q).trans_lt (max_lt hp hq))) hdeg

end RKCert.ReviewedNative.HermiteNodeDegree

#print axioms RKCert.ReviewedNative.HermiteNodeDegree.double_roots_card_le
#print axioms RKCert.ReviewedNative.HermiteNodeDegree.eq_of_hermite_read
