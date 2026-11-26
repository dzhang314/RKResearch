module

public import RKResearch.OrderConditions

public section

namespace RKResearch

open FiniteRootedTree

@[expose] def ERK {ι R : Type _} [LinearOrder ι] [Zero R]
    (A : Matrix ι ι R) : Prop :=
  ∀ ⦃i j⦄, i ≤ j → A i j = 0

variable {s : ℕ} {R : Type _} [CommSemiring R] {A : Matrix (Fin s) (Fin s) R}

theorem ERK.Φ_tallTree_eq_zero (hA : ERK A) (n : ℕ+) (i : Fin s)
    (hi : (i : ℕ) + 1 < n) : Φ (tallTree n) A i = 0 := by
  unfold tallTree
  induction n generalizing i with
  | one => cases Nat.lt_of_succ_lt_succ hi
  | succ n ih =>
    simp only [PNat.recOn_succ, Φ, one_mul, Matrix.mulVec_apply_eq_sum]
    apply Finset.sum_eq_zero
    intro j _
    rcases le_or_gt i j with hij | hji
    · exact mul_eq_zero_of_left (hA hij) _
    · exact mul_eq_zero_of_right _
        (ih j (Nat.lt_of_le_of_lt hji (Nat.lt_of_succ_lt_succ hi)))

theorem ERK.order_le_stages [Nontrivial R] {b : Fin s → R} {p : ℕ}
    (hA : ERK A) (hp : HasOrder p A b) : p ≤ s := by
  apply Nat.le_of_not_lt
  intro hsp
  have hz : Φ (tallTree s.succPNat) A = 0 := by
    funext i
    exact hA.Φ_tallTree_eq_zero _ i i.succ.isLt
  simpa only [hz, dotProduct_zero, mul_zero, zero_ne_one] using
    hp (tallTree s.succPNat) (order_tallTree _ ▸ hsp)

end RKResearch
