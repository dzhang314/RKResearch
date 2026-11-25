module
public import RKCert.ReviewedNative.ClockLocalAnnihilator
public import RKCert.ReviewedNative.PaidClockCapacityStaircase

@[expose] public section

/-! # Preservation and rank of the clock-local part of the paid staircase -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module

variable {K : Type*} [Field K] {s p : ℕ}

/-- Every paid positive reverse grade has the same clock-local part. Its rank
is capped by the measured rank of grade one, and equality detects actual
clock invariance at that grade. -/
structure PaidClockLocalRank (A : Matrix (Fin s) (Fin s) K)
    (b : Fin s → K) (j n : ℕ) : Prop where
  stablePart : ∀ k, 1 ≤ k → k ≤ n →
    clockLocal (nodes A) (primitiveBack A b k) =
      clockLocal (nodes A) (annih (treeSpace A j))
  rankCap : finrank K (clockLocal (nodes A) (annih (treeSpace A j))) ≤
    finrank K (back A b 0) + 1
  rankExactIff :
    finrank K (clockLocal (nodes A) (annih (treeSpace A j))) = finrank K (back A b 0) + 1 ↔
      (primitiveBack A b 1).map (diag (nodes A)) ≤ primitiveBack A b 1

variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {j n : ℕ}

/-- The consumer needs only the measured staircase and a positive top grade;
no characteristic-zero assumption or further paid grade is used here. -/
theorem paid_clock_local_rank_of_staircase
    (H : PaidClockCapacityStaircase A b j n) (positive : 1 ≤ n) :
    PaidClockLocalRank A b j n := by
  let W := clockLocal (nodes A) (annih (treeSpace A j))
  have byHeight : ∀ m : ℕ, m + 1 ≤ n →
      clockLocal (nodes A) (annih (treeSpace A (j + m))) = W := by
    intro m
    induction m with
    | zero =>
        intro _
        simp only [Nat.add_zero, W]
    | succ m ih =>
        intro hm
        have ht : j + m.succ = j + m + 1 := by omega
        rw [ht, (H.forwardUnit m (by omega)).1, clockLocal_annih_clockStep]
        exact ih (by omega)
  have preserved : ∀ k : ℕ, 1 ≤ k → k ≤ n →
      clockLocal (nodes A) (primitiveBack A b k) = W := by
    intro k hk hkn
    have hn : n - k + 1 ≤ n := by omega
    have hfull := (H.forwardCapacity (n - k) hn).primitiveFull
    rw [show n - (n - k) = k by omega] at hfull
    rw [hfull]
    exact byHeight (n - k) hn
  let P₁ := primitiveBack A b 1
  have first : clockLocal (nodes A) P₁ = W := preserved 1 le_rfl positive
  have inc : W ≤ P₁ := by
    rw [← first]
    exact clockLocal_le (nodes A) P₁
  have rankP : finrank K P₁ = finrank K (back A b 0) + 1 := by
    have base := H.forwardCapacity 0 (by omega)
    exact (base.flagExact 1 (by omega)).2.2
  have cap : finrank K W ≤ finrank K (back A b 0) + 1 :=
    (Submodule.finrank_mono inc).trans rankP.le
  refine ⟨preserved, cap, ?_⟩
  constructor
  · intro rankW
    have dle : finrank K P₁ ≤ finrank K W := (rankP.trans rankW.symm).le
    have e : W = P₁ := Submodule.eq_of_le_of_finrank_le inc dle
    exact (clockLocal_eq_iff (nodes A) P₁).mp (first.trans e)
  · intro stable
    have e : W = P₁ := first.symm.trans ((clockLocal_eq_iff (nodes A) P₁).mpr stable)
    exact (congrArg (fun Q : Submodule K (Fin s → K) => finrank K Q) e).trans rankP

/-- The exact two-height entry point. The second paid height need not be the
height of the saturated first annihilator. -/
theorem paid_clock_local_rank_of_heights [CharZero K]
    (ha : ∀ a d, a ≤ d → A a d = 0) (ho : HasOrder p A b)
    {i : ℕ} (positive : 1 ≤ n) (pay : j + n + 2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n)
    (nextPay : i + (n + 1) + 2 ≤ p)
    (tight : s < finrank K (treeSpace A i) + finrank K (back A b 0) + n + (n + 2) / 2) :
    PaidClockLocalRank A b j n :=
  paid_clock_local_rank_of_staircase
    (paid_clock_capacity_staircase_of_heights (i := i) ha ho pay capacity nextPay tight) positive

end RKResearch.Certified.Graded.Reverse
