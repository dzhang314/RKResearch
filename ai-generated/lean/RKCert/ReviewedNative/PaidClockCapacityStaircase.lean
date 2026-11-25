module

public import RKCert.ReviewedNative.ReverseMeasuredCapacity
public import RKCert.ReviewedNative.ReverseClockGain

@[expose] public section

/-! # Exact clock steps from two actually paid tree heights

The first height has saturated measured reverse capacity. A second height
bounds its next primitive reverse flag tightly enough to exclude clock
invariance. The existing Hermite gain pays each paired unit step. All the
submodules are the original physical ones; no terminal mark is assumed. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Advance the actual forward flag and descend the actual reverse flag. -/
private theorem paid_tree_clock_advance
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    {j n : ℕ} (positive : 1 ≤ n) (pay : j+n+2 ≤ p)
    (here : MeasuredReverseCapacity A b j n)
    (escape : ¬ (primitiveBack A b n).map (diag (reflectedClock A)) ≤ primitiveBack A b n) :
    MeasuredReverseCapacity A b (j+1) (n-1) ∧
    treeSpace A (j+1) = treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) ∧
    (treeSpace A j).map (mat A) ≤ treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) := by
  have esc : ¬ (treeSpace A j).map (diag (nodes A)) ≤ treeSpace A j := by
    intro inv
    have yStable : treeSpace A j ≤ (treeSpace A j).comap (diag (reflectedClock A)) := by
      intro v hv
      change diag (reflectedClock A) v ∈ treeSpace A j
      have eq : diag (reflectedClock A) v = v - diag (nodes A) v := by
        ext i
        simp [diag_apply,reflectedClock,sub_mul]
      rw [eq]
      exact (treeSpace A j).sub_mem hv (inv (Submodule.mem_map_of_mem hv))
    apply escape
    rw [here.primitiveFull]
    exact annih_map_diag yStable
  have lt : treeSpace A j < treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) :=
    lt_of_le_of_ne le_sup_left (fun eq => esc (le_sup_right.trans eq.ge))
  have inc : treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) ≤ treeSpace A (j+1) :=
    sup_le (treeSpace_mono A (Nat.le_succ j)) (Submodule.map_le_iff_le_comap.mpr (diag_treeSpace A j))
  have low := Submodule.finrank_lt_finrank_of_lt lt
  have mid := Submodule.finrank_mono inc
  have hpay : (j+1)+(n-1)+2 ≤ p := by omega
  have cap := backward_count ha ho (j+1) (n-1) hpay
  have hereCount := here.stageCount
  have advance : MeasuredReverseCapacity A b (j+1) (n-1) :=
    reverse_capacity_paid_measured ha ho hpay (by omega)
  have split : treeSpace A (j+1) = treeSpace A j ⊔ (treeSpace A j).map (diag (nodes A)) :=
    (Submodule.eq_of_le_of_finrank_le inc (by omega)).symm
  have into : (treeSpace A j).map (mat A) ≤ treeSpace A (j+1) :=
    Submodule.map_le_iff_le_comap.mpr (mat_treeSpace A j)
  exact ⟨advance,split,into.trans split.le⟩

/-- Exact reverse clock escape and paired steps between actual heights.
The last forward height has reverse grade one; grade one need not escape. -/
structure PaidClockCapacityStaircase (A : Matrix (Fin s) (Fin s) K)
    (b : Fin s → K) (j n : ℕ) : Prop where
  reverseEscape : ∀ k, 2 ≤ k → k ≤ n →
    ¬ (primitiveBack A b k).map (diag (reflectedClock A)) ≤ primitiveBack A b k
  reverseUnit : ∀ k, 2 ≤ k → k < n →
    primitiveBack A b (k+1) = primitiveBack A b k ⊔
      (primitiveBack A b k).map (diag (reflectedClock A)) ∧
    (primitiveBack A b k).map (mat A.transpose) ≤ primitiveBack A b k ⊔
      (primitiveBack A b k).map (diag (reflectedClock A))
  forwardCapacity : ∀ m, m+1 ≤ n → MeasuredReverseCapacity A b (j+m) (n-m)
  forwardUnit : ∀ m, m+2 ≤ n →
    treeSpace A (j+m+1) = treeSpace A (j+m) ⊔ (treeSpace A (j+m)).map (diag (nodes A)) ∧
    (treeSpace A (j+m)).map (mat A) ≤ treeSpace A (j+m) ⊔
      (treeSpace A (j+m)).map (diag (nodes A))

/-- The independently paid height `i` caps the next reverse flag. It need
not be the saturated tree height `j`; both payments are explicit. -/
theorem paid_clock_capacity_staircase_of_heights [CharZero K]
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder p A b)
    {i j n : ℕ} (pay : j+n+2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j) + finrank K (back A b 0) + n)
    (nextPay : i+(n+1)+2 ≤ p)
    (tight : s < finrank K (treeSpace A i) + finrank K (back A b 0) + n + (n+2)/2) :
    PaidClockCapacityStaircase A b j n := by
  have start : MeasuredReverseCapacity A b j n := reverse_capacity_paid_measured ha ho pay capacity
  have escape (k : ℕ) (k2 : 2 ≤ k) (kn : k ≤ n) :
      ¬ (primitiveBack A b k).map (diag (reflectedClock A)) ≤ primitiveBack A b k := by
    intro inv
    have gain := reverse_clock_invariant_gain ha ho k (by omega) inv
    rw [(start.flagExact k kn).2.2] at gain
    by_cases eq : k = n
    · subst k
      have upper := Submodule.finrank_mono (primitiveBack_annih ho i (n+1) nextPay)
      have ambient := finrank_annih (treeSpace A i)
      rw [Fintype.card_fin] at ambient
      omega
    · rw [(start.flagExact (k+1) (by omega)).2.2] at gain
      omega
  have advance (m : ℕ) (hm : m+2 ≤ n)
      (current : MeasuredReverseCapacity A b (j+m) (n-m)) :
      MeasuredReverseCapacity A b (j+m+1) (n-m-1) ∧
      treeSpace A (j+m+1) = treeSpace A (j+m) ⊔ (treeSpace A (j+m)).map (diag (nodes A)) ∧
      (treeSpace A (j+m)).map (mat A) ≤ treeSpace A (j+m) ⊔
        (treeSpace A (j+m)).map (diag (nodes A)) :=
    paid_tree_clock_advance ha ho (by omega) (by omega) current (escape (n-m) (by omega) (by omega))
  have slices : ∀ m : ℕ, m+1 ≤ n → MeasuredReverseCapacity A b (j+m) (n-m) := by
    intro m
    induction m with
    | zero =>
        intro _
        simpa only [Nat.add_zero,Nat.sub_zero] using start
    | succ m ih =>
        intro hm
        have next := (advance m (by omega) (ih (by omega))).1
        have hsub : n-m-1 = n-(m+1) := by omega
        simpa only [Nat.succ_eq_add_one,Nat.add_assoc,hsub] using next
  refine ⟨escape,?_,slices,?_⟩
  · intro k k2 kn
    have strict : primitiveBack A b k < primitiveBack A b k ⊔
        (primitiveBack A b k).map (diag (reflectedClock A)) :=
      lt_of_le_of_ne le_sup_left (fun eq => escape k k2 (by omega) (le_sup_right.trans eq.ge))
    have inc : primitiveBack A b k ⊔ (primitiveBack A b k).map (diag (reflectedClock A)) ≤
        primitiveBack A b (k+1) :=
      sup_le (adjointFlag_le_succ (A:=A) (b:=b) (monomialCredit A b) k)
        (adjointFlag_clock (A:=A) (b:=b) (monomialCredit A b) k)
    have low := Submodule.finrank_lt_finrank_of_lt strict
    have r0 := (start.flagExact k (by omega)).2.2
    have r1 := (start.flagExact (k+1) (by omega)).2.2
    have split : primitiveBack A b (k+1) = primitiveBack A b k ⊔
        (primitiveBack A b k).map (diag (reflectedClock A)) :=
      (Submodule.eq_of_le_of_finrank_le inc (by omega)).symm
    refine ⟨split,?_⟩
    rw [← split]
    exact adjointFlag_transpose (A:=A) (b:=b) (monomialCredit A b) k
  · intro m hm
    exact (advance m hm (slices m (by omega))).2

end RKResearch.Certified.Graded.Reverse
