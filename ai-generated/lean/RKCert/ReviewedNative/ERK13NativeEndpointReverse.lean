module

public import RKCert.ReviewedNative.ERK13NativePenultimate
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # The endpoint prefix has the opposite first-seed behavior

The full method must have zero first reflected seed; its mandatory
last-row order-six output has a nonzero first seed, equally on the
literal 18-stage prefix. Every positive-index reflected row of the
original method has its last nonzero entry at the literal penultimate. -/
namespace RKResearch.Certified.Graded.ERK13NativeFirst
open RKResearch Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Matrix (Fin 19) (Fin 19) K} {b : Fin 19→K}

private theorem last_of_after_penultimate {j : Fin 19} (hj : penultimate19<j) : j=Fin.last 18 := by
  apply Fin.ext
  have := j.isLt
  change 17<j.val at hj
  change j.val=18
  omega

theorem terminal_row_firstSeed_ne13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    firstSeed A (A (Fin.last 18))≠0 := by
  intro seed
  have live : LastActive (A (Fin.last 18)) penultimate19 :=
    ⟨penultimate_feeds_terminal13 ha ho,fun j hj=>by rw [last_of_after_penultimate hj]; exact ha _ _ le_rfl⟩
  exact penultimate_clock_ne_one13 ha ho (live.node_eq_one ha seed)

theorem terminal_prefix_firstSeed_ne13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b) :
    firstSeed (prefixMatrix A (by decide : 18≤19))
      (fun j:Fin 18=>A (Fin.last 18) (Fin.castLE (by decide : 18≤19) j))≠0 := by
  let len : 18≤19 := by decide
  let v : Fin 18→K := fun j=>A (Fin.last 18) (Fin.castLE len j)
  have L : LastActive v (Fin.last 17) :=
    ⟨penultimate_feeds_terminal13 ha ho,fun j hj=>((not_lt_of_ge (Fin.le_last j)) hj).elim⟩
  have clock : nodes (prefixMatrix A len) (Fin.last 17)=nodes A penultimate19 :=
    congrFun (prefix_mulVec ha len (1 : Fin 19→K)) (Fin.last 17)
  intro seed
  exact penultimate_clock_ne_one13 ha ho (clock.symm.trans (L.node_eq_one (prefix_strict_lower ha len) seed))

theorem penultimate_reflected_row13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (k : ℕ) : reflectedStageRow A b (k+1) penultimate19 =
      -(b penultimate19*(1-nodes A penultimate19)^(k+2)) := by
  have cl := (width19_last_node_clean_six ha ho).1
  have after (j : Fin 19) (hj : penultimate19<j) : reflectedStageWeight A b (k+1) j=0 := by
    rw [last_of_after_penultimate hj]
    change b (Fin.last 18) * (1 - nodes A (Fin.last 18))^(k+1) = 0
    rw [cl, sub_self, zero_pow (Nat.succ_ne_zero k), mul_zero]
  have z : (A.transpose*ᵥreflectedStageWeight A b (k+1)) penultimate19=0 :=
    transpose_tail_zero ha after le_rfl
  simp only [reflectedStageRow,Pi.sub_apply,Pi.smul_apply,z,smul_zero,zero_sub,reflectedStageWeight] <;> rfl

theorem penultimate_reflected_rows_ne13 (ha : ∀ i j,i≤j → A i j=0) (ho : HasOrder 13 A b)
    (k : ℕ) : reflectedStageRow A b (k+1) penultimate19≠0 := by
  rw [penultimate_reflected_row13 ha ho,neg_ne_zero]
  exact mul_ne_zero (penultimate_live13 ha ho) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm (penultimate_clock_ne_one13 ha ho))))

end
end RKResearch.Certified.Graded.ERK13NativeFirst
