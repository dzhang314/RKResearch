module

public import RKCert.ReviewedNative.ReverseFlag

@[expose] public section

/-! # A jointly invariant reverse mask must pay its own rank
The counted directions enlarge the invariant plane in the original
coordinate space, retaining the causal argument on actual stages.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix
noncomputable section
variable {K : Type*} [Field K] {s p j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- Applying the reflected clock moves the actual weighted power one step. -/
theorem diag_reflectedStageWeight (k : ℕ) :
    diag (reflectedClock A) (reflectedStageWeight A b k) =
      reflectedStageWeight A b (k+1) := by
  ext i
  simp only [diag_apply,reflectedStageWeight,pow_succ]
  ring

private theorem quadratic_as_ops (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    quadraticSeed A b = (2:K) • mat A.transpose (diag (reflectedClock A) b) -
       diag (reflectedClock A) (diag (reflectedClock A) b) := by
  have e : reflectedStageWeight A b 0 = b := by ext i; simp [reflectedStageWeight]
  have d : diag (reflectedClock A) b = reflectedStageWeight A b 1 := by
    simpa only [e] using (diag_reflectedStageWeight (A:=A) (b:=b) 0)
  rw [d,diag_reflectedStageWeight]
  change (((1+1:ℕ):K) • (A.transpose *ᵥ reflectedStageWeight A b 1) - _) =
    (2:K) • (A.transpose *ᵥ reflectedStageWeight A b 1) - _
  norm_num

/-- An invariant reverse plane cannot refund any of the n quadratic
causal gains, even if it intersects the initial adjoint flag. -/
theorem reverse_invariant_rank_debit (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : j+n+2 ≤ p)
    (U : Submodule K (Fin s → K)) (uM : U ≤ annih (treeSpace A j))
    (uN : ∀ v ∈ U, mat A.transpose v ∈ U)
    (uC : ∀ v ∈ U, diag (reflectedClock A) v ∈ U) :
    finrank K U+n ≤ finrank K (annih (treeSpace A j)) := by
  let M := annih (treeSpace A j)
  let W (k : ℕ) := U ⊔ back A b k
  have inM (k : ℕ) (hk : k ≤ n) : W k ≤ M :=
    sup_le uM (back_annih ho j k (by omega))
  have out : diag (reflectedClock A) b ∉ M := by
    intro v
    exact reflected_target_ne_zero ho (by omega) (mem_annih.mp v _ (one_mem_treeSpace A j))
  have strict (k : ℕ) (hk : k < n) : W k < W (k+1) := by
    refine lt_of_le_of_ne (sup_le_sup le_rfl (adjointFlag_le_succ _ _)) ?_
    intro eq
    have left : U ≤ W (k+1) := le_sup_left
    have right : back A b (k+1) ≤ W (k+1) := le_sup_right
    have lift (op : Module.End K (Fin s → K))
        (uop : ∀ v ∈ U, op v ∈ U) (flag : (back A b k).map op ≤ back A b (k+1)) :
        ∀ v ∈ W k, op v ∈ W k := by
      intro v hv
      obtain ⟨u,hu,w,hw,rfl⟩ := Submodule.mem_sup.mp hv
      rw [eq,map_add]
      exact (W (k+1)).add_mem (left (uop u hu))
        (right (flag (Submodule.mem_map_of_mem hw)))
    have seed : quadraticSeed A b ∈ W (k+1) :=
      right (adjointFlag_credit (pairCredit A b) k (Submodule.mem_span_singleton_self _))
    have target := mem_of_invariant_seed Fin.revPerm (mat A.transpose) (causal_transpose ha)
      (reflectedClock A) b (W k) (lift _ uN (adjointFlag_transpose (pairCredit A b) k))
      (lift _ uC (adjointFlag_clock (pairCredit A b) k))
      (by rwa [←quadratic_as_ops,eq])
    exact out (inM k hk.le target)
  have rank (k : ℕ) (hk : k ≤ n) : finrank K U+k ≤ finrank K (W k) := by
    induction k with
    | zero => simpa using Submodule.finrank_mono (le_sup_left : U ≤ W 0)
    | succ k ih =>
      have l := ih (by omega)
      have e := Submodule.finrank_lt_finrank_of_lt (strict k (by omega))
      omega
  exact (rank n le_rfl).trans (Submodule.finrank_mono (inM n le_rfl))

theorem no_joint_invariant_of_paid_capacity (ha : ∀ i j, i ≤ j → A i j = 0)
    (ho : HasOrder p A b) (pay : j+n+2 ≤ p)
    (capacity : s ≤ finrank K (treeSpace A j)+n)
    (U : Submodule K (Fin s → K)) (uM : U ≤ annih (treeSpace A j))
    (uN : ∀ v ∈ U, mat A.transpose v ∈ U)
    (uC : ∀ v ∈ U, diag (reflectedClock A) v ∈ U) : U = ⊥ := by
  have deb := reverse_invariant_rank_debit ha ho pay U uM uN uC
  have dim := finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at dim
  exact Submodule.finrank_eq_zero.mp (by omega)

end
end RKResearch.Certified.Graded.Reverse
