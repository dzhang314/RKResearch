module
public import RKCert.ReviewedNative.RowAnnihilator
public import RKCert.ReviewedNative.ReflectedMoments
public import RKCert.ReviewedNative.CausalStage

@[expose] public section

/-! # Paid physical reverse flags on reviewed tableaux

The two-row and all-monomial versions share the same flag constructor,
chronological growth proof and annihilator budget. Polynomials do not
require an old tree representation.
-/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch FiniteRootedTree Module
open scoped Matrix

variable {K : Type*} [Field K] {s p : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
noncomputable section

abbrev firstSeed (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :=
  reflectedStageRow A b 0

abbrev quadraticSeed (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :=
  reflectedStageRow A b 1

def adjointFlag (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (credit : ℕ → Submodule K (Fin s → K)) : ℕ → Submodule K (Fin s → K)
  | 0 => K ∙ firstSeed A b
  | n+1 =>
    let V := adjointFlag A b credit n
    V ⊔ V.map (mat A.transpose) ⊔ V.map (diag (reflectedClock A)) ⊔ credit n

abbrev pairCredit (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (_ : ℕ) : Submodule K (Fin s → K) := K ∙ quadraticSeed A b

def monomialCredit (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K)
    (n : ℕ) : Submodule K (Fin s → K) :=
  Submodule.span K (Set.range (fun k : Fin (n+2) => reflectedStageRow A b k.val))

abbrev back (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :=
  adjointFlag A b (pairCredit A b)

abbrev primitiveBack (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :=
  adjointFlag A b (monomialCredit A b)

theorem adjointFlag_mono_credit
    {U W : ℕ → Submodule K (Fin s → K)} (inc : ∀ n, U n ≤ W n) :
    ∀ n, adjointFlag A b U n ≤ adjointFlag A b W n
  | 0 => le_rfl
  | n+1 =>
    sup_le_sup (sup_le_sup (sup_le_sup (adjointFlag_mono_credit inc n)
      (Submodule.map_mono (adjointFlag_mono_credit inc n)))
      (Submodule.map_mono (adjointFlag_mono_credit inc n))) (inc n)

theorem adjointFlag_le_succ (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) :
    adjointFlag A b C n ≤ adjointFlag A b C (n+1) :=
  le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem adjointFlag_transpose (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) :
    (adjointFlag A b C n).map (mat A.transpose) ≤ adjointFlag A b C (n+1) :=
  le_sup_right.trans (le_sup_left.trans le_sup_left)

theorem adjointFlag_clock (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) :
    (adjointFlag A b C n).map (diag (reflectedClock A)) ≤ adjointFlag A b C (n+1) :=
  le_sup_right.trans le_sup_left

theorem adjointFlag_credit (C : ℕ → Submodule K (Fin s → K)) (n : ℕ) :
    C n ≤ adjointFlag A b C (n+1) := le_sup_right

theorem monomial_mem_credit (n k : ℕ) (hk : k≤n+1) :
    reflectedStageRow A b k ∈ monomialCredit A b n :=
  Submodule.subset_span ⟨⟨k,by omega⟩,rfl⟩

theorem back_le_primitiveBack (n : ℕ) : back A b n ≤ primitiveBack A b n := by
  apply adjointFlag_mono_credit
  intro k
  exact (Submodule.span_singleton_le_iff_mem ..).mpr
    (monomial_mem_credit (A:=A) (b:=b) k 1 (by omega))

theorem reflectedClock_treeSpace (A : Matrix (Fin s) (Fin s) K) (j : ℕ) :
    treeSpace A j ≤ (treeSpace A (j+1)).comap (diag (reflectedClock A)) := by
  intro v hv
  have e : diag (reflectedClock A) v = v-diag (nodes A) v := by
    ext i
    simp [reflectedClock,sub_mul]
  change diag (reflectedClock A) v ∈ treeSpace A (j+1)
  rw [e]
  exact (treeSpace A (j+1)).sub_mem (treeSpace_mono A (by omega) hv) (diag_treeSpace A j hv)

theorem reflectedStageRow_annih (ho : HasOrder A b p) (j k : ℕ) (pay : j+k+2≤p) :
    reflectedStageRow A b k ∈ annih (treeSpace A j) := by
  apply mem_annih.mpr
  intro v hv
  exact reflectedStageRow_treeSpace ho j k pay hv

theorem adjointFlag_annih (ho : HasOrder A b p) (C : ℕ → Submodule K (Fin s → K))
    (paid : ∀ j n, j+n+3≤p → C n ≤ annih (treeSpace A j))
    (j n : ℕ) (pay : j+n+2≤p) :
    adjointFlag A b C n ≤ annih (treeSpace A j) := by
  induction n generalizing j with
  | zero =>
    change (K ∙ firstSeed A b) ≤ annih (treeSpace A j)
    exact (Submodule.span_singleton_le_iff_mem (firstSeed A b) _).mpr
      (reflectedStageRow_annih ho j 0 (by omega))
  | succ n ih =>
    have cut := ih (j+1) (by omega)
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    exact sup_le (sup_le (sup_le (ih j (by omega))
      ((Submodule.map_mono cut).trans (annih_map_transpose (mat_treeSpace A j))))
      ((Submodule.map_mono cut).trans (annih_map_diag (reflectedClock_treeSpace A j))))
      (paid j n (by omega))

theorem paid_pairCredit (ho : HasOrder A b p) (j n : ℕ) (pay : j+n+3≤p) :
    pairCredit A b n ≤ annih (treeSpace A j) :=
  (Submodule.span_singleton_le_iff_mem ..).mpr (reflectedStageRow_annih ho j 1 (by omega))

theorem paid_monomialCredit (ho : HasOrder A b p) (j n : ℕ) (pay : j+n+3≤p) :
    monomialCredit A b n ≤ annih (treeSpace A j) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨k,rfl⟩
  exact reflectedStageRow_annih ho j k.val (by have := k.isLt; omega)

theorem back_annih (ho : HasOrder A b p) (j n : ℕ) (pay : j+n+2≤p) :
    back A b n ≤ annih (treeSpace A j) :=
  adjointFlag_annih ho _ (paid_pairCredit ho) j n pay

theorem primitiveBack_annih (ho : HasOrder A b p) (j n : ℕ) (pay : j+n+2≤p) :
    primitiveBack A b n ≤ annih (treeSpace A j) :=
  adjointFlag_annih ho _ (paid_monomialCredit ho) j n pay

private theorem quadraticSeed_exact (A : Matrix (Fin s) (Fin s) K) (b : Fin s → K) :
    quadraticSeed A b = (2:K) • mat A.transpose (diag (reflectedClock A) b) -
      diag (reflectedClock A) (diag (reflectedClock A) b) := by
  have r₁ : reflectedStageWeight A b 1=diag (reflectedClock A) b := by
    ext i
    simp [reflectedStageWeight,mul_comm]
  have r₂ : reflectedStageWeight A b (1+1)=diag (reflectedClock A) (diag (reflectedClock A) b) := by
    ext i
    simp only [reflectedStageWeight,diag_apply]
    ring
  change reflectedStageRow A b 1 =
    (2:K) • (A.transpose *ᵥ diag (reflectedClock A) b) -
      diag (reflectedClock A) (diag (reflectedClock A) b)
  rw [reflectedStageRow,r₁,r₂]
  norm_num

theorem one_mem_treeSpace (A : Matrix (Fin s) (Fin s) K) (j : ℕ) :
    (1 : Fin s→K) ∈ treeSpace A j := by
  have h : ((FiniteRootedTree.leaf.order : ℕ))≤j+1 := by simp [FiniteRootedTree.order]
  simpa using Φ_mem_treeSpace A .leaf h

theorem reflected_target_ne_zero (ho : HasOrder A b p) (hp : 2≤p) :
    row (diag (reflectedClock A) b) 1 ≠ 0 := by
  have z : row (diag (reflectedClock A) b) 1 =
      stageMass b (nodes A) 0 - stageMass b (nodes A) 1 := by
    simp only [row_apply,stageMass,dotProduct,diag_apply,Pi.one_apply,mul_one,Pi.pow_apply,
      pow_zero,pow_one,←Finset.sum_sub_distrib,reflectedClock,Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h₀ : stageMass b (nodes A) 0=1 := by simpa using ho.bushy_moment 0 (by omega)
  have h₁ : (2:K)*stageMass b (nodes A) 1=1 := by simpa using ho.bushy_moment 1 hp
  have d : (2:K)*row (diag (reflectedClock A) b) 1=1 := by
    rw [z]
    linear_combination 2*h₀-h₁
  intro e
  rw [e,mul_zero] at d
  exact zero_ne_one d

private theorem flag_strict (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (C : ℕ → Submodule K (Fin s → K))
    (paid : ∀ j n, j+n+3≤p → C n ≤ annih (treeSpace A j))
    (creditSecond : ∀ n, quadraticSeed A b∈C n) (n : ℕ) (pay : n+3≤p) :
    adjointFlag A b C n < adjointFlag A b C (n+1) := by
  refine lt_of_le_of_ne (adjointFlag_le_succ C n) ?_
  intro eq
  have yes : diag (reflectedClock A) b ∈ adjointFlag A b C n := by
    apply mem_of_invariant_seed Fin.revPerm (mat A.transpose) (causal_transpose ha)
    · intro w hw
      rw [eq]
      exact adjointFlag_transpose C n (Submodule.mem_map_of_mem hw)
    · intro w hw
      rw [eq]
      exact adjointFlag_clock C n (Submodule.mem_map_of_mem hw)
    · rw [←quadraticSeed_exact,eq]
      exact adjointFlag_credit C n (creditSecond n)
  have h := adjointFlag_annih ho C paid 0 n (by omega) yes
  exact reflected_target_ne_zero ho (by omega) (mem_annih.mp h _ (one_mem_treeSpace A 0))

private theorem flag_interval (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (C : ℕ → Submodule K (Fin s → K))
    (paid : ∀ j n, j+n+3≤p → C n ≤ annih (treeSpace A j))
    (creditSecond : ∀ n, quadraticSeed A b∈C n) (n d : ℕ) (pay : n+d+2≤p) :
    finrank K (adjointFlag A b C n)+d ≤ finrank K (adjointFlag A b C (n+d)) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have lo:=ih (by omega)
    have gain:=Submodule.finrank_lt_finrank_of_lt (flag_strict ha ho C paid creditSecond (n+d) (by omega))
    change finrank K (adjointFlag A b C n)+(d+1) ≤ finrank K (adjointFlag A b C (n+d+1))
    omega

theorem back_interval (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (n d : ℕ) (pay : n+d+2≤p) :
    finrank K (back A b n)+d≤finrank K (back A b (n+d)) :=
  flag_interval ha ho _ (paid_pairCredit ho) (fun _=>Submodule.mem_span_singleton_self _) n d pay

theorem primitiveBack_interval (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (n d : ℕ) (pay : n+d+2≤p) :
    finrank K (primitiveBack A b n)+d≤finrank K (primitiveBack A b (n+d)) :=
  flag_interval ha ho _ (paid_monomialCredit ho) (fun n=>monomial_mem_credit n 1 (by omega)) n d pay

theorem back_finrank (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (n : ℕ) (pay : n+2≤p) : finrank K (back A b 0)+n≤finrank K (back A b n) := by
  have h := back_interval ha ho 0 n (by omega)
  rw [Nat.zero_add] at h
  exact h

theorem backward_count (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder A b p)
    (j n : ℕ) (pay : j+n+2≤p) :
    finrank K (treeSpace A j)+finrank K (back A b 0)+n≤s := by
  have lo:=back_finrank ha ho n (by omega)
  have inc:=Submodule.finrank_mono (back_annih ho j n pay)
  have eq:=finrank_annih (treeSpace A j)
  rw [Fintype.card_fin] at eq
  omega

end
end RKResearch.Certified.Graded.Reverse
