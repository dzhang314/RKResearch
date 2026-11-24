module

public import RKCert.DirkReverseMoments
public import RKCert.BackwardGrowth
public import RKCert.GradeSeparation

@[expose] public section

namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] {s : ℕ}

noncomputable abbrev dirkFront (A : Fin s → Fin s → K) :=
  twoOrbit (mat A) (diag (nodes A)) (0 : Vec K s) (q₂ (mat A) (nodes A) 1) (q₃ (mat A) (nodes A) 1)

noncomputable abbrev dirkBack (A : Fin s → Fin s → K) (b : Vec K s) :=
  twoOrbit (transMat A) (diag (mirror A)) (backSeed1 A b)
    (q₂ (transMat A) (mirror A) b) (q₃ (transMat A) (mirror A) b)

theorem front_seed3 (A : Fin s → Fin s → K) : q₃ (mat A) (nodes A) 1 ∈ zeroSpace A 3 := by
  have h := normDiff_mem (n:=3) A ((Tree.bush 2).attach .leaf) (Tree.bush 3)
    (by decide) (by decide)
  rw [normTree_unary, Tree.order_bush, normTree_bush, normTree_bush] at h
  have eqn : diag (nodes A) (diag (nodes A) 1) = (fun i => nodes A i ^ 2) := by
    ext i; simp [pow_two]
  have eqn' : diag (nodes A) (diag (nodes A) (diag (nodes A) 1)) = (fun i => nodes A i ^ 3) := by
    ext i; simp; ring
  rw [q₃, eqn', eqn]
  simpa only [Nat.reduceAdd, Nat.cast_ofNat] using h

theorem dirkFront_zeroSpace {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (n : ℕ) (hn : n+2≤p) :
    dirkFront A n ≤ zeroSpace A (n+2) := by
  induction n with
  | zero =>
    change _ ⊔ _ ≤ _
    refine sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr (Submodule.zero_mem _))
      ((Submodule.span_singleton_le_iff_mem ..).mpr (forward_seed_mem A))
  | succ n ih =>
    have hi := ih (by omega)
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    refine sup_le (sup_le (sup_le (hi.trans (zeroSpace_mono A (by omega))) ?_) ?_)
      ((Submodule.span_singleton_le_iff_mem ..).mpr (zeroSpace_mono A (by omega) (front_seed3 A)))
    · exact Submodule.map_le_iff_le_comap.mpr (hi.trans (mat_zeroSpace ho _ (by omega)))
    · exact Submodule.map_le_iff_le_comap.mpr (hi.trans (diag_zeroSpace A _))

theorem dirkFront_rank {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : ∀ i j : Fin s, i.val < j.val → A i j=0) (ho : HasTreeOrderAtLeast A b p)
    (n : ℕ) (hn : n+3≤p) :
    n+finrank K (dirkFront A 0) ≤ finrank K (zeroSpace A (n+2)) := by
  have hs := dirkFront_zeroSpace ho n (by omega)
  have hnc : diag (nodes A) 1 ∉ dirkFront A n := by
    intro h
    have hz : probe A b 0 (diag (nodes A) 1) = 0 :=
      probe_zeroSpace ho (by omega : 0+(n+2)+1 ≤ p) (hs h)
    have ht : normTree A (Tree.bush 1) = diag (nodes A) 1 := by ext i; simp [normTree_bush]
    have hh := probe_normTree ho (Tree.bush 1) 0 (by simp; omega)
    rw [ht, hz, mul_zero] at hh
    exact zero_ne_one hh
  exact (twoOrbit_rank (Equiv.refl _) (mat A) (fun i => A i i) (causalDiag_mat ha)
    (nodes A) 1 0 n hnc).trans (Submodule.finrank_mono hs)

theorem back_seed3 (A : Fin s → Fin s → K) (b : Vec K s) :
    q₃ (transMat A) (mirror A) b = reflected A b 2 := by
  have h₂ : diag (mirror A) (diag (mirror A) b) = reflWeight A b 2 := by
    ext i; simp [mirror, reflWeight, reflNode]; ring
  have h₃ : diag (mirror A) (diag (mirror A) (diag (mirror A) b)) = reflWeight A b 3 := by
    ext i; simp [mirror, reflWeight, reflNode]; ring
  rw [q₃, h₃, h₂]
  rfl

/-- Every low reverse word annihilates *every* actual tree at complementary grade. -/
theorem dirkBack_annih {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hpay : j+n+3≤p) :
    dirkBack A b n ≤ annih (treeSpace A j) := by
  induction n generalizing j with
  | zero =>
    change _ ⊔ _ ≤ _
    exact sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr (backSeed1_annih ho (by omega)))
      ((Submodule.span_singleton_le_iff_mem ..).mpr (backSeed2_annih ho (by omega)))
  | succ n ih =>
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    refine sup_le (sup_le (sup_le (ih j (by omega)) ?_) ?_) ?_
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr; intro v hv
      rw [row_flip_mat]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mat_treeSpace A j hv)
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr; intro v hv
      rw [row_flip_diag]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mirror_treeSpace A j hv)
    · apply (Submodule.span_singleton_le_iff_mem ..).mpr
      rw [back_seed3, mem_annih]
      exact reflected_treeSpace ho j 2 (by decide) (by omega)

theorem dirkBack_rank {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : ∀ i j : Fin s, i.val < j.val → A i j=0) (ho : HasTreeOrderAtLeast A b p)
    (n : ℕ) (hn : n+3≤p) :
    n+finrank K (dirkBack A b 0) ≤ finrank K (dirkBack A b n) := by
  apply twoOrbit_rank Fin.revPerm (transMat A) _ (causalDiag_transpose ha)
  intro h
  have hr := dirkBack_annih ho 0 n (by omega) h
  have hm : (1:Vec K s)∈treeSpace A 0 := stageWeight_mem_space A .leaf (by decide)
  exact back_target_nonzero ho (by omega) (mem_annih.mp hr _ hm)

/-- The paired inequality, retaining the low defects whose vanishing is
forced at any equality candidate. -/
theorem dirk_rank_budget {A : Fin s → Fin s → K} {b : Vec K s} {p m n r : ℕ}
    (ha : ∀ i j : Fin s, i.val < j.val → A i j=0) (ho : HasTreeOrderAtLeast A b p)
    (hm : m=n+2) (hp : 2*m+1 ≤ p) (hpay : m+r+3 ≤ p) :
    m+1 + n + r + finrank K (dirkFront A 0) + finrank K (dirkBack A b 0) ≤ s := by
  have hf := dirkFront_rank ha ho n (by omega)
  have hr := dirkBack_rank ha ho r (by omega)
  have he := treeSpace_rank ho (q:=m) hp
  have hs := finrank_annih_le (dirkBack_annih ho m r hpay)
  rw [← hm] at hf
  omega

end RKCert.Paired
