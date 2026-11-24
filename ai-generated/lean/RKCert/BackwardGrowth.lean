module

public import RKCert.BackwardMoments

@[expose] public section

/-! # Paired forward and reverse rank count

At level n+1, build the reverse space starting with the linear residual;
the quadratic residual and the images under the two backward maps enter
from the next level on. These spaces need not contain all reverse residuals.
Their own strict growth suffices for the paired rank certificate.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s : ℕ}

noncomputable def back (A : Fin s → Fin s → K) (b : Vec K s) : ℕ → Submodule K (Vec K s)
  | 0 => Submodule.span K {backSeed1 A b}
  | n+1 =>
    let U := back A b n
    U ⊔ U.map (transMat A) ⊔ U.map (diag (mirror A)) ⊔ Submodule.span K {backSeed2 A b}

theorem back_le_succ (A : Fin s → Fin s → K) (b : Vec K s) (n : ℕ) :
    back A b n ≤ back A b (n+1) := le_sup_left.trans (le_sup_left.trans le_sup_left)

theorem mirror_treeSpace (A : Fin s → Fin s → K) (j : ℕ) :
    treeSpace A j ≤ (treeSpace A (j+1)).comap (diag (mirror A)) := by
  intro v hv
  have he : diag (mirror A) v = v - diag (nodes A) v := by
    ext i; simp [mirror, sub_mul]
  change diag (mirror A) v ∈ treeSpace A (j+1)
  rw [he]
  exact (treeSpace A (j+1)).sub_mem (treeSpace_mono A (by omega) hv) (diag_treeSpace A j hv)

theorem back_annih {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hj : j+n+2≤p) :
    back A b n ≤ annih (treeSpace A j) := by
  induction n generalizing j with
  | zero =>
    apply (Submodule.span_singleton_le_iff_mem ..).mpr
    exact backSeed1_annih ho (by omega)
  | succ n ih =>
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    refine sup_le (sup_le (sup_le (ih j (by omega)) ?_) ?_)
      ((Submodule.span_singleton_le_iff_mem ..).mpr (backSeed2_annih ho (by omega)))
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr
      intro v hv
      rw [row_flip_mat]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mat_treeSpace A j hv)
    · rintro _ ⟨u,hu,rfl⟩
      apply mem_annih.mpr
      intro v hv
      rw [row_flip_diag]
      exact mem_annih.mp (ih (j+1) (by omega) hu) _ (mirror_treeSpace A j hv)

theorem back_target_nonzero {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hp : 2≤p) :
    row (diag (mirror A) b) 1 ≠ 0 := by
  have h2 : (2:K)≠0 := by simpa using cast_ne_zero_of_budget ho (n:=2) (by decide) hp
  have h : 2 * row (diag (mirror A) b) 1 = 1 := by
    rw [row_mirror, ← normTree_leaf A, probe_norm_inv ho .leaf 0 (by change 0+1≤p; omega),
      probe_norm_inv ho .leaf 1 (by change 1+1≤p; omega)]
    simp only [Tree.order, Nat.cast_zero, Nat.cast_one, add_zero, inv_one]
    rw [show (1:K)+1=2 by ring, mul_sub, mul_one, mul_inv_cancel₀ h2]
    ring
  intro hz
  rw [hz, mul_zero] at h
  exact zero_ne_one h

theorem back_target_out {A : Fin s → Fin s → K} {b : Vec K s} {p n : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hn : n+2≤p) :
    diag (mirror A) b ∉ back A b n := by
  intro hv
  have ho' := back_annih ho 0 n (by omega) hv
  have hm : (1 : Vec K s) ∈ treeSpace A 0 := stageWeight_mem_space A .leaf (by decide)
  exact back_target_nonzero ho (by omega) (mem_annih.mp ho' 1 hm)

/-- A plateau would make both reverse maps invariant while the quadratic
seed is present. The causal obstruction would then give a row with nonzero
value at the leaf, contradicting annihilation of every permitted tree. -/
theorem back_lt_succ {A : Fin s → Fin s → K} {b : Vec K s} {p n : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (hn : n+3≤p) :
    back A b n < back A b (n+1) := by
  refine lt_of_le_of_ne (back_le_succ A b n) ?_
  intro he
  apply back_target_out ho (n:=n) (by omega)
  apply mem_of_invariant_seed Fin.revPerm (transMat A) (causal_transpose ha)
    (mirror A) b (back A b n)
  · intro x hx
    rw [he]
    apply (show (back A b n).map (transMat A) ≤ back A b (n+1) from le_sup_right.trans (le_sup_left.trans le_sup_left))
    exact Submodule.mem_map_of_mem hx
  · intro x hx
    rw [he]
    apply (show (back A b n).map (diag (mirror A)) ≤ back A b (n+1) from le_sup_right.trans le_sup_left)
    exact Submodule.mem_map_of_mem hx
  · rw [he]
    apply (show Submodule.span K {backSeed2 A b} ≤ back A b (n+1) from le_sup_right)
    exact Submodule.subset_span (Set.mem_singleton (backSeed2 A b))

theorem back_finrank {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (n : ℕ) (hn : n+2≤p) :
    finrank K (back A b 0) + n ≤ finrank K (back A b n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hr := Submodule.finrank_lt_finrank_of_lt (back_lt_succ ha ho (n:=n) (by omega))
    have hl := ih (by omega)
    omega

/-- The basic rank count with the first backward defect still visible.
Grade p-1-j corresponds to index n=p-2-j in the zero-based back filtration. -/
theorem backward_count {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hj : j+n+2≤p) :
    finrank K (treeSpace A j) + finrank K (back A b 0) + n ≤ s := by
  have hl := back_finrank ha ho n (by omega)
  have hr := finrank_annih_le (back_annih ho j n hj)
  omega

end RKCert.Paired
