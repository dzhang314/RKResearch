module

public import RKCert.BackwardGrowth
public import Mathlib.Data.Finset.Max

@[expose] public section

/-! # The last nonzero output and the missing odd dimension

No tableau is shortened. Choose the *last nonzero weight*, which may precede
arbitrarily many inactive stages. When the linear backward defect is zero,
its node is one and all generated backward defects vanish there.
-/
namespace RKCert.Paired
open Module

variable {K : Type*} [Field K] {s : ℕ}

theorem exists_last_weight {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ho : HasTreeOrderAtLeast A b p) (hp : 1 ≤ p) :
    ∃ i : Fin s, b i ≠ 0 ∧ ∀ j, i < j → b j = 0 := by
  classical
  have hb : ∃ i : Fin s, b i ≠ 0 := by
    by_contra! hz
    have h := ho .leaf hp
    simp [weight,hz] at h
  let T := Finset.univ.filter (fun i : Fin s => b i ≠ 0)
  obtain ⟨i,hi⟩ := hb
  have hT : T.Nonempty := ⟨i,by simpa [T] using hi⟩
  have hmax : T.max' hT ∈ T := T.max'_mem hT
  refine ⟨T.max' hT,by simpa [T] using hmax,?_⟩
  intro j hj
  by_contra h
  exact (not_le_of_gt hj) (T.le_max' j (by simpa [T] using h))

/-- Vectors vanishing at and after the selected index. -/
def vanishFrom (i : Fin s) : Submodule K (Vec K s) where
  carrier := {v | ∀ j, i ≤ j → v j = 0}
  zero_mem' := by simp
  add_mem' := by intro v w hv hw j hj; simp [hv j hj, hw j hj]
  smul_mem' := by intro a v hv j hj; simp [hv j hj]

theorem transMat_vanish {A : Fin s → Fin s → K} (ha : StrictLower A)
    (i : Fin s) (v : Vec K s) (hv : ∀ k, i < k → v k = 0) :
    transMat A v ∈ vanishFrom i := by
  intro j hj
  change (∑ k, A k j * v k) = 0
  apply Finset.sum_eq_zero
  intro k _
  by_cases hkj : k ≤ j
  · rw [ha k j hkj,zero_mul]
  · rw [hv k (lt_of_le_of_lt hj (lt_of_not_ge hkj)),mul_zero]

theorem last_mirror_zero {A : Fin s → Fin s → K} {b : Vec K s} (ha : StrictLower A)
    {i : Fin s} (hi : b i ≠ 0) (hlast : ∀ j, i < j → b j = 0)
    (hd : backSeed1 A b = 0) : mirror A i = 0 := by
  have htr := transMat_vanish ha i b hlast i le_rfl
  have h := congrFun hd i
  change transMat A b i - mirror A i * b i = 0 at h
  rw [htr, zero_sub, neg_eq_zero] at h
  exact (mul_eq_zero.mp h).resolve_right hi

theorem back_vanish {A : Fin s → Fin s → K} {b : Vec K s} (ha : StrictLower A)
    {i : Fin s} (hi : b i ≠ 0) (hlast : ∀ j, i < j → b j = 0)
    (hd : backSeed1 A b = 0) (n : ℕ) : back A b n ≤ vanishFrom i := by
  have hy := last_mirror_zero ha hi hlast hd
  have hD (w : Vec K s) (hw : w ∈ vanishFrom i) : diag (mirror A) w ∈ vanishFrom i := by
    intro j hj; simp [hw j hj]
  have hN (w : Vec K s) (hw : w ∈ vanishFrom i) : transMat A w ∈ vanishFrom i :=
    transMat_vanish ha i w (fun j hj => hw j hj.le)
  have hz : diag (mirror A) b ∈ vanishFrom i := by
    intro j hj
    rcases eq_or_lt_of_le hj with rfl|h
    · simp [hy]
    · simp [hlast j h]
  have h2 : backSeed2 A b ∈ vanishFrom i := by
    unfold backSeed2
    exact (vanishFrom (K:=K) i).sub_mem ((vanishFrom i).smul_mem (2:K) (hN _ hz)) (hD _ hz)
  induction n with
  | zero => apply (Submodule.span_singleton_le_iff_mem ..).mpr; rw [hd]; exact (vanishFrom i).zero_mem
  | succ n ih =>
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    refine sup_le (sup_le (sup_le ih ?_) ?_) ((Submodule.span_singleton_le_iff_mem ..).mpr h2)
    · rintro _ ⟨w,hw,rfl⟩; exact hN _ (ih hw)
    · rintro _ ⟨w,hw,rfl⟩; exact hD _ (ih hw)

/-- Gain a dimension from a known column outside the forward space on
which all the constructed backward rows vanish. -/
theorem back_count_extra {A : Fin s → Fin s → K} {b : Vec K s} {p : ℕ}
    (ha : StrictLower A) (ho : HasTreeOrderAtLeast A b p) (j n : ℕ) (hp : j+n+2≤p)
    (z : Vec K s) (hz : z ∉ treeSpace A j) (hback : ∀ w ∈ back A b n, row w z=0) :
    finrank K (treeSpace A j) + n + 1 ≤ s := by
  let E := treeSpace A j
  let E' := E ⊔ Submodule.span K {z}
  have hlt : E < E' := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro he
    apply hz
    change z ∈ E
    rw [he]
    exact (show Submodule.span K {z} ≤ E' from le_sup_right) (Submodule.subset_span (Set.mem_singleton z))
  have hA : back A b n ≤ annih E' := by
    intro w hw
    apply mem_annih.mpr
    change E ⊔ Submodule.span K {z} ≤ (row w).ker
    refine sup_le ?_ ((Submodule.span_singleton_le_iff_mem ..).mpr (hback w hw))
    exact fun v hv => mem_annih.mp (back_annih ho j n hp hw) v hv
  have hdim := Submodule.finrank_lt_finrank_of_lt hlt
  have hr := finrank_annih_le hA
  have hl := back_finrank ha ho n (by omega)
  change finrank K E + n + 1 ≤ s
  omega

end RKCert.Paired
