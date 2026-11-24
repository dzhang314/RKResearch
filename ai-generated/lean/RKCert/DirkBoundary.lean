module

public import RKCert.DirkRanks

@[expose] public section
namespace RKCert.Paired
variable {K : Type*} [Field K] {s p : ℕ} {A : Fin s → Fin s → K} {b : Vec K s}

/-- No conditioning of the tableau is performed: the final nonzero output
weight is selected even when arbitrary zero-weight stages follow it. -/
theorem last_output (ho : HasTreeOrderAtLeast A b p) (hp : 1≤p) :
    ∃ i : Fin s, b i ≠ 0 ∧ ∀ j : Fin s, i<j → b j=0 := by
  classical
  let S := Finset.univ.filter (fun i : Fin s => b i ≠ 0)
  have hn : S.Nonempty := by
    by_contra h
    have hz (i : Fin s) : b i=0 := by
      by_contra hh
      exact h ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩⟩
    have ht := ho .leaf hp
    simp [weight,hz] at ht
  let i := S.max' hn
  refine ⟨i, (Finset.mem_filter.mp (S.max'_mem hn)).2, ?_⟩
  intro j hj
  by_contra h
  exact (not_le_of_gt hj) (S.le_max' j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))

/-- At equality, vanishing of the quadratic seed forces the first row to be zero. -/
theorem dirk_first_row {A : Fin (s+1) → Fin (s+1) → K}
    (ha : ∀ i j : Fin (s+1), i.val<j.val → A i j=0)
    (hg : q₂ (mat A) (nodes A) 1=0) : ∀ j, A 0 j=0 := by
  have hh (v : Vec K (s+1)) : mat A v 0=A 0 0*v 0 :=
    causalDiag_mat ha 0 v (by intro j hj; exact False.elim (Nat.not_lt_zero _ hj))
  have hc : nodes A 0=A 0 0 := by simpa [mat_apply,nodes] using hh 1
  have h₂ := congrFun hg 0
  change 2 * mat A (diag (nodes A) 1) 0 - nodes A 0 * (nodes A 0 * 1) = 0 at h₂
  rw [hh,diag_apply,hc] at h₂
  have haa : A 0 0 * A 0 0=0 := by
    convert h₂ using 1; simp only [Pi.one_apply]; ring
  have hn : A 0 0=0 := (mul_eq_zero.mp haa).elim id id
  intro j
  by_cases hj : j=0
  · simpa [hj] using hn
  · apply ha
    have hne : j.val≠0 := by intro hv; apply hj; exact Fin.ext hv
    change 0<j.val; omega

theorem dirk_last_node (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (i : Fin s) (hb : b i ≠ 0) (hlast : ∀ j : Fin s, i<j → b j=0)
    (h₁ : backSeed1 A b=0) (h₂ : q₂ (transMat A) (mirror A) b=0) :
    mirror A i=0 := by
  have ht (v : Vec K s) (hv : ∀ j : Fin s, i<j → v j=0) :
      transMat A v i = A i i * v i :=
    causalDiag_transpose ha i v (fun j hj => hv j (Fin.rev_lt_rev.mp hj))
  let y := mirror A
  have h1 := congrFun h₁ i
  change transMat A b i - y i * b i = 0 at h1
  rw [ht b hlast, ← sub_mul] at h1
  have hdi : A i i=y i := sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hb)
  have h2 := congrFun h₂ i
  change 2*transMat A (diag y b) i - y i*(y i*b i)=0 at h2
  rw [ht _ (fun j hj => by simp [hlast j hj]), diag_apply, hdi] at h2
  have hz : (y i*y i)*b i=0 := by
    convert h2 using 1; ring
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hb)).elim id id

/-- Rows supported strictly before an index. -/
def prior (i : Fin s) : Submodule K (Vec K s) where
  carrier := {x | ∀ j, i ≤ j → x j = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy j hj; change x j+y j=0; rw [hx j hj,hy j hj,add_zero]
  smul_mem' := by intro a x hx j hj; change a*x j=0; rw [hx j hj,mul_zero]

theorem prior_transp (ha : ∀ i j : Fin s, i.val<j.val → A i j=0) (i : Fin s) :
    prior (K:=K) i ≤ (prior i).comap (transMat A) := by
  intro v hv j hj
  change ∑ k, A k j*v k=0
  apply Finset.sum_eq_zero
  intro k _
  by_cases h : k<j
  · rw [ha k j h,zero_mul]
  · rw [hv k (hj.trans (le_of_not_gt h)),mul_zero]

theorem prior_diag (y : Vec K s) (i : Fin s) : prior (K:=K) i ≤ (prior i).comap (diag y) := by
  intro v hv j hj; change y j * v j=0; rw [hv j hj,mul_zero]

theorem dirkBack_prior (ha : ∀ i j : Fin s, i.val<j.val → A i j=0)
    (i : Fin s) (hlast : ∀ j : Fin s, i<j → b j=0) (hc : mirror A i=0)
    (h₁ : backSeed1 A b=0) (h₂ : q₂ (transMat A) (mirror A) b=0) (r : ℕ) :
    dirkBack A b r ≤ prior i := by
  have hy : diag (mirror A) b ∈ prior i := by
    intro j hj
    rcases lt_or_eq_of_le hj with hl|rfl
    · simp [hlast j hl]
    · simp [hc]
  have h₃ : q₃ (transMat A) (mirror A) b ∈ prior i := by
    unfold q₃
    apply (prior (K:=K) i).sub_mem
    · apply Submodule.smul_mem
      exact prior_transp ha i (prior_diag _ i hy)
    · exact prior_diag _ i (prior_diag _ i hy)
  induction r with
  | zero =>
    change _ ⊔ _ ≤ _
    refine sup_le ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
      ((Submodule.span_singleton_le_iff_mem ..).mpr ?_)
    · rw [h₁]; exact Submodule.zero_mem _
    · rw [h₂]; exact Submodule.zero_mem _
  | succ r ih =>
    change _ ⊔ _ ⊔ _ ⊔ _ ≤ _
    exact sup_le (sup_le (sup_le ih (Submodule.map_le_iff_le_comap.mpr (ih.trans (prior_transp ha _))))
      (Submodule.map_le_iff_le_comap.mpr (ih.trans (prior_diag _ _))))
      ((Submodule.span_singleton_le_iff_mem ..).mpr h₃)

end RKCert.Paired
