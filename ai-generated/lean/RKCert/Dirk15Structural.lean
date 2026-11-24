module

public import RKCert.Dirk15NativeReverse
public import RKCert.Dirk15RadauPorts
public import RKCert.Dirk15SignatureAlgebra

@[expose] public section

/-! # Exhaustive rank charts for a hypothetical 20-stage method at order 15
This is a structural reduction. The cases are not claimed to be realizable
or excluded, and this module does not state a new stage lower bound. -/
namespace RKCert.Paired
open Module
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

omit [CharZero K] in
theorem Order15NonC2Chart.marked_rank_exact (h : Order15NonC2Chart A b)
    (j : ℕ) (hl : 2≤j) (hu : j≤7) : finrank K (marked A 15 j)=j-2 := by
  have he := h.treeBand (15-1-j) (by omega) (by omega)
  have hM := marked_rank A 15 j
  change finrank K (treeSpace A (15-1-j))+finrank K (marked A 15 j)=20 at hM
  omega

/-- Exhaustive native chart split: non-C(2), anchored early marked surplus,
or anchored minimal marks with actual terminal-deleted tree ranks. -/
theorem order15_twenty_native_cases (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15) :
    (q₂ (mat A) (nodes A) 1≠0 ∧ Order15NonC2Chart A b ∧
      ∀ j : ℕ, 4≤j → j≤7 → ¬(marked A 15 j).map (diag (mirror A))≤marked A 15 j) ∨
    (q₂ (mat A) (nodes A) 1=0 ∧ Order15AnchoredChart A b ∧
      (∀ j : ℕ, 4≤j → j≤7 → finrank K (marked A 15 j)=j-1) ∧
      ∀ j : ℕ, 4≤j → j≤7 → ¬(marked A 15 j).map (diag (mirror A))≤marked A 15 j) ∨
    (q₂ (mat A) (nodes A) 1=0 ∧ finrank K (marked A 15 4)=2 ∧
      Order15MinimalMarkedChart A b ∧
      ∀ j : ℕ, 7≤j → j≤11 →
        deletedTreeSpace A j=annih (deletedMarkedZero A (14-j)) ∧
          finrank K (deletedTreeSpace A j)=j+7) := by
  by_cases hq : q₂ (mat A) (nodes A) 1=0
  · have h23 := Submodule.finrank_lt_finrank_of_lt
      (marked_strict ha ho (j:=2) (by decide) (by decide))
    have h34 := Submodule.finrank_lt_finrank_of_lt
      (marked_strict ha ho (j:=3) (by decide) (by decide))
    change finrank K (marked A 15 2)<finrank K (marked A 15 3) at h23
    change finrank K (marked A 15 3)<finrank K (marked A 15 4) at h34
    by_cases hm : finrank K (marked A 15 4)=2
    · have h := order15_minimal_marked_chart ha ho hq hm
      exact Or.inr (Or.inr ⟨hq,hm,h,order15_minimal_deleted_band ha ho h⟩)
    · have he (j : ℕ) (hl : 4≤j) (hu : j≤7) : finrank K (marked A 15 j)=j-1 :=
        order15_early_marked_ranks ha ho hq (by omega) hl hu
      refine Or.inr (Or.inl ⟨hq,order15_anchored_rank_chart ha ho hq,he,?_⟩)
      apply order15_full_marked_escape_of_unit ha ho
      intro j h₄ h₆
      rw [he j h₄ (by omega),he (j+1) (by omega) (by omega)]
      omega
  · have h := order15_nonC2_rank_chart ha ho hq
    refine Or.inl ⟨hq,h,?_⟩
    apply order15_full_marked_escape_of_unit ha ho
    intro j h₄ h₆
    rw [h.marked_rank_exact j (by omega) (by omega),h.marked_rank_exact (j+1) (by omega) (by omega)]
    omega

end RKCert.Paired
