module

public import RKCert.ReviewedNative.ReverseMeasuredCapacity
public import Mathlib.Algebra.Module.Pi

public section

namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix

noncomputable section

variable {K α : Type*} [Field K] {s j n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The vector of row pairings with a family of actual stage columns. -/
def reverseRowFamily (C : α → Fin s → K) : (Fin s → K) →ₗ[K] (α → K) :=
  LinearMap.pi (fun a => row (C a))

private theorem ker_reverseRowFamily (C : α → Fin s → K) :
    LinearMap.ker (reverseRowFamily C) = annih (Submodule.span K (Set.range C)) := by
  ext w
  rw [LinearMap.mem_ker, mem_annih]
  constructor
  · intro hz
    have each (a : α) : row w (C a) = 0 := by
      have e : row (C a) w = 0 := congrFun hz a
      rwa [row_apply, dotProduct_comm, ← row_apply] at e
    have incl : Submodule.span K (Set.range C) ≤ LinearMap.ker (row w) := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact LinearMap.mem_ker.mpr (each a)
    intro u hu
    exact LinearMap.mem_ker.mp (incl hu)
  · intro hz
    funext a
    change row (C a) w = 0
    rw [row_apply, dotProduct_comm, ← row_apply]
    exact hz (C a) (Submodule.subset_span ⟨a, rfl⟩)

private theorem row_annih_sup (U V : Submodule K (Fin s → K)) :
    annih (U ⊔ V) = annih U ⊓ annih V := by
  ext w
  rw [Submodule.mem_inf]
  constructor
  · intro h
    exact ⟨annih_antitone le_sup_left h, annih_antitone le_sup_right h⟩
  · rintro ⟨hu, hv⟩
    apply mem_annih.mpr
    intro z hz
    obtain ⟨u, ui, v, vi, rfl⟩ := Submodule.mem_sup.mp hz
    rw [map_add, mem_annih.mp hu u ui, mem_annih.mp hv v vi, add_zero]

private theorem reverse_family_rank_nullity (B : Submodule K (Fin s → K))
    (M : (Fin s → K) →ₗ[K] (α → K)) :
    finrank K (B.map M) + finrank K (B ⊓ LinearMap.ker M : Submodule K (Fin s → K)) = finrank K B := by
  have h := (M.domRestrict B).finrank_range_add_finrank_ker
  rw [LinearMap.range_domRestrict,
    ← Submodule.finrank_map_subtype_eq B (LinearMap.ker (M.domRestrict B)),
    LinearMap.ker_domRestrict, Submodule.map_comap_subtype] at h
  exact h

/-- The rank of the outstanding reverse pairing image is exactly the
forward dimension gained by adjoining the entire probe family. -/
theorem MeasuredReverseCapacity.row_family_rank_identity
    (H : MeasuredReverseCapacity A b j n) (C : α → Fin s → K) :
    finrank K (treeSpace A j ⊔ Submodule.span K (Set.range C) : Submodule K (Fin s → K)) =
      finrank K (treeSpace A j) +
        finrank K ((back A b n).map (reverseRowFamily C)) := by
  have ki : back A b n ⊓ LinearMap.ker (reverseRowFamily C) =
      annih (treeSpace A j ⊔ Submodule.span K (Set.range C)) := by
    rw [H.backFull, ker_reverseRowFamily, row_annih_sup]
  have rn := reverse_family_rank_nullity (back A b n) (reverseRowFamily C)
  rw [ki] at rn
  have old := finrank_annih (treeSpace A j)
  have new := finrank_annih (treeSpace A j ⊔ Submodule.span K (Set.range C))
  rw [Fintype.card_fin, ← H.backFull] at old
  rw [Fintype.card_fin] at new
  omega

/-- Balanced reverse directions are subtracted from the measured budget. -/
theorem MeasuredReverseCapacity.row_family_rank_le_deficit
    (H : MeasuredReverseCapacity A b j n) (C : α → Fin s → K)
    {U : Submodule K (Fin s → K)} (inside : U ≤ back A b n)
    (balanced : U ≤ LinearMap.ker (reverseRowFamily C)) :
    finrank K ((back A b n).map (reverseRowFamily C)) ≤
      finrank K (back A b 0) + n - finrank K U := by
  have rn := reverse_family_rank_nullity (back A b n) (reverseRowFamily C)
  have used := Submodule.finrank_mono (le_inf inside balanced)
  rw [(H.flagExact n le_rfl).2.1] at rn
  omega

theorem MeasuredReverseCapacity.row_family_rank_eq_zero_iff
    (H : MeasuredReverseCapacity A b j n) (C : α → Fin s → K) :
    finrank K ((back A b n).map (reverseRowFamily C)) = 0 ↔
      ∀ a, C a ∈ treeSpace A j := by
  have h := H.row_family_rank_identity C
  constructor
  · intro hz a
    have eq : treeSpace A j = treeSpace A j ⊔ Submodule.span K (Set.range C) :=
      Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have incl : Submodule.span K (Set.range C) ≤
        treeSpace A j ⊔ Submodule.span K (Set.range C) := le_sup_right
    have found := incl (Submodule.subset_span (show C a ∈ Set.range C from ⟨a, rfl⟩))
    rwa [← eq] at found
  · intro inTree
    have incl : Submodule.span K (Set.range C) ≤ treeSpace A j := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a, rfl⟩
      exact inTree a
    have eq : treeSpace A j ⊔ Submodule.span K (Set.range C) = treeSpace A j :=
      le_antisymm (sup_le le_rfl incl) le_sup_left
    rw [eq] at h
    omega

end
end RKResearch.Certified.Graded.Reverse
