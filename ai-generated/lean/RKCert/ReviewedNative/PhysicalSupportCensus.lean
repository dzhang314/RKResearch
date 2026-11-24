module

public import RKCert.ReviewedNative.RowAnnihilator

@[expose] public section

/-! Source-only draft. Equality in disjoint supported ranks covers each
*physical* row, provided its whole label indicator belongs to the ambient
space. No clock ordering, polynomial structure, or RK hypothesis enters. -/
namespace RKResearch.Certified.Graded.PhysicalCensus
open Module
open scoped Classical
noncomputable section

variable {K α : Type*} [Field K] {s : ℕ}

def labelIndicator (label : Fin s→α) (a : α) : Fin s→K :=
  fun i=>if label i=a then 1 else 0

def OnLabels (label : Fin s→α) (S : Set α) (V : Submodule K (Fin s→K)) : Prop :=
  ∀ v∈V,∀ i,label i∉S → v i=0

theorem onLabels_sup {label : Fin s→α} {S T : Set α} {V W : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) :
    OnLabels label (S∪T) (V⊔W) := by
  intro v hv i off
  obtain ⟨x,hx,y,hy,rfl⟩ := Submodule.mem_sup.mp hv
  rw [Pi.add_apply,hV x hx i (fun e=>off (Or.inl e)),hW y hy i (fun e=>off (Or.inr e)),add_zero]

theorem onLabels_same_sup {label : Fin s→α} {S : Set α} {V W : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label S W) :
    OnLabels label S (V⊔W) := by
  simpa only [Set.union_self] using onLabels_sup hV hW

theorem onLabels_inf_bot {label : Fin s→α} {S T : Set α} {V W : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) (separate : Disjoint S T) :
    V⊓W=⊥ := by
  apply le_antisymm _ bot_le
  intro x hx
  have none : x=0 := by
    funext i
    by_cases on : label i∈S
    · exact hW x hx.2 i (Set.disjoint_left.mp separate on)
    · exact hV x hx.1 i on
  rw [none]
  exact (⊥ : Submodule K (Fin s→K)).zero_mem

theorem finrank_supported_triple {label : Fin s→α} {S T R : Set α}
    {V W Z : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) (hZ : OnLabels label R Z)
    (st : Disjoint S T) (sr : Disjoint S R) (tr : Disjoint T R) :
    finrank K (V⊔W⊔Z : Submodule K (Fin s→K))=finrank K V+finrank K W+finrank K Z := by
  have sep : Disjoint (S∪T) R := by
    rw [Set.disjoint_left]
    intro a on ar
    rcases on with as'|at'
    · exact Set.disjoint_left.mp sr as' ar
    · exact Set.disjoint_left.mp tr at' ar
  have vw := Submodule.finrank_sup_add_finrank_inf_eq V W
  have total := Submodule.finrank_sup_add_finrank_inf_eq (V⊔W) Z
  rw [onLabels_inf_bot hV hW st,finrank_bot,add_zero] at vw
  rw [onLabels_inf_bot (onLabels_sup hV hW) hZ sep,finrank_bot,add_zero,vw] at total
  exact total

/-- Saturation upgrades a weighted-site census to coverage of all rows,
including rows carrying zero of every selected physical vector. -/
theorem cover_of_supported_rank_equality {label : Fin s→α} {S T R : Set α}
    {V W Z M : Submodule K (Fin s→K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) (hZ : OnLabels label R Z)
    (st : Disjoint S T) (sr : Disjoint S R) (tr : Disjoint T R)
    (joined : V⊔W⊔Z≤M)
    (rank : finrank K M≤finrank K V+finrank K W+finrank K Z)
    (block : ∀ i,(labelIndicator label (label i) : Fin s→K)∈M) :
    ∀ i,label i∈S ∨ label i∈T ∨ label i∈R := by
  have e : V⊔W⊔Z=M := Submodule.eq_of_le_of_finrank_le joined (by
    rw [finrank_supported_triple hV hW hZ st sr tr]
    exact rank)
  have support := onLabels_sup (onLabels_sup hV hW) hZ
  intro i
  by_contra! z
  have off : label i∉(S∪T)∪R := by
    rintro ((s'|t')|r')
    · exact z.1 s'
    · exact z.2.1 t'
    · exact z.2.2 r'
  have ind : (labelIndicator label (label i) : Fin s→K)∈V⊔W⊔Z := e.symm ▸ block i
  have test : (labelIndicator label (label i) : Fin s→K) i=0 := support _ ind i off
  simp [labelIndicator] at test

end
end RKResearch.Certified.Graded.PhysicalCensus
