module

public import RKCert.ReviewedNative.PhysicalSupportCensus

@[expose] public section

/-! # Literal row witnesses from saturated supported ranks

Source-only. The whole-label indicator witnesses a live value in its
assigned summand. No choice of a representative stage is used. -/
namespace RKResearch.Certified.Graded.PhysicalCensus
open Module
open scoped Classical
noncomputable section

variable {K α : Type*} [Field K] {s : ℕ}

theorem exact_supported_triple_live {label : Fin s → α} {S T R : Set α}
    {V W Z M : Submodule K (Fin s → K)}
    (hV : OnLabels label S V) (hW : OnLabels label T W) (hZ : OnLabels label R Z)
    (st : Disjoint S T) (sr : Disjoint S R) (tr : Disjoint T R)
    (joined : V ⊔ W ⊔ Z ≤ M)
    (rank : finrank K M ≤ finrank K V + finrank K W + finrank K Z)
    (block : ∀ i, (labelIndicator label (label i) : Fin s → K) ∈ M) :
    (V ⊔ W ⊔ Z = M) ∧
      ∀ i, (label i ∈ S ∧ ∃ v ∈ V, v i = 1) ∨
        (label i ∈ T ∧ ∃ w ∈ W, w i = 1) ∨
        (label i ∈ R ∧ ∃ z ∈ Z, z i = 1) := by
  have eq : V ⊔ W ⊔ Z = M := Submodule.eq_of_le_of_finrank_le joined (by
    rw [finrank_supported_triple hV hW hZ st sr tr]
    exact rank)
  have cov := cover_of_supported_rank_equality hV hW hZ st sr tr joined rank block
  refine ⟨eq, ?_⟩
  intro i
  have hi : (labelIndicator label (label i) : Fin s → K) ∈ V ⊔ W ⊔ Z :=
    eq.symm ▸ block i
  obtain ⟨vw, hvw, z, hz, hvz⟩ := Submodule.mem_sup.mp hi
  obtain ⟨v, hv, w, hw, hvw'⟩ := Submodule.mem_sup.mp hvw
  have value : v i + w i + z i = 1 := by
    change ((v + w) + z) i = 1
    rw [hvw', hvz]
    simp [labelIndicator]
  rcases cov i with si | ti | ri
  · have wi := hW w hw i (Set.disjoint_left.mp st si)
    have zi := hZ z hz i (Set.disjoint_left.mp sr si)
    exact Or.inl ⟨si, v, hv, by simpa only [wi, zi, add_zero] using value⟩
  · have vi := hV v hv i (fun s' => Set.disjoint_left.mp st s' ti)
    have zi := hZ z hz i (Set.disjoint_left.mp tr ti)
    exact Or.inr (Or.inl ⟨ti, w, hw, by simpa only [vi, zi, zero_add, add_zero] using value⟩)
  · have vi := hV v hv i (fun s' => Set.disjoint_left.mp sr s' ri)
    have wi := hW w hw i (fun t' => Set.disjoint_left.mp tr t' ri)
    exact Or.inr (Or.inr ⟨ri, z, hz, by simpa only [vi, wi, zero_add] using value⟩)

end
end RKResearch.Certified.Graded.PhysicalCensus
