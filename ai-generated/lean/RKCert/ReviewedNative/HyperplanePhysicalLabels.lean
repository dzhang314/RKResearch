module

public import RKCert.ReviewedNative.HyperplanePhysicalClassGrade

@[expose] public section

/-! # The hyperplane cut stated directly on arbitrary original row labels

No enumeration, distinguished row, compressed matrix, or class coordinate
system is required as input.  The chronological selection is the actual
least physical row of each label fibre.
-/
namespace RKResearch.Certified.Graded.HyperplaneTerminal

open RKResearch Reverse Module
open scoped Classical Matrix
noncomputable section
variable {K α : Type*} [Field K] [CharZero K] [DecidableEq α] {s j p : ℕ}

theorem physical_label_grade_impossible {A : Matrix (Fin s) (Fin s) K} {b : Fin s→K}
    (ha : ∀ i j, i≤j → A i j=0) (ho : HasOrder p A b) (f : Fin s→α)
    (cy : ∀i h,f i=f h → reflectedClock A i=reflectedClock A h)
    (rank : finrank K (treeSpace A j)+1=(Finset.univ.image f).card)
    (same : ∀v∈treeSpace A (j+1), ∀i h,f i=f h → v i=v h)
    (pay : j+4≤p)
    (excluded : ∀h,(∑ i ∈ Finset.univ.filter (fun i=>f i=f h), b i)≠0 →
      reflectedClock A h=0 → (fun i=>if f i=f h then (1:K) else 0)∉treeSpace A j) :
    False := by
  classical
  let first (i : Fin s) := ∀ h, h < i → f h≠f i
  let S := Finset.univ.filter first
  let e := S.orderEmbOfFin rfl
  have repr (i : Fin s) : ∃ t : Fin S.card, e t ≤ i ∧ f (e t)=f i := by
    let T : Set (Fin s) := {h | f h=f i}
    obtain ⟨h,hh,least⟩:=wellFounded_lt.has_min T ⟨i,rfl⟩
    have clean : first h := fun v prior eq=>least v (eq.trans hh) prior
    have mem : h∈S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,clean⟩
    have ran : h∈Set.range e := by rw [Finset.range_orderEmbOfFin]; exact mem
    obtain ⟨t,rfl⟩:=ran
    exact ⟨t,le_of_not_gt (least i rfl),hh⟩
  choose r earlier label using repr
  have once : Set.InjOn f (S : Set (Fin s)) := by
    intro i hi h hh eq
    have a := (Finset.mem_filter.mp hi).2
    have d := (Finset.mem_filter.mp hh).2
    rcases lt_trichotomy i h with k|k|k
    · exact (d i k eq).elim
    · exact k
    · exact (a h k eq.symm).elim
  have image : S.image f=Finset.univ.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image (Finset.subset_univ S))
    intro z hz
    obtain ⟨i,_,rfl⟩:=Finset.mem_image.mp hz
    exact Finset.mem_image.mpr ⟨e (r i),S.orderEmbOfFin_mem rfl _,label i⟩
  have card : S.card=(Finset.univ.image f).card := by
    rw [←image,Finset.card_image_of_injOn once]
  have fibres (i : Fin s) (t : Fin S.card) : r i=t ↔ f i=f (e t) := by
    constructor
    · intro eq
      rw [←eq]
      exact (label i).symm
    · intro eq
      apply e.injective
      exact once (S.orderEmbOfFin_mem rfl _) (S.orderEmbOfFin_mem rfl _) ((label i).trans eq)
  apply physical_class_grade_impossible ha ho e r e.monotone earlier
    (fun i=>cy _ _ (label i)) (rank.trans card.symm)
    (fun v hv i=>same _ hv _ _ (label i)) pay
  intro t wt clk
  have w : (∑ i ∈ Finset.univ.filter (fun i=>f i=f (e t)), b i)≠0 := by
    simpa only [folded,fibres] using wt
  have mask : (fun i=>coordinate (K:=K) t (r i))=
      (fun i=>if f i=f (e t) then (1:K) else 0) := by
    ext i
    by_cases eq : r i=t
    · simp [coordinate,eq,(fibres i t).mp eq]
    · have de : f i≠f (e t) := fun same=>eq ((fibres i t).mpr same)
      simp [coordinate,eq,Ne.symm eq,de]
  rw [mask]
  exact excluded _ w clk

end
end RKResearch.Certified.Graded.HyperplaneTerminal
