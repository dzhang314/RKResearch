module

public import RKCert.DirkWeightedFiveHeads

@[expose] public section

namespace RKCert.Paired.LocalProjection.WeightedFive
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {s n : ℕ}
variable (D : WeightedFive K s)

/-- A chronological list of distinct nonzero supported clocks that
really accounts for every earlier active physical row. -/
structure Debuts (n : ℕ) where
  index : Fin n→Fin s
  ordered : StrictMono index
  active : ∀ i,D.base (index i)≠0
  nz : ∀ i,D.clock (index i)≠0
  inj : Function.Injective (D.clock ∘ index)
  covered : ∀ i l,l < index i → D.base l≠0 → D.clock l≠0 →
    ∃ j : Fin n,j < i ∧ D.clock l=D.clock (index j)

variable {D}

theorem Debuts.advance (E : D.Debuts n) (has : n<D.sites.card) :
    Nonempty (D.Debuts (n+1)) := by
  classical
  let S := Finset.univ.image (D.clock ∘ E.index)
  have hs : S.card≤n := Finset.card_image_le.trans (by simp)
  obtain ⟨i,h⟩ := D.next_debut S (hs.trans_lt has)
  have before (j : Fin n) : E.index j < i := by
    by_contra! no
    apply h.fresh
    rcases lt_or_eq_of_le no with he | he
    · obtain ⟨k,_,v⟩ := E.covered j i he h.active h.nz
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,v.symm⟩
    · exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg D.clock he.symm⟩
  let f : Fin (n+1)→Fin s := Fin.snoc E.index i
  have ord : StrictMono f := by
    intro a b hab
    revert hab
    refine Fin.lastCases ?_ (fun x => ?_) a
    · intro e
      exact (not_le_of_gt e (Fin.le_last b)).elim
    refine Fin.lastCases ?_ (fun y => ?_) b
    · intro _
      simpa only [f,Fin.snoc_last,Fin.snoc_castSucc] using before x
    · intro e
      simpa only [f,Fin.snoc_castSucc] using E.ordered (Fin.castSucc_lt_castSucc_iff.mp e)
  refine ⟨⟨f,ord,?_,?_,?_,?_⟩⟩
  · exact Fin.lastCases (by simpa only [f,Fin.snoc_last] using h.active)
      (fun j => by simpa only [f,Fin.snoc_castSucc] using E.active j)
  · exact Fin.lastCases (by simpa only [f,Fin.snoc_last] using h.nz)
      (fun j => by simpa only [f,Fin.snoc_castSucc] using E.nz j)
  · change Function.Injective (D.clock ∘ Fin.snoc E.index i)
    rw [Fin.comp_snoc]
    apply Fin.snoc_injective_of_injective E.inj
    rintro ⟨j,e⟩
    exact h.fresh (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,e⟩)
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · intro l hl ba na
      have old : l < i := by simpa only [f,Fin.snoc_last] using hl
      obtain ⟨t,_,et⟩ := Finset.mem_image.mp (h.old l old ba na)
      exact ⟨t.castSucc,Fin.castSucc_lt_last _,by simpa only [f,Fin.snoc_castSucc,Function.comp_apply] using et.symm⟩
    · intro l hl ba na
      have old : l < E.index j := by simpa only [f,Fin.snoc_castSucc] using hl
      obtain ⟨t,ht,et⟩ := E.covered j l old ba na
      exact ⟨t.castSucc,Fin.castSucc_lt_castSucc_iff.mpr ht,
        by simpa only [f,Fin.snoc_castSucc] using et⟩

theorem exists_debuts (D : WeightedFive K s) (n : ℕ) (hn : n≤D.sites.card) :
    Nonempty (D.Debuts n) := by
  induction n with
  | zero =>
    refine ⟨⟨Fin.elim0,?_,?_,?_,?_,?_⟩⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  | succ n ih =>
    obtain ⟨E⟩ := ih (by omega)
    exact E.advance (by omega)

def Debuts.priorIndex (E : D.Debuts n) (i : Fin n) (j : Fin i.val) : Fin s :=
  E.index (Fin.castLE i.isLt.le j)

theorem Debuts.debut_at (E : D.Debuts n) (i : Fin n) :
    D.Debut (Finset.univ.image (D.clock ∘ E.priorIndex i)) (E.index i) := by
  classical
  refine ⟨E.active i,E.nz i,?_,?_⟩
  · intro incl
    obtain ⟨j,_,he⟩ := Finset.mem_image.mp incl
    have h := E.inj he
    exact (Nat.ne_of_lt j.isLt) (congrArg (fun a : Fin n => a.val) h)
  · intro l hl hlb hlc
    obtain ⟨j,hj,eq⟩ := E.covered i l hl hlb hlc
    exact Finset.mem_image.mpr ⟨⟨j.val,hj⟩,Finset.mem_univ _,eq.symm⟩

end
end RKCert.Paired.LocalProjection.WeightedFive
