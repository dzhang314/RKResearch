module

public import RKCert.Dirk15OrdinaryGhosts
public import Mathlib.LinearAlgebra.Pi

@[expose] public section

/-! # Physical ghost coordinate counts before terminal deletion

The rank is the number of original ghost positions, including those at
repeated clocks; Mathlib's equivalence for kernels of projections is used.
-/
namespace RKCert.Paired
open Module
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] {A : Fin 20 → Fin 20 → K} {b : Vec K 20}

def ghostPositions (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Finset (Fin 20) :=
  Finset.univ.filter (fun i => i≠0 ∧ b i=0 ∧ reverseCubic A b i=0)

theorem mem_ghostPositions {i : Fin 20} :
    i∈ghostPositions A b ↔ i≠0 ∧ b i=0 ∧ reverseCubic A b i=0 := by
  simp [ghostPositions]

theorem ghostPositions_vanish {i : Fin 20} {v : Vec K 20}
    (hv : v∈simultaneousGhosts A b) (hi : i∉ghostPositions A b) : v i=0 := by
  obtain ⟨z,hz⟩ := simultaneousGhosts_mem.mp hv
  by_cases e : i=0
  · exact e.symm ▸ z
  · apply hz i
    by_contra! no
    exact hi (mem_ghostPositions.mpr ⟨e,no.1,no.2⟩)

theorem simultaneousGhosts_eq_kernels :
    simultaneousGhosts A b =
      ⨅ (i : Fin 20) (_ : i∉ghostPositions A b),
        LinearMap.ker (LinearMap.proj i) := by
  ext v
  simp only [Submodule.mem_iInf,LinearMap.mem_ker,LinearMap.proj_apply]
  refine ⟨fun h i hi => ghostPositions_vanish h hi,fun h => ?_⟩
  refine simultaneousGhosts_mem.mpr ⟨h 0 (fun hz => (mem_ghostPositions.mp hz).1 rfl),
    fun i hi => h i (fun x => ?_)⟩
  obtain ⟨_,e,f⟩ := mem_ghostPositions.mp x
  exact hi.elim (fun hn => hn e) (fun hn => hn f)

theorem simultaneousGhosts_rank_positions :
    finrank K (simultaneousGhosts A b)=(ghostPositions A b).card := by
  let S : Set (Fin 20) := ghostPositions A b
  have hd : Disjoint S Sᶜ := disjoint_compl_right
  have hu : Set.univ⊆S∪Sᶜ := by simp
  rw [simultaneousGhosts_eq_kernels]
  have e := LinearMap.iInfKerProjEquiv K (fun _ : Fin 20 => K) hd hu
  exact e.finrank_eq.trans ((finrank_fintype_fun_eq_card K).trans (Fintype.card_coe _))

def retainedNonghostPositions (A : Fin 20 → Fin 20 → K) (b : Vec K 20) : Finset (Fin 20) :=
  (Finset.univ.erase (Fin.last 19)) \ ghostPositions A b

theorem mem_retainedNonghostPositions {i : Fin 20} :
    i∈retainedNonghostPositions A b ↔ i≠Fin.last 19 ∧ i∉ghostPositions A b := by
  simp [retainedNonghostPositions,Finset.mem_sdiff]

theorem retainedNonghostPositions_card (hb : b (Fin.last 19)≠0) :
    (retainedNonghostPositions A b).card=19-finrank K (simultaneousGhosts A b) := by
  have sub : ghostPositions A b⊆Finset.univ.erase (Fin.last 19) := by
    intro i mi
    have g := (mem_ghostPositions.mp mi).2.1
    exact Finset.mem_erase.mpr ⟨fun eq => hb (eq ▸ g),Finset.mem_univ _⟩
  rw [retainedNonghostPositions,Finset.card_sdiff_of_subset sub,
    ←simultaneousGhosts_rank_positions]
  simp

theorem exists_retained_nonghost_indices (hb : b (Fin.last 19)≠0) {n : ℕ}
    (num : n=19-finrank K (simultaneousGhosts A b)) :
    ∃ idx : Fin n → Fin 20, Function.Injective idx ∧
      (∀ i,idx i≠Fin.last 19 ∧ idx i∉ghostPositions A b) ∧
      ∀ i : Fin 20,i≠Fin.last 19 → i∉ghostPositions A b → ∃ j,idx j=i := by
  let S := retainedNonghostPositions A b
  have card : Fintype.card (↑S) = n := by
    rw [Fintype.card_coe,retainedNonghostPositions_card hb,num]
  let e : (↑S) ≃ Fin n := (Fintype.equivFin (↑S)).trans (finCongr card)
  let idx : Fin n → Fin 20 := fun i => (e.symm i).val
  refine ⟨idx,Subtype.val_injective.comp e.symm.injective,fun i => ?_,fun i it ig => ?_⟩
  · exact mem_retainedNonghostPositions.mp (e.symm i).property
  · let si : ↑S := ⟨i,mem_retainedNonghostPositions.mpr ⟨it,ig⟩⟩
    exact ⟨e si,congrArg Subtype.val (e.symm_apply_apply si)⟩

end
end RKCert.Paired
