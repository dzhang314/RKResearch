module

public import RKCert.Dirk15DirtyCount
public import RKCert.Dirk15NonC2RadauCut

@[expose] public section

/-! # The true non-C(2) clean port count
The two ordinary cubic dimensions occupy literal b-and-tau zero slots.
No zero-weight row is removed from chronology. -/
namespace RKCert.Paired
open Module
open scoped Classical

noncomputable section
variable {K : Type*} [Field K] [CharZero K]
variable {A : Fin 20→Fin 20→K} {b : Vec K 20}

def cleanRows (A : Fin 20→Fin 20→K) (b : Vec K 20) : Finset (Fin 20) :=
  Finset.univ.filter (fun i => b i≠0 ∧ reverseCubic A b i=0)

def ghostRows (A : Fin 20→Fin 20→K) (b : Vec K 20) : Finset (Fin 20) :=
  Finset.univ.filter (fun i => b i=0 ∧ reverseCubic A b i=0)

def cleanPortSites (A : Fin 20→Fin 20→K) (b : Vec K 20) : Finset K :=
  (cleanRows A b).image (mirror A)

omit [CharZero K] in
theorem mem_cleanRows (i : Fin 20) : i∈cleanRows A b ↔ b i≠0 ∧ reverseCubic A b i=0 := by
  simp [cleanRows]

omit [CharZero K] in
theorem mem_ghostRows (i : Fin 20) : i∈ghostRows A b ↔ b i=0 ∧ reverseCubic A b i=0 := by
  simp [ghostRows]

theorem order15_nonC2_ghost_count (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : 2≤(ghostRows A b).card := by
  classical
  let X := ghostRows A b
  let T := X.image (fun i => Pi.single i (1:K))
  let U := Submodule.span K (T:Set (Vec K 20))
  have allv : zeroSpace A 3≤U := by
    intro v hv
    have support (i : Fin 20) (h : i∉X) : v i=0 :=
      order15_nonC2_cubic_channels ha ho hq hv i (by
        apply or_iff_not_imp_left.mpr
        intro bi
        by_contra ti
        exact h ((mem_ghostRows i).mpr ⟨not_not.mp bi,ti⟩))
    have e : v=∑ i∈X,v i • Pi.single i (1:K) := by
      ext j
      rw [Finset.sum_apply]
      by_cases hj : j∈X
      · rw [Finset.sum_eq_single_of_mem j hj]
        · simp
        · intro i _ hne
          simp [Pi.single_eq_of_ne hne.symm]
      · rw [support _ hj]
        symm
        exact Finset.sum_eq_zero (fun i hi => by
          have hn : j≠i := fun e => hj (e.symm ▸ hi)
          simp [Pi.single_eq_of_ne hn])
    rw [e]
    apply U.sum_mem
    intro i hi
    exact U.smul_mem _ (Submodule.subset_span (Finset.mem_image_of_mem _ hi))
  have rank := Submodule.finrank_mono allv
  have f3 := (order15_nonC2_rank_chart ha ho hq).f3
  rw [f3] at rank
  exact rank.trans ((finrank_span_finset_le_card T).trans Finset.card_image_le)

theorem order15_nonC2_clean_count (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : (cleanRows A b).card≤5 := by
  classical
  let D := dirtyRows A b
  let C := cleanRows A b
  let G := ghostRows A b
  have DC : Disjoint D C := by
    apply Finset.disjoint_left.mpr
    intro i hd hc
    exact (Finset.mem_filter.mp hd).2 ((mem_cleanRows i).mp hc).2
  have DG : Disjoint D G := by
    apply Finset.disjoint_left.mpr
    intro i hd hg
    exact (Finset.mem_filter.mp hd).2 ((mem_ghostRows i).mp hg).2
  have CG : Disjoint C G := by
    apply Finset.disjoint_left.mpr
    intro i hc hg
    exact ((mem_cleanRows i).mp hc).1 ((mem_ghostRows i).mp hg).1
  have hu : (D∪C)∪G=Finset.univ := by
    ext i
    by_cases hi : reverseCubic A b i=0 <;> by_cases bi : b i=0 <;>
      simp [D,C,G,dirtyRows,cleanRows,ghostRows,hi,bi]
  have h := congrArg Finset.card hu
  rw [Finset.card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨DG,CG⟩),
    Finset.card_union_of_disjoint DC,Finset.card_univ,Fintype.card_fin] at h
  have hd : 13≤D.card := (order15_nonC2_dirty_count ha ho hq).1
  have hg : 2≤G.card := order15_nonC2_ghost_count ha ho hq
  change C.card≤5
  omega

theorem order15_nonC2_clean_port_count (ha : LowerArray A) (ho : HasTreeOrderAtLeast A b 15)
    (hq : q₂ (mat A) (nodes A) 1≠0) : (cleanPortSites A b).card≤5 :=
  Finset.card_image_le.trans (order15_nonC2_clean_count ha ho hq)

end
end RKCert.Paired
