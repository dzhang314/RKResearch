module

public import RKCert.ReviewedNative.RowAnnihilator

@[expose] public section

/-! # Exact annihilator support from real coordinate restrictions

All lifted rows still belong to the original space. The coordinate
restriction is a linear map onto a type of labels, not a reduction of
an RK method or of its native order. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Classical Matrix
noncomputable section
variable {K : Type*} [Field K] {s : ℕ}

def restrictStageColumns (T : Finset (Fin s)) : (Fin s → K) →ₗ[K] (T→K) :=
  LinearMap.pi fun i => LinearMap.proj i.val

@[simp] theorem restrictStageColumns_apply (T : Finset (Fin s)) (v : Fin s→K) (i : T) :
    restrictStageColumns T v i=v i.val := rfl

def extendStageRows (T : Finset (Fin s)) : (T→K) →ₗ[K] (Fin s→K) :=
  dotDual.symm.toLinearMap.comp ((Module.Dual.transpose (restrictStageColumns T)).comp dotDual.toLinearMap)

theorem row_extendStageRows (T : Finset (Fin s)) (w : T→K) (v : Fin s→K) :
    row (extendStageRows T w) v=row w (restrictStageColumns T v) := by
  change dotDual (dotDual.symm (Module.Dual.transpose (restrictStageColumns T) (dotDual w))) v=_
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem extendStageRows_off (T : Finset (Fin s)) (w : T→K) {i : Fin s} (hi : i∉T) :
    extendStageRows T w i=0 := by
  rw [←row_coordinate (extendStageRows T w) i,row_extendStageRows]
  have ev : restrictStageColumns T (coordinate (K:=K) i)=0 := by
    ext k
    rw [restrictStageColumns_apply]
    have ne : k.val≠i := fun e=>hi (e ▸ k.property)
    simp [coordinate,ne]
  rw [ev,map_zero]

theorem extendStageRows_injective (T : Finset (Fin s)) :
    Function.Injective (extendStageRows (K:=K) T) := by
  intro v w h
  ext j
  have e := congrArg (fun x => row x (coordinate (K:=K) j.val)) h
  rw [row_extendStageRows,row_extendStageRows] at e
  have d : restrictStageColumns T (coordinate (K:=K) j.val)=coordinate j := by
    ext k
    rw [restrictStageColumns_apply]
    by_cases z : k=j
    · subst k;simp [coordinate]
    · have ne : k.val≠j.val := fun e=>z (Subtype.ext e)
      simp [coordinate,ne,z]
  rwa [d,row_coordinate,row_coordinate] at e

/-- Once the permitted original support has enough coordinate rank to
pay the full terminal-zero complement, no other coefficient can be
nonzero in that complement. The terminal is outside the support. -/
theorem complement_supported_of_stage_restriction (E : Submodule K (Fin s→K))
    (T : Finset (Fin s)) {t : Fin s} (out : t∉T)
    (pay : finrank K (zeroAt (annih E) t)+finrank K (E.map (restrictStageColumns T))≤T.card) :
    ∀ v∈zeroAt (annih E) t,∀ i∉T,v i=0 := by
  let R := restrictStageColumns (K:=K) T
  let L := extendStageRows (K:=K) T
  let C := annih (E.map R)
  let D := C.map L
  let B := zeroAt (annih E) t
  have sub : D≤B := by
    rintro _ ⟨w,hw,rfl⟩
    refine mem_zeroAt.mpr ⟨mem_annih.mpr ?_, extendStageRows_off T w out⟩
    intro x hx
    rw [row_extendStageRows]
    exact mem_annih.mp hw _ (Submodule.mem_map_of_mem hx)
  have eq : D=LinearMap.range (L.comp C.subtype) := by
    dsimp [D]
    rw [LinearMap.range_comp,Submodule.range_subtype]
  have dr : finrank K D=finrank K C := by
    rw [eq]
    exact LinearMap.finrank_range_of_inj ((extendStageRows_injective T).comp Subtype.val_injective)
  have sum : finrank K (E.map R)+finrank K C=T.card := by
    simpa only [Fintype.card_coe] using finrank_annih (E.map R)
  have rank : finrank K B≤finrank K D := by
    change finrank K B+finrank K (E.map R)≤T.card at pay
    omega
  have fill := Submodule.eq_of_le_of_finrank_le sub rank
  intro v hv i hi
  change v∈B at hv
  rw [←fill] at hv
  obtain ⟨w,_,rfl⟩ := hv
  exact extendStageRows_off T w hi

end
end RKResearch.Certified.Graded.Reverse
