module

public import RKCert.ReviewedNative.RowAnnihilator

import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

@[expose] public section

/-! # Rank-many actual coordinate restrictions and their rows

This is finite linear algebra on the original coordinate labels.
A selected frame determines a subspace column by its ordinary
evaluations, and its dual realizes any row on the subspace by a row
supported on the selected labels. No tableau or tree is shortened here.
-/

namespace RKResearch.Certified.Graded.RankCoordinates

open Module RKResearch.Certified.Graded.Reverse

noncomputable section

variable {ι κ K : Type*} [Field K]

/-- Evaluate a column on a family of its original coordinates. -/
def restrictColumns (a : κ → ι) : (ι → K) →ₗ[K] (κ → K) :=
  LinearMap.pi fun j => LinearMap.proj (a j)

@[simp] theorem restrictColumns_apply (a : κ → ι) (v : ι → K) (j : κ) :
    restrictColumns a v j = v (a j) := rfl

/-- The same evaluation, restricted to a subspace of columns. -/
def restrictSubspace (U : Submodule K (ι → K)) (a : κ → ι) : U →ₗ[K] (κ → K) :=
  (restrictColumns a).comp U.subtype

@[simp] theorem restrictSubspace_apply (U : Submodule K (ι → K)) (a : κ → ι)
    (x : U) (j : κ) : restrictSubspace U a x j = (x : ι → K) (a j) := rfl

/-- An injective evaluation on exactly as many distinct ambient labels
as the subspace has dimensions. -/
structure CoordinateFrame (U : Submodule K (ι → K)) where
  labels : Fin (finrank K U) ↪ ι
  injective : Function.Injective (restrictSubspace U labels)

variable [Fintype ι]

/-- The frame is produced on actual coordinates, not assumed as an
abstract vector-space isomorphism or supplied pivot. -/
theorem exists_coordinateFrame (U : Submodule K (ι → K)) :
    Nonempty (CoordinateFrame U) := by
  classical
  let eval : ι → Module.Dual K U := fun i => (LinearMap.proj i).comp U.subtype
  obtain ⟨J, a, ha, span_eq, independent⟩ := exists_linearIndependent' K eval
  letI : Fintype J := Fintype.ofInjective a ha
  have inj : Function.Injective (restrictSubspace U a) := by
    intro x y h
    apply Subtype.ext
    funext i
    let Z := LinearMap.ker (Module.Dual.eval K U (x-y))
    have sub : Submodule.span K (Set.range (eval ∘ a)) ≤ Z := by
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      change eval (a j) (x-y) = 0
      rw [map_sub]
      exact sub_eq_zero.mpr (congrFun h j)
    have mem : eval i ∈ Submodule.span K (Set.range (eval ∘ a)) := by
      rw [span_eq]
      exact Submodule.subset_span ⟨i, rfl⟩
    have hz : eval i ∈ Z := sub mem
    change eval i (x-y) = 0 at hz
    rw [map_sub] at hz
    exact sub_eq_zero.mp hz
  have le₁ : finrank K U ≤ Fintype.card J := by
    simpa only [Module.finrank_fintype_fun_eq_card] using
      (LinearMap.finrank_le_finrank_of_injective inj)
  have le₂ : Fintype.card J ≤ finrank K U := by
    have bound : finrank K (Submodule.span K (Set.range (eval ∘ a))) ≤
        finrank K (Module.Dual K U) := Submodule.finrank_le _
    rwa [finrank_span_eq_card independent, Subspace.dual_finrank_eq] at bound
  let e : J ≃ Fin (finrank K U) := Fintype.equivFinOfCardEq (le₂.antisymm le₁)
  let labels : Fin (finrank K U) ↪ ι :=
    ⟨fun j => a (e.symm j), ha.comp e.symm.injective⟩
  refine ⟨⟨labels, ?_⟩⟩
  intro x y h
  apply inj
  funext j
  have h' := congrFun h (e j)
  change (x : ι → K) (a (e.symm (e j))) = (y : ι → K) (a (e.symm (e j))) at h'
  change (x : ι → K) (a j) = (y : ι → K) (a j)
  simpa only [Equiv.symm_apply_apply] using h'

/-- An injective frame is surjective because it has the exact rank. -/
def CoordinateFrame.restrictEquiv {U : Submodule K (ι → K)} (F : CoordinateFrame U) :
    U ≃ₗ[K] (Fin (finrank K U) → K) :=
  (restrictSubspace U F.labels).linearEquivOfInjective F.injective
    (by rw [Module.finrank_fin_fun])

@[simp] theorem CoordinateFrame.restrictEquiv_apply {U : Submodule K (ι → K)}
    (F : CoordinateFrame U) (x : U) (j : Fin (finrank K U)) :
    F.restrictEquiv x j = (x : ι → K) (F.labels j) := rfl

section RowExtension

variable [Fintype κ]

/-- Transpose of coordinate restriction in ordinary dot-row coordinates. -/
def extendRows (a : κ → ι) : (κ → K) →ₗ[K] (ι → K) :=
  dotDual.symm.toLinearMap.comp
    ((Module.Dual.transpose (restrictColumns a)).comp dotDual.toLinearMap)

theorem row_extendRows (a : κ → ι) (w : κ → K) (v : ι → K) :
    row (extendRows a w) v = row w (restrictColumns a v) := by
  change dotDual (dotDual.symm (Module.Dual.transpose (restrictColumns a) (dotDual w))) v =
    row w (restrictColumns a v)
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem extendRows_off (a : κ → ι) (w : κ → K) {i : ι} (hi : i ∉ Set.range a) :
    extendRows a w i = 0 := by
  classical
  rw [← row_coordinate (extendRows a w) i, row_extendRows]
  have zero : restrictColumns a (coordinate (K:=K) i) = 0 := by
    funext j
    rw [restrictColumns_apply]
    have ne : a j ≠ i := fun e => hi ⟨j, e⟩
    simp [coordinate, ne]
  rw [zero, map_zero]

/-- For a selection without repeated labels the transpose is literal
extension by zero, with the original coefficient on each chosen label. -/
theorem extendRows_on (a : κ ↪ ι) (w : κ → K) (j : κ) :
    extendRows a w (a j) = w j := by
  classical
  rw [← row_coordinate (extendRows a w) (a j), row_extendRows]
  have point : restrictColumns a (coordinate (K:=K) (a j)) = coordinate (K:=K) j := by
    funext k
    rw [restrictColumns_apply]
    by_cases eq : k = j
    · subst k
      simp [coordinate]
    · have ne : a k ≠ a j := fun e => eq (a.injective e)
      simp [coordinate, eq, ne]
  rw [point, row_coordinate]

end RowExtension

/-- A linear functional on the original subspace as a row on the selected
coordinates. This is the transpose of the inverse frame. -/
def CoordinateFrame.rowOver {U : Submodule K (ι → K)} (F : CoordinateFrame U) :
    Module.Dual K U →ₗ[K] (Fin (finrank K U) → K) :=
  dotDual.symm.toLinearMap.comp (Module.Dual.transpose F.restrictEquiv.symm.toLinearMap)

theorem CoordinateFrame.row_rowOver {U : Submodule K (ι → K)} (F : CoordinateFrame U)
    (f : Module.Dual K U) (x : U) :
    row (F.rowOver f) (F.restrictEquiv x) = f x := by
  change dotDual (dotDual.symm (Module.Dual.transpose F.restrictEquiv.symm.toLinearMap f))
    (F.restrictEquiv x) = f x
  rw [LinearEquiv.apply_symm_apply]
  change f (F.restrictEquiv.symm (F.restrictEquiv x)) = f x
  rw [LinearEquiv.symm_apply_apply]

/-- The same functional extended to an actual ambient row supported on
the frame labels. -/
def CoordinateFrame.extendFunctional {U : Submodule K (ι → K)} (F : CoordinateFrame U) :
    Module.Dual K U →ₗ[K] (ι → K) :=
  (extendRows F.labels).comp F.rowOver

theorem CoordinateFrame.row_extendFunctional {U : Submodule K (ι → K)} (F : CoordinateFrame U)
    (f : Module.Dual K U) (x : U) :
    row (F.extendFunctional f) (x : ι → K) = f x := by
  change row (extendRows F.labels (F.rowOver f)) (x : ι → K) = f x
  rw [row_extendRows]
  have eq : restrictColumns F.labels (x : ι → K) = F.restrictEquiv x := by
    funext j
    rw [restrictColumns_apply, CoordinateFrame.restrictEquiv_apply]
  rw [eq, F.row_rowOver]

theorem CoordinateFrame.extendFunctional_off {U : Submodule K (ι → K)}
    (F : CoordinateFrame U) (f : Module.Dual K U) {i : ι}
    (hi : i ∉ Set.range F.labels) : F.extendFunctional f i = 0 :=
  extendRows_off F.labels (F.rowOver f) hi

end

end RKResearch.Certified.Graded.RankCoordinates
