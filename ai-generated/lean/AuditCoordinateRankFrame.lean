module

import RKCert.ReviewedNative.CoordinateRankFrame

open Module RKResearch.Certified.Graded RKResearch.Certified.Graded.RankCoordinates

/- The frame is produced at the true rank in actual distinct labels. -/
example {ι K : Type*} [Fintype ι] [Field K] (U : Submodule K (ι → K)) :
    ∃ a : Fin (finrank K U) ↪ ι, Function.Injective (restrictSubspace U a) := by
  obtain ⟨F⟩ := exists_coordinateFrame U
  exact ⟨F.labels, F.injective⟩

example {ι K : Type*} [Fintype ι] [Field K] {U : Submodule K (ι → K)}
    (F : CoordinateFrame U) (x : U) (j : Fin (finrank K U)) :
    F.restrictEquiv x j = (x : ι → K) (F.labels j) :=
  F.restrictEquiv_apply x j

/- The ambient transpose is the same row on each selected label, zero off them. -/
example {ι κ K : Type*} [Fintype ι] [Fintype κ] [Field K]
    (a : κ ↪ ι) (w : κ → K) :
    (∀ v : ι → K, row (extendRows a w) v = row w (restrictColumns a v)) ∧
      (∀ j, extendRows a w (a j) = w j) ∧
      (∀ i, i ∉ Set.range a → extendRows a w i = 0) :=
  ⟨row_extendRows a w, extendRows_on a w, fun _ hi => extendRows_off a w hi⟩

example {ι K : Type*} [Fintype ι] [Field K] {U : Submodule K (ι → K)}
    (F : CoordinateFrame U) (f : Module.Dual K U) (x : U) :
    row (F.rowOver f) (F.restrictEquiv x) = f x :=
  F.row_rowOver f x

example {ι K : Type*} [Fintype ι] [Field K] {U : Submodule K (ι → K)}
    (F : CoordinateFrame U) (f : Module.Dual K U) :
    (∀ x : U, row (F.extendFunctional f) (x : ι → K) = f x) ∧
      (∀ i, i ∉ Set.range F.labels → F.extendFunctional f i = 0) :=
  ⟨F.row_extendFunctional f, fun _ hi => F.extendFunctional_off f hi⟩

#print axioms RKResearch.Certified.Graded.RankCoordinates.exists_coordinateFrame
#print axioms RKResearch.Certified.Graded.RankCoordinates.CoordinateFrame.restrictEquiv_apply
#print axioms RKResearch.Certified.Graded.RankCoordinates.row_extendRows
#print axioms RKResearch.Certified.Graded.RankCoordinates.extendRows_on
#print axioms RKResearch.Certified.Graded.RankCoordinates.extendRows_off
#print axioms RKResearch.Certified.Graded.RankCoordinates.CoordinateFrame.row_rowOver
#print axioms RKResearch.Certified.Graded.RankCoordinates.CoordinateFrame.row_extendFunctional
#print axioms RKResearch.Certified.Graded.RankCoordinates.CoordinateFrame.extendFunctional_off
