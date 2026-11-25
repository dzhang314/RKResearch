module

public import RKCert.ReviewedNative.PhysicalSupportExactCover

@[expose] public section

/-! # Weighted physical label ranges

A whole-label indicator is not a representative row. This module counts
labels occupied by nonzero coordinates, preserves the signed weight of
each original row, and constructs the exact weighted label subspace. -/
namespace RKResearch.Certified.Graded.PhysicalCensus

open Module Reverse RKResearch
open scoped Classical Matrix BigOperators
noncomputable section

variable {K α β : Type*} [Field K] {s : ℕ}

def activeLabels (lab : Fin s → α) (w : Fin s → K) : Finset α :=
  (Finset.univ.filter fun i => w i ≠ 0).image lab

theorem mem_activeLabels {lab : Fin s → α} {w : Fin s → K} {a : α} :
    a ∈ activeLabels lab w ↔ ∃ i, w i ≠ 0 ∧ lab i = a := by
  simp only [activeLabels, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]

theorem activeLabels_project (lab : Fin s → α) (w : Fin s → K) (f : α → β) :
    activeLabels (fun i => f (lab i)) w = (activeLabels lab w).image f := by
  simp only [activeLabels, Finset.image_image, Function.comp_def]

theorem activeLabels_card_project_le (lab : Fin s → α) (w : Fin s → K) (f : α → β) :
    (activeLabels (fun i => f (lab i)) w).card ≤ (activeLabels lab w).card := by
  exact (congrArg Finset.card (activeLabels_project lab w f)).trans_le Finset.card_image_le

/-- Two distinct genuinely live labels above one coarser label give
a strict gain; no injectivity on the physical row set is needed. -/
theorem activeLabels_card_project_lt {lab : Fin s → α} {w : Fin s → K}
    (f : α → β) {a b : α}
    (ha : a ∈ activeLabels lab w) (hb : b ∈ activeLabels lab w)
    (dist : a ≠ b) (same : f a = f b) :
    (activeLabels (fun i => f (lab i)) w).card < (activeLabels lab w).card := by
  rw [activeLabels_project]
  apply lt_of_le_of_ne Finset.card_image_le
  intro eq
  exact dist ((Finset.card_image_iff.mp eq) ha hb same)

def labelSlice (lab : Fin s → α) (w : Fin s → K) (a : α) : Fin s → K :=
  diag (labelIndicator lab a) w

theorem labelSlice_apply (lab : Fin s → α) (w : Fin s → K) (a : α) (i : Fin s) :
    labelSlice lab w a i = if lab i = a then w i else 0 := by
  by_cases eq : lab i = a <;> simp [labelSlice, diag_apply, labelIndicator, eq]

def labelCombination (lab : Fin s → α) (w : Fin s → K) :
    (activeLabels lab w → K) →ₗ[K] (Fin s → K) where
  toFun f := ∑ a : activeLabels lab w, f a • labelSlice lab w a.val
  map_add' f g := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' r f := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

def labelOrbit (lab : Fin s → α) (w : Fin s → K) : Submodule K (Fin s → K) :=
  (labelCombination lab w).range

theorem labelCombination_eval_of_live (lab : Fin s → α) (w : Fin s → K)
    (f : activeLabels lab w → K) {i : Fin s} (wi : w i ≠ 0) :
    labelCombination lab w f i =
      f ⟨lab i, mem_activeLabels.mpr ⟨i, wi, rfl⟩⟩ * w i := by
  let a : activeLabels lab w := ⟨lab i, mem_activeLabels.mpr ⟨i, wi, rfl⟩⟩
  change (∑ t : activeLabels lab w, f t • labelSlice lab w t.val) i = f a * w i
  rw [Finset.sum_apply, Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
  · simp [Pi.smul_apply, smul_eq_mul, labelSlice_apply, a]
  · intro t _ ne
    have off : lab i ≠ t.val := fun eq => ne (Subtype.ext eq.symm)
    simp [Pi.smul_apply, labelSlice_apply, off]

theorem labelCombination_eval_of_off (lab : Fin s → α) (w : Fin s → K)
    (f : activeLabels lab w → K) {i : Fin s} (wi : w i = 0) :
    labelCombination lab w f i = 0 := by
  change (∑ t : activeLabels lab w, f t • labelSlice lab w t.val) i = 0
  rw [Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro t _
  simp [Pi.smul_apply, labelSlice_apply, wi]

theorem labelCombination_injective (lab : Fin s → α) (w : Fin s → K) :
    Function.Injective (labelCombination lab w) := by
  intro f g equal
  funext a
  obtain ⟨i, live, point⟩ := mem_activeLabels.mp a.property
  have atI := congrFun equal i
  rw [labelCombination_eval_of_live lab w f live, labelCombination_eval_of_live lab w g live] at atI
  have eq : (⟨lab i, mem_activeLabels.mpr ⟨i, live, rfl⟩⟩ :
      activeLabels lab w) = a := Subtype.ext point
  rw [eq] at atI
  exact mul_right_cancel₀ live atI

theorem labelOrbit_rank (lab : Fin s → α) (w : Fin s → K) :
    finrank K (labelOrbit lab w) = (activeLabels lab w).card := by
  rw [labelOrbit, LinearMap.finrank_range_of_inj (labelCombination_injective lab w),
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe]

theorem labelOrbit_eval_off {lab : Fin s → α} {w v : Fin s → K} {i : Fin s}
    (hv : v ∈ labelOrbit lab w) (wi : w i = 0) : v i = 0 := by
  obtain ⟨f, rfl⟩ := hv
  exact labelCombination_eval_of_off lab w f wi

theorem labelOrbit_live_of_unit {lab : Fin s → α} {w v : Fin s → K} {i : Fin s}
    (hv : v ∈ labelOrbit lab w) (value : v i = 1) : w i ≠ 0 :=
  fun wi => zero_ne_one ((labelOrbit_eval_off hv wi).symm.trans value)

theorem labelOrbit_on_of_live {lab : Fin s → α} {group : Fin s → β} {w : Fin s → K}
    {B : Set α} (live : ∀ i, w i ≠ 0 → lab i ∈ B) :
    OnLabels lab B (labelOrbit group w) := by
  intro u hu i off
  exact labelOrbit_eval_off hu (by_contra fun wi => off (live i wi))

theorem labelOrbit_annih_of_masks {lab : Fin s → α} {w : Fin s → K}
    {U : Submodule K (Fin s → K)} (orth : w ∈ annih U)
    (stable : ∀ a, U.map (diag (labelIndicator lab a : Fin s → K)) ≤ U) :
    labelOrbit lab w ≤ annih U := by
  rintro _ ⟨f, rfl⟩
  change (∑ a : activeLabels lab w, f a • labelSlice lab w a.val) ∈ annih U
  refine (annih U).sum_mem (fun a _ => (annih U).smul_mem _ ?_)
  apply mem_annih.mpr
  intro z hz
  rw [labelSlice, row_diag]
  exact mem_annih.mp orth _ (stable a.val (Submodule.mem_map_of_mem hz))

theorem labelIndicator_product (lab : Fin s → α) (other : Fin s → β) (a : α) (b : β) :
    (labelIndicator (fun i => (lab i, other i)) (a,b) : Fin s → K) =
      labelIndicator lab a * labelIndicator other b := by
  funext i
  by_cases h : lab i = a <;> by_cases j : other i = b <;>
    simp [labelIndicator, h, j]

/-- Product labels require the actual coordinate masks for both
factors. Repeatedly applying this covers any finite tuple of axes. -/
theorem labelMasks_product {lab : Fin s → α} {other : Fin s → β}
    {U : Submodule K (Fin s → K)}
    (one : ∀ a, U.map (diag (labelIndicator lab a : Fin s → K)) ≤ U)
    (two : ∀ b, U.map (diag (labelIndicator other b : Fin s → K)) ≤ U) :
    ∀ t : α × β, U.map (diag (labelIndicator (fun i => (lab i, other i)) t : Fin s → K)) ≤ U := by
  rintro ⟨a,b⟩ _ ⟨u,hu,rfl⟩
  have mem := one a (Submodule.mem_map_of_mem (two b (Submodule.mem_map_of_mem hu)))
  convert mem using 1
  funext i
  rw [labelIndicator_product]
  simp only [diag_apply, Pi.mul_apply, mul_assoc]

theorem labelIndicator_annih_of_masks {lab : Fin s → α} {U : Submodule K (Fin s → K)}
    (stable : ∀ a, U.map (diag (labelIndicator lab a : Fin s → K)) ≤ U)
    (mass : ∀ u ∈ U, (∑ i, u i) = 0) (a : α) :
    (labelIndicator lab a : Fin s → K) ∈ annih U := by
  apply mem_annih.mpr
  intro u hu
  have test := mass _ (stable a (Submodule.mem_map_of_mem hu))
  simpa only [row_apply, dotProduct, diag_apply] using test

end
end RKResearch.Certified.Graded.PhysicalCensus
