module

public import RKCert.ReviewedNative.PhysicalLabelOrbit
public import RKCert.ReviewedNative.LocalLinearJointBands

@[expose] public section

/-! # A true refined joint-band census

The head uses the joint (clock, axis) labels. The clean contrast still
uses ordinary clock labels. Saturation produces literal support at
every physical row, including rows with initially zero amplitude. -/
namespace RKResearch.Certified.Graded.Reverse.LocalLinear

open RKResearch Module Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock PhysicalCensus
open scoped Classical Matrix BigOperators
noncomputable section

variable {K : Type*} [Field K] {s : ℕ}
variable {y f ξ e τ W : Fin s → K} {Q : K[X]} {U J : Submodule K (Fin s → K)}

theorem scalar_label_masks_of_diag {a : Fin s → K}
    (stable : U.map (diag a) ≤ U) :
    ∀ x, U.map (diag (labelIndicator a x : Fin s → K)) ≤ U := by
  rintro x _ ⟨v,hv,rfl⟩
  have mem := clock_function_mem (fun _ hz => stable (Submodule.mem_map_of_mem hz))
    (fun t => if t=x then (1 : K) else 0) hv
  have same : diag (labelIndicator a x : Fin s → K) v = (fun i => (if a i = x then 1 else 0) * v i) := by
    ext i
    simp only [diag_apply, labelIndicator]
  rw [same]
  exact mem

def jointClock (y ξ : Fin s → K) (i : Fin s) : K × K := (y i, ξ i)

def refinedLabel (y f ξ e : Fin s → K) (i : Fin s) : K × K × K × K :=
  (y i, f i, ξ i, e i)

def refinedCoreLabels : Set (K × K × K × K) := {x | x.2.2.2 = 1}

def refinedHeadLabels (Q : K[X]) (T : Finset (K × K)) : Set (K × K × K × K) :=
  {x | x.2.2.2 = 0 ∧ x.2.1 = Q.eval x.1 ∧ (x.1,x.2.2.1) ∈ T}

def refinedContrastLabels (Q : K[X]) (T : Finset K) : Set (K × K × K × K) :=
  {x | x.2.2.2 = 0 ∧ x.2.1 = 0 ∧ x.2.2.1 = 0 ∧ Q.eval x.1 ≠ 0 ∧ x.1 ∈ T}

theorem ordinary_clock_labels_eq_weightedSites (y v : Fin s → K) :
    activeLabels y v = weightedSites y v := by
  ext a
  rw [mem_activeLabels, mem_weightedSites]

theorem ordinary_le_joint_clock_labels (y ξ τ : Fin s → K) :
    (weightedSites y τ).card ≤ (activeLabels (jointClock y ξ) τ).card := by
  rw [←ordinary_clock_labels_eq_weightedSites]
  exact activeLabels_card_project_le (jointClock y ξ) τ Prod.fst

theorem ordinary_lt_joint_clock_labels_of_split {a : K} {i j : Fin s}
    (ti : τ i ≠ 0) (tj : τ j ≠ 0) (hi : y i = a) (hj : y j = a) (ne : ξ i ≠ ξ j) :
    (weightedSites y τ).card < (activeLabels (jointClock y ξ) τ).card := by
  rw [←ordinary_clock_labels_eq_weightedSites]
  exact activeLabels_card_project_lt (lab:=jointClock y ξ) Prod.fst
    (mem_activeLabels.mpr ⟨i,ti,rfl⟩) (mem_activeLabels.mpr ⟨j,tj,rfl⟩)
    (fun eq => ne (congrArg Prod.snd eq)) (hi.trans hj.symm)

structure RefinedJointBandCensus (y f ξ e τ W : Fin s → K) (Q : K[X])
    (U J : Submodule K (Fin s → K)) : Prop where
  ordinary : JointBandCensus y f e τ W Q U J
  headStable : U.map (diag f) ≤ U
  axisStable : U.map (diag ξ) ≤ U
  markStable : U.map (diag e) ≤ U
  contrastOffAxis : ∀ i, W i ≠ 0 → ξ i = 0
  mass : ∀ u ∈ U, (∑ i, u i) = 0

private theorem refined_separations (Q : K[X]) (T : Finset (K × K)) (S : Finset K) :
    Disjoint refinedCoreLabels (refinedHeadLabels Q T) ∧
    Disjoint refinedCoreLabels (refinedContrastLabels Q S) ∧
    Disjoint (refinedHeadLabels Q T) (refinedContrastLabels Q S) := by
  refine ⟨Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_, Set.disjoint_left.mpr ?_⟩
  · intro x hc ht
    change x.2.2.2 = 1 at hc
    exact one_ne_zero (hc.symm.trans ht.1)
  · intro x hc hw
    change x.2.2.2 = 1 at hc
    exact one_ne_zero (hc.symm.trans hw.1)
  · intro x ht hw
    exact hw.2.2.2.1 (ht.2.1.symm.trans hw.2.1)

namespace RefinedJointBandCensus

private theorem core_on (C : RefinedJointBandCensus y f ξ e τ W Q U J) :
    OnLabels (refinedLabel y f ξ e) refinedCoreLabels J := by
  intro v hv i off
  rcases C.ordinary.binary i with zero | one
  · exact C.ordinary.offCore v hv i zero
  · exact (off one).elim

private theorem head_on (C : RefinedJointBandCensus y f ξ e τ W Q U J) :
    OnLabels (refinedLabel y f ξ e) (refinedHeadLabels Q (activeLabels (jointClock y ξ) τ))
      (labelOrbit (jointClock y ξ) τ) := by
  apply labelOrbit_on_of_live
  intro i ti
  exact ⟨(C.ordinary.tauRows i ti).1, (C.ordinary.tauRows i ti).2,
    mem_activeLabels.mpr ⟨i,ti,rfl⟩⟩

private theorem contrast_on (C : RefinedJointBandCensus y f ξ e τ W Q U J) :
    OnLabels (refinedLabel y f ξ e) (refinedContrastLabels Q (weightedSites y W))
      (completeOrbit y W) := by
  rintro _ ⟨R,rfl⟩ i off
  rw [weightedEval_apply]
  by_cases wi : W i = 0
  · rw [wi,mul_zero]
  · obtain ⟨ei, fi, qi⟩ := C.ordinary.contrastRows i wi
    exact (off ⟨ei, fi, C.contrastOffAxis i wi, qi, mem_weightedSites.mpr ⟨i,wi,rfl⟩⟩).elim

private theorem joined (C : RefinedJointBandCensus y f ξ e τ W Q U J) :
    J ⊔ labelOrbit (jointClock y ξ) τ ⊔ completeOrbit y W ≤ annih U := by
  refine sup_le (sup_le C.ordinary.coreOrth ?_)
    (completeOrbit_annih C.ordinary.clockStable C.ordinary.contrastOrth)
  exact labelOrbit_annih_of_masks C.ordinary.tauOrth
    (labelMasks_product (scalar_label_masks_of_diag C.ordinary.clockStable)
      (scalar_label_masks_of_diag C.axisStable))

theorem refined_indicator (C : RefinedJointBandCensus y f ξ e τ W Q U J)
    (x : K × K × K × K) :
    (labelIndicator (refinedLabel y f ξ e) x : Fin s → K) ∈ annih U := by
  apply labelIndicator_annih_of_masks _ C.mass
  exact labelMasks_product (scalar_label_masks_of_diag C.ordinary.clockStable)
    (labelMasks_product (scalar_label_masks_of_diag C.headStable)
      (labelMasks_product (scalar_label_masks_of_diag C.axisStable)
        (scalar_label_masks_of_diag C.markStable)))

theorem rank (C : RefinedJointBandCensus y f ξ e τ W Q U J) :
    finrank K U + finrank K J + (activeLabels (jointClock y ξ) τ).card +
      (weightedSites y W).card ≤ s := by
  obtain ⟨st,sr,tr⟩ := refined_separations Q (activeLabels (jointClock y ξ) τ) (weightedSites y W)
  have dims := finrank_supported_triple C.core_on C.head_on C.contrast_on st sr tr
  have upper := Submodule.finrank_mono C.joined
  rw [dims, labelOrbit_rank, completeOrbit_rank] at upper
  have all := finrank_annih U
  rw [Fintype.card_fin] at all
  omega

/-- Saturation is on the actual four-axis physical labels. In either
noncore role it supplies the actual row's nonzero amplitude, not just
the existence of some other live stage in its clock fibre. -/
theorem physical_live_cover (C : RefinedJointBandCensus y f ξ e τ W Q U J)
    (fill : s ≤ finrank K U + finrank K J + (activeLabels (jointClock y ξ) τ).card +
      (weightedSites y W).card) :
    ∀ i, e i = 1 ∨ (e i = 0 ∧ f i = Q.eval (y i) ∧ τ i ≠ 0) ∨
      (e i = 0 ∧ f i = 0 ∧ ξ i = 0 ∧ Q.eval (y i) ≠ 0 ∧ W i ≠ 0) := by
  obtain ⟨st,sr,tr⟩ := refined_separations Q (activeLabels (jointClock y ξ) τ) (weightedSites y W)
  have ranks : finrank K (annih U) ≤
      finrank K J + finrank K (labelOrbit (jointClock y ξ) τ) + finrank K (completeOrbit y W) := by
    rw [labelOrbit_rank, completeOrbit_rank]
    have all := finrank_annih U
    rw [Fintype.card_fin] at all
    omega
  have cover := exact_supported_triple_live C.core_on C.head_on C.contrast_on st sr tr
    C.joined ranks (fun i => C.refined_indicator _)
  intro i
  rcases cover.2 i with ⟨ci, _, _, _⟩ | ⟨hi,v,hv,v1⟩ | ⟨wi,v,hv,v1⟩
  · exact Or.inl ci
  · exact Or.inr (Or.inl ⟨hi.1, hi.2.1, labelOrbit_live_of_unit hv v1⟩)
  · refine Or.inr (Or.inr ⟨wi.1, wi.2.1, wi.2.2.1, wi.2.2.2.1, ?_⟩)
    intro zero
    obtain ⟨P,rfl⟩ := hv
    rw [weightedEval_apply, zero, mul_zero] at v1
    exact zero_ne_one v1

end RefinedJointBandCensus
end
end RKResearch.Certified.Graded.Reverse.LocalLinear
