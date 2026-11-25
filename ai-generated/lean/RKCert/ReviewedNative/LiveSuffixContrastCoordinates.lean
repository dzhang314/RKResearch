module

public import RKCert.ReviewedNative.ConstantLiveSuffixContrasts
public import RKCert.ReviewedNative.CompensatedRestrictionRank

@[expose] public section

/-! # Physical coordinates of the native live-suffix contrast space

The carrier of ConstantLiveSuffixContrasts is identified with the kernel
of genuinely signed mass on its actual live subset. No silent row is
included in the isolated pairing, even when it lies between live rows. -/
namespace RKResearch.Certified.Graded.Reverse

open Module RKCert.ReviewedNative.CompensatedRestrictionRank
open scoped Classical Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] {s : ℕ}

abbrev liveSuffixWeights (b : Fin s → K) (u : Fin s) :
    suffixLiveStages b u → K := fun i => b i.val

def liveSuffixRestriction (b : Fin s → K) (u : Fin s) :
    (Fin s → K) →ₗ[K] (suffixLiveStages b u → K) :=
  LinearMap.pi (fun i => LinearMap.proj i.val)

@[simp] theorem liveSuffixRestriction_apply (b : Fin s → K) (u : Fin s)
    (v : Fin s → K) (i : suffixLiveStages b u) :
    liveSuffixRestriction b u v i = v i.val := rfl

/-- Zero extension across the original live subset, not a trimming of A. -/
def extendLiveSuffix (b : Fin s → K) (u : Fin s) :
    (suffixLiveStages b u → K) →ₗ[K] (Fin s → K) where
  toFun v i := if h : i ∈ suffixLiveStages b u then v ⟨i, h⟩ else 0
  map_add' v w := by
    funext i
    by_cases h : i ∈ suffixLiveStages b u
    · simp only [dite_eq_left h, Pi.add_apply]
    · simp only [dite_eq_right h, Pi.add_apply, add_zero]
  map_smul' a v := by
    funext i
    by_cases h : i ∈ suffixLiveStages b u
    · simp only [dite_eq_left h, Pi.smul_apply, RingHom.id_apply]
    · simp only [dite_eq_right h, Pi.smul_apply, smul_zero]

@[simp] theorem extendLiveSuffix_apply (b : Fin s → K) (u : Fin s)
    (v : suffixLiveStages b u → K) (i : Fin s) :
    extendLiveSuffix b u v i = if h : i ∈ suffixLiveStages b u then v ⟨i, h⟩ else 0 := rfl

theorem leftInverse_liveSuffixRestriction_extend (b : Fin s → K) (u : Fin s) :
    Function.LeftInverse (liveSuffixRestriction b u) (extendLiveSuffix b u) := by
  intro v
  funext i
  change extendLiveSuffix b u v i.val = v i
  rw [extendLiveSuffix_apply, dite_eq_left i.property]

theorem extend_restrict_liveSuffix (b : Fin s → K) (u : Fin s) {v : Fin s → K}
    (off : ∀ i, i ∉ suffixLiveStages b u → v i = 0) :
    extendLiveSuffix b u (liveSuffixRestriction b u v) = v := by
  funext i
  by_cases h : i ∈ suffixLiveStages b u
  · simp [h]
  · simp [h, off i h]

/-- Evaluating ambient signed mass after zero extension equals the
coordinate-mass functional already used by the paid rank-one module. -/
theorem row_extendLiveSuffix (b : Fin s → K) (u : Fin s)
    (v : suffixLiveStages b u → K) :
    row b (extendLiveSuffix b u v) = coordinateMass (liveSuffixWeights b u) v := by
  simp only [row_apply, dotProduct, coordinateMass_apply, liveSuffixWeights]
  calc
    _ = ∑ i ∈ suffixLiveStages b u, b i * extendLiveSuffix b u v i := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ h
      rw [extendLiveSuffix_apply, dite_eq_right h, mul_zero]
    _ = _ := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro i _
      rw [extendLiveSuffix_apply, dite_eq_left i.property]

/-- Literal coordinate model for the physical ambient contrast space. -/
def suffixLiveContrastsEquivMassKernel (b : Fin s → K) (u : Fin s) :
    suffixLiveContrasts b u ≃ₗ[K] LinearMap.ker (coordinateMass (liveSuffixWeights b u)) where
  toFun v := ⟨liveSuffixRestriction b u v.val, by
    have h := mem_suffixLiveContrasts.mp v.property
    rw [LinearMap.mem_ker, ← row_extendLiveSuffix, extend_restrict_liveSuffix b u h.1]
    exact h.2⟩
  invFun w := ⟨extendLiveSuffix b u w.val, by
    apply mem_suffixLiveContrasts.mpr
    exact ⟨fun i hi => by simp [hi],
      (row_extendLiveSuffix b u w.val).trans (LinearMap.mem_ker.mp w.property)⟩⟩
  left_inv v := Subtype.ext (extend_restrict_liveSuffix b u (mem_suffixLiveContrasts.mp v.property).1)
  right_inv w := Subtype.ext (leftInverse_liveSuffixRestriction_extend b u w.val)
  map_add' v w := Subtype.ext (map_add (liveSuffixRestriction b u) v.val w.val)
  map_smul' a v := Subtype.ext (map_smul (liveSuffixRestriction b u) a v.val)

/-- Nonemptiness is used exactly here: on one live coordinate the
functional is nonzero, so the signed hyperplane costs one dimension. -/
theorem finrank_suffixLiveContrasts_add_one (b : Fin s → K) (u : Fin s)
    (live : (suffixLiveStages b u).Nonempty) :
    finrank K (suffixLiveContrasts b u) + 1 = (suffixLiveStages b u).card := by
  let f := coordinateMass (liveSuffixWeights b u)
  obtain ⟨i, hi⟩ := live
  let a : suffixLiveStages b u := ⟨i, hi⟩
  have bi : b i ≠ 0 := (mem_suffixLiveStages.mp hi).2
  have h : f (coordinate (K := K) a) = b i := by
    rw [show f = coordinateMass (liveSuffixWeights b u) from rfl, coordinateMass_apply]
    change row (liveSuffixWeights b u) (coordinate a) = b i
    exact row_coordinate _ _
  have surj : Function.Surjective f := by
    intro x
    refine ⟨(x * (b i)⁻¹) • coordinate (K := K) a, ?_⟩
    rw [map_smul, smul_eq_mul, h, mul_assoc, inv_mul_cancel₀ bi, mul_one]
  have r := f.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr surj, finrank_top, Module.finrank_self,
    Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at r
  rw [(suffixLiveContrastsEquivMassKernel b u).finrank_eq, add_comm]
  exact r

end
end RKResearch.Certified.Graded.Reverse
