module

public import RKCert.ReviewedNative.LiveSuffixContrastCoordinates
public import RKCert.ReviewedNative.LiveSuffixContrastOddPaid
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact rank of the signed live-suffix contrast pairing

The radical is exactly the supported constant line when total signed
mass cancels, and zero otherwise. This only uses live, nonzero individual
weights, not their signs or any order hypothesis. -/
namespace RKResearch.Certified.Graded.Reverse

open RKResearch Module
open scoped Matrix Classical

noncomputable section

variable {K : Type*} [Field K] {s p q n : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K} {u : Fin s} {y : K}

/-- The original signed mass of exactly the live sites of this cut. -/
abbrev liveSuffixMass (b : Fin s → K) (u : Fin s) : K :=
  row b (extendLiveSuffix b u (1 : suffixLiveStages b u → K))

private theorem coord_off {i j : Fin s} (h : j ≠ i) :
    coordinate (K := K) i j = 0 := by
  classical
  simp [coordinate, h]

private theorem signedPairing_mul_coordinate (b v : Fin s → K) (i : Fin s) :
    suffixSignedPairing b v (coordinate (K := K) i) = v i * b i := by
  have e : v * coordinate (K := K) i = v i • coordinate i := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [coordinate, Pi.smul_apply, smul_eq_mul]
    · simp only [Pi.mul_apply, Pi.smul_apply, coord_off hj, mul_zero, smul_zero]
  rw [suffixSignedPairing_apply, e, map_smul, smul_eq_mul, row_coordinate]

private theorem signedPairing_supported_one (b : Fin s → K) (u : Fin s)
    {v : Fin s → K} (hv : v ∈ suffixLiveContrasts b u) :
    suffixSignedPairing b (extendLiveSuffix b u (1 : suffixLiveStages b u → K)) v =
      row b v := by
  rw [suffixSignedPairing_apply]
  have eq : extendLiveSuffix b u (1 : suffixLiveStages b u → K) * v = v := by
    funext i
    change extendLiveSuffix b u (1 : suffixLiveStages b u → K) i * v i = v i
    by_cases hi : i ∈ suffixLiveStages b u
    · rw [extendLiveSuffix_apply, dite_eq_left hi, Pi.one_apply, one_mul]
    · rw [(mem_suffixLiveContrasts.mp hv).1 i hi, mul_zero]
  rw [eq]

/-- A radical vector on the supported carrier is a multiple of its
literal supported constant column. The converse needs no nonemptiness. -/
theorem suffixContrastPairing_mem_ker_iff
    (live : (suffixLiveStages b u).Nonempty) (v : suffixLiveContrasts b u) :
    v ∈ LinearMap.ker (suffixContrastPairing b u) ↔
      ∃ a : K, v.val = a • extendLiveSuffix b u (1 : suffixLiveStages b u → K) := by
  classical
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := live
    have bi : b i ≠ 0 := (mem_suffixLiveStages.mp hi).2
    refine ⟨v.val i, funext (fun j => ?_)⟩
    by_cases hj : j ∈ suffixLiveStages b u
    · have bj : b j ≠ 0 := (mem_suffixLiveStages.mp hj).2
      let e : Fin s → K := b i • coordinate j - b j • coordinate i
      have eh : e ∈ suffixLiveContrasts b u := by
        apply mem_suffixLiveContrasts.mpr
        refine ⟨fun l nl => ?_, ?_⟩
        · have lj : l ≠ j := fun x => nl (x.symm ▸ hj)
          have li : l ≠ i := fun x => nl (x.symm ▸ hi)
          dsimp only [e]
          simp only [Pi.sub_apply, Pi.smul_apply, coord_off lj, coord_off li, smul_zero, sub_zero]
        · dsimp only [e]
          simp only [map_sub, map_smul, row_coordinate, smul_eq_mul]
          ring
      have hz : suffixContrastPairing b u v = (0 : Module.Dual K (suffixLiveContrasts b u)) := by
        rw [← LinearMap.mem_ker]
        exact hv
      have h := DFunLike.congr_fun hz (⟨e, eh⟩ : suffixLiveContrasts b u)
      change suffixSignedPairing b v.val e = 0 at h
      dsimp only [e] at h
      simp only [map_sub, map_smul, signedPairing_mul_coordinate, smul_eq_mul] at h
      have h' : b i * b j * (v.val j - v.val i) = 0 := by
        calc
          _ = b i * (v.val j * b j) - b j * (v.val i * b i) := by ring
          _ = 0 := h
      have eq : v.val j = v.val i :=
        sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_left (mul_ne_zero bi bj))
      simpa only [Pi.smul_apply, smul_eq_mul, extendLiveSuffix_apply, dite_eq_left hj,
        Pi.one_apply, mul_one] using eq
    · rw [(mem_suffixLiveContrasts.mp v.property).1 j hj]
      simp only [Pi.smul_apply, extendLiveSuffix_apply, dite_eq_right hj, smul_zero]
  · rintro ⟨a, e⟩
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro w
    change suffixSignedPairing b v.val w.val = 0
    rw [e, map_smul, LinearMap.smul_apply, signedPairing_supported_one b u w.property,
      (mem_suffixLiveContrasts.mp w.property).2, smul_zero]

/-- The native contrast pairing rank is exactly k−1, losing exactly one
more only if the unmodified signed mass of this same subset is zero. -/
theorem finrank_suffixContrastPairing_range_add_losses
    (live : (suffixLiveStages b u).Nonempty) :
    finrank K (suffixContrastPairing b u).range +
      (if liveSuffixMass b u = 0 then 1 else 0) + 1 = (suffixLiveStages b u).card := by
  classical
  let w := extendLiveSuffix b u (1 : suffixLiveStages b u → K)
  have dimC := finrank_suffixLiveContrasts_add_one b u live
  have dim := (suffixContrastPairing b u).finrank_range_add_finrank_ker
  by_cases mass : liveSuffixMass b u = 0
  · have wm : w ∈ suffixLiveContrasts b u := by
      apply mem_suffixLiveContrasts.mpr
      exact ⟨fun i hi => by simp [w, hi], mass⟩
    let W : suffixLiveContrasts b u := ⟨w, wm⟩
    have wn : W ≠ 0 := by
      obtain ⟨i, hi⟩ := live
      intro h
      have z := congrArg (fun v : suffixLiveContrasts b u => v.val i) h
      change w i = 0 at z
      rw [show w i = 1 by simp [w, hi]] at z
      exact one_ne_zero z
    have ker : LinearMap.ker (suffixContrastPairing b u) = K ∙ W := by
      ext v
      rw [suffixContrastPairing_mem_ker_iff live, Submodule.mem_span_singleton]
      constructor
      · rintro ⟨a, h⟩
        exact ⟨a, Subtype.ext h.symm⟩
      · rintro ⟨a, h⟩
        exact ⟨a, (congrArg Subtype.val h).symm⟩
    rw [ker, finrank_span_singleton wn] at dim
    simp only [if_pos mass]
    omega
  · have ker : LinearMap.ker (suffixContrastPairing b u) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro v hv
      obtain ⟨a, h⟩ := (suffixContrastPairing_mem_ker_iff live v).mp hv
      have z : row b v.val = 0 := (mem_suffixLiveContrasts.mp v.property).2
      rw [h, map_smul, smul_eq_mul] at z
      have az := (mul_eq_zero.mp z).resolve_right mass
      rw [az, zero_smul] at h
      exact (Submodule.mem_bot K).mpr (Subtype.ext h)
    rw [ker, finrank_bot] at dim
    simp only [if_neg mass, add_zero]
    omega

/-- Explicit ceiling-half contrast charge living entirely in reverse
slack, with the same signed mass and the same original live support. -/
theorem odd_paid_live_suffix_contrast_reverse_width
    (ha : A.IsLowerTriangular) (ho : HasOrder p A b) (rpay : q+n+2 ≤ p)
    (opay : 2*q+1 ≤ p) (first : firstSeed A b ∈ tailZero u)
    (cl : ∀ i, u ≤ i → b i ≠ 0 → reflectedClock A i = y)
    (live : (suffixLiveStages b u).Nonempty) :
    let k := (suffixLiveStages b u).card
    let loss : ℕ := if liveSuffixMass b u = 0 then 1 else 0
    finrank K (treeSpace A q) + finrank K (primitiveBack A b n) +
      ((k-1-loss)+1)/2 ≤ s := by
  classical
  let loss : ℕ := if liveSuffixMass b u = 0 then 1 else 0
  let k := (suffixLiveStages b u).card
  change finrank K (treeSpace A q) + finrank K (primitiveBack A b n) +
    ((k-1-loss)+1)/2 ≤ s
  apply suffix_contrast_rank_floor_add_reverse_le_stages
    (a := k-1-loss) ha ho rpay opay first cl
  have rank := finrank_suffixContrastPairing_range_add_losses (b := b) (u := u) live
  change finrank K (suffixContrastPairing b u).range + loss + 1 = k at rank
  omega

end
end RKResearch.Certified.Graded.Reverse
