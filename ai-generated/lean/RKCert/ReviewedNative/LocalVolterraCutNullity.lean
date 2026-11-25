module

public import RKCert.ReviewedNative.MixedNodalCut
public import RKCert.ReviewedNative.RowAnnihilator
public import Mathlib.Data.Fin.Rev

@[expose] public section

/-! # Physical local zero-diagonal budgets, on either side of a cut -/

namespace RKResearch.Certified.Graded

open Module
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] {s p k : ℕ}
variable {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}

/-- The zero diagonals in a selected original-stage set. -/
def zeroDiagonalSites (A : Matrix (Fin s) (Fin s) K) (S : Finset (Fin s)) :
    Finset (Fin s) := by
  classical
  exact S.filter (fun i => A i i = 0)

theorem mem_zeroDiagonalSites_iff {S : Finset (Fin s)} {i : Fin s} :
    i ∈ zeroDiagonalSites A S ↔ i ∈ S ∧ A i i = 0 := by
  classical
  exact Finset.mem_filter

/-- A column Volterra kernel supported outside S injects into the local
zero-diagonal coordinates. No condition is needed on the diagonals in S. -/
theorem volterra_column_cutKer_le_zeroSites (ha : A.IsLowerTriangular) (S : Finset (Fin s)) :
    finrank K (cutZeroSpace K S ⊓ (volterra A).ker : Submodule K (Fin s → K)) ≤
      (zeroDiagonalSites A (Finset.univ \ S)).card := by
  let W : Submodule K (Fin s → K) := cutZeroSpace K S ⊓ (volterra A).ker
  let Z := zeroDiagonalSites A (Finset.univ \ S)
  let f : W →ₗ[K] (Z → K) := (cutRestrict K Z).comp W.subtype
  have hf : Function.Injective f := by
    apply (injective_iff_map_eq_zero _).mpr
    intro v hv
    have hs := (Submodule.mem_inf.mp v.property).1
    have hk := (Submodule.mem_inf.mp v.property).2
    change (volterra A) (v : Fin s → K) = 0 at hk
    change cutRestrict K Z (v : Fin s → K) = 0 at hv
    have hz := (mem_cutZeroSpace Z (v : Fin s → K)).mp
      (show (v : Fin s → K) ∈ cutZeroSpace K Z from hv)
    apply Subtype.ext
    funext i
    change (v : Fin s → K) i = 0
    induction i using Fin.strong_induction_on with
    | _ i ih =>
      by_cases hi : i ∈ S
      · exact (mem_cutZeroSpace S (v : Fin s → K)).mp hs i hi
      · by_cases hzero : A i i = 0
        · exact hz i (mem_zeroDiagonalSites_iff.mpr
            ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hi⟩,hzero⟩)
        · have hv' : (volterra A) (v : Fin s → K) i = 0 := congrFun hk i
          rw [volterra_pivot ha i _ ih] at hv'
          exact (mul_eq_zero.mp hv').resolve_left (neg_ne_zero.mpr (pow_ne_zero 2 hzero))
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective hf

private theorem coordinate_off (i j : Fin s) (h : j ≠ i) :
    Reverse.coordinate (K := K) i j = 0 := by
  classical
  simp [Reverse.coordinate,Pi.single_apply,h,Ne.symm h]

private theorem coordinate_volterra_above (ha : A.IsLowerTriangular)
    (i j : Fin s) (h : j < i) : volterra A (Reverse.coordinate i) j = 0 := by
  have hp : ∀ l, l < j → Reverse.coordinate (K := K) i l = 0 := by
    intro l hl
    exact coordinate_off i l (ne_of_lt (lt_trans hl h))
  rw [volterra_pivot ha j _ hp,coordinate_off i j (ne_of_lt h),mul_zero]

private theorem coordinate_volterra_diagonal (ha : A.IsLowerTriangular) (i : Fin s) :
    volterra A (Reverse.coordinate i) i = -(A i i)^2 := by
  have hp : ∀ j, j < i → Reverse.coordinate (K := K) i j = 0 :=
    fun j hj => coordinate_off i j (ne_of_lt hj)
  rw [volterra_pivot ha i _ hp]
  classical
  simp [Reverse.coordinate]

/-- The dual Volterra kernel supported on S injects into the zero
diagonals of S by the reverse pivot. No output weights are involved. -/
theorem volterra_row_cutKer_le_zeroSites (ha : A.IsLowerTriangular) (S : Finset (Fin s)) :
    finrank K ((cutZeroSpace K S).dualAnnihilator ⊓ (volterra A).dualMap.ker :
      Submodule K (ClockCovector K s)) ≤ (zeroDiagonalSites A S).card := by
  let W : Submodule K (ClockCovector K s) :=
    (cutZeroSpace K S).dualAnnihilator ⊓ (volterra A).dualMap.ker
  let Z := zeroDiagonalSites A S
  let e : (Fin s → K) ≃ₗ[K] ClockCovector K s := Reverse.dotDual
  let g : W →ₗ[K] (Z → K) := (cutRestrict K Z).comp (e.symm.toLinearMap.comp W.subtype)
  have hg : Function.Injective g := by
    apply (injective_iff_map_eq_zero _).mpr
    intro f hf
    let w : Fin s → K := e.symm (f : ClockCovector K s)
    change cutRestrict K Z w = 0 at hf
    have hz := (mem_cutZeroSpace Z w).mp (show w ∈ cutZeroSpace K Z from hf)
    have hann := (Submodule.mem_inf.mp f.property).1
    have hker := (Submodule.mem_inf.mp f.property).2
    change (volterra A).dualMap (f : ClockCovector K s) = 0 at hker
    have hrow (v : Fin s → K) : (f : ClockCovector K s) v = row w v := by
      have h := LinearMap.congr_fun (e.apply_symm_apply (f : ClockCovector K s)) v
      change row w v = (f : ClockCovector K s) v at h
      exact h.symm
    have hs (i : Fin s) (hi : i ∉ S) : w i = 0 := by
      have hcoord : Reverse.coordinate (K := K) i ∈ cutZeroSpace K S := by
        apply (mem_cutZeroSpace S _).mpr
        intro j hj
        exact coordinate_off i j (fun h => hi (h ▸ hj))
      have h := (Submodule.mem_dualAnnihilator _).mp hann _ hcoord
      rwa [hrow,Reverse.row_coordinate] at h
    have hw : ∀ j : Fin s, w j.rev = 0 := by
      intro j
      induction j using Fin.strong_induction_on with
      | _ j ih =>
        let i := j.rev
        change w i = 0
        by_cases hi : i ∈ S
        · by_cases hz' : A i i = 0
          · exact hz i (mem_zeroDiagonalSites_iff.mpr ⟨hi,hz'⟩)
          · have hv : (f : ClockCovector K s) (volterra A (Reverse.coordinate i)) = 0 :=
              LinearMap.congr_fun hker (Reverse.coordinate i)
            rw [hrow,row_apply,dotProduct,Finset.sum_eq_single i] at hv
            · rw [coordinate_volterra_diagonal ha] at hv
              exact (mul_eq_zero.mp hv).resolve_right (neg_ne_zero.mpr (pow_ne_zero 2 hz'))
            · intro l _ hl
              rcases lt_or_gt_of_ne hl with hli | hil
              · rw [coordinate_volterra_above ha i l hli,mul_zero]
              · have he : l.rev < j := by
                  have hl' : l.rev < i.rev := Fin.rev_lt_rev.mpr hil
                  simpa only [i,Fin.rev_rev] using hl'
                have hl' : w l = 0 := by simpa only [Fin.rev_rev] using ih l.rev he
                rw [hl',zero_mul]
            · simp
        · exact hs i hi
    apply Subtype.ext
    apply e.symm.injective
    change w = e.symm (0 : ClockCovector K s)
    rw [map_zero]
    funext i
    change w i = 0
    simpa only [Fin.rev_rev] using hw i.rev
  simpa only [Module.finrank_fintype_fun_eq_card,Fintype.card_coe] using
    LinearMap.finrank_le_finrank_of_injective hg

/-- Both chronological mixed-diagonal cuts with explicit counted-side
zero budgets. The two guards require their own positive effective orders. -/
theorem mixed_chronological_clock_cut (ho : RKResearch.HasOrder p A b)
    (ha : A.IsLowerTriangular) (hk : k ≤ s) :
    (2*(headPhysicalClocks A hk).card < p →
      localNullityCutFloor (p-2*(headPhysicalClocks A hk).card)
        (zeroDiagonalSites A (Finset.univ \ chronologicalHead hk)).card ≤ s-k) ∧
    (2*(tailActiveClocks A b hk).card < p →
      localNullityCutFloor (p-2*(tailActiveClocks A b hk).card)
        (zeroDiagonalSites A (chronologicalHead hk)).card ≤ k) := by
  classical
  let S := chronologicalHead hk
  constructor
  · intro hp
    have h := mixed_head_clock_cut_of_kernel ho ha S (chronologicalHead_downward hk)
      (headPhysicalClocks A hk) hp (fun i hi => Finset.mem_image.mpr ⟨i,hi,rfl⟩)
      (volterra_column_cutKer_le_zeroSites ha S)
    simpa only [S,chronologicalHead_card] using h
  · intro hp
    have hc (i : Fin s) (hi : i ∉ S) (hb : b i ≠ 0) : nodes A i ∈ tailActiveClocks A b hk :=
      Finset.mem_image.mpr
        ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨Finset.mem_univ i,hi⟩,hb⟩,rfl⟩
    have h := mixed_tail_active_clock_cut_of_kernel ho ha S (chronologicalHead_downward hk)
      (tailActiveClocks A b hk) hp hc (volterra_row_cutKer_le_zeroSites ha S)
    simpa only [S,chronologicalHead_card] using h

end
end RKResearch.Certified.Graded
