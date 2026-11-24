module
public import RKCert.ReviewedNative.LocalLinearBand
public import RKCert.ReviewedNative.ERK19BroadPorts

@[expose] public section

/-! # Actual local reverse frame for the remaining nonzero ERK19 branch -/
namespace RKResearch.Certified.ERK19
open RKResearch Module Graded Graded.Reverse RKCert.Endpoint.WeightedClock
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {A : Matrix (Fin 29) (Fin 29) K} {b : Fin 29→K}

theorem width29_nonzero_local_first_frame (ha : ∀ i j,i ≤ j → A i j=0)
    (ho : HasOrder 19 A b) (nz : firstSeed A b≠0) :
    ∃ r U τ, LocalLinearBand A b 8 r U τ ∧
      primitiveBack A b 8=annih (treeSpace A 9) ∧
      10-r≤(weightedSites (reflectedClock A) τ).card := by
  have h := (ordered_width29_frame ha ho).1
  have rank (n : ℕ) (hn : n≤8) : finrank K (primitiveBack A b n)=n+1 := by
    obtain ⟨r,e⟩ := h.reverse.flagExact n hn
    rw [←e,r,first_dim_one nz]
  obtain ⟨r,U,w,F⟩ := local_linear_band_of_paid_ranks (by decide : 3≤8) nz
    (width29_nonzero_first_seed_at_most_two ha ho nz) rank
    (fun n lo hi=>width29_reverse_clock_escape ha ho lo hi)
  exact ⟨r,U,w,F,(h.reverse.flagExact 8 (by decide)).2.symm.trans (h.reverse.firstNonzero nz),
    by have a := F.site_count; rcases F.coreRank with t|t <;> omega⟩

end RKResearch.Certified.ERK19
