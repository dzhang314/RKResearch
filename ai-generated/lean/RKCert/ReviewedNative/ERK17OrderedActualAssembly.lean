module

public import RKCert.ReviewedNative.ERK17OrderedTwoGates
public import RKCert.ReviewedNative.OrderedOriginPositiveClock
public import RKCert.ReviewedNative.StagePadding

import Lean.Elab.Tactic.Omega

@[expose] public section

/-! # Exact-width exclusion using the two true chronological windows

After the zero/wide split, only actual original-row packets are used.
In particular there is no assertion that an abstract MeshPorts has
enough reverse chronology.
-/
namespace RKResearch.Certified.ERK17

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKResearch.Certified.StagePadding
open RKCert.Endpoint.WeightedClock RKCert.ReviewedNative.OriginSignedSquares

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact two still-separate pure scalar inputs, on the actual array. -/
theorem ordered_width26_impossible_of_actual_origin_gates
    (radau : RadauFirstGate K) (smallest : NoSmallestClock K)
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : False := by
  rcases ordered_width26_first_seed_zero_or_wide ha ho with zero | wide
  · obtain ⟨W,θ,P,H,rows,trace⟩ := ordered_width26_actual_four_port radau ha ho zero
    by_cases origin : (0 : K) ∈ sites (nodes A) W
    · obtain ⟨u,v,w,T⟩ := H.actual_two_sided_origin ha origin rows trace
      exact TwoSidedThreeClockMoments.impossible_of_positive_and_not_smallest
        positiveFirstClock_of_finite_sign smallest T
    · exact H.no_origin_of_quartic ha native_ordered_quartic_gate origin
  · have nz : firstSeed A b ≠ 0 := by
      intro z
      rw [z] at wide
      simp [weightedSites] at wide
    let S := (ordered_width26_full_frame ha ho).1
    rcases width26_linear_broad_or_local ha ho S nz with small | B
    · omega
    obtain ⟨W,θ,P,H⟩ := B.very_wide_unit_ports ha ho S nz wide
    exact H.impossible_of_radau ha radau

/-- Reviewed zero padding transfers the exact-width exclusion to all
smaller widths. It preserves the original elementary weights literally. -/
theorem ordered_erk17_stage_floor27_of_actual_origin_gates
    (radau : RadauFirstGate K) (smallest : NoSmallestClock K)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  Nat.succ_le_of_lt (strict_stages_gt_of_exact_exclusion (n:=26) (p:=17)
    (fun _ _ hT hW => ordered_width26_impossible_of_actual_origin_gates radau smallest hT hW)
    ha ho)

end RKResearch.Certified.ERK17
