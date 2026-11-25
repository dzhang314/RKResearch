module

public import RKCert.ReviewedNative.ERK17TinySupportDispatch
public import RKCert.ReviewedNative.ERK17BalancedFirstExclusion
public import RKCert.ReviewedNative.ERK17FourPortProducer
public import RKCert.ReviewedNative.ERK17VeryWideProducer
public import RKCert.ReviewedNative.ERK17UnitFourClose

@[expose] public section

/-! # The remaining scalar obligations for the reviewed order-17 stage floor -/

namespace RKResearch.Certified.ERK17

open RKResearch Polynomial RKCert.Endpoint RKCert.Endpoint.WeightedClock
open RKResearch.Certified.Graded RKResearch.Certified.Graded.Reverse
open RKCert.ReviewedNative.ERK17.Scalar

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- At width 26 a nonzero first reverse seed has at least seventeen clocks. -/
theorem ordered_width26_first_seed_zero_or_wide
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) :
    firstSeed A b = 0 ∨ 17 ≤ (weightedSites (reflectedClock A) (firstSeed A b)).card := by
  by_cases zero : firstSeed A b = 0
  · exact Or.inl zero
  · rcases ordered_width26_first_seed_local_or_ge_seventeen ha ho zero with tiny | wide
    · exact False.elim (ordered_width26_tiny_nonzero_first_impossible ha ho zero tiny)
    · exact Or.inr wide

/-- The remaining proof is purely scalar: one native Radau gate
and the two alternatives for a zero-seed four-port packet. -/
theorem ordered_width26_impossible_of_scalar_gates
    (radau : RadauFirstGate K) (quartic : QuarticGate K)
    (mesh : ∀ (P N : K[X]) (u : K), MeshPorts P N u → False)
    {A : Matrix (Fin 26) (Fin 26) K} {b : Fin 26 → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : False := by
  rcases ordered_width26_first_seed_zero_or_wide ha ho with zero | wide
  · obtain ⟨W, θ, P, H⟩ := ordered_width26_physical_four_port radau ha ho zero
    by_cases origin : (0 : K) ∈ sites (nodes A) W
    · obtain ⟨N,u,h⟩ := H.mesh_of_origin ha origin
      exact mesh P N u h
    · exact H.no_origin_of_quartic ha quartic origin
  · have nz : firstSeed A b ≠ 0 := by
      intro z
      rw [z] at wide
      simp [weightedSites] at wide
    let S := (ordered_width26_full_frame ha ho).1
    rcases width26_linear_broad_or_local ha ho S nz with small | B
    · omega
    obtain ⟨W, θ, P, H⟩ := B.very_wide_unit_ports ha ho S nz wide
    exact H.impossible_of_radau ha radau

theorem ordered_erk17_stage_floor27_of_scalar_gates
    (radau : RadauFirstGate K) (quartic : QuarticGate K)
    (mesh : ∀ (P N : K[X]) (u : K), MeshPorts P N u → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s := by
  have floor := ordered_erk17_stage_floor26 ha ho
  by_contra! small
  have width : s = 26 := by omega
  subst s
  exact ordered_width26_impossible_of_scalar_gates radau quartic mesh ha ho

end RKResearch.Certified.ERK17
