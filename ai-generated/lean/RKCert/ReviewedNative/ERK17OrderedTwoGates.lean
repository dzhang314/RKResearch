module

public import RKCert.ReviewedNative.ERK17OrderedConditional
import RKCert.ReviewedNative.PhysicalEndpointMomentPorts

@[expose] public section

/-! # Discharge the ordered ERK17 quartic port using the public two-clock cut

The Radau and origin-mesh gates remain explicit. The existing native
dispatcher and the proof on the original array are unchanged. -/
namespace RKResearch.Certified.ERK17

open RKResearch Polynomial
open RKCert.ReviewedNative.ERK17.Scalar

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The no-origin local tests match the public 3+2 quartic theorem
literally, in both primitive normalization and degree caps. -/
theorem native_ordered_quartic_gate : QuarticGate K := by
  intro Q deg u v hu hv hvu first second
  exact RKCert.EndpointPhysical.ordered_quartic_eq_zero_of_primitives
    deg hu hv hvu ⟨first, second⟩

/-- The checked native conditional endpoint with its quartic premise removed. -/
theorem ordered_erk17_stage_floor27_of_radau_and_mesh
    (radau : RadauFirstGate K)
    (mesh : ∀ (P N : K[X]) (u : K), MeshPorts P N u → False)
    {s : ℕ} {A : Matrix (Fin s) (Fin s) K} {b : Fin s → K}
    (ha : ∀ i j, i ≤ j → A i j = 0) (ho : HasOrder 17 A b) : 27 ≤ s :=
  ordered_erk17_stage_floor27_of_scalar_gates radau native_ordered_quartic_gate mesh ha ho

end RKResearch.Certified.ERK17
