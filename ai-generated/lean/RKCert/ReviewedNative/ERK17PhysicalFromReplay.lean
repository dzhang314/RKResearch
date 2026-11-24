module

public import RKCert.ReviewedNative.ERK17PhysicalPorts
public import Mathlib.Algebra.Order.Field.Basic
import RKCert.ReviewedNative.ERK17ScalarFromReplay
import RKCert.ERKEightPureContrast

@[expose] public section

/-! # Exclude the four-port geometric data over an ordered field

Only the scalar conclusion of the legacy quartic lemma is used. The
chronological selection, matrix-vector action, and signed quadrature live
in the native producer module. -/
namespace RKResearch.Certified.ERK17

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.ERK17.Scalar
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem ordered_quartic_gate : QuarticGate K := by
  intro Q d u v hu hv hne h₁ h₂
  refine ordered_quartic_physical Q d hu hv hne ?_ ?_
  · intro R r
    simpa only [formalPrimitive_eq_treePrimitive] using h₁ R r
  · intro R r
    simpa only [formalPrimitive_eq_treePrimitive] using h₂ R r

/-- The native exact-width proof need only produce the physical four-port
record on its zero-seed branch. This theorem does not establish that production. -/
theorem no_physical_four_port {s : ℕ} {A : Matrix (Fin (s+1)) (Fin (s+1)) K}
    {w θ : Fin (s+1) → K} {P : K[X]} (ha : ∀ i j, i ≤ j → A i j = 0) :
    ¬ PhysicalFourPort A w θ P := by
  intro B
  classical
  by_cases origin : (0:K) ∈ sites (Graded.nodes A) w
  · obtain ⟨N,u,h⟩ := B.mesh_of_origin ha origin
    exact no_mesh_ports h
  · exact B.no_origin_of_quartic ha ordered_quartic_gate origin

end RKResearch.Certified.ERK17
