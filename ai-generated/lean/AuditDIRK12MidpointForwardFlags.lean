module
import RKCert.ReviewedNative.DIRK12MidpointForwardFlags

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DualSupport12VectorReplay
open scoped Matrix

theorem auditCausalRows {K : Type*} [Field K] [CharZero K]
    (P : Feed K) (a0 : P.a ≠ 0) :
    nodes P.tableau = P.clocks ∧ Matrix.IsLowerTriangular P.tableau ∧
      P.tableau 0 0=0 ∧ P.tableau (hidden 0) (hidden 0) ≠ 0 :=
  ⟨P.nodes_tableau,P.genuine_DIRK a0⟩

theorem auditAdjoint {K : Type*} [Field K] [CharZero K]
    (P : Feed K) (bT : P.b terminal ≠ 0)
    (scalar : ∀ j < 12, ((j+1:Nat):K)*row P.b (P.clocks^j)=1) :
    mat P.tableau.transpose P.b=P.b*(1-P.clocks) := by
  apply P.paid_adjoint bT
  · simpa using scalar 0 (by decide)
  · simpa using scalar 1 (by decide)

theorem auditForwardSlice {K : Type*} [Field K] [CharZero K]
    (P : Feed K) (bT : P.b terminal ≠ 0)
    (bG : ∀ g : Fin 4, P.b (hidden g)=0)
    (scalar : ∀ j < 12, ((j+1:Nat):K)*row P.b (P.clocks^j)=1)
    (live : P.LiveBudget) :
    (∀ j ≤ 2, forwardBand K j=⊥) ∧
    (∀ j ≤ 5, ∀ v ∈ forwardBand K j, DualSupport12.supported ghost v) ∧
    (∀ j < 5, ∀ v ∈ forwardBand K j, mat P.tableau v ∈ forwardBand K (j+1)) ∧
    (∀ j < 5, ∀ v ∈ forwardBand K j, nodes P.tableau*v ∈ forwardBand K (j+1)) ∧
    (∀ j < 5, DualSupport12.forward P.tableau j ∈ forwardBand K (j+1)) :=
  ⟨fw_zero,fun j _ => fw_support j,P.fw_A bT bG (auditAdjoint P bT scalar),P.fw_C,
    P.fw_primitive bT bG (auditAdjoint P bT scalar) scalar live⟩

#print axioms auditCausalRows
#print axioms auditAdjoint
#print axioms auditForwardSlice
