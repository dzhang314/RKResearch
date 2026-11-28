module
import RKCert.ReviewedNative.DIRK12MidpointRealForwardWiring

open RKResearch RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DIRK12MidpointRealInterval RKResearch.Certified.DirectedRatBox
open scoped Matrix

theorem auditLiteralRealForward (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x = 0) (hf0 : realF x f = 0) :
    let P := realFeed x f alpha mu nu L
    Matrix.IsLowerTriangular P.tableau ∧
    P.tableau (hidden 0) (hidden 0)=1/16 ∧
    P.tableau terminal terminal=0 ∧
    nodes P.tableau = P.clocks ∧
    (∀ i, ¬ ghostRow i → P.b i≠0) ∧
    mat P.tableau.transpose P.b=P.b*(1-P.clocks) ∧
    (∀ j < 12, ((j+1:Nat):ℝ)*row P.b (P.clocks^j)=1) ∧
    (∀ m : Fin 4, DualSupport12.forward P.tableau (m.val+1) (visible 0)=0) ∧
    (∀ j < 5, ∀ v ∈ forwardBand ℝ j, mat P.tableau v ∈ forwardBand ℝ (j+1)) ∧
    ¬ HasOrder 13 P.tableau P.b :=
  ⟨(real_DIRK x f alpha mu nu L).1,literal_second_diag x f alpha mu nu L,
    literal_terminal_diag x f alpha mu nu L,(realFeed x f alpha mu nu L).nodes_tableau,
    real_weight_guard x f alpha mu nu L hx hf,real_adjoint x f alpha mu nu L hx hf hx0 hf0,
    real_scalar x f alpha mu nu L hx hf hx0 hf0,first_live_primitive x f alpha mu nu L,
    real_fw_A x f alpha mu nu L hx hf hx0 hf0,real_not_order13 x f alpha mu nu L hx hf hx0 hf0⟩

#print axioms auditLiteralRealForward
