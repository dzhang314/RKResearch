module
import RKCert.ReviewedNative.DIRK12MidpointGhostImageBridge

open RKResearch.Certified.Graded RKResearch.Certified.DIRK12MidpointForward
open RKResearch.Certified.DualSupport12VectorReplay
open RKResearch.Certified.DIRK12MidpointRealInterval RKResearch.Certified.DirectedRatBox

theorem auditActualAG5 (x f alpha mu nu : ℝ) (L : Fin 10 → Fin 10 → ℝ)
    (hx : Encloses xBox x) (hf : Encloses fBox f) (hx0 : realX x=0) (hf0 : realF x f=0)
    (B : Nat → Submodule ℝ (Fin 15 → ℝ))
    (silent : ∀ z∈B 5, ∀ k≤6, row z ((nodes (realFeed x f alpha mu nu L).tableau)^k)=0)
    (ghosts : ∀ z∈B 5, DualSupport12.zeroAt ghost z)
    (last : ∀ z∈B 5, z terminal=0) :
    let P := realFeed x f alpha mu nu L
    ∀ w ∈ forwardBand ℝ 5, mat P.tableau w ∈ DualSupport12.high P.tableau P.b B 5 :=
  real_AG5_bridge x f alpha mu nu L hx hf hx0 hf0 B silent ghosts last

#print axioms auditActualAG5
