import RKResearch.OrderConditions
import RKCert.ReviewedNative.ERK17ScalarFromReplay
import RKCert.ReviewedNative.JacobiMomentBand

open Polynomial RKCert.Endpoint
open RKCert.ReviewedNative.JacobiMoments RKCert.ReviewedNative.ERK17.Scalar
open scoped Matrix

-- Independent small client, with the actual reviewed matrix clock convention.
-- The hypotheses are exactly the outstanding scalar output of a geometry proof.
example {K : Type*} [Field K] [CharZero K] (A : Matrix (Fin 26) (Fin 26) K)
    (w : Fin 26 → K) (P : K[X]) (u : K) (B : LocalPaid P u) (pd : P.natDegree ≤ 5)
    (S : Finset K) (small : S.card ≤ 3) (member : u ∈ S)
    (cover : ∀ i, w i ≠ 0 → (A *ᵥ 1) i = 0 ∨ (A *ᵥ 1) i ∈ S)
    (rule : ∀ R : K[X], R.natDegree ≤ 10 →
      (formalPrimitive (R*((1-X)*P))).eval 1 = ∑ i, R.eval ((A *ᵥ 1) i)*w i) :
    False :=
  no_mesh_ports (MeshPorts.of_quadrature B pd (A *ᵥ 1) w S small member cover rule)

-- The degree-seven instance needed in the order-fifteen pencil has no p17 premise.
example {K : Type*} [Field K] [CharZero K] (D : K[X]) (d : D.natDegree ≤ 7)
    (h : MomentDifferences D 5) :
    ∃ v w : K, D = C v*signedSlope K 8 + C w*signedSlope K 7 :=
  signedSlope_band (r:=5) d h

#check @RKResearch.HasOrder
#check @RKCert.ReviewedNative.JacobiMoments.signedSlope_band
#check @RKCert.ReviewedNative.ERK17.Scalar.MeshPorts.of_quadrature
#check @RKCert.ReviewedNative.ERK17.Scalar.no_pencil_ports
#check @RKCert.ReviewedNative.ERK17.Scalar.no_mesh_ports

#print axioms RKCert.ReviewedNative.JacobiMoments.signedSlope_band
#print axioms RKCert.ReviewedNative.ERK17.Scalar.MeshPorts.of_quadrature
#print axioms RKCert.ReviewedNative.ERK17.Scalar.no_pencil_ports
#print axioms RKCert.ReviewedNative.ERK17.Scalar.no_mesh_ports
