module

public import RKCert.ReviewedNative.SDIRKNineReplayC10
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.IntervalCases

@[expose] public section

namespace RKResearch.Certified.SDIRKNineReplay

open RKResearch FiniteRootedTree
open RKCert.ReviewedNative.IntegerHornerCertificate
open RKCert.ReviewedNative.QuadraticHornerReplay
open scoped Matrix FiniteRootedTree

set_option maxHeartbeats 4500000
set_option maxRecDepth 12000

/-- The homogeneous numerator weight identity for a reviewed tree. -/
abbrev Paid {R : Type*} [CommRing R] (x y : R) (t : FiniteRootedTree) : Prop :=
  (t.factorial:R) * (VecVal x y rawB ⬝ᵥ Φ t (numA x y)) =
    (weightDen:R) * ((stageDen:R)*x)^((t.order:ℕ)-1)

end RKResearch.Certified.SDIRKNineReplay
