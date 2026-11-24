module

public import RKCert.ReviewedNative.SDIRKNineReplayP14
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

theorem pay132 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree132 := by
  refine checked_weight h (t := tree132) (v := point v4 v5) ?_ (by decide +kernel)
  change Φ tree4 (numA x y) * (numA x y *ᵥ Φ tree3 (numA x y)) = _
  rw [phi4 h, phi3 h, act3 h, point_val h]

theorem pay134 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree134 := by
  refine checked_weight h (t := tree134) (v := point v5 v5) ?_ (by decide +kernel)
  change Φ tree5 (numA x y) * (numA x y *ᵥ Φ tree3 (numA x y)) = _
  rw [phi5 h, phi3 h, act3 h, point_val h]

theorem pay135 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree135 := by
  refine checked_weight h (t := tree135) (v := point v6 v4) ?_ (by decide +kernel)
  change Φ tree6 (numA x y) * (numA x y *ᵥ Φ tree2 (numA x y)) = _
  rw [phi6 h, phi2 h, act2 h, point_val h]

theorem pay136 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree136 := by
  refine checked_weight h (t := tree136) (v := point v6 v5) ?_ (by decide +kernel)
  change Φ tree6 (numA x y) * (numA x y *ᵥ Φ tree3 (numA x y)) = _
  rw [phi6 h, phi3 h, act3 h, point_val h]

theorem pay139 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree139 := by
  refine checked_weight h (t := tree139) (v := point v7 v4) ?_ (by decide +kernel)
  change Φ tree8 (numA x y) * (numA x y *ᵥ Φ tree2 (numA x y)) = _
  rw [phi8 h, phi2 h, act2 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
