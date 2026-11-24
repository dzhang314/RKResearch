module

public import RKCert.ReviewedNative.SDIRKNineReplayP11
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

theorem pay111 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree111 := by
  refine checked_weight h (t := tree111) (v := point v1 v20) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree13 (numA x y)) = _
  rw [phi1 h, phi13 h, act11 h, point_val h]

theorem pay112 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree112 := by
  refine checked_weight h (t := tree112) (v := point v1 v21) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree14 (numA x y)) = _
  rw [phi1 h, phi14 h, act12 h, point_val h]

theorem pay113 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree113 := by
  refine checked_weight h (t := tree113) (v := point v1 v22) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree15 (numA x y)) = _
  rw [phi1 h, phi15 h, act13 h, point_val h]

theorem pay114 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree114 := by
  refine checked_weight h (t := tree114) (v := point v1 v23) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree16 (numA x y)) = _
  rw [phi1 h, phi16 h, act14 h, point_val h]

theorem pay115 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree115 := by
  refine checked_weight h (t := tree115) (v := point v1 v24) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree17 (numA x y)) = _
  rw [phi1 h, phi17 h, act15 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
