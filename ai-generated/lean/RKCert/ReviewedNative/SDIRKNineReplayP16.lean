module

public import RKCert.ReviewedNative.SDIRKNineReplayP15
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

theorem pay140 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree140 := by
  refine checked_weight h (t := tree140) (v := point v7 v5) ?_ (by decide +kernel)
  change Φ tree8 (numA x y) * (numA x y *ᵥ Φ tree3 (numA x y)) = _
  rw [phi8 h, phi3 h, act3 h, point_val h]

theorem pay148 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree148 := by
  refine checked_weight h (t := tree148) (v := point v14 v2) ?_ (by decide +kernel)
  change Φ tree16 (numA x y) * (numA x y *ᵥ Φ tree1 (numA x y)) = _
  rw [phi16 h, phi1 h, act1 h, point_val h]

theorem pay149 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree149 := by
  refine checked_weight h (t := tree149) (v := point v15 v2) ?_ (by decide +kernel)
  change Φ tree17 (numA x y) * (numA x y *ᵥ Φ tree1 (numA x y)) = _
  rw [phi17 h, phi1 h, act1 h, point_val h]

theorem pay154 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree154 := by
  refine checked_weight h (t := tree154) (v := point v16 v2) ?_ (by decide +kernel)
  change Φ tree22 (numA x y) * (numA x y *ᵥ Φ tree1 (numA x y)) = _
  rw [phi22 h, phi1 h, act1 h, point_val h]

theorem pay196 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree196 := by
  refine checked_weight h (t := tree196) (v := point v36 v1) ?_ (by decide +kernel)
  change Φ tree64 (numA x y) * (numA x y *ᵥ Φ tree0 (numA x y)) = _
  rw [phi64 h, phi0 h, act0 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
