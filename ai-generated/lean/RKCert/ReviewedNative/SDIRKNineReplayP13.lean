module

public import RKCert.ReviewedNative.SDIRKNineReplayP12
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

theorem pay120 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree120 := by
  refine checked_weight h (t := tree120) (v := point v1 v25) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree22 (numA x y)) = _
  rw [phi1 h, phi22 h, act16 h, point_val h]

theorem pay121 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree121 := by
  refine checked_weight h (t := tree121) (v := point v2 v8) ?_ (by decide +kernel)
  change Φ tree2 (numA x y) * (numA x y *ᵥ Φ tree4 (numA x y)) = _
  rw [phi2 h, phi4 h, act4 h, point_val h]

theorem pay122 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree122 := by
  refine checked_weight h (t := tree122) (v := point v2 v9) ?_ (by decide +kernel)
  change Φ tree2 (numA x y) * (numA x y *ᵥ Φ tree5 (numA x y)) = _
  rw [phi2 h, phi5 h, act5 h, point_val h]

theorem pay123 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree123 := by
  refine checked_weight h (t := tree123) (v := point v2 v10) ?_ (by decide +kernel)
  change Φ tree2 (numA x y) * (numA x y *ᵥ Φ tree6 (numA x y)) = _
  rw [phi2 h, phi6 h, act6 h, point_val h]

theorem pay125 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree125 := by
  refine checked_weight h (t := tree125) (v := point v2 v11) ?_ (by decide +kernel)
  change Φ tree2 (numA x y) * (numA x y *ᵥ Φ tree8 (numA x y)) = _
  rw [phi2 h, phi8 h, act7 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
