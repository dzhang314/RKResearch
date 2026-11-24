module

public import RKCert.ReviewedNative.SDIRKNineReplayP13
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

theorem pay126 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree126 := by
  refine checked_weight h (t := tree126) (v := point v3 v8) ?_ (by decide +kernel)
  change Φ tree3 (numA x y) * (numA x y *ᵥ Φ tree4 (numA x y)) = _
  rw [phi3 h, phi4 h, act4 h, point_val h]

theorem pay127 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree127 := by
  refine checked_weight h (t := tree127) (v := point v3 v9) ?_ (by decide +kernel)
  change Φ tree3 (numA x y) * (numA x y *ᵥ Φ tree5 (numA x y)) = _
  rw [phi3 h, phi5 h, act5 h, point_val h]

theorem pay128 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree128 := by
  refine checked_weight h (t := tree128) (v := point v3 v10) ?_ (by decide +kernel)
  change Φ tree3 (numA x y) * (numA x y *ᵥ Φ tree6 (numA x y)) = _
  rw [phi3 h, phi6 h, act6 h, point_val h]

theorem pay130 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree130 := by
  refine checked_weight h (t := tree130) (v := point v3 v11) ?_ (by decide +kernel)
  change Φ tree3 (numA x y) * (numA x y *ᵥ Φ tree8 (numA x y)) = _
  rw [phi3 h, phi8 h, act7 h, point_val h]

theorem pay131 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree131 := by
  refine checked_weight h (t := tree131) (v := point v4 v4) ?_ (by decide +kernel)
  change Φ tree4 (numA x y) * (numA x y *ᵥ Φ tree2 (numA x y)) = _
  rw [phi4 h, phi2 h, act2 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
