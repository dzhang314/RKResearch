module

public import RKCert.ReviewedNative.SDIRKNineReplayP10
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

theorem pay92 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree92 := by
  refine checked_weight h (t := tree92) (v := point v0 v55) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree50 (numA x y)) = _
  rw [phi0 h, phi50 h, act35 h, point_val h]

theorem pay106 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree106 := by
  refine checked_weight h (t := tree106) (v := point v0 v56) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree64 (numA x y)) = _
  rw [phi0 h, phi64 h, act36 h, point_val h]

theorem pay107 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree107 := by
  refine checked_weight h (t := tree107) (v := point v1 v17) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree9 (numA x y)) = _
  rw [phi1 h, phi9 h, act8 h, point_val h]

theorem pay108 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree108 := by
  refine checked_weight h (t := tree108) (v := point v1 v18) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree10 (numA x y)) = _
  rw [phi1 h, phi10 h, act9 h, point_val h]

theorem pay109 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree109 := by
  refine checked_weight h (t := tree109) (v := point v1 v19) ?_ (by decide +kernel)
  change Φ tree1 (numA x y) * (numA x y *ᵥ Φ tree11 (numA x y)) = _
  rw [phi1 h, phi11 h, act10 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
