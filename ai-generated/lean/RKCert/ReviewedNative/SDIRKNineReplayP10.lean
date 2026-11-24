module

public import RKCert.ReviewedNative.SDIRKNineReplayP9
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

theorem pay84 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree84 := by
  refine checked_weight h (t := tree84) (v := point v0 v50) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree42 (numA x y)) = _
  rw [phi0 h, phi42 h, act30 h, point_val h]

theorem pay85 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree85 := by
  refine checked_weight h (t := tree85) (v := point v0 v51) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree43 (numA x y)) = _
  rw [phi0 h, phi43 h, act31 h, point_val h]

theorem pay86 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree86 := by
  refine checked_weight h (t := tree86) (v := point v0 v52) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree44 (numA x y)) = _
  rw [phi0 h, phi44 h, act32 h, point_val h]

theorem pay87 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree87 := by
  refine checked_weight h (t := tree87) (v := point v0 v53) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree45 (numA x y)) = _
  rw [phi0 h, phi45 h, act33 h, point_val h]

theorem pay90 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree90 := by
  refine checked_weight h (t := tree90) (v := point v0 v54) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree48 (numA x y)) = _
  rw [phi0 h, phi48 h, act34 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
