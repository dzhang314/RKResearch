module

public import RKCert.ReviewedNative.SDIRKNineReplayP8
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

theorem pay78 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree78 := by
  refine checked_weight h (t := tree78) (v := point v0 v45) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree36 (numA x y)) = _
  rw [phi0 h, phi36 h, act25 h, point_val h]

theorem pay79 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree79 := by
  refine checked_weight h (t := tree79) (v := point v0 v46) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree37 (numA x y)) = _
  rw [phi0 h, phi37 h, act26 h, point_val h]

theorem pay80 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree80 := by
  refine checked_weight h (t := tree80) (v := point v0 v47) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree38 (numA x y)) = _
  rw [phi0 h, phi38 h, act27 h, point_val h]

theorem pay81 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree81 := by
  refine checked_weight h (t := tree81) (v := point v0 v48) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree39 (numA x y)) = _
  rw [phi0 h, phi39 h, act28 h, point_val h]

theorem pay83 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree83 := by
  refine checked_weight h (t := tree83) (v := point v0 v49) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree41 (numA x y)) = _
  rw [phi0 h, phi41 h, act29 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
