module

public import RKCert.ReviewedNative.SDIRKNineReplayP6
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

theorem pay50 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree50 := by
  exact checked_weight h (t := tree50) (phi50 h) (by decide +kernel)

theorem pay64 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree64 := by
  exact checked_weight h (t := tree64) (phi64 h) (by decide +kernel)

theorem pay65 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree65 := by
  refine checked_weight h (t := tree65) (v := point v0 v37) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree23 (numA x y)) = _
  rw [phi0 h, phi23 h, act17 h, point_val h]

theorem pay66 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree66 := by
  refine checked_weight h (t := tree66) (v := point v0 v38) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree24 (numA x y)) = _
  rw [phi0 h, phi24 h, act18 h, point_val h]

theorem pay67 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree67 := by
  refine checked_weight h (t := tree67) (v := point v0 v39) ?_ (by decide +kernel)
  change Φ tree0 (numA x y) * (numA x y *ᵥ Φ tree25 (numA x y)) = _
  rw [phi0 h, phi25 h, act19 h, point_val h]


end RKResearch.Certified.SDIRKNineReplay
