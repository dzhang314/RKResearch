module

public import RKCert.ReviewedNative.SDIRKNineReplayP5
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

theorem pay42 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree42 := by
  exact checked_weight h (t := tree42) (phi42 h) (by decide +kernel)

theorem pay43 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree43 := by
  exact checked_weight h (t := tree43) (phi43 h) (by decide +kernel)

theorem pay44 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree44 := by
  exact checked_weight h (t := tree44) (phi44 h) (by decide +kernel)

theorem pay45 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree45 := by
  exact checked_weight h (t := tree45) (phi45 h) (by decide +kernel)

theorem pay48 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree48 := by
  exact checked_weight h (t := tree48) (phi48 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
