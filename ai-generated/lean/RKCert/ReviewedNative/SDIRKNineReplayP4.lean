module

public import RKCert.ReviewedNative.SDIRKNineReplayP3
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

theorem pay27 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree27 := by
  exact checked_weight h (t := tree27) (phi27 h) (by decide +kernel)

theorem pay28 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree28 := by
  exact checked_weight h (t := tree28) (phi28 h) (by decide +kernel)

theorem pay29 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree29 := by
  exact checked_weight h (t := tree29) (phi29 h) (by decide +kernel)

theorem pay30 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree30 := by
  exact checked_weight h (t := tree30) (phi30 h) (by decide +kernel)

theorem pay31 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree31 := by
  exact checked_weight h (t := tree31) (phi31 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
