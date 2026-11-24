module

public import RKCert.ReviewedNative.SDIRKNineReplayP1
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

theorem pay11 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree11 := by
  exact checked_weight h (t := tree11) (phi11 h) (by decide +kernel)

theorem pay13 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree13 := by
  exact checked_weight h (t := tree13) (phi13 h) (by decide +kernel)

theorem pay14 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree14 := by
  exact checked_weight h (t := tree14) (phi14 h) (by decide +kernel)

theorem pay15 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree15 := by
  exact checked_weight h (t := tree15) (phi15 h) (by decide +kernel)

theorem pay16 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree16 := by
  exact checked_weight h (t := tree16) (phi16 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
