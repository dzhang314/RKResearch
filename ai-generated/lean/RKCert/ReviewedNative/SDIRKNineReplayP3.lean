module

public import RKCert.ReviewedNative.SDIRKNineReplayP2
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

theorem pay17 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree17 := by
  exact checked_weight h (t := tree17) (phi17 h) (by decide +kernel)

theorem pay22 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree22 := by
  exact checked_weight h (t := tree22) (phi22 h) (by decide +kernel)

theorem pay23 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree23 := by
  exact checked_weight h (t := tree23) (phi23 h) (by decide +kernel)

theorem pay24 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree24 := by
  exact checked_weight h (t := tree24) (phi24 h) (by decide +kernel)

theorem pay25 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree25 := by
  exact checked_weight h (t := tree25) (phi25 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
