module

public import RKCert.ReviewedNative.SDIRKNineReplayP4
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

theorem pay36 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree36 := by
  exact checked_weight h (t := tree36) (phi36 h) (by decide +kernel)

theorem pay37 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree37 := by
  exact checked_weight h (t := tree37) (phi37 h) (by decide +kernel)

theorem pay38 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree38 := by
  exact checked_weight h (t := tree38) (phi38 h) (by decide +kernel)

theorem pay39 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree39 := by
  exact checked_weight h (t := tree39) (phi39 h) (by decide +kernel)

theorem pay41 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree41 := by
  exact checked_weight h (t := tree41) (phi41 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
