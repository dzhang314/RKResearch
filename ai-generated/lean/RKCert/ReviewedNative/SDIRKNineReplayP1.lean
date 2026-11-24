module

public import RKCert.ReviewedNative.SDIRKNineReplayP0
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

theorem pay5 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree5 := by
  exact checked_weight h (t := tree5) (phi5 h) (by decide +kernel)

theorem pay6 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree6 := by
  exact checked_weight h (t := tree6) (phi6 h) (by decide +kernel)

theorem pay8 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree8 := by
  exact checked_weight h (t := tree8) (phi8 h) (by decide +kernel)

theorem pay9 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree9 := by
  exact checked_weight h (t := tree9) (phi9 h) (by decide +kernel)

theorem pay10 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree10 := by
  exact checked_weight h (t := tree10) (phi10 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
