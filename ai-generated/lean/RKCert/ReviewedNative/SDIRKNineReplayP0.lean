module

public import RKCert.ReviewedNative.SDIRKNineReplayPay
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

theorem pay0 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree0 := by
  exact checked_weight h (t := tree0) (phi0 h) (by decide +kernel)

theorem pay1 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree1 := by
  exact checked_weight h (t := tree1) (phi1 h) (by decide +kernel)

theorem pay2 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree2 := by
  exact checked_weight h (t := tree2) (phi2 h) (by decide +kernel)

theorem pay3 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree3 := by
  exact checked_weight h (t := tree3) (phi3 h) (by decide +kernel)

theorem pay4 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Paid x y tree4 := by
  exact checked_weight h (t := tree4) (phi4 h) (by decide +kernel)


end RKResearch.Certified.SDIRKNineReplay
