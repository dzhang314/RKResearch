module

public import RKCert.ReviewedNative.SDIRKNineReplayC8
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

theorem phi54 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree54 (numA x y) = VecVal x y v28 := by
  rw [← phi39 h]
  change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree7 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree6 (numA x y)))
  rw [phi7 h, phi0 h, phi6 h, act6 h, act0 h]
  all_goals ac_rfl

theorem phi55 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree55 (numA x y) = VecVal x y v29 := by
  rw [← phi41 h]
  change (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree8 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree8 (numA x y)))
  rw [phi8 h, phi0 h, act7 h, act0 h]
  all_goals ac_rfl

theorem phi56 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree56 (numA x y) = VecVal x y v32 := by
  rw [← phi44 h]
  change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
  rw [phi0 h, phi2 h, act0 h, act2 h]
  all_goals ac_rfl

theorem phi57 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree57 (numA x y) = VecVal x y v33 := by
  rw [← phi45 h]
  change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
  rw [phi0 h, phi3 h, act0 h, act3 h]
  all_goals ac_rfl

theorem phi58 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree58 (numA x y) = VecVal x y v34 := by
  rw [← phi48 h]
  change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
  rw [phi1 h, phi0 h, act1 h, act0 h]
  all_goals ac_rfl

theorem phi59 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree59 (numA x y) = VecVal x y v35 := by
  rw [← phi50 h]
  change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
  rw [phi0 h, phi1 h, act0 h, act1 h]
  all_goals ac_rfl

theorem phi60 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree60 (numA x y) = VecVal x y v32 := by
  rw [← phi44 h]
  change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree2 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree2 (numA x y)))
  rw [phi2 h, phi0 h, act2 h, act0 h]
  all_goals ac_rfl

theorem phi61 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree61 (numA x y) = VecVal x y v33 := by
  rw [← phi45 h]
  change ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree3 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = ((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree3 (numA x y)))
  rw [phi3 h, phi0 h, act3 h, act0 h]
  all_goals ac_rfl

theorem phi62 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree62 (numA x y) = VecVal x y v35 := by
  rw [← phi50 h]
  change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
  rw [phi0 h, phi1 h, act0 h, act1 h]
  all_goals ac_rfl

theorem phi63 {R : Type*} [CommRing R] {x y : R} (h : RootPair x y) : Φ tree63 (numA x y) = VecVal x y v35 := by
  rw [← phi50 h]
  change (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree1 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) = (((((1 : Fin 9 → R) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree0 (numA x y))) * (numA x y *ᵥ Φ tree1 (numA x y)))
  rw [phi1 h, phi0 h, act1 h, act0 h]
  all_goals ac_rfl


end RKResearch.Certified.SDIRKNineReplay
